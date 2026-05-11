"""
Harris County, Texas – Motivated Seller Lead Scraper
=====================================================
Targets:
  • Harris County Clerk Real Property portal  → RP.aspx  (Playwright)
  • Harris County Clerk Foreclosures portal   → FRCL_R.aspx (Playwright)
  • HCAD bulk parcel data                     → pdata.hcad.org (requests)

Confirmed portal URLs (live as of 2025):
  Real Property  : https://www.cclerk.hctx.net/applications/websearch/RP.aspx
  Foreclosures   : https://www.cclerk.hctx.net/applications/websearch/FRCL_R.aspx

Lead types: LP, NOFC, TAXDEED, JUD, CCJ, DRJUD, LNCORPTX, LNIRS, LNFED,
            LN, LNMECH, LNHOA, MEDLN, PRO, NOC, RELLP
"""

from __future__ import annotations

import asyncio
import csv
import json
import logging
import os
import re
import sys
import time
import traceback
import zipfile
from datetime import datetime, timedelta, timezone
from pathlib import Path

import requests
from bs4 import BeautifulSoup

try:
    from dbfread import DBF
    HAS_DBF = True
except ImportError:
    HAS_DBF = False

try:
    from playwright.async_api import async_playwright, TimeoutError as PWTimeout
    HAS_PW = True
except ImportError:
    HAS_PW = False

# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.StreamHandler(sys.stdout)],
)
log = logging.getLogger("harris_scraper")

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------
LOOKBACK_DAYS: int = int(os.getenv("LOOKBACK_DAYS", "14"))

# Confirmed live URLs
CLERK_BASE      = "https://www.cclerk.hctx.net"
CLERK_RP_URL    = "https://www.cclerk.hctx.net/applications/websearch/RP.aspx"
CLERK_FRCL_URL  = "https://www.cclerk.hctx.net/applications/websearch/FRCL_R.aspx"

# HCAD
HCAD_BULK_PAGE  = "https://pdata.hcad.org/download/index.html"

# Output paths
ROOT           = Path(__file__).resolve().parent.parent
DASHBOARD_JSON = ROOT / "dashboard" / "records.json"
DATA_JSON      = ROOT / "data" / "records.json"
GHL_CSV        = ROOT / "data" / "ghl_export.csv"
TMP_DIR        = ROOT / "tmp"

# Doc-type map  ->  (category, human label)
DOC_TYPE_MAP: dict[str, tuple[str, str]] = {
    "L/P":    ("lp",          "Lis Pendens"),
    "JUDGE":  ("jud",         "Judgment"),
    "A/J":    ("jud",         "Abstract of Judgment"),
    "LIEN":   ("lien",        "Lien"),
    "T/L":    ("lien",        "Tax Lien"),
    "PROB":   ("probate",     "Probate Document"),
    "REL":    ("rellp",       "Release"),
    "NOTICE": ("noc",         "Notice"),
    "DECREE": ("jud",         "Divorce Decree"),
    "BNKRCY": ("lp",          "Bankruptcy"),
    "NOFC":   ("foreclosure", "Notice of Foreclosure"),
}

# NOFC comes from FRCL_R.aspx (year/month dropdowns), not RP.aspx
FRCL_TYPES: set[str] = {"NOFC"}

TARGET_CODES = [c for c in DOC_TYPE_MAP.keys() if c not in FRCL_TYPES]

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
def _parse_date(raw: str) -> str:
    if not raw:
        return ""
    raw = raw.strip()
    for fmt in ("%m/%d/%Y", "%Y-%m-%d", "%m-%d-%Y", "%d/%m/%Y", "%B %d, %Y"):
        try:
            return datetime.strptime(raw, fmt).strftime("%Y-%m-%d")
        except ValueError:
            continue
    m = re.search(r"(\d{1,2})[/\-](\d{1,2})[/\-](\d{2,4})", raw)
    if m:
        mm, dd, yy = m.groups()
        yy = "20" + yy if len(yy) == 2 else yy
        return f"{yy}-{mm.zfill(2)}-{dd.zfill(2)}"
    return raw


def _parse_amount(raw: str) -> float | None:
    if not raw:
        return None
    clean = re.sub(r"[^\d.]", "", raw)
    try:
        return float(clean) if clean else None
    except ValueError:
        return None


def _extract_address_from_legal(legal: str) -> str:
    if not legal:
        return ""
    m = re.search(
        r'\b(\d{1,5})\s+([NSEW]\s+)?([A-Z][A-Z0-9\s]{2,30}(?:ST|AVE|BLVD|DR|LN|RD|WAY|CT|PL|TRL|FWY|PKWY|HWY|CIR|LOOP))\b',
        legal.upper()
    )
    if m:
        return m.group(0).strip()
    return ""


def _deduplicate(records: list[dict]) -> list[dict]:
    """Deduplicate by doc_num alone — catches cross-chunk duplicates."""
    seen: set[str] = set()
    out: list[dict] = []
    for rec in records:
        doc_num = rec.get("doc_num", "")
        key = doc_num if doc_num else f"{rec.get('doc_type','')}:{rec.get('owner','')}:{rec.get('filed','')}"
        if key not in seen:
            seen.add(key)
            out.append(rec)
    log.info("Dedup: %d raw -> %d unique", len(records), len(out))
    return out


# ---------------------------------------------------------------------------
# Score calculator
# ---------------------------------------------------------------------------
def compute_score(rec: dict) -> tuple[int, list[str]]:
    flags: list[str] = []
    score = 30
    doc_type  = rec.get("doc_type", "")
    cat       = rec.get("cat", "")
    amount    = rec.get("amount") or 0
    filed_str = rec.get("filed", "")
    owner     = rec.get("owner", "") or ""
    prop_addr = rec.get("prop_address", "") or ""

    if doc_type in ("L/P", "REL"):
        flags.append("Lis pendens")
    if doc_type in ("NOFC", "TAXDEED"):
        flags.append("Pre-foreclosure")
    if cat == "jud":
        flags.append("Judgment lien")
    if doc_type in ("T/L", "TAXDEED"):
        flags.append("Tax lien")
    if doc_type == "LIEN":
        flags.append("Mechanic lien")
    if cat == "probate":
        flags.append("Probate / estate")
    if doc_type == "BNKRCY":
        flags.append("Bankruptcy")
    if re.search(r"\b(LLC|INC|CORP|LTD|LP|LLP|PLLC|TRUST)\b", owner, re.I):
        flags.append("LLC / corp owner")

    try:
        filed_dt = datetime.strptime(filed_str[:10], "%Y-%m-%d")
        if (datetime.utcnow() - filed_dt).days <= 14:
            flags.append("New this week")
    except Exception:
        pass

    score += 10 * len(flags)

    has_lp = any("lis pendens" in f.lower() for f in flags)
    has_fc = any("pre-foreclosure" in f.lower() for f in flags)
    if has_lp and has_fc:
        score += 20

    try:
        amt = float(amount)
        if amt > 100_000:
            score += 15
        elif amt > 50_000:
            score += 10
    except (TypeError, ValueError):
        pass

    if "New this week" in flags:
        score += 5
    if prop_addr and prop_addr.strip():
        score += 5

    return min(score, 100), list(dict.fromkeys(flags))


# ---------------------------------------------------------------------------
# HCAD Parcel Lookup
# ---------------------------------------------------------------------------
class ParcelLookup:
    def __init__(self):
        self._idx: dict[str, dict] = {}
        self._prefix_idx: dict[str, dict] = {}
        self._loaded = False

    def _normalise(self, name: str) -> str:
        return re.sub(r"\s+", " ", name.upper().strip())

    def load(self):
        single = ROOT / "data" / "hcad_lookup.csv.gz"
        parts  = [ROOT / "data" / f"hcad_lookup_part{i}.csv.gz" for i in range(1, 4)]

        files_to_load = []
        if single.exists() and single.stat().st_size > 1000:
            files_to_load = [single]
        else:
            files_to_load = [p for p in parts if p.exists() and p.stat().st_size > 1000]

        if not files_to_load:
            log.warning("No hcad_lookup*.csv.gz files found — address enrichment disabled.")
            return

        import gzip as gz
        count = 0
        for csv_path in files_to_load:
            log.info("Loading HCAD lookup: %s (%d bytes)", csv_path.name, csv_path.stat().st_size)
            try:
                with gz.open(csv_path, "rt", encoding="utf-8", errors="replace") as fh:
                    reader = csv.DictReader(fh)
                    for row in reader:
                        owner = (row.get("owner") or "").strip().upper()
                        if not owner:
                            continue
                        parcel = {
                            "prop_address": (row.get("site_addr") or "").strip(),
                            "prop_city":    (row.get("site_city") or "Houston").strip(),
                            "prop_state":   "TX",
                            "prop_zip":     (row.get("site_zip") or "").strip(),
                            "mail_address": (row.get("mail_addr") or "").strip(),
                            "mail_city":    (row.get("mail_city") or "").strip(),
                            "mail_state":   (row.get("mail_state") or "TX").strip(),
                            "mail_zip":     (row.get("mail_zip") or "").strip(),
                        }
                        if parcel["prop_address"]:
                            self._idx[owner] = parcel
                            words = owner.split()
                            if len(words) >= 2:
                                prefix = f"{words[0]} {words[1]}"
                                if prefix not in self._prefix_idx:
                                    self._prefix_idx[prefix] = parcel
                            count += 1
            except Exception as exc:
                log.error("Failed to load %s: %s", csv_path.name, exc)

        if count > 0:
            log.info("HCAD lookup loaded: %d records, %d prefixes", count, len(self._prefix_idx))
            self._loaded = True
        else:
            log.warning("HCAD lookup loaded 0 records — address enrichment disabled.")

    def lookup(self, owner: str) -> dict:
        if not self._loaded or not owner:
            return {}
        if ";" in owner:
            best = {}
            for part in owner.split(";"):
                hit = self._lookup_single(part.strip())
                if hit and hit.get("prop_address"):
                    if not hit["prop_address"].startswith("0 "):
                        return hit
                    if not best:
                        best = hit
            return best
        return self._lookup_single(owner)

    def _lookup_single(self, owner: str) -> dict:
        if not owner:
            return {}
        n = self._normalise(owner)

        hit = self._idx.get(n)
        if hit:
            return hit

        estate_m = re.match(r'^ESTATE\s+OF\s+(.+)', n)
        if estate_m:
            words = estate_m.group(1).split()
            if words:
                last = words[-1]
                rearranged = f"{last} {' '.join(words[:-1])}".strip()
                hit = self._idx.get(rearranged)
                if hit and hit.get("prop_address"):
                    return hit
                for key, val in self._idx.items():
                    if key.startswith(last + " ") and val.get("prop_address") and not val["prop_address"].startswith("0 "):
                        return val

        n_clean = re.sub(r"\s*\b(EST|ESTATE|SR|JR|II|III|IV)\b.*", "", n).strip()
        if n_clean != n:
            hit = self._idx.get(n_clean)
            if hit:
                return hit

        parts = n_clean.split()

        if len(parts) >= 2:
            prefix2 = f"{parts[0]} {parts[1]}"
            hit = self._prefix_idx.get(prefix2)
            if hit and hit.get("prop_address") and not hit["prop_address"].startswith("0 "):
                return hit

        if len(parts) >= 2:
            short = parts[1][:3]
            for key, val in self._idx.items():
                kparts = key.split()
                if (len(kparts) >= 2
                        and kparts[0] == parts[0]
                        and kparts[1].startswith(short)
                        and val.get("prop_address")
                        and not val["prop_address"].startswith("0 ")):
                    return val

        if len(parts) >= 2:
            rev = f"{parts[-1]} {parts[0]}"
            hit = self._prefix_idx.get(rev)
            if hit and hit.get("prop_address") and not hit["prop_address"].startswith("0 "):
                return hit

        if len(parts) >= 2:
            prefix2 = f"{parts[0]} {parts[1]}"
            hit = self._prefix_idx.get(prefix2)
            if hit:
                return hit

        return {}


# ---------------------------------------------------------------------------
# Clerk Doc Number Lookup (from deeds/owners/permits HCAD data)
# ---------------------------------------------------------------------------
class ClerkLookup:
    """
    Fast exact lookup of owner name + property address by RP doc number.
    Built from HCAD deeds.txt + owners.txt + permits.txt data files.
    File: data/clerk_lookup.json.gz
    """

    def __init__(self):
        self._idx: dict[str, dict] = {}
        self._loaded = False

    def load(self):
        path = ROOT / "data" / "clerk_lookup.json.gz"
        if not path.exists():
            log.warning("clerk_lookup.json.gz not found — clerk enrichment disabled")
            return
        import gzip as gz
        try:
            with gz.open(path, "rt", encoding="utf-8") as f:
                self._idx = json.load(f)
            log.info("ClerkLookup loaded: %d records", len(self._idx))
            self._loaded = True
        except Exception as exc:
            log.error("Failed to load clerk_lookup.json.gz: %s", exc)

    def lookup(self, doc_num: str) -> dict:
        if not self._loaded or not doc_num:
            return {}
        return self._idx.get(doc_num, {})


# ---------------------------------------------------------------------------
# Harris County Clerk - Playwright scraper
# ---------------------------------------------------------------------------
class ClerkScraper:

    def __init__(self, date_from: str, date_to: str):
        self.date_from = date_from
        self.date_to   = date_to

    @staticmethod
    def _to_portal_date(iso: str) -> str:
        try:
            return datetime.strptime(iso, "%Y-%m-%d").strftime("%m/%d/%Y")
        except Exception:
            return iso

    async def _dump_inputs(self, page):
        inputs = await page.evaluate("""
            () => Array.from(document.querySelectorAll('input,select,textarea'))
              .filter(el => el.id || el.name)
              .map(el => el.tagName + ' id=' + el.id + ' name=' + el.name + ' type=' + el.type)
        """)
        log.info("  === ALL PAGE INPUTS ===")
        for inp in inputs:
            log.info("  %s", inp)
        log.info("  === END INPUTS ===")

    async def _set_field(self, page, fragments: list[str], value: str, field_name: str) -> bool:
        for frag in fragments:
            js = f"""
            () => {{
                const els = Array.from(document.querySelectorAll(
                    'input[id*="{frag}"], input[name*="{frag}"], select[id*="{frag}"], select[name*="{frag}"]'
                )).filter(el => el.type !== 'hidden');
                if (!els.length) return null;
                const el = els[0];
                const nativeInputValueSetter = Object.getOwnPropertyDescriptor(
                    window.HTMLInputElement.prototype, 'value'
                )?.set;
                if (nativeInputValueSetter) {{
                    nativeInputValueSetter.call(el, '{value}');
                }} else {{
                    el.value = '{value}';
                }}
                el.dispatchEvent(new Event('input', {{ bubbles: true }}));
                el.dispatchEvent(new Event('change', {{ bubbles: true }}));
                return el.id || el.name;
            }}
            """
            try:
                result = await page.evaluate(js)
                if result:
                    log.info("  %s filled '%s' via JS (element: %s)", field_name, value, result)
                    return True
            except Exception as exc:
                log.debug("  JS fill fragment '%s' failed: %s", frag, exc)
                continue
        log.warning("  Could not fill %s — tried fragments: %s", field_name, fragments)
        return False

    async def _fill_rp_form(self, page, doc_code: str, url: str = ""):
        portal_from = self._to_portal_date(self.date_from)
        portal_to   = self._to_portal_date(self.date_to)

        try:
            await page.wait_for_selector(
                '#ctl00_ContentPlaceHolder1_txtFrom',
                state="attached", timeout=15_000
            )
        except Exception:
            log.warning("  Form not ready after 15s — proceeding anyway")

        if doc_code == TARGET_CODES[0]:
            await self._dump_inputs(page)

        await self._set_field(page, [
            "txtFrom", "txtBegDate", "txtStartDate", "DateFrom",
            "dateFrom", "tbDateFrom", "BeginDate",
        ], portal_from, "DateFrom")

        await self._set_field(page, [
            "txtTo", "txtEndDate", "txtStopDate", "DateTo",
            "dateTo", "tbDateTo", "EndDate",
        ], portal_to, "DateTo")

        await self._set_field(page, [
            "txtInstrument", "txtDocType", "Instrument",
            "InstrType", "InstrumentType", "DocType",
        ], doc_code, "InstrType")

        for sel in [
            '#ctl00_ContentPlaceHolder1_btnSearch',
            'input[id*="btnSearch"]',
            'input[value="Search"]',
            'button:has-text("Search")',
            'input[type="submit"]',
        ]:
            el = page.locator(sel).first
            if await el.count():
                actual = await el.get_attribute("id") or sel
                log.info("  Search btn matched: %s", actual)
                await el.click()
                break
        else:
            log.warning("  Could not find Search button!")

        await page.wait_for_load_state("networkidle", timeout=45_000)

    async def _parse_rp_page(self, page, doc_code: str) -> list[dict]:
        records: list[dict] = []
        cat, cat_label = DOC_TYPE_MAP.get(doc_code, ("other", doc_code))
        html = await page.content()
        soup = BeautifulSoup(html, "lxml")

        result_table = None
        for tbl in soup.find_all("table"):
            tbl_text = tbl.get_text(" ", strip=True)
            if "File Number" in tbl_text and "File Date" in tbl_text:
                result_table = tbl
                break
        if not result_table:
            for tbl in soup.find_all("table"):
                tbl_text = tbl.get_text(" ", strip=True)
                if "Grantor:" in tbl_text or "Grantor :" in tbl_text:
                    result_table = tbl
                    break

        if not result_table:
            log.warning("  No result table found for %s (page has %d tables)",
                       doc_code, len(soup.find_all("table")))
            return records

        rows = result_table.find_all("tr")
        log.info("  Table found for %s: %d rows", doc_code, len(rows))
        if len(rows) < 2:
            return records

        if len(rows) > 1:
            first_cells = rows[1].find_all(["td", "th"])
            log.info("  First row has %d cells: %s",
                     len(first_cells),
                     " | ".join(c.get_text(" ", strip=True)[:25] for c in first_cells[:8]))

        current: dict | None = None
        grouped: list[dict] = []

        for row in rows[1:]:
            cells = row.find_all(["td", "th"])
            if not cells:
                continue
            row_text = " ".join(c.get_text(" ", strip=True) for c in cells)
            doc_match  = re.search(r'\b([A-Z]{1,4}-\d{4}-\d{4,8})\b', row_text)
            date_match = re.search(r'\b(\d{2}/\d{2}/\d{4})\b', row_text)

            if doc_match and date_match:
                if current:
                    grouped.append(current)
                current = {
                    "doc_num": doc_match.group(1),
                    "filed":   _parse_date(date_match.group(1)),
                    "text":    row_text,
                    "hrefs":   [a.get("href","") for a in row.find_all("a", href=True)],
                }
            elif current:
                current["text"]  += " " + row_text
                current["hrefs"] += [a.get("href","") for a in row.find_all("a", href=True)]

        if current:
            grouped.append(current)

        log.info("  Grouped into %d records for %s", len(grouped), doc_code)

        for raw in grouped:
            try:
                full = raw["text"]

                grantors = []
                for m in re.finditer(
                    r'Grantor\s*:\s*([\w][^\|]{2,60}?)(?=\s*(?:Grantor\s*:|Grantee\s*:|\s*\|\s*\w|\s*$))',
                    full
                ):
                    name = m.group(1).strip().strip("|").strip()
                    if name and len(name) > 1 and name not in grantors:
                        grantors.append(name)

                grantees = []
                for m in re.finditer(
                    r'Grantee\s*:\s*([\w][^\|]{2,60}?)(?=\s*(?:Grantor\s*:|Grantee\s*:|\s*\|\s*\w|\s*$))',
                    full
                ):
                    name = m.group(1).strip().strip("|").strip()
                    if name and len(name) > 1 and name not in grantees:
                        grantees.append(name)
                        break  # Take only first grantee to avoid duplicates

                grantor = "; ".join(grantors)
                grantee = grantees[0] if grantees else ""

                legal_text = ""
                for key in ("Desc:", "Comment:", "Lot:", "Block:", "Abstract:", "Sec:"):
                    m = re.search(key + r'\s*(.{3,80}?)(?=\s*(?:Desc:|Comment:|Lot:|Block:|$))', full)
                    if m:
                        legal_text = key + " " + m.group(1).strip()
                        break

                clerk_url = (
                    f"https://www.cclerk.hctx.net/applications/websearch/RP.aspx"
                    f"?FileNo={raw['doc_num']}"
                )
                for href in raw["hrefs"]:
                    if (href and "javascript" not in href.lower()
                            and "EComm" not in href and len(href) > 5):
                        clerk_url = href if href.startswith("http") else CLERK_BASE + "/" + href.lstrip("/")
                        break

                prop_addr = _extract_address_from_legal(legal_text)

                records.append({
                    "doc_num":      raw["doc_num"],
                    "doc_type":     doc_code,
                    "filed":        raw["filed"],
                    "cat":          cat,
                    "cat_label":    cat_label,
                    "owner":        grantor,
                    "grantee":      grantee,
                    "amount":       None,
                    "legal":        legal_text,
                    "prop_address": prop_addr,
                    "prop_city":    "Houston",
                    "prop_state":   "TX",
                    "prop_zip":     "",
                    "mail_address": "",
                    "mail_city":    "",
                    "mail_state":   "",
                    "mail_zip":     "",
                    "clerk_url":    clerk_url,
                    "flags":        [],
                    "score":        0,
                })
            except Exception as exc:
                log.debug("Record build error (%s): %s", doc_code, exc)
                continue

        return records

    async def _paginate(self, page, doc_code: str) -> list[dict]:
        all_recs: list[dict] = []
        page_num = 1

        while True:
            recs = await self._parse_rp_page(page, doc_code)
            all_recs.extend(recs)
            log.info("  %s page %d: %d records (total so far: %d)",
                     doc_code, page_num, len(recs), len(all_recs))

            if page_num >= 15:
                log.warning("  %s: page limit reached, stopping", doc_code)
                break

            next_el = page.locator('#ctl00_ContentPlaceHolder1_BtnNext')
            if await next_el.count() == 0:
                log.info("  %s: no next page, done at page %d", doc_code, page_num)
                break
            try:
                await next_el.click(force=True, timeout=15_000)
                await page.wait_for_load_state("networkidle", timeout=30_000)
                await asyncio.sleep(2)
                page_num += 1
            except Exception as exc:
                log.warning("  %s: pagination stopped at page %d: %s", doc_code, page_num, exc)
                break
        return all_recs

    async def _scrape_doc_type(self, page, doc_code: str, url: str) -> list[dict]:
        for attempt in range(1, 4):
            try:
                await page.goto(url, wait_until="domcontentloaded", timeout=60_000)
                await page.wait_for_load_state("networkidle", timeout=30_000)
                await asyncio.sleep(2)
                await self._fill_rp_form(page, doc_code, url)
                recs = await self._paginate(page, doc_code)

                if len(recs) == 0 and attempt < 3:
                    content = await page.content()
                    if any(x in content.lower() for x in ["session expired", "access denied",
                                                           "temporarily unavailable", "too many requests"]):
                        wait = 30 * attempt
                        log.warning("  Portal blocking detected for %s, waiting %ds...", doc_code, wait)
                        await asyncio.sleep(wait)
                        continue

                return recs
            except Exception as exc:
                log.warning("Attempt %d scraping %s: %s", attempt, doc_code, exc)
                if attempt < 3:
                    await asyncio.sleep(3 * attempt)
        return []

    # ------------------------------------------------------------------
    # FRCL_R.aspx — year/month dropdown form
    # ------------------------------------------------------------------

    @staticmethod
    def _months_in_range(date_from: str, date_to: str) -> list[tuple[int, int]]:
        start = datetime.strptime(date_from, "%Y-%m-%d").replace(day=1)
        end   = datetime.strptime(date_to,   "%Y-%m-%d")
        months: list[tuple[int, int]] = []
        cur = start
        while cur <= end:
            months.append((cur.year, cur.month))
            cur = cur.replace(month=cur.month + 1) if cur.month < 12 else cur.replace(year=cur.year + 1, month=1)
        return months

    async def _fill_frcl_form(self, page, year: int, month: int):
        await page.wait_for_selector(
            "#ctl00_ContentPlaceHolder1_ddlYear",
            state="attached", timeout=15_000,
        )

        await self._dump_inputs(page)

        for val in (str(year), f"{year:04d}"):
            try:
                await page.select_option("#ctl00_ContentPlaceHolder1_ddlYear", val)
                log.info("  FRCL ddlYear = %s", val)
                break
            except Exception as exc:
                log.debug("  ddlYear val=%s: %s", val, exc)

        for val in (str(month), f"{month:02d}"):
            try:
                await page.select_option("#ctl00_ContentPlaceHolder1_ddlMonth", val)
                log.info("  FRCL ddlMonth = %s", val)
                break
            except Exception as exc:
                log.debug("  ddlMonth val=%s: %s", val, exc)

        await page.click("#ctl00_ContentPlaceHolder1_btnSearch")
        log.info("  FRCL Search btn clicked")
        await page.wait_for_load_state("networkidle", timeout=45_000)

    @staticmethod
    def _detect_frcl_columns(header_cells: list[str]) -> dict[str, int]:
        """
        Map FRCL table column names to their index positions.
        The FRCL_R.aspx table header varies but typically includes:
        File Number | Sale Date | File Date | Pages | Trustor | Trustee | Property Address | ...
        """
        mapping: dict[str, int] = {}
        for i, cell in enumerate(header_cells):
            c = cell.lower().strip()
            if not mapping.get("doc_num") and any(k in c for k in ("file number", "file no", "doc")):
                mapping["doc_num"] = i
            elif not mapping.get("sale_date") and any(k in c for k in ("sale date", "sale")):
                mapping["sale_date"] = i
            elif not mapping.get("file_date") and any(k in c for k in ("file date", "filed")):
                mapping["file_date"] = i
            elif not mapping.get("trustor") and any(k in c for k in ("trustor", "grantor", "debtor", "owner", "borrower")):
                mapping["trustor"] = i
            elif not mapping.get("trustee") and any(k in c for k in ("trustee", "grantee", "substitute")):
                mapping["trustee"] = i
            elif not mapping.get("address") and any(k in c for k in ("address", "property", "legal", "location")):
                mapping["address"] = i
        return mapping

    async def _parse_frcl_page(self, page, year: int, month: int) -> list[dict]:
        """
        Parse FRCL_R.aspx results using Playwright directly.
        Reads ALL columns including Trustor (grantor/owner) and address if present.
        """
        records: list[dict] = []

        # Use Playwright to find all rows containing FRCL- doc numbers
        try:
            frcl_rows = await page.locator('tr:has(td:has-text("FRCL-"))').all()
        except Exception as exc:
            log.warning("  FRCL %04d-%02d: row locator failed: %s", year, month, exc)
            return records

        log.info("  FRCL %04d-%02d: %d data rows found", year, month, len(frcl_rows))
        if not frcl_rows:
            log.warning("  FRCL %04d-%02d: no FRCL- rows found", year, month)
            return records

        # --- DIAGNOSTIC: dump all table headers so we can map columns exactly ---
        try:
            full_html = await page.content()
            from bs4 import BeautifulSoup as _BS
            _soup = _BS(full_html, "lxml")
            for _tbl in _soup.find_all("table"):
                _tbl_text = _tbl.get_text(" ", strip=True)
                if "FRCL-" in _tbl_text:
                    _headers = [th.get_text(" ", strip=True) for th in _tbl.find_all("th")]
                    log.info("  FRCL TABLE HEADERS (%d): %s", len(_headers),
                             " | ".join(f"[{i}]{h[:25]}" for i, h in enumerate(_headers)))
                    _first_data = None
                    for _tr in _tbl.find_all("tr"):
                        if "FRCL-" in _tr.get_text():
                            _first_data = _tr
                            break
                    if _first_data:
                        _dcells = [td.get_text(" ", strip=True) for td in _first_data.find_all("td")]
                        log.info("  FRCL FIRST DATA ROW (%d cells): %s", len(_dcells),
                                 " | ".join(f"[{i}]{c[:25]}" for i, c in enumerate(_dcells)))
                    break
        except Exception as _exc:
            log.debug("  FRCL diagnostic dump failed: %s", _exc)

        # Detect column layout from header row
        col_map: dict[str, int] = {}
        try:
            header_rows = await page.locator("tr:has(th)").all()
            if header_rows:
                header_cells = await header_rows[0].locator("th").all_text_contents()
                log.info("  FRCL th headers (%d): %s", len(header_cells),
                         " | ".join(f"[{i}]{h[:20]}" for i, h in enumerate(header_cells)))
                col_map = self._detect_frcl_columns(header_cells)
                log.info("  FRCL column map: %s", col_map)
        except Exception as exc:
            log.debug("  FRCL header detection failed: %s", exc)

        for frcl_row in frcl_rows:
            try:
                # Use evaluate to get innerText of each td (catches nested <a>, <span> text)
                cells_text = await frcl_row.evaluate(
                    "row => Array.from(row.querySelectorAll('td')).map(td => td.innerText.trim())"
                )
                if not cells_text or len(cells_text) < 3:
                    continue

                # Always log every row's full cell contents at INFO level
                log.info("  FRCL row cells (%d): %s",
                         len(cells_text),
                         " | ".join(f"[{i}]{c[:25]}" for i, c in enumerate(cells_text)))

                # Use detected column map; fallback of -1 is intentionally disabled
                def get_col(key: str, fallback: int) -> str:
                    idx = col_map.get(key, fallback)
                    if idx < 0 or idx >= len(cells_text):
                        return ""
                    return cells_text[idx].strip()

                doc_num   = get_col("doc_num", 1)
                sale_date = get_col("sale_date", 2)
                file_date = get_col("file_date", 3)
                trustor   = get_col("trustor", -1)
                prop_addr = get_col("address", -1)

                # Fallback: scan cells 4+ for first name-like value (not a date/digit/short)
                if not trustor:
                    for ci, cell in enumerate(cells_text[4:], start=4):
                        c = cell.strip()
                        if (c and 5 < len(c) < 80
                                and not re.match(r'\d', c)
                                and not re.match(r'\d{2}/\d{2}/\d{4}', c)
                                and re.search(r'[A-Za-z]{4,}', c)):
                            trustor = c
                            log.info("  FRCL trustor fallback col[%d]: %s", ci, c[:40])
                            break

                # Fallback: extract doc_num from href if cells_text didn't give it
                if not re.search(r'FRCL-\d{4}-\d+', doc_num):
                    # Try to find FRCL- pattern anywhere in the row cells
                    all_text = " ".join(cells_text)
                    m = re.search(r'(FRCL-\d{4}-\d+)', all_text)
                    if m:
                        doc_num = m.group(1)
                        log.info("  FRCL doc_num rescued from row text: %s", doc_num)
                    else:
                        continue

                # Use sale date as filed date (more relevant for motivated sellers)
                filed = _parse_date(sale_date) or _parse_date(file_date)

                doc_code = "NOFC"
                cat, cat_label = DOC_TYPE_MAP[doc_code]
                # Capture ViewECdocs URL from the href attribute directly
                clerk_url = f"{CLERK_FRCL_URL}?FileNo={doc_num}"
                try:
                    link_el = frcl_row.locator("a").first
                    if await link_el.count() > 0:
                        href = await link_el.get_attribute("href")
                        if href:
                            log.info("  FRCL href for %s: %s", doc_num, href[:80])
                        if href and len(href) > 10 and "javascript" not in href.lower():
                            if href.startswith("http"):
                                clerk_url = href
                            elif href.startswith("/"):
                                clerk_url = f"https://www.cclerk.hctx.net{href}"
                            else:
                                # Relative URL like "ViewECdocs.aspx?ID=..."
                                clerk_url = f"https://www.cclerk.hctx.net/applications/websearch/{href}"
                except Exception as exc:
                    log.debug("FRCL href capture error: %s", exc)

                records.append({
                    "doc_num":      doc_num,
                    "doc_type":     doc_code,
                    "filed":        filed,
                    "cat":          cat,
                    "cat_label":    cat_label,
                    # trustor = property owner (grantor in foreclosure context)
                    # grantee = foreclosing trustee — left blank, filled by ViewECdocs
                    "owner":        trustor,
                    "grantee":      "",
                    "amount":       None,
                    "legal":        "",
                    "prop_address": prop_addr,
                    "prop_city":    "Houston",
                    "prop_state":   "TX",
                    "prop_zip":     "",
                    "mail_address": "",
                    "mail_city":    "",
                    "mail_state":   "",
                    "mail_zip":     "",
                    "clerk_url":    clerk_url,
                    "flags":        [],
                    "score":        0,
                })
                if trustor:
                    log.info("  FRCL list row %s -> trustor=%s addr=%s",
                             doc_num, trustor[:35], prop_addr[:35] if prop_addr else "")
            except Exception as exc:
                log.debug("FRCL record build error: %s", exc)

        log.info("  FRCL %04d-%02d: %d records", year, month, len(records))
        return records

    async def _paginate_frcl(self, page, year: int, month: int) -> list[dict]:
        all_recs: list[dict] = []
        page_num = 1
        while True:
            recs = await self._parse_frcl_page(page, year, month)
            all_recs.extend(recs)
            log.info("  FRCL %04d-%02d page %d: %d records", year, month, page_num, len(recs))
            next_el = page.locator(
                'a:has-text("Next"), input[value*="Next"], a[id*="Next"], '
                'a[id*="next"], a:has-text(">"), td a:has-text(">")'
            ).first
            if await next_el.count() == 0:
                break
            try:
                await next_el.click()
                await page.wait_for_load_state("networkidle", timeout=30_000)
                page_num += 1
            except Exception as exc:
                log.warning("  FRCL pagination stopped at page %d: %s", page_num, exc)
                break
        return all_recs

    async def _scrape_frcl_month(self, page, year: int, month: int) -> list[dict]:
        for attempt in range(1, 4):
            try:
                await page.goto(CLERK_FRCL_URL, wait_until="domcontentloaded", timeout=60_000)
                await page.wait_for_load_state("networkidle", timeout=30_000)
                await asyncio.sleep(2)
                await self._fill_frcl_form(page, year, month)
                return await self._paginate_frcl(page, year, month)
            except Exception as exc:
                log.warning("FRCL %04d-%02d attempt %d: %s", year, month, attempt, exc)
                if attempt < 3:
                    await asyncio.sleep(3 * attempt)
        return []

    async def _enrich_frcl_record(self, page, rec: dict, parcel_db) -> dict:
        """Visit the stored ViewECdocs URL to get grantor/grantee/legal."""
        doc_url = rec.get("clerk_url", "")
        doc_num = rec.get("doc_num", "")

        log.info("  FRCL enrich %s: url=%s", doc_num, doc_url[:80] if doc_url else "EMPTY")

        # Only visit ViewECdocs URLs — skip plain FRCL search URLs
        if not doc_url or "ViewECdocs" not in doc_url:
            log.info("  FRCL enrich %s: skipped (no ViewECdocs in url)", doc_num)
            return rec

        try:
            await page.goto(doc_url, wait_until="networkidle", timeout=30_000)
            await asyncio.sleep(1.5)
            html = await page.content()
            grantors, grantees, legal = self._parse_viewecdocs_html(html)
            if grantors:
                rec["owner"] = "; ".join(grantors)
            if grantees:
                rec["grantee"] = "; ".join(grantees)
            if legal:
                rec["legal"] = legal
            if rec.get("owner") or rec.get("grantee"):
                log.info("  FRCL xref %s -> grantor=%s | grantee=%s",
                         doc_num, (rec.get("owner") or "")[:35], (rec.get("grantee") or "")[:35])
        except Exception as exc:
            log.debug("FRCL xref %s failed: %s", doc_num, exc)
        return rec

    async def enrich_frcl_records(self, page, records: list[dict], parcel_db=None) -> list[dict]:
        """Click each FRCL doc link to get grantor/grantee/legal from ViewECdocs page."""
        if page is None:
            return records
        nofc_recs = [r for r in records if r.get("doc_type") == "NOFC" and not r.get("owner")]
        if not nofc_recs:
            return records
        log.info("FRCL enrichment: looking up %d foreclosure records via doc links...", len(nofc_recs))
        enriched = 0
        for rec in nofc_recs:
            rec = await self._enrich_frcl_record(page, rec, parcel_db)
            if rec.get("owner"):
                enriched += 1
            await asyncio.sleep(1)
        log.info("FRCL enrichment: enriched %d/%d records", enriched, len(nofc_recs))
        return records

    @staticmethod
    def _parse_viewecdocs_html(html: str) -> tuple[list, list, str]:
        """
        Extract grantors, grantees, and legal description from a ViewECdocs page.
        Handles both table-based (tr/td) and label/value div/span layouts.
        Returns (grantors, grantees, legal).
        """
        soup = BeautifulSoup(html, "lxml")
        grantors, grantees, legal = [], [], ""

        # Strategy 1: tr/td table rows with label in first cell
        for row in soup.find_all("tr"):
            cells = [td.get_text(" ", strip=True) for td in row.find_all(["td", "th"])]
            if len(cells) < 2:
                continue
            label = cells[0].lower().strip().rstrip(":")
            value = cells[1].strip()
            if not value or len(value) < 2:
                continue
            if "grantor" in label and value not in grantors:
                grantors.append(value)
            elif "grantee" in label and value not in grantees:
                grantees.append(value)
            elif any(k in label for k in ("legal", "desc", "lot", "block")) and not legal:
                legal = value

        # Strategy 2: full-text regex scan (catches span/div label layouts)
        if not grantors or not grantees:
            full_text = soup.get_text(" ", strip=True)
            if not grantors:
                for m in re.finditer(
                    r'Grantor\s*[:\-]\s*([A-Z][A-Z0-9\s,\.\-\']{2,60}?)(?=\s*(?:Grantor|Grantee|Legal|Desc|Lot|Block|Sale|File|\d{2}/|\Z))',
                    full_text, re.IGNORECASE
                ):
                    name = m.group(1).strip().rstrip(",").strip()
                    if name and len(name) > 2 and name not in grantors:
                        grantors.append(name)
            if not grantees:
                for m in re.finditer(
                    r'Grantee\s*[:\-]\s*([A-Z][A-Z0-9\s,\.\-\']{2,60}?)(?=\s*(?:Grantor|Grantee|Legal|Desc|Lot|Block|Sale|File|\d{2}/|\Z))',
                    full_text, re.IGNORECASE
                ):
                    name = m.group(1).strip().rstrip(",").strip()
                    if name and len(name) > 2 and name not in grantees:
                        grantees.append(name)
            if not legal:
                m = re.search(
                    r'(?:Legal|Description|Desc)\s*[:\-]\s*(.{5,120}?)(?=\s*(?:Grantor|Grantee|Sale|File|\Z))',
                    full_text, re.IGNORECASE
                )
                if m:
                    legal = m.group(1).strip()

        # Strategy 3: look for labelled spans/divs
        if not grantors or not grantees:
            for el in soup.find_all(["span", "div", "td", "th", "label"]):
                el_text = el.get_text(" ", strip=True).lower()
                if not el_text:
                    continue
                sib = el.find_next_sibling()
                sib_text = sib.get_text(" ", strip=True) if sib else ""
                if not sib_text or len(sib_text) < 2:
                    continue
                if "grantor" in el_text and sib_text not in grantors:
                    grantors.append(sib_text)
                elif "grantee" in el_text and sib_text not in grantees:
                    grantees.append(sib_text)

        return grantors, grantees, legal

    async def fetch_frcl_on_page(self, page) -> list[dict]:
        months = self._months_in_range(self.date_from, self.date_to)
        log.info("FRCL scraping %d month(s): %s",
                 len(months), ", ".join(f"{y}-{m:02d}" for y, m in months))
        all_records: list[dict] = []
        for i, (year, month) in enumerate(months):
            recs = await self._scrape_frcl_month(page, year, month)
            log.info("  FRCL %04d-%02d -> %d records", year, month, len(recs))
            # ViewECdocs URLs trigger a file download (PDF), not a normal page load.
            # We use requests with the browser's cookies to fetch the HTML version instead.
            enriched_count = 0
            try:
                # Extract cookies from the live Playwright session
                cookies = await page.context.cookies()
                session_cookies = {c["name"]: c["value"] for c in cookies}
                headers = {
                    "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                                  "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36",
                    "Referer": CLERK_FRCL_URL,
                    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
                }
                import requests as _requests
                session = _requests.Session()
                session.headers.update(headers)
                session.cookies.update(session_cookies)

                for rec in recs:
                    doc_url = rec.get("clerk_url", "")
                    if "ViewECdocs" not in doc_url:
                        continue
                    try:
                        resp = session.get(doc_url, timeout=20, allow_redirects=True)
                        log.info("  FRCL xref %s: status=%s len=%d snip=%s",
                                 rec["doc_num"], resp.status_code, len(resp.content),
                                 resp.text[:100].replace("\n", " "))
                        if resp.status_code == 200 and "<html" in resp.text.lower():
                            grantors, grantees, legal = self._parse_viewecdocs_html(resp.text)
                            if grantors:
                                rec["owner"] = "; ".join(grantors)
                            if grantees:
                                rec["grantee"] = "; ".join(grantees)
                            if legal:
                                rec["legal"] = legal
                            if rec.get("owner") or rec.get("grantee"):
                                enriched_count += 1
                                log.info("  FRCL xref %s -> grantor=%s | grantee=%s",
                                         rec["doc_num"],
                                         (rec.get("owner") or "")[:35],
                                         (rec.get("grantee") or "")[:35])
                            else:
                                log.info("  FRCL xref %s: HTML received but no names parsed", rec["doc_num"])
                        elif resp.headers.get("content-type", "").startswith("application/pdf"):
                            log.info("  FRCL xref %s: got PDF, cannot parse", rec["doc_num"])
                        else:
                            log.info("  FRCL xref %s: unexpected content-type=%s",
                                     rec["doc_num"], resp.headers.get("content-type", "?"))
                    except Exception as exc:
                        log.info("  FRCL xref %s failed: %s", rec.get("doc_num", "?"), exc)
            except Exception as exc:
                log.warning("  FRCL ViewECdocs session setup failed: %s", exc)
            log.info("  FRCL %04d-%02d enriched %d/%d via ViewECdocs",
                     year, month, enriched_count, len(recs))
            all_records.extend(recs)
            if i < len(months) - 1:
                await page.goto(CLERK_FRCL_URL, wait_until="domcontentloaded", timeout=20_000)
                await asyncio.sleep(2)
        return all_records

    async def fetch_all_on_page(self, page) -> list[dict]:
        all_records: list[dict] = []
        for doc_code in TARGET_CODES:
            url = CLERK_FRCL_URL if doc_code in FRCL_TYPES else CLERK_RP_URL
            log.info("Fetching %s from %s", doc_code, url)
            recs = await self._scrape_doc_type(page, doc_code, url)
            log.info("  %s -> %d records", doc_code, len(recs))
            all_records.extend(recs)
        return all_records

    async def fetch_all(self) -> list[dict]:
        if not HAS_PW:
            log.error("Playwright not installed.")
            return []

        all_records: list[dict] = []
        async with async_playwright() as pw:
            browser = await pw.chromium.launch(
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage"],
            )
            context = await browser.new_context(
                user_agent="Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                           "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36",
                viewport={"width": 1280, "height": 900},
            )
            page = await context.new_page()
            page.set_default_timeout(60_000)

            for i, doc_code in enumerate(TARGET_CODES):
                url = CLERK_FRCL_URL if doc_code in FRCL_TYPES else CLERK_RP_URL
                log.info("Fetching %s from %s", doc_code, url)
                recs = await self._scrape_doc_type(page, doc_code, url)
                log.info("  %s -> %d records", doc_code, len(recs))
                all_records.extend(recs)
                _save_partial(all_records, self.date_from, self.date_to)
                if i < len(TARGET_CODES) - 1:
                    await asyncio.sleep(2 + (i % 3))

            await browser.close()

        return all_records


# ---------------------------------------------------------------------------
# Fallback static scraper
# ---------------------------------------------------------------------------
class StaticClerkScraper:
    HEADERS = {
        "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                      "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    }

    def __init__(self, date_from: str, date_to: str):
        self.date_from = self._fmt(date_from)
        self.date_to   = self._fmt(date_to)
        self.session   = requests.Session()
        self.session.headers.update(self.HEADERS)

    @staticmethod
    def _fmt(iso: str) -> str:
        try:
            return datetime.strptime(iso, "%Y-%m-%d").strftime("%m/%d/%Y")
        except Exception:
            return iso

    def _viewstate(self, html: str) -> dict[str, str]:
        soup = BeautifulSoup(html, "lxml")
        fields = {}
        for name in ["__VIEWSTATE", "__VIEWSTATEGENERATOR", "__EVENTVALIDATION"]:
            el = soup.find("input", {"name": name})
            if el:
                fields[name] = el.get("value", "")
        return fields

    def _search(self, url: str, doc_code: str) -> list[dict]:
        cat, cat_label = DOC_TYPE_MAP.get(doc_code, ("other", doc_code))
        records: list[dict] = []
        try:
            resp = self.session.get(url, timeout=30)
            resp.raise_for_status()
            vs = self._viewstate(resp.text)
            payload = {
                **vs,
                "__EVENTTARGET":   "",
                "__EVENTARGUMENT": "",
                "ctl00$ContentPlaceHolder1$txtFrom":       self.date_from,
                "ctl00$ContentPlaceHolder1$txtTo":         self.date_to,
                "ctl00$ContentPlaceHolder1$txtInstrument": doc_code,
                "ctl00$ContentPlaceHolder1$btnSearch":     "Search",
            }
            resp = self.session.post(url, data=payload, timeout=60)
            resp.raise_for_status()
            soup = BeautifulSoup(resp.text, "lxml")
            records.extend(self._parse_table(soup, doc_code, cat, cat_label))
        except Exception as exc:
            log.warning("Static scraper %s @ %s: %s", doc_code, url, exc)
        return records

    def _parse_table(self, soup, doc_code, cat, cat_label) -> list[dict]:
        records = []
        for tbl in soup.find_all("table"):
            text = tbl.get_text(" ", strip=True).lower()
            if not any(k in text for k in ("grantor", "filed", "file number")):
                continue
            for row in tbl.find_all("tr")[1:]:
                cells = row.find_all("td")
                if not cells:
                    continue
                try:
                    texts = [c.get_text(" ", strip=True) for c in cells]
                    records.append({
                        "doc_num":      texts[0] if texts else "",
                        "doc_type":     doc_code,
                        "filed":        _parse_date(texts[1] if len(texts) > 1 else ""),
                        "cat":          cat,
                        "cat_label":    cat_label,
                        "owner":        texts[2] if len(texts) > 2 else "",
                        "grantee":      texts[3] if len(texts) > 3 else "",
                        "amount":       None,
                        "legal":        "",
                        "prop_address": "", "prop_city": "Houston",
                        "prop_state":   "TX", "prop_zip": "",
                        "mail_address": "", "mail_city": "",
                        "mail_state":   "", "mail_zip": "",
                        "clerk_url":    "",
                        "flags":        [], "score": 0,
                    })
                except Exception:
                    continue
        return records

    def fetch_all(self) -> list[dict]:
        all_records: list[dict] = []
        for doc_code in TARGET_CODES:
            url = CLERK_FRCL_URL if doc_code in FRCL_TYPES else CLERK_RP_URL
            log.info("Static scraping %s", doc_code)
            try:
                recs = self._search(url, doc_code)
                log.info("  %s -> %d records", doc_code, len(recs))
                all_records.extend(recs)
            except Exception as exc:
                log.warning("  %s failed: %s", doc_code, exc)
        return all_records


# ---------------------------------------------------------------------------
# GHL CSV export
# ---------------------------------------------------------------------------
def export_ghl_csv(records: list[dict], path: Path):
    path.parent.mkdir(parents=True, exist_ok=True)
    columns = [
        "First Name", "Last Name", "Mailing Address", "Mailing City",
        "Mailing State", "Mailing Zip", "Property Address", "Property City",
        "Property State", "Property Zip", "Lead Type", "Document Type",
        "Date Filed", "Document Number", "Amount/Debt Owed", "Seller Score",
        "Motivated Seller Flags", "Source", "Public Records URL",
    ]

    def split_name(full: str) -> tuple[str, str]:
        parts = full.strip().split(None, 1)
        return (parts[0], parts[1]) if len(parts) == 2 else (full, "")

    with open(path, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=columns)
        w.writeheader()
        for r in records:
            # Use grantee (property owner) for name fields; fall back to grantor
            name_source = r.get("grantee", "") or r.get("owner", "")
            first, last = split_name(name_source)
            w.writerow({
                "First Name":             first,
                "Last Name":              last,
                "Mailing Address":        r.get("mail_address", ""),
                "Mailing City":           r.get("mail_city", ""),
                "Mailing State":          r.get("mail_state", ""),
                "Mailing Zip":            r.get("mail_zip", ""),
                "Property Address":       r.get("prop_address", ""),
                "Property City":          r.get("prop_city", ""),
                "Property State":         r.get("prop_state", ""),
                "Property Zip":           r.get("prop_zip", ""),
                "Lead Type":              r.get("cat_label", ""),
                "Document Type":          r.get("doc_type", ""),
                "Date Filed":             r.get("filed", ""),
                "Document Number":        r.get("doc_num", ""),
                "Amount/Debt Owed":       r.get("amount", ""),
                "Seller Score":           r.get("score", 0),
                "Motivated Seller Flags": "; ".join(r.get("flags", [])),
                "Source":                 "Harris County Clerk",
                "Public Records URL":     r.get("clerk_url", ""),
            })
    log.info("GHL CSV -> %s (%d rows)", path, len(records))


# ---------------------------------------------------------------------------
# Save JSON outputs
# ---------------------------------------------------------------------------
def save_output(records: list[dict], date_from: str, date_to: str):
    with_addr = sum(1 for r in records if r.get("prop_address"))
    payload = {
        "fetched_at":   datetime.utcnow().isoformat() + "Z",
        "source":       "Harris County Clerk",
        "date_range":   {"from": date_from, "to": date_to},
        "total":        len(records),
        "with_address": with_addr,
        "records":      records,
    }
    for dest in [DASHBOARD_JSON, DATA_JSON]:
        dest.parent.mkdir(parents=True, exist_ok=True)
        with open(dest, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, indent=2, default=str)
        log.info("Saved: %s (%d records)", dest, len(records))


def _save_partial(records: list[dict], date_from: str, date_to: str):
    try:
        deduped = _deduplicate(list(records))
        with_addr = sum(1 for r in deduped if r.get("prop_address"))
        payload = {
            "fetched_at":   datetime.utcnow().isoformat() + "Z",
            "source":       "Harris County Clerk (partial)",
            "date_range":   {"from": date_from, "to": date_to},
            "total":        len(deduped),
            "with_address": with_addr,
            "records":      deduped,
        }
        for dest in [DASHBOARD_JSON, DATA_JSON]:
            dest.parent.mkdir(parents=True, exist_ok=True)
            with open(dest, "w", encoding="utf-8") as fh:
                json.dump(payload, fh, indent=2, default=str)
    except Exception:
        pass


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
async def main():
    now       = datetime.now(timezone.utc)
    date_to   = now.strftime("%Y-%m-%d")
    date_from = (now - timedelta(days=LOOKBACK_DAYS)).strftime("%Y-%m-%d")

    log.info("=" * 60)
    log.info("Harris County Motivated Seller Scraper")
    log.info("Date range : %s -> %s", date_from, date_to)
    log.info("Doc types  : %s", ", ".join(TARGET_CODES))
    log.info("Portal RP  : %s", CLERK_RP_URL)
    log.info("Portal FRCL: %s", CLERK_FRCL_URL)
    log.info("=" * 60)

    CHUNK_DAYS  = 14
    CHUNK_DELAY = 45

    chunks = []
    cur = datetime.strptime(date_from, "%Y-%m-%d").replace(tzinfo=timezone.utc)
    end = datetime.strptime(date_to,   "%Y-%m-%d").replace(tzinfo=timezone.utc)
    while cur <= end:
        nxt = min(cur + timedelta(days=CHUNK_DAYS), end)
        chunks.append((cur.strftime("%Y-%m-%d"), nxt.strftime("%Y-%m-%d")))
        cur = nxt + timedelta(days=1)

    log.info("Scraping %d chunks of %d days (delay: %ds each)", len(chunks), CHUNK_DAYS, CHUNK_DELAY)

    all_raw: list[dict] = []
    pw_page = None  # saved for FRCL enrichment

    if HAS_PW:
        async with async_playwright() as pw:
            browser = await pw.chromium.launch(
                headless=True,
                args=["--no-sandbox", "--disable-dev-shm-usage"],
            )
            context = await browser.new_context(
                user_agent="Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                           "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36",
                viewport={"width": 1280, "height": 900},
            )
            page = await context.new_page()
            page.set_default_timeout(60_000)

            for i, (c_from, c_to) in enumerate(chunks, 1):
                log.info("--- Chunk %d/%d: %s -> %s ---", i, len(chunks), c_from, c_to)
                try:
                    scraper = ClerkScraper(c_from, c_to)
                    recs = await scraper.fetch_all_on_page(page)
                    log.info("Chunk %d: %d records (total: %d)", i, len(recs), len(all_raw) + len(recs))
                    all_raw.extend(recs)
                except Exception as exc:
                    log.warning("Chunk %d failed: %s — skipping", i, exc)

                if i < len(chunks):
                    log.info("Waiting %ds...", CHUNK_DELAY)
                    try:
                        await page.goto("about:blank", wait_until="domcontentloaded", timeout=10_000)
                    except Exception:
                        pass
                    await asyncio.sleep(CHUNK_DELAY)

            # FRCL scraping — NOFC foreclosures
            log.info("--- FRCL scraping: NOFC ---")
            frcl_recs = []
            try:
                frcl_scraper = ClerkScraper(date_from, date_to)
                frcl_recs = await frcl_scraper.fetch_frcl_on_page(page)
                log.info("FRCL total: %d records", len(frcl_recs))
                all_raw.extend(frcl_recs)
                _save_partial(all_raw, date_from, date_to)
            except Exception as exc:
                log.warning("FRCL scrape failed: %s", exc)

            pw_page = page
            await browser.close()
    else:
        log.warning("Playwright unavailable - using static scraper.")
        import time as _time
        for i, (c_from, c_to) in enumerate(chunks, 1):
            log.info("--- Chunk %d/%d: %s -> %s ---", i, len(chunks), c_from, c_to)
            scraper = StaticClerkScraper(c_from, c_to)
            recs = scraper.fetch_all()
            log.info("Chunk %d: %d records", i, len(recs))
            all_raw.extend(recs)
            if i < len(chunks):
                _time.sleep(CHUNK_DELAY)

    records = all_raw
    log.info("Raw records fetched: %d", len(records))

    records = _deduplicate(records)
    log.info("After dedup: %d", len(records))

    log.info("Loading clerk doc number lookup...")
    clerk_db = ClerkLookup()
    clerk_db.load()

    log.info("Loading HCAD parcel data (fallback)...")
    parcel_db = ParcelLookup()
    parcel_db.load()

    enriched_clerk = 0
    enriched_parcel = 0
    for rec in records:
        doc_num = rec.get("doc_num", "")
        owner   = rec.get("owner", "")    # grantor
        grantee = rec.get("grantee", "")  # current property owner (who we want address for)

        # 1. Try exact clerk lookup by doc number (fast, accurate)
        hit = clerk_db.lookup(doc_num)
        if hit and hit.get("address"):
            rec["prop_address"] = hit["address"]
            rec["prop_city"]    = "Houston"
            rec["prop_state"]   = "TX"
            if not owner and hit.get("owner"):
                rec["owner"] = hit["owner"]
            enriched_clerk += 1
            continue

        # 2. Fall back to fuzzy HCAD name matching.
        #    Always look up by GRANTEE first (they are the property owner whose
        #    address we want). Only fall back to grantor if grantee is blank.
        lookup_name = grantee if grantee else owner
        if lookup_name:
            hit2 = parcel_db.lookup(lookup_name)
            if hit2 and hit2.get("prop_address"):
                rec.update({k: v for k, v in hit2.items() if v})
                enriched_parcel += 1

    log.info("Enrichment: %d clerk lookup + %d HCAD fuzzy = %d/%d total",
             enriched_clerk, enriched_parcel, enriched_clerk + enriched_parcel, len(records))

    for rec in records:
        score, flags = compute_score(rec)
        rec["score"] = score
        rec["flags"] = flags
    records.sort(key=lambda r: r.get("score", 0), reverse=True)

    save_output(records, date_from, date_to)
    export_ghl_csv(records, GHL_CSV)

    log.info("=" * 60)
    log.info("DONE - %d total leads", len(records))
    for code in TARGET_CODES + ["NOFC"]:
        cnt = sum(1 for r in records if r.get("doc_type") == code)
        if cnt:
            log.info("  %-12s %d", code, cnt)
    log.info("=" * 60)
    return 0


if __name__ == "__main__":
    sys.exit(asyncio.run(main()))
