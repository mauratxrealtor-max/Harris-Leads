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
import io
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
        self._addr_idx: dict[str, dict] = {}
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
                            site_addr_key = parcel["prop_address"].upper().strip()
                            if site_addr_key and not site_addr_key.startswith("0 "):
                                self._addr_idx[site_addr_key] = {**parcel, "owner": owner}
                            count += 1
            except Exception as exc:
                log.error("Failed to load %s: %s", csv_path.name, exc)

        if count > 0:
            log.info("HCAD lookup loaded: %d records, %d prefixes", count, len(self._prefix_idx))
            self._loaded = True
        else:
            log.warning("HCAD lookup loaded 0 records — address enrichment disabled.")

    def lookup_by_address(self, address: str) -> dict:
        if not self._loaded or not address:
            return {}
        addr = re.sub(r'\s+', ' ', address.upper().strip())
        hit = self._addr_idx.get(addr)
        if hit: return hit
        addr_base = re.sub(r'\s+(APT|UNIT|STE|#)\s*\S+.*$', '', addr).strip()
        hit = self._addr_idx.get(addr_base)
        if hit: return hit
        m = re.match(r'^(\d+)\s+(\w+)', addr_base)
        if m:
            num, street = m.group(1), m.group(2)
            for key, val in self._addr_idx.items():
                if key.startswith(f"{num} {street}"):
                    return val
        return {}

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
                        break

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
            if cur.month == 12:
                cur = cur.replace(year=cur.year + 1, month=1)
            else:
                cur = cur.replace(month=cur.month + 1)
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
        records: list[dict] = []

        try:
            frcl_rows = await page.locator('tr:has(td:has-text("FRCL-"))').all()
        except Exception as exc:
            log.warning("  FRCL %04d-%02d: row locator failed: %s", year, month, exc)
            return records

        log.info("  FRCL %04d-%02d: %d data rows found", year, month, len(frcl_rows))
        if not frcl_rows:
            log.warning("  FRCL %04d-%02d: no FRCL- rows found", year, month)
            return records

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
                    break
        except Exception as _exc:
            log.debug("  FRCL diagnostic dump failed: %s", _exc)

        col_map: dict[str, int] = {}
        try:
            header_rows = await page.locator("tr:has(th)").all()
            if header_rows:
                header_cells = await header_rows[0].locator("th").all_text_contents()
                col_map = self._detect_frcl_columns(header_cells)
        except Exception as exc:
            log.debug("  FRCL header detection failed: %s", exc)

        for frcl_row in frcl_rows:
            try:
                cells_text = await frcl_row.evaluate(
                    "row => Array.from(row.querySelectorAll('td')).map(td => td.innerText.trim())"
                )
                if not cells_text or len(cells_text) < 3:
                    continue

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

                if not re.search(r'FRCL-\d{4}-\d+', doc_num):
                    all_text = " ".join(cells_text)
                    m = re.search(r'(FRCL-\d{4}-\d+)', all_text)
                    if m: doc_num = m.group(1)
                    else: continue

                filed = _parse_date(sale_date) or _parse_date(file_date)
                doc_code = "NOFC"
                cat, cat_label = DOC_TYPE_MAP[doc_code]
                clerk_url = f"{CLERK_FRCL_URL}?FileNo={doc_num}"
                try:
                    link_el = frcl_row.locator("a").first
                    if await link_el.count() > 0:
                        href = await link_el.get_attribute("href")
                        if href and len(href) > 10 and "javascript" not in href.lower():
                            if href.startswith("http"): clerk_url = href
                            elif href.startswith("/"): clerk_url = f"https://www.cclerk.hctx.net{href}"
                            else: clerk_url = f"https://www.cclerk.hctx.net/applications/websearch/{href}"
                except Exception: pass

                records.append({
                    "doc_num":      doc_num,
                    "doc_type":     doc_code,
                    "filed":        filed,
                    "cat":          cat,
                    "cat_label":    cat_label,
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
            except Exception: pass
        return records

    async def fetch_frcl_on_page(self, page) -> list[dict]:
        """
        Downloads NOFC scanned PDFs, converts them to images, 
        and applies OCR to parse names and legal descriptions.
        """
        import os
        import re
        import io
        import pypdf
        import requests
        from pdf2image import convert_from_path
        import pytesseract

        months = self._months_in_range(self.date_from, self.date_to)
        log.info("FRCL scraping %d month(s): %s", len(months), ", ".join(f"{y}-{m:02d}" for y, m in months))
        all_records: list[dict] = []

        for i, (year, month) in enumerate(months):
            recs = await self._scrape_frcl_month(page, year, month)
            
            try:
                cookies = await page.context.cookies()
                session_cookies = {c["name"]: c["value"] for c in cookies}
                headers = {
                    "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36",
                    "Referer": CLERK_FRCL_URL,
                    "Accept": "application/pdf,text/html,*/*",
                }
                session = requests.Session()
                session.headers.update(headers)
                session.cookies.update(session_cookies)

                for rec in recs:
                    doc_url = rec.get("clerk_url", "")
                    doc_id = rec.get("doc_num", "?")
                    if "ViewECdocs" not in doc_url:
                        continue

                    try:
                        resp = session.get(doc_url, timeout=20, allow_redirects=True)
                        if resp.status_code == 200 and (resp.headers.get("content-type", "").startswith("application/pdf") or b"%PDF" in resp.content[:10]):
                            
                            # Try normal text reading first
                            reader = pypdf.PdfReader(io.BytesIO(resp.content))
                            full_text = ""
                            for pdf_page in reader.pages:
                                text = pdf_page.extract_text()
                                if text:
full_text += text + "\n"
# Your Legal approach: If it's a scanned image file, run OCR
                        if len(full_text.strip()) < 50:
                            log.info("  [OCR Engine] Scanning pixels for scanned image PDF: %s", doc_id)
                            os.makedirs("tmp", exist_ok=True)
                            temp_pdf = f"tmp/{doc_id}.pdf"
                            with open(temp_pdf, "wb") as f:
                                f.write(resp.content)
                            
                            images = convert_from_path(temp_pdf, dpi=150)
                            for img in images:
                                full_text += pytesseract.image_to_string(img) + "\n"
                            
                            if os.path.exists(temp_pdf):
                                os.remove(temp_pdf)

                        # Parse out standard keywords
                        owner_match = re.search(r'(?:Debtor|Trustor|Grantor|Borrower)\s*:\s*([^\n]+)', full_text, re.I)
                        if owner_match:
                            rec["owner"] = owner_match.group(1).strip().upper()

                        lender_match = re.search(r'(?:Beneficiary|Lender|Mortgagee)\s*:\s*([^\n]+)', full_text, re.I)
                        if lender_match:
                            rec["grantee"] = lender_match.group(1).strip().upper()

                        # Parse legal fallback block or structural layout
                        legal_match = re.search(r'Lot\s+(\d+)\s*,\s*Block\s+(\d+)', full_text, re.I)
                        if legal_match:
                            rec["legal"] = f"LOT {legal_match.group(1)} BLOCK {legal_match.group(2)}"
                            log.info("  [Legal Description Found] Doc %s -> Lot: %s, Block: %s", doc_id, legal_match.group(1), legal_match.group(2))

                        addr_match = re.search(r'\b(\d{1,5})\s+([NSEW]\s+)?([A-Z0-9\s]{2,30}(?:ST|AVE|BLVD|DR|LN|RD|WAY|CT|PL|TRL|FWY|PKWY|HWY|CIR|LOOP))\b', full_text.upper())
                        if addr_match:
                            rec["prop_address"] = addr_match.group(0).strip()

                        log.info("  FRCL processed %s -> Owner: %s, Addr: %s", doc_id, rec['owner'], rec['prop_address'])

                except Exception as exc:
                    log.info("  FRCL extraction error on document %s: %s", doc_id, exc)

        except Exception as exc:
            log.warning("  FRCL ViewECdocs session setup failed: %s", exc)

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
            all_records.extend(recs)
        return all_records
