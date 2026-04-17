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
LOOKBACK_DAYS: int = int(os.getenv("LOOKBACK_DAYS", "7"))

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
    "LP":       ("lp",      "Lis Pendens"),
    "NOFC":     ("nofc",    "Notice of Foreclosure"),
    "TAXDEED":  ("taxdeed", "Tax Deed"),
    "JUD":      ("jud",     "Judgment"),
    "CCJ":      ("jud",     "Certified Judgment"),
    "DRJUD":    ("jud",     "Domestic Judgment"),
    "LNCORPTX": ("lien",    "Corp Tax Lien"),
    "LNIRS":    ("lien",    "IRS Lien"),
    "LNFED":    ("lien",    "Federal Lien"),
    "LN":       ("lien",    "Lien"),
    "LNMECH":   ("lien",    "Mechanic Lien"),
    "LNHOA":    ("lien",    "HOA Lien"),
    "MEDLN":    ("lien",    "Medicaid Lien"),
    "PRO":      ("probate", "Probate Document"),
    "NOC":      ("noc",     "Notice of Commencement"),
    "RELLP":    ("rellp",   "Release Lis Pendens"),
}

# Doc types that live on the Foreclosures page instead of RP
FRCL_TYPES = {"NOFC", "TAXDEED"}

TARGET_CODES = list(DOC_TYPE_MAP.keys())

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
    """
    Try to extract a street address from a Harris County legal description.
    Examples: '1234 MAIN ST', '5678 W BELLFORT AVE UNIT 2'
    """
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
    seen: set[str] = set()
    out: list[dict] = []
    for rec in records:
        key = f"{rec.get('doc_type','')}:{rec.get('doc_num','')}"
        if key not in seen:
            seen.add(key)
            out.append(rec)
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

    if doc_type in ("LP", "RELLP"):
        flags.append("Lis pendens")
    if doc_type in ("NOFC", "TAXDEED"):
        flags.append("Pre-foreclosure")
    if cat == "jud":
        flags.append("Judgment lien")
    if doc_type in ("LNCORPTX", "LNIRS", "LNFED", "TAXDEED"):
        flags.append("Tax lien")
    if doc_type == "LNMECH":
        flags.append("Mechanic lien")
    if cat == "probate":
        flags.append("Probate / estate")
    if re.search(r"\b(LLC|INC|CORP|LTD|LP|LLP|PLLC|TRUST)\b", owner, re.I):
        flags.append("LLC / corp owner")

    try:
        filed_dt = datetime.strptime(filed_str[:10], "%Y-%m-%d")
        if (datetime.utcnow() - filed_dt).days <= LOOKBACK_DAYS:
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
    """
    Downloads HCAD Real_acct_owner.zip which contains real_acct.txt —
    a tab-delimited text file with owner name, site address, mailing address.

    Confirmed file structure from HCAD codebook:
      real_acct.txt columns (tab-delimited):
        0  acct         account number
        1  yr           year
        2  owner_name   owner name
        3  owner_name2  (secondary)
        7  site_addr_1  site street address
        8  site_city    site city
        9  state_cd     state
        10 site_zip     site zip
        11 mail_addr_1  mailing address line 1
        12 mail_addr_2  mailing address line 2
        13 mail_addr_3  mailing address line 3
        14 mail_city    mailing city
        15 mail_state   mailing state
        16 mail_zip     mailing zip
    """

    # Confirmed working URL from HCAD pdata server
    DOWNLOAD_URLS = [
        "https://pdata.hcad.org/data/cama/2026/Real_acct_owner.zip",
        "https://pdata.hcad.org/data/cama/2025/Real_acct_owner.zip",
        "https://pdata.hcad.org/data/cama/2026/real_acct_owner.zip",
        "https://pdata.hcad.org/data/cama/2025/real_acct_owner.zip",
    ]

    def __init__(self):
        self._idx: dict[str, dict] = {}
        self._loaded = False

    def _normalise(self, name: str) -> str:
        return re.sub(r"\s+", " ", name.upper().strip())

    def _name_variants(self, raw: str) -> list[str]:
        n = self._normalise(raw)
        variants = [n]
        if "," in n:
            parts = [p.strip() for p in n.split(",", 1)]
            if len(parts) == 2:
                variants.append(f"{parts[1]} {parts[0]}")
        else:
            tokens = n.split()
            if len(tokens) >= 2:
                variants.append(f"{tokens[-1]} {' '.join(tokens[:-1])}")
                variants.append(f"{tokens[-1]}, {' '.join(tokens[:-1])}")
        return list(dict.fromkeys(variants))

    def _download_bulk(self) -> Path | None:
        TMP_DIR.mkdir(parents=True, exist_ok=True)
        dest = TMP_DIR / "hcad_real_acct.zip"
        if dest.exists() and dest.stat().st_size > 100_000:
            log.info("Using cached HCAD zip: %s (%d bytes)", dest, dest.stat().st_size)
            return dest

        for url in self.DOWNLOAD_URLS:
            try:
                log.info("Trying HCAD download: %s", url)
                r = requests.get(url, timeout=180, stream=True)
                if r.status_code == 200:
                    size = 0
                    with open(dest, "wb") as fh:
                        for chunk in r.iter_content(65536):
                            fh.write(chunk)
                            size += len(chunk)
                    if size > 100_000:
                        log.info("Downloaded HCAD -> %s (%d bytes)", dest, size)
                        return dest
                    else:
                        log.warning("Downloaded file too small (%d bytes), skipping", size)
                        dest.unlink(missing_ok=True)
                else:
                    log.warning("HTTP %d for %s", r.status_code, url)
            except Exception as exc:
                log.warning("HCAD download failed (%s): %s", url, exc)

        log.error("All HCAD download URLs failed — address enrichment disabled.")
        return None

    def _load_txt(self, zip_path: Path):
        """Parse real_acct.txt (tab-delimited) from the zip file."""
        extract_dir = TMP_DIR / "hcad_extracted"
        extract_dir.mkdir(parents=True, exist_ok=True)

        try:
            with zipfile.ZipFile(zip_path, "r") as zf:
                members = zf.namelist()
                log.info("HCAD zip contents: %s", members)
                txt_members = [m for m in members if m.lower().endswith(".txt")]
                if not txt_members:
                    log.error("No .txt files in HCAD zip: %s", members)
                    return
                zf.extractall(extract_dir)
        except Exception as exc:
            log.error("Failed to extract HCAD zip: %s", exc)
            return

        # Find real_acct.txt
        chosen = None
        for name in ["real_acct.txt", "Real_acct.txt", "REAL_ACCT.TXT"]:
            c = extract_dir / name
            if c.exists():
                chosen = c
                break
        if chosen is None:
            # Just take the first .txt
            chosen = extract_dir / txt_members[0]

        log.info("Loading HCAD parcel txt: %s (%d bytes)", chosen, chosen.stat().st_size)
        count = 0
        errors = 0

        try:
            with open(chosen, "r", encoding="latin-1", errors="replace") as fh:
                for line in fh:
                    try:
                        cols = line.rstrip("\n").split("\t")
                        if len(cols) < 10:
                            continue

                        owner_raw = str(cols[2]).strip() if len(cols) > 2 else ""
                        if not owner_raw or owner_raw.lower() in ("owner_name", "owner"):
                            continue  # skip header row

                        # Site address
                        site_addr = str(cols[7]).strip()  if len(cols) > 7  else ""
                        site_city = str(cols[8]).strip()  if len(cols) > 8  else "Houston"
                        site_zip  = str(cols[10]).strip() if len(cols) > 10 else ""

                        # Mailing address
                        mail_addr = str(cols[11]).strip() if len(cols) > 11 else ""
                        mail_city = str(cols[14]).strip() if len(cols) > 14 else ""
                        mail_state= str(cols[15]).strip() if len(cols) > 15 else "TX"
                        mail_zip  = str(cols[16]).strip() if len(cols) > 16 else ""

                        parcel = {
                            "prop_address": site_addr,
                            "prop_city":    site_city or "Houston",
                            "prop_state":   "TX",
                            "prop_zip":     site_zip,
                            "mail_address": mail_addr,
                            "mail_city":    mail_city,
                            "mail_state":   mail_state or "TX",
                            "mail_zip":     mail_zip,
                        }

                        for variant in self._name_variants(owner_raw):
                            if variant not in self._idx:
                                self._idx[variant] = parcel
                        count += 1

                    except Exception:
                        errors += 1
                        continue

        except Exception as exc:
            log.error("Failed to read HCAD txt: %s", exc)
            return

        log.info("Parcel index built: %d records, %d variants, %d errors",
                 count, len(self._idx), errors)
        if count > 0:
            self._loaded = True

    def load(self):
        zip_path = self._download_bulk()
        if zip_path:
            self._load_txt(zip_path)

    def lookup(self, owner: str) -> dict:
        if not self._loaded or not owner:
            return {}
        for variant in self._name_variants(owner):
            hit = self._idx.get(variant)
            if hit:
                return hit
        return {}


# ---------------------------------------------------------------------------
# Harris County Clerk - Playwright scraper
# ---------------------------------------------------------------------------
class ClerkScraper:
    """
    Drives the Harris County Clerk Document Search Portal using Playwright.

    Real Property page (RP.aspx) - all property doc types.
    Foreclosures page (FRCL_R.aspx) - NOFC / TAXDEED only.

    Confirmed form field IDs from live portal log (run #4):
      Search btn : ctl00_ContentPlaceHolder1_btnSearch
      Date From  : ctl00_ContentPlaceHolder1_tbDateFrom  (assumed same pattern)
      Date To    : ctl00_ContentPlaceHolder1_tbDateTo
      Inst. Type : ctl00_ContentPlaceHolder1_tbInstrType
    """

    def __init__(self, date_from: str, date_to: str):
        self.date_from = date_from   # YYYY-MM-DD
        self.date_to   = date_to

    @staticmethod
    def _to_portal_date(iso: str) -> str:
        """YYYY-MM-DD -> MM/DD/YYYY (portal format)"""
        try:
            return datetime.strptime(iso, "%Y-%m-%d").strftime("%m/%d/%Y")
        except Exception:
            return iso

    async def _dump_inputs(self, page):
        """Log all input/select IDs on page so we can identify correct field names."""
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
        """
        Fill a form field by injecting value directly via JavaScript.
        This bypasses Playwright visibility checks which fail on ASP.NET portals
        where fields exist in DOM but may not be 'visible' per Playwright's rules.
        """
        for frag in fragments:
            js = f"""
            () => {{
                // Search all inputs/selects whose id or name contains the fragment
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
        """Fill the Real Property search form and submit."""
        portal_from = self._to_portal_date(self.date_from)
        portal_to   = self._to_portal_date(self.date_to)

        # Wait for form to be ready
        try:
            await page.wait_for_selector(
                '#ctl00_ContentPlaceHolder1_txtFrom',
                state="attached", timeout=15_000
            )
        except Exception:
            log.warning("  Form not ready after 15s — proceeding anyway")

        # Dump all inputs on first call for each page type
        if doc_code == TARGET_CODES[0] or (doc_code in FRCL_TYPES and doc_code == list(FRCL_TYPES)[0]):
            await self._dump_inputs(page)

        # Date From — RP page: txtFrom / FRCL page: may use txtBegDate or txtFrom
        await self._set_field(page, [
            "txtFrom", "txtBegDate", "txtStartDate", "DateFrom",
            "dateFrom", "tbDateFrom", "BeginDate",
        ], portal_from, "DateFrom")

        # Date To — RP page: txtTo / FRCL page: may use txtEndDate or txtTo
        await self._set_field(page, [
            "txtTo", "txtEndDate", "txtStopDate", "DateTo",
            "dateTo", "tbDateTo", "EndDate",
        ], portal_to, "DateTo")

        # Instrument Type — RP page: txtInstrument
        await self._set_field(page, [
            "txtInstrument", "txtDocType", "Instrument",
            "InstrType", "InstrumentType", "DocType",
        ], doc_code, "InstrType")

        # Search button — confirmed id from run #4 log
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
        """
        Parse results table from Harris County Clerk portal.

        Confirmed column structure from live portal (April 2026):
          0: File Number
          1: File Date
          2: Type Vol Page
          3: Names (contains Grantor:/Grantee: lines)
          4: Legal Description (contains Desc:/Lot:/Block:/Sec: etc.)
          5: Pgs
          6: Film Code  ← has the direct document link
        """
        records: list[dict] = []
        cat, cat_label = DOC_TYPE_MAP.get(doc_code, ("other", doc_code))
        html = await page.content()
        soup = BeautifulSoup(html, "lxml")

        # Find results table — confirmed structure: has "File Number" header
        # and "Grantor:" text in the body
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

        # Log first data row for debugging
        if len(rows) > 1:
            first_cells = rows[1].find_all(["td", "th"])
            log.info("  First row has %d cells: %s",
                     len(first_cells),
                     " | ".join(c.get_text(" ", strip=True)[:30] for c in first_cells[:5]))

        for row in rows[1:]:
            cells = row.find_all(["td", "th"])
            if not cells or len(cells) < 3:
                continue
            try:
                def ct(idx: int) -> str:
                    return cells[idx].get_text(" ", strip=True) if idx < len(cells) else ""

                # Col 0: File Number
                doc_num = ct(0).strip()
                # Skip header rows and empty rows
                if not doc_num or doc_num.lower() in ("file number", ""):
                    continue
                # Skip rows that don't look like doc numbers (RP-YYYY-NNNNNN pattern)
                # but still accept any non-empty value

                # Col 1: File Date
                filed = _parse_date(ct(1).strip())

                # Col 3: Names — parse Grantor/Grantee
                names_text = ct(3) if len(cells) > 3 else ""
                grantors, grantees = [], []
                for line in names_text.replace("Grantor:", "\nGrantor:").replace("Grantee:", "\nGrantee:").split("\n"):
                    line = line.strip()
                    if line.lower().startswith("grantor:"):
                        val = line[8:].strip()
                        if val:
                            grantors.append(val)
                    elif line.lower().startswith("grantee:"):
                        val = line[8:].strip()
                        if val:
                            grantees.append(val)
                grantor = "; ".join(grantors) if grantors else names_text[:100]
                grantee = "; ".join(grantees)

                # Col 4: Legal Description
                legal_text = ct(4).strip() if len(cells) > 4 else ""

                # Col 6: Film Code link
                clerk_url = ""
                if len(cells) > 6:
                    a = cells[6].find("a", href=True)
                    if a:
                        href = a.get("href", "")
                        if href.startswith("http"):
                            clerk_url = href
                        elif href.startswith("/"):
                            clerk_url = CLERK_BASE + href
                # Fallback: any link in the row
                if not clerk_url:
                    a = row.find("a", href=True)
                    if a:
                        href = a.get("href", "")
                        if href.startswith("http"):
                            clerk_url = href
                        elif href.startswith("/"):
                            clerk_url = CLERK_BASE + href

                prop_addr = _extract_address_from_legal(legal_text)

                records.append({
                    "doc_num":      doc_num,
                    "doc_type":     doc_code,
                    "filed":        filed,
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
                log.debug("Row parse error (%s): %s", doc_code, exc)
                continue

        return records

    async def _paginate(self, page, doc_code: str) -> list[dict]:
        all_recs: list[dict] = []
        while True:
            recs = await self._parse_rp_page(page, doc_code)
            all_recs.extend(recs)
            next_el = page.locator(
                'a:has-text("Next"), input[value*="Next"], a[id*="Next"], a[id*="next"]'
            ).first
            if await next_el.count() == 0:
                break
            try:
                await next_el.click()
                await page.wait_for_load_state("networkidle", timeout=30_000)
            except Exception:
                break
        return all_recs

    async def _scrape_doc_type(self, page, doc_code: str, url: str) -> list[dict]:
        for attempt in range(1, 4):
            try:
                await page.goto(url, wait_until="domcontentloaded", timeout=60_000)
                # Wait for full JS render — portal uses ASP.NET UpdatePanels
                await page.wait_for_load_state("networkidle", timeout=30_000)
                await asyncio.sleep(2)  # extra buffer for JS to finish rendering form
                await self._fill_rp_form(page, doc_code, url)
                return await self._paginate(page, doc_code)
            except Exception as exc:
                log.warning("Attempt %d scraping %s: %s", attempt, doc_code, exc)
                if attempt < 3:
                    await asyncio.sleep(3 * attempt)
        return []

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

            for doc_code in TARGET_CODES:
                url = CLERK_FRCL_URL if doc_code in FRCL_TYPES else CLERK_RP_URL
                log.info("Fetching %s from %s", doc_code, url)
                recs = await self._scrape_doc_type(page, doc_code, url)
                log.info("  %s -> %d records", doc_code, len(recs))
                all_records.extend(recs)

            await browser.close()

        return all_records


# ---------------------------------------------------------------------------
# Fallback static scraper (requests + BeautifulSoup)
# ---------------------------------------------------------------------------
class StaticClerkScraper:
    """Fallback when Playwright unavailable. Handles ASP.NET __doPostBack."""

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
        for name in ["__VIEWSTATE", "__VIEWSTATEGENERATOR", "__EVENTVALIDATION",
                     "__SCROLLPOSITIONX", "__SCROLLPOSITIONY"]:
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

            while True:
                soup = BeautifulSoup(resp.text, "lxml")
                rows = self._parse_table(soup, doc_code, cat, cat_label)
                records.extend(rows)

                next_link = soup.find("a", string=re.compile(r"Next|>", re.I))
                if not next_link:
                    break
                onclick = next_link.get("href", "")
                m = re.search(r"__doPostBack\('([^']+)','([^']*)'\)", onclick)
                if not m:
                    break
                vs2 = self._viewstate(resp.text)
                payload2 = {**vs2, "__EVENTTARGET": m.group(1), "__EVENTARGUMENT": m.group(2)}
                resp = self.session.post(url, data=payload2, timeout=60)
                resp.raise_for_status()

        except Exception as exc:
            log.warning("Static scraper %s @ %s: %s", doc_code, url, exc)
        return records

    def _parse_table(self, soup, doc_code, cat, cat_label) -> list[dict]:
        records = []
        for tbl in soup.find_all("table"):
            text = tbl.get_text(" ", strip=True).lower()
            if not any(k in text for k in ("grantor", "filed", "instrument", "file number")):
                continue
            for row in tbl.find_all("tr")[1:]:
                cells = row.find_all("td")
                if not cells:
                    continue
                try:
                    link = row.find("a", href=True)
                    href = link.get("href", "") if link else ""
                    clerk_url = (href if href.startswith("http")
                                 else (CLERK_BASE + "/" + href.lstrip("/")) if href else "")
                    texts = [c.get_text(" ", strip=True) for c in cells]
                    records.append({
                        "doc_num":      texts[0] if texts else "",
                        "doc_type":     doc_code,
                        "filed":        _parse_date(texts[1] if len(texts) > 1 else ""),
                        "cat":          cat,
                        "cat_label":    cat_label,
                        "owner":        texts[2] if len(texts) > 2 else "",
                        "grantee":      texts[3] if len(texts) > 3 else "",
                        "amount":       _parse_amount(texts[4] if len(texts) > 4 else ""),
                        "legal":        texts[5] if len(texts) > 5 else "",
                        "prop_address": "", "prop_city": "Houston",
                        "prop_state":   "TX", "prop_zip": "",
                        "mail_address": "", "mail_city": "",
                        "mail_state":   "", "mail_zip": "",
                        "clerk_url":    clerk_url,
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
            for attempt in range(1, 4):
                try:
                    recs = self._search(url, doc_code)
                    log.info("  %s -> %d records", doc_code, len(recs))
                    all_records.extend(recs)
                    break
                except Exception as exc:
                    log.warning("  Attempt %d failed: %s", attempt, exc)
                    if attempt < 3:
                        time.sleep(3 * attempt)
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
            first, last = split_name(r.get("owner", ""))
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

    # 1. Clerk scrape
    if HAS_PW:
        scraper = ClerkScraper(date_from, date_to)
        records = await scraper.fetch_all()
    else:
        log.warning("Playwright unavailable - using static scraper.")
        scraper = StaticClerkScraper(date_from, date_to)
        records = scraper.fetch_all()

    log.info("Raw records fetched: %d", len(records))

    # 2. Dedup
    records = _deduplicate(records)
    log.info("After dedup: %d", len(records))

    # 3. HCAD enrichment
    log.info("Loading HCAD parcel data...")
    parcel_db = ParcelLookup()
    parcel_db.load()
    enriched = 0
    for rec in records:
        hit = parcel_db.lookup(rec.get("owner", ""))
        if hit:
            rec.update({k: v for k, v in hit.items() if v})
            enriched += 1
    log.info("Parcel enrichment: %d/%d matched", enriched, len(records))

    # 4. Score
    for rec in records:
        score, flags = compute_score(rec)
        rec["score"] = score
        rec["flags"] = flags
    records.sort(key=lambda r: r.get("score", 0), reverse=True)

    # 5. Save
    save_output(records, date_from, date_to)
    export_ghl_csv(records, GHL_CSV)

    log.info("=" * 60)
    log.info("DONE - %d total leads", len(records))
    for code in TARGET_CODES:
        cnt = sum(1 for r in records if r.get("doc_type") == code)
        if cnt:
            log.info("  %-12s %d", code, cnt)
    log.info("=" * 60)
    return 0


if __name__ == "__main__":
    sys.exit(asyncio.run(main()))
