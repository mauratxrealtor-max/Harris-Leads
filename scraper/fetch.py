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
        dest = TMP_DIR / "hcad_parcel.zip"
        if dest.exists() and dest.stat().st_size > 10_000:
            log.info("Using cached HCAD parcel zip: %s", dest)
            return dest

        year = datetime.utcnow().year
        candidate_urls = [
            f"https://pdata.hcad.org/data/cama/{year}/real_acct.zip",
            f"https://pdata.hcad.org/data/cama/{year-1}/real_acct.zip",
            "https://pdata.hcad.org/Pdata/property_account.zip",
        ]
        try:
            resp = requests.get(HCAD_BULK_PAGE, timeout=30)
            soup = BeautifulSoup(resp.text, "lxml")
            for a in soup.find_all("a", href=True):
                href = a["href"]
                if "real_acct" in href.lower() and href.endswith(".zip"):
                    if not href.startswith("http"):
                        href = "https://pdata.hcad.org" + href
                    candidate_urls.insert(0, href)
                    break
        except Exception as exc:
            log.warning("Could not parse HCAD bulk page: %s", exc)

        for url in candidate_urls:
            try:
                log.info("Trying HCAD download: %s", url)
                r = requests.get(url, timeout=120, stream=True)
                if r.status_code == 200 and int(r.headers.get("content-length", 1)) > 10_000:
                    with open(dest, "wb") as fh:
                        for chunk in r.iter_content(65536):
                            fh.write(chunk)
                    log.info("Downloaded HCAD -> %s (%d bytes)", dest, dest.stat().st_size)
                    return dest
            except Exception as exc:
                log.warning("HCAD download failed (%s): %s", url, exc)
        return None

    def _load_dbf(self, zip_path: Path):
        if not HAS_DBF:
            log.warning("dbfread not installed - skipping parcel enrichment.")
            return
        extract_dir = TMP_DIR / "hcad_extracted"
        extract_dir.mkdir(parents=True, exist_ok=True)
        try:
            with zipfile.ZipFile(zip_path, "r") as zf:
                members = zf.namelist()
                dbf_members = [m for m in members if m.lower().endswith(".dbf")]
                if not dbf_members:
                    return
                zf.extractall(extract_dir)
        except Exception as exc:
            log.error("Failed to extract HCAD zip: %s", exc)
            return

        priority = ["real_acct.dbf", "account.dbf", "realprop.dbf"]
        chosen = None
        for p in priority:
            c = extract_dir / p
            if c.exists():
                chosen = c
                break
        if chosen is None:
            chosen = extract_dir / dbf_members[0]

        log.info("Loading parcel DBF: %s", chosen)
        count = 0
        try:
            table = DBF(str(chosen), ignore_missing_memofile=True, encoding="latin-1")
            for row in table:
                try:
                    ku = {k.upper(): v for k, v in dict(row).items()}
                    owner_raw = str(ku.get("OWNER") or ku.get("OWN1") or ku.get("OWNER_NAME") or "").strip()
                    if not owner_raw:
                        continue
                    parcel = {
                        "prop_address": str(ku.get("SITE_ADDR") or ku.get("SITEADDR") or "").strip(),
                        "prop_city":    str(ku.get("SITE_CITY") or "Houston").strip(),
                        "prop_state":   "TX",
                        "prop_zip":     str(ku.get("SITE_ZIP") or "").strip(),
                        "mail_address": str(ku.get("ADDR_1") or ku.get("MAILADR1") or "").strip(),
                        "mail_city":    str(ku.get("CITY") or ku.get("MAILCITY") or "").strip(),
                        "mail_state":   str(ku.get("STATE") or ku.get("MAILSTATE") or "").strip(),
                        "mail_zip":     str(ku.get("ZIP") or ku.get("MAILZIP") or "").strip(),
                    }
                    for variant in self._name_variants(owner_raw):
                        if variant not in self._idx:
                            self._idx[variant] = parcel
                    count += 1
                except Exception:
                    continue
        except Exception as exc:
            log.error("Failed to read DBF: %s", exc)
            return
        log.info("Parcel index: %d records, %d name variants", count, len(self._idx))
        self._loaded = True

    def load(self):
        zip_path = self._download_bulk()
        if zip_path:
            self._load_dbf(zip_path)

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
        """Try every id/name fragment until one matches, then fill."""
        for frag in fragments:
            for attr in ["id", "name"]:
                sel = f'input[{attr}*="{frag}"], select[{attr}*="{frag}"]'
                try:
                    el = page.locator(sel).first
                    if await el.count():
                        actual = await el.get_attribute(attr) or frag
                        tag = await el.evaluate("el => el.tagName.toLowerCase()")
                        if tag == "select":
                            await el.select_option(value=value)
                        else:
                            await el.triple_click()
                            await el.fill(value)
                        log.info("  %s filled (matched %s='%s')", field_name, attr, actual)
                        return True
                except Exception:
                    continue
        log.warning("  Could not fill %s — no fragment matched %s", field_name, fragments)
        return False

    async def _fill_rp_form(self, page, doc_code: str):
        """Fill the Real Property search form and submit."""
        portal_from = self._to_portal_date(self.date_from)
        portal_to   = self._to_portal_date(self.date_to)

        # Dump all inputs on first call so we can read real IDs from the log
        if doc_code == TARGET_CODES[0]:
            await self._dump_inputs(page)

        # Date From — try every plausible fragment
        await self._set_field(page, [
            "DateFrom", "dateFrom", "tbDateFrom", "BeginDate", "StartDate",
            "dtFrom", "Date_From", "date_from", "FileDateFrom", "RecordDateFrom",
        ], portal_from, "DateFrom")

        # Date To
        await self._set_field(page, [
            "DateTo", "dateTo", "tbDateTo", "EndDate", "StopDate",
            "dtTo", "Date_To", "date_to", "FileDateTo", "RecordDateTo",
        ], portal_to, "DateTo")

        # Instrument Type
        await self._set_field(page, [
            "InstrType", "instrType", "tbInstrType", "InstrumentType",
            "DocType", "docType", "tbDocType", "instrument_type",
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
        """Extract records from the current result page."""
        records: list[dict] = []
        cat, cat_label = DOC_TYPE_MAP.get(doc_code, ("other", doc_code))
        html = await page.content()
        soup = BeautifulSoup(html, "lxml")

        # Find the results grid
        result_table = None
        for tbl in soup.find_all("table"):
            text = tbl.get_text(" ", strip=True).lower()
            if any(k in text for k in ("file number", "instrument", "grantor", "filed date", "film code")):
                result_table = tbl
                break

        if not result_table:
            log.debug("No result table found for %s", doc_code)
            return records

        rows = result_table.find_all("tr")
        if not rows:
            return records

        header_cells = [th.get_text(" ", strip=True).lower()
                        for th in rows[0].find_all(["th", "td"])]

        def colidx(*names) -> int:
            for name in names:
                for i, h in enumerate(header_cells):
                    if name in h:
                        return i
            return -1

        idx_doc     = colidx("file number", "instrument", "doc number", "film code")
        idx_filed   = colidx("filed", "date filed", "record date", "date")
        idx_grantor = colidx("grantor", "owner", "name")
        idx_grantee = colidx("grantee", "lender", "party")
        idx_amount  = colidx("amount", "consideration", "debt")
        idx_legal   = colidx("legal", "description", "subdivision")

        for row in rows[1:]:
            cells = row.find_all(["td", "th"])
            if not cells or len(cells) < 2:
                continue
            try:
                def cell_text(idx: int) -> str:
                    return cells[idx].get_text(" ", strip=True) if 0 <= idx < len(cells) else ""

                link_tag  = row.find("a", href=True)
                clerk_url = ""
                if link_tag:
                    href = link_tag.get("href", "")
                    clerk_url = href if href.startswith("http") else CLERK_BASE + "/" + href.lstrip("/")

                doc_num = cell_text(idx_doc)
                if not doc_num and link_tag:
                    doc_num = link_tag.get_text(" ", strip=True)

                records.append({
                    "doc_num":      doc_num.strip(),
                    "doc_type":     doc_code,
                    "filed":        _parse_date(cell_text(idx_filed)),
                    "cat":          cat,
                    "cat_label":    cat_label,
                    "owner":        cell_text(idx_grantor).strip(),
                    "grantee":      cell_text(idx_grantee).strip(),
                    "amount":       _parse_amount(cell_text(idx_amount)),
                    "legal":        cell_text(idx_legal).strip(),
                    "prop_address": "",
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
                await page.wait_for_load_state("networkidle", timeout=30_000)
                await self._fill_rp_form(page, doc_code)
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
                "ctl00$ContentPlaceHolder1$tbDateFrom":  self.date_from,
                "ctl00$ContentPlaceHolder1$tbDateTo":    self.date_to,
                "ctl00$ContentPlaceHolder1$tbInstrType": doc_code,
                "ctl00$ContentPlaceHolder1$btnSearch":   "Search",
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
