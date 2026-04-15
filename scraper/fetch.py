"""
Harris County, Texas – Motivated Seller Lead Scraper
=====================================================
Targets:
  • Harris County Clerk public records portal (Playwright / dynamic JS)
  • HCAD (Harris County Appraisal District) bulk parcel data (requests)

Lead types: LP, NOFC, TAXDEED, JUD, CCJ, DRJUD, LNCORPTX, LNIRS, LNFED,
            LN, LNMECH, LNHOA, MEDLN, PRO, NOC, RELLP
"""

from __future__ import annotations

import asyncio
import csv
import io
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
from typing import Any

import requests
from bs4 import BeautifulSoup

# dbfread may not be present in every env – handled gracefully below
try:
    from dbfread import DBF
    HAS_DBF = True
except ImportError:
    HAS_DBF = False

# Playwright – async API
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
# Constants / configuration
# ---------------------------------------------------------------------------
LOOKBACK_DAYS: int = int(os.getenv("LOOKBACK_DAYS", "7"))

# Harris County Clerk – Official Records Search
CLERK_BASE = "https://www.cclerk.hctx.net/Applications/WebSearch/OfficialPublicRecords.aspx"
CLERK_DOC_BASE = "https://www.cclerk.hctx.net"

# HCAD bulk data page
HCAD_BULK_PAGE = "https://pdata.hcad.org/download/index.html"
HCAD_BULK_DIRECT = "https://pdata.hcad.org/data/cama/"  # fallback listing

# Output paths
ROOT = Path(__file__).resolve().parent.parent
DASHBOARD_JSON = ROOT / "dashboard" / "records.json"
DATA_JSON = ROOT / "data" / "records.json"
GHL_CSV = ROOT / "data" / "ghl_export.csv"
TMP_DIR = ROOT / "tmp"

# Doc-type map: clerk code → (category, human label)
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

TARGET_CODES = list(DOC_TYPE_MAP.keys())

# ---------------------------------------------------------------------------
# Retry helper
# ---------------------------------------------------------------------------
def retry(fn, attempts: int = 3, delay: float = 2.0, label: str = ""):
    """Synchronous retry wrapper."""
    last_exc: Exception | None = None
    for attempt in range(1, attempts + 1):
        try:
            return fn()
        except Exception as exc:
            last_exc = exc
            log.warning("Attempt %d/%d failed for %s: %s", attempt, attempts, label, exc)
            if attempt < attempts:
                time.sleep(delay * attempt)
    raise RuntimeError(f"All {attempts} attempts failed for {label}") from last_exc

# ---------------------------------------------------------------------------
# Score calculator
# ---------------------------------------------------------------------------
def compute_score(rec: dict) -> tuple[int, list[str]]:
    """Return (score 0-100, flags list)."""
    flags: list[str] = []
    score = 30  # base

    doc_type = rec.get("doc_type", "")
    cat = rec.get("cat", "")
    amount = rec.get("amount") or 0
    filed_str = rec.get("filed", "")
    owner = rec.get("owner", "") or ""
    prop_addr = rec.get("prop_address", "") or ""

    # Flags
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

    # "New this week" – filed within LOOKBACK_DAYS
    try:
        filed_dt = datetime.strptime(filed_str[:10], "%Y-%m-%d")
        if (datetime.utcnow() - filed_dt).days <= LOOKBACK_DAYS:
            flags.append("New this week")
    except Exception:
        pass

    # Score additions
    score += 10 * len(flags)

    # LP + Foreclosure combo bonus
    has_lp = any("lis pendens" in f.lower() for f in flags)
    has_fc = any("pre-foreclosure" in f.lower() for f in flags)
    if has_lp and has_fc:
        score += 20

    # Amount bonuses
    try:
        amt = float(amount)
        if amt > 100_000:
            score += 15
        elif amt > 50_000:
            score += 10
    except (TypeError, ValueError):
        pass

    # New this week bonus
    if "New this week" in flags:
        score += 5

    # Has address bonus
    if prop_addr and prop_addr.strip():
        score += 5

    return min(score, 100), list(dict.fromkeys(flags))  # cap at 100, dedup flags

# ---------------------------------------------------------------------------
# HCAD Parcel Lookup
# ---------------------------------------------------------------------------
class ParcelLookup:
    """
    Downloads HCAD bulk parcel data and builds a name → address index.
    HCAD publishes a zip of DBF files each year at pdata.hcad.org.
    """

    def __init__(self):
        self._idx: dict[str, dict] = {}   # normalised_name → parcel dict
        self._loaded = False

    # ------------------------------------------------------------------ #
    def _normalise(self, name: str) -> str:
        return re.sub(r"\s+", " ", name.upper().strip())

    def _name_variants(self, raw: str) -> list[str]:
        """Generate lookup variants from a raw owner name."""
        n = self._normalise(raw)
        variants = [n]
        # "LAST, FIRST" → "FIRST LAST"
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

    # ------------------------------------------------------------------ #
    def _download_bulk(self) -> Path | None:
        """Download the HCAD real_acct zip file. Returns local path or None."""
        TMP_DIR.mkdir(parents=True, exist_ok=True)
        dest = TMP_DIR / "hcad_parcel.zip"
        if dest.exists() and dest.stat().st_size > 10_000:
            log.info("Using cached HCAD parcel zip: %s", dest)
            return dest

        # Try to scrape the download page for the current year's zip
        year = datetime.utcnow().year
        candidate_urls = [
            f"https://pdata.hcad.org/data/cama/{year}/real_acct.zip",
            f"https://pdata.hcad.org/data/cama/{year-1}/real_acct.zip",
            "https://pdata.hcad.org/Pdata/property_account.zip",
        ]

        # Try to parse the bulk page for a link
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
                log.info("Trying HCAD parcel download: %s", url)
                r = requests.get(url, timeout=120, stream=True)
                if r.status_code == 200 and int(r.headers.get("content-length", 1)) > 10_000:
                    with open(dest, "wb") as fh:
                        for chunk in r.iter_content(65536):
                            fh.write(chunk)
                    log.info("Downloaded HCAD parcel data → %s (%d bytes)", dest, dest.stat().st_size)
                    return dest
            except Exception as exc:
                log.warning("Download failed (%s): %s", url, exc)

        log.error("Could not download HCAD parcel data – address enrichment disabled.")
        return None

    # ------------------------------------------------------------------ #
    def _load_dbf(self, zip_path: Path):
        """Extract DBF from zip and build the name index."""
        if not HAS_DBF:
            log.warning("dbfread not installed – skipping parcel enrichment.")
            return

        extract_dir = TMP_DIR / "hcad_extracted"
        extract_dir.mkdir(parents=True, exist_ok=True)

        try:
            with zipfile.ZipFile(zip_path, "r") as zf:
                members = zf.namelist()
                log.info("HCAD zip contents: %s", members)
                dbf_members = [m for m in members if m.lower().endswith(".dbf")]
                if not dbf_members:
                    log.error("No DBF files found in HCAD zip.")
                    return
                zf.extractall(extract_dir)
        except Exception as exc:
            log.error("Failed to extract HCAD zip: %s", exc)
            return

        # Prefer files that look like the main account table
        priority = ["real_acct.dbf", "account.dbf", "realprop.dbf"]
        chosen = None
        for p in priority:
            candidate = extract_dir / p
            if candidate.exists():
                chosen = candidate
                break
        if chosen is None:
            chosen = extract_dir / dbf_members[0]

        log.info("Loading parcel DBF: %s", chosen)
        count = 0
        try:
            table = DBF(str(chosen), ignore_missing_memofile=True, encoding="latin-1")
            for row in table:
                try:
                    row_dict = dict(row)
                    keys_upper = {k.upper(): v for k, v in row_dict.items()}

                    owner_raw = (
                        keys_upper.get("OWNER")
                        or keys_upper.get("OWN1")
                        or keys_upper.get("OWNER_NAME")
                        or ""
                    )
                    if not owner_raw:
                        continue
                    owner_raw = str(owner_raw).strip()

                    parcel = {
                        "prop_address": str(keys_upper.get("SITE_ADDR") or keys_upper.get("SITEADDR") or "").strip(),
                        "prop_city":    str(keys_upper.get("SITE_CITY") or keys_upper.get("CITY_NM") or "Houston").strip(),
                        "prop_state":   "TX",
                        "prop_zip":     str(keys_upper.get("SITE_ZIP") or keys_upper.get("ZIP") or "").strip(),
                        "mail_address": str(keys_upper.get("ADDR_1") or keys_upper.get("MAILADR1") or "").strip(),
                        "mail_city":    str(keys_upper.get("CITY") or keys_upper.get("MAILCITY") or "").strip(),
                        "mail_state":   str(keys_upper.get("STATE") or keys_upper.get("MAILSTATE") or "").strip(),
                        "mail_zip":     str(keys_upper.get("ZIP") or keys_upper.get("MAILZIP") or "").strip(),
                    }

                    for variant in self._name_variants(owner_raw):
                        if variant not in self._idx:
                            self._idx[variant] = parcel
                    count += 1
                except Exception:
                    continue
        except Exception as exc:
            log.error("Failed to read DBF rows: %s", exc)
            return

        log.info("Parcel index built: %d records, %d name variants", count, len(self._idx))
        self._loaded = True

    # ------------------------------------------------------------------ #
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
# Harris County Clerk Scraper (Playwright)
# ---------------------------------------------------------------------------
class ClerkScraper:
    """
    Scrapes Harris County Clerk official records search.
    The portal uses ASP.NET WebForms with __doPostBack for pagination / doc-type
    selection, so we use Playwright to drive the browser.
    """

    BASE_URL = CLERK_BASE

    def __init__(self, date_from: str, date_to: str):
        self.date_from = date_from  # YYYY-MM-DD
        self.date_to = date_to

    # ------------------------------------------------------------------ #
    async def _search_doc_type(self, page, doc_code: str) -> list[dict]:
        """Search a single document type and return raw records."""
        records: list[dict] = []

        try:
            # Navigate fresh each call to avoid stale form state
            await page.goto(self.BASE_URL, wait_until="domcontentloaded", timeout=60_000)
            await page.wait_for_load_state("networkidle", timeout=30_000)

            # Fill document type field (text box or dropdown)
            dt_sel = 'input[id*="DocType"], input[name*="DocType"], select[id*="DocType"]'
            dt_el = page.locator(dt_sel).first
            tag = await dt_el.evaluate("el => el.tagName.toLowerCase()") if await dt_el.count() else None

            if tag == "select":
                await dt_el.select_option(value=doc_code)
            elif tag == "input":
                await dt_el.fill(doc_code)
            else:
                log.warning("Cannot find DocType field for %s – skipping.", doc_code)
                return records

            # Fill date range
            from_sel = 'input[id*="DateFrom"], input[name*="DateFrom"], input[id*="BeginDate"]'
            to_sel   = 'input[id*="DateTo"],   input[name*="DateTo"],   input[id*="EndDate"]'
            await page.locator(from_sel).first.fill(self.date_from)
            await page.locator(to_sel).first.fill(self.date_to)

            # Submit search
            btn_sel = 'input[type="submit"], input[id*="Search"], button[id*="Search"]'
            await page.locator(btn_sel).first.click()
            await page.wait_for_load_state("networkidle", timeout=45_000)

            # Paginate through results
            while True:
                rows = await self._parse_results_page(page, doc_code)
                records.extend(rows)

                # Check for "Next" page link
                next_btn = page.locator('a:has-text("Next"), input[value="Next >"]').first
                if await next_btn.count() == 0:
                    break
                await next_btn.click()
                await page.wait_for_load_state("networkidle", timeout=30_000)

        except PWTimeout as exc:
            log.warning("Timeout scraping %s: %s", doc_code, exc)
        except Exception as exc:
            log.warning("Error scraping %s: %s\n%s", doc_code, exc, traceback.format_exc())

        return records

    # ------------------------------------------------------------------ #
    async def _parse_results_page(self, page, doc_code: str) -> list[dict]:
        """Extract records from the current result page."""
        records: list[dict] = []
        html = await page.content()
        soup = BeautifulSoup(html, "lxml")
        cat, cat_label = DOC_TYPE_MAP.get(doc_code, ("other", doc_code))

        # Harris County Clerk result tables are usually inside a GridView
        tables = soup.find_all("table")
        result_table = None
        for tbl in tables:
            headers = [th.get_text(strip=True).lower() for th in tbl.find_all("th")]
            if any(h in headers for h in ("document number", "doc number", "instrument", "filed", "grantor")):
                result_table = tbl
                break

        if result_table is None:
            # No results or different layout
            return records

        rows = result_table.find_all("tr")
        header_cells = [th.get_text(strip=True).lower() for th in rows[0].find_all(["th", "td"])] if rows else []

        def col(cells, *names) -> str:
            for name in names:
                for i, h in enumerate(header_cells):
                    if name in h and i < len(cells):
                        return cells[i].get_text(strip=True)
            return ""

        for row in rows[1:]:
            cells = row.find_all(["td", "th"])
            if not cells:
                continue
            try:
                # Find hyperlink for doc number / direct URL
                link_tag = row.find("a", href=True)
                clerk_url = ""
                if link_tag:
                    href = link_tag.get("href", "")
                    if not href.startswith("http"):
                        href = CLERK_DOC_BASE + "/" + href.lstrip("/")
                    clerk_url = href

                doc_num   = col(cells, "document", "instrument", "doc num", "doc no")
                if not doc_num and link_tag:
                    doc_num = link_tag.get_text(strip=True)

                filed     = col(cells, "filed", "date", "record date")
                grantor   = col(cells, "grantor", "owner", "name")
                grantee   = col(cells, "grantee", "lender", "party")
                legal     = col(cells, "legal", "description")
                amount_raw = col(cells, "amount", "consideration", "debt")

                # Normalise date
                filed_norm = _parse_date(filed)

                # Parse amount
                amount_float = _parse_amount(amount_raw)

                rec = {
                    "doc_num":   doc_num.strip(),
                    "doc_type":  doc_code,
                    "filed":     filed_norm,
                    "cat":       cat,
                    "cat_label": cat_label,
                    "owner":     grantor.strip(),
                    "grantee":   grantee.strip(),
                    "amount":    amount_float,
                    "legal":     legal.strip(),
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
                }
                records.append(rec)
            except Exception as exc:
                log.debug("Row parse error: %s", exc)
                continue

        return records

    # ------------------------------------------------------------------ #
    async def fetch_all(self) -> list[dict]:
        if not HAS_PW:
            log.error("Playwright not installed – clerk scraping disabled.")
            return []

        all_records: list[dict] = []
        async with async_playwright() as pw:
            browser = await pw.chromium.launch(headless=True, args=["--no-sandbox"])
            context = await browser.new_context(
                user_agent="Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                           "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"
            )
            page = await context.new_page()
            page.set_default_timeout(60_000)

            for doc_code in TARGET_CODES:
                log.info("Fetching clerk records: %s (%s–%s)", doc_code, self.date_from, self.date_to)
                for attempt in range(1, 4):
                    try:
                        recs = await self._search_doc_type(page, doc_code)
                        log.info("  %s → %d records", doc_code, len(recs))
                        all_records.extend(recs)
                        break
                    except Exception as exc:
                        log.warning("  Attempt %d for %s failed: %s", attempt, doc_code, exc)
                        if attempt < 3:
                            await asyncio.sleep(3 * attempt)

            await browser.close()

        return all_records

# ---------------------------------------------------------------------------
# Fallback: Static HTML scraper (requests + BeautifulSoup)
# Used when Playwright is unavailable or for supplemental data
# ---------------------------------------------------------------------------
class StaticClerkScraper:
    """
    Fallback scraper using requests + BeautifulSoup for static or
    semi-static pages. Also handles __doPostBack via session cookies.
    """

    SESSION_HEADERS = {
        "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                      "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.5",
    }

    def __init__(self, date_from: str, date_to: str):
        self.date_from = date_from
        self.date_to = date_to
        self.session = requests.Session()
        self.session.headers.update(self.SESSION_HEADERS)

    def _get_viewstate(self, html: str) -> dict[str, str]:
        """Extract ASP.NET hidden form fields."""
        soup = BeautifulSoup(html, "lxml")
        fields = {}
        for name in ["__VIEWSTATE", "__VIEWSTATEGENERATOR", "__EVENTVALIDATION"]:
            el = soup.find("input", {"name": name})
            if el:
                fields[name] = el.get("value", "")
        return fields

    def _search_doc_type(self, doc_code: str) -> list[dict]:
        records: list[dict] = []
        cat, cat_label = DOC_TYPE_MAP.get(doc_code, ("other", doc_code))

        try:
            # Initial GET
            resp = self.session.get(CLERK_BASE, timeout=30)
            resp.raise_for_status()
            vs = self._get_viewstate(resp.text)

            # POST search
            payload = {
                **vs,
                "__EVENTTARGET": "",
                "__EVENTARGUMENT": "",
                "ctl00$cphBody$txtDocType": doc_code,
                "ctl00$cphBody$txtDateFrom": self.date_from,
                "ctl00$cphBody$txtDateTo": self.date_to,
                "ctl00$cphBody$btnSearch": "Search",
            }
            resp = self.session.post(CLERK_BASE, data=payload, timeout=60)
            resp.raise_for_status()

            while True:
                soup = BeautifulSoup(resp.text, "lxml")
                rows = self._parse_table(soup, doc_code, cat, cat_label)
                records.extend(rows)

                # Pagination via __doPostBack
                next_link = soup.find("a", string=re.compile(r"Next|>", re.I))
                if not next_link:
                    break
                onclick = next_link.get("href", "")
                m = re.search(r"__doPostBack\('([^']+)','([^']*)'\)", onclick)
                if not m:
                    break
                vs2 = self._get_viewstate(resp.text)
                payload2 = {
                    **vs2,
                    "__EVENTTARGET": m.group(1),
                    "__EVENTARGUMENT": m.group(2),
                }
                resp = self.session.post(CLERK_BASE, data=payload2, timeout=60)
                resp.raise_for_status()

        except Exception as exc:
            log.warning("StaticScraper %s failed: %s", doc_code, exc)

        return records

    def _parse_table(self, soup: BeautifulSoup, doc_code: str, cat: str, cat_label: str) -> list[dict]:
        records: list[dict] = []
        tables = soup.find_all("table")
        for tbl in tables:
            headers = [th.get_text(strip=True).lower() for th in tbl.find_all("th")]
            if not any(h in headers for h in ("document", "grantor", "filed", "instrument")):
                continue
            for row in tbl.find_all("tr")[1:]:
                cells = row.find_all("td")
                if not cells:
                    continue
                try:
                    link = row.find("a", href=True)
                    clerk_url = ""
                    if link:
                        href = link.get("href", "")
                        clerk_url = href if href.startswith("http") else CLERK_DOC_BASE + "/" + href.lstrip("/")

                    texts = [c.get_text(strip=True) for c in cells]
                    doc_num = texts[0] if texts else ""
                    filed_norm = _parse_date(texts[1] if len(texts) > 1 else "")
                    grantor = texts[2] if len(texts) > 2 else ""
                    grantee = texts[3] if len(texts) > 3 else ""
                    amount_float = _parse_amount(texts[4] if len(texts) > 4 else "")
                    legal = texts[5] if len(texts) > 5 else ""

                    records.append({
                        "doc_num":   doc_num,
                        "doc_type":  doc_code,
                        "filed":     filed_norm,
                        "cat":       cat,
                        "cat_label": cat_label,
                        "owner":     grantor,
                        "grantee":   grantee,
                        "amount":    amount_float,
                        "legal":     legal,
                        "prop_address": "", "prop_city": "Houston",
                        "prop_state": "TX", "prop_zip": "",
                        "mail_address": "", "mail_city": "",
                        "mail_state": "", "mail_zip": "",
                        "clerk_url": clerk_url,
                        "flags": [], "score": 0,
                    })
                except Exception:
                    continue
        return records

    def fetch_all(self) -> list[dict]:
        all_records: list[dict] = []
        for doc_code in TARGET_CODES:
            log.info("Static scraping: %s", doc_code)
            for attempt in range(1, 4):
                try:
                    recs = self._search_doc_type(doc_code)
                    log.info("  %s → %d records", doc_code, len(recs))
                    all_records.extend(recs)
                    break
                except Exception as exc:
                    log.warning("  Attempt %d for %s failed: %s", attempt, doc_code, exc)
                    if attempt < 3:
                        time.sleep(3 * attempt)
        return all_records

# ---------------------------------------------------------------------------
# Utility helpers
# ---------------------------------------------------------------------------
def _parse_date(raw: str) -> str:
    """Normalise various date formats to YYYY-MM-DD."""
    if not raw:
        return ""
    raw = raw.strip()
    for fmt in ("%m/%d/%Y", "%Y-%m-%d", "%m-%d-%Y", "%d/%m/%Y", "%B %d, %Y"):
        try:
            return datetime.strptime(raw, fmt).strftime("%Y-%m-%d")
        except ValueError:
            continue
    # Fallback: extract digits
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
    """Deduplicate by doc_num+doc_type."""
    seen: set[str] = set()
    out: list[dict] = []
    for rec in records:
        key = f"{rec.get('doc_type','')}:{rec.get('doc_num','')}"
        if key not in seen:
            seen.add(key)
            out.append(rec)
    return out

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
        writer = csv.DictWriter(fh, fieldnames=columns)
        writer.writeheader()
        for r in records:
            first, last = split_name(r.get("owner", ""))
            writer.writerow({
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
    log.info("GHL CSV exported: %s (%d rows)", path, len(records))

# ---------------------------------------------------------------------------
# Save output JSON
# ---------------------------------------------------------------------------
def save_output(records: list[dict], date_from: str, date_to: str):
    with_addr = sum(1 for r in records if r.get("prop_address"))
    payload = {
        "fetched_at":  datetime.utcnow().isoformat() + "Z",
        "source":      "Harris County Clerk",
        "date_range":  {"from": date_from, "to": date_to},
        "total":       len(records),
        "with_address": with_addr,
        "records":     records,
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
    now = datetime.now(timezone.utc)
    date_to   = now.strftime("%Y-%m-%d")
    date_from = (now - timedelta(days=LOOKBACK_DAYS)).strftime("%Y-%m-%d")

    log.info("Harris County Motivated Seller Scraper")
    log.info("Date range: %s → %s", date_from, date_to)
    log.info("Target doc types: %s", ", ".join(TARGET_CODES))

    # ── 1. Fetch clerk records ────────────────────────────────────────────
    if HAS_PW:
        log.info("Using Playwright scraper.")
        scraper = ClerkScraper(date_from, date_to)
        records = await scraper.fetch_all()
    else:
        log.info("Playwright unavailable – using static HTTP scraper.")
        scraper_static = StaticClerkScraper(date_from, date_to)
        records = scraper_static.fetch_all()

    log.info("Total raw records fetched: %d", len(records))

    # ── 2. Deduplicate ───────────────────────────────────────────────────
    records = _deduplicate(records)
    log.info("After dedup: %d records", len(records))

    # ── 3. Enrich with parcel data ───────────────────────────────────────
    log.info("Loading HCAD parcel data…")
    parcel_db = ParcelLookup()
    parcel_db.load()

    enriched = 0
    for rec in records:
        hit = parcel_db.lookup(rec.get("owner", ""))
        if hit:
            rec.update({k: v for k, v in hit.items() if v})
            enriched += 1

    log.info("Parcel enrichment: %d/%d records matched", enriched, len(records))

    # ── 4. Compute scores & flags ────────────────────────────────────────
    for rec in records:
        score, flags = compute_score(rec)
        rec["score"] = score
        rec["flags"] = flags

    # Sort by score descending
    records.sort(key=lambda r: r.get("score", 0), reverse=True)

    # ── 5. Save outputs ──────────────────────────────────────────────────
    save_output(records, date_from, date_to)
    export_ghl_csv(records, GHL_CSV)

    # Summary
    log.info("=" * 60)
    log.info("SUMMARY")
    log.info("  Total leads:        %d", len(records))
    log.info("  With address:       %d", sum(1 for r in records if r.get("prop_address")))
    log.info("  High score (≥70):   %d", sum(1 for r in records if r.get("score", 0) >= 70))
    log.info("  Score avg:          %.1f", (sum(r.get("score", 0) for r in records) / len(records)) if records else 0)
    log.info("=" * 60)
    for code in TARGET_CODES:
        cnt = sum(1 for r in records if r.get("doc_type") == code)
        if cnt:
            log.info("  %-12s %d", code, cnt)

    return 0


if __name__ == "__main__":
    sys.exit(asyncio.run(main()))
