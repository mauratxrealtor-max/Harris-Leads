import os
import re
import io
import json
import logging
import asyncio
from datetime import datetime, timedelta
import pypdf
import requests
from bs4 import BeautifulSoup

# --- Configure Logging ---
logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("harris_scraper")

# --- Constants & Configuration ---
CLERK_RP_URL = "https://www.cclerk.hctx.net/applications/websearch/RP.aspx"
CLERK_FRCL_URL = "https://www.cclerk.hctx.net/applications/websearch/FRCL.aspx"

TARGET_CODES = ["NOFC", "DB", "MTG", "NTC", "NOT", "TXD"]
FRCL_TYPES = ["NOFC"]

DOC_TYPE_MAP = {
    "NOFC": ("foreclosure", "Notice of Foreclosure Sale"),
    "DB": ("deed", "Deed of Trust"),
    "MTG": ("mortgage", "Mortgage"),
    "NTC": ("notice", "Notice"),
    "NOT": ("notice", "Notice"),
    "TXD": ("tax", "Tax Deed"),
}

class HarrisScraper:
    def __init__(self, days_lookback: int = 14):
        now = datetime.now()
        self.date_to = now.strftime("%m/%d/%Y")
        self.date_from = (now - timedelta(days=days_lookback)).strftime("%m/%d/%Y")
        log.info("Initialized scraper: Lookback from %s to %s", self.date_from, self.date_to)

    def _months_in_range(self, from_str: str, to_str: str) -> list[tuple[int, int]]:
        d1 = datetime.strptime(from_str, "%m/%d/%Y")
        d2 = datetime.strptime(to_str, "%m/%d/%Y")
        months = []
        curr = datetime(d1.year, d1.month, 1)
        while curr <= d2:
            months.append((curr.year, curr.month))
            if curr.month == 12:
                curr = datetime(curr.year + 1, 1, 1)
            else:
                curr = datetime(curr.year, curr.month + 1, 1)
        return months

    async def _scrape_frcl_month(self, page, year: int, month: int) -> list[dict]:
        records: list[dict] = []
        try:
            await page.goto(CLERK_FRCL_URL, wait_until="domcontentloaded", timeout=30_000)
            
            # Form selections
            await page.select_option("select#ctl00_ContentPlaceHolder1_ddlYears", str(year))
            await page.select_option("select#ctl00_ContentPlaceHolder1_ddlMonths", f"{month:02d}")
            await page.click("input#ctl00_ContentPlaceHolder1_btnSearch")
            await page.wait_for_load_state("domcontentloaded")

            # Simple grid read layout
            rows = await page.locator("table#ctl00_ContentPlaceHolder1_gvDocList tr").all()
            if len(rows) <= 1:
                return records

            for row in rows[1:]:
                cells = await row.locator("td").all_contents()
                if len(cells) < 5:
                    continue
                
                doc_num = cells[1].strip()
                sale_date = cells[2].strip()
                file_date = cells[3].strip()
                
                href_el = row.locator("td a").first
                href = await href_el.get_attribute("href") or ""
                
                doc_url = ""
                if "ViewECDocs.aspx" in href:
                    doc_url = f"https://www.cclerk.hctx.net/applications/websearch/{href.strip()}"
                else:
                    doc_url = f"https://www.cclerk.hctx.net/applications/websearch/ViewECDocs.aspx?f=RP-{doc_num}"

                records.append({
                    "id": f"FRCL-{doc_num}",
                    "doc_num": doc_num,
                    "date": file_date,
                    "sale_date": sale_date,
                    "type": "NOFC",
                    "owner": "UNKNOWN OWNER",
                    "grantee": "UNKNOWN LENDER",
                    "prop_address": "HOUSTON, TX",
                    "legal": "",
                    "score": 50,
                    "clerk_url": doc_url
                })
        except Exception as e:
            log.error("Error scraping foreclosure grid month %d/%d: %s", month, year, e)
        return records

    async def _scrape_doc_type(self, page, doc_code: str, base_url: str) -> list[dict]:
        records: list[dict] = []
        try:
            await page.goto(base_url, wait_until="domcontentloaded", timeout=30_000)
            await page.fill("input#ctl00_ContentPlaceHolder1_txtFrom", self.date_from)
            await page.fill("input#ctl00_ContentPlaceHolder1_txtTo", self.date_to)
            await page.fill("input#ctl00_ContentPlaceHolder1_txtInstrument", doc_code)
            await page.click("input#ctl00_ContentPlaceHolder1_btnSearch")
            await page.wait_for_load_state("domcontentloaded")

            rows = await page.locator("table#ctl00_ContentPlaceHolder1_gvDocList tr").all()
            if len(rows) <= 1:
                return records

            cat, _ = DOC_TYPE_MAP.get(doc_code, ("other", doc_code))
            for row in rows[1:]:
                cells = await row.locator("td").all_contents()
                if len(cells) < 7:
                    continue
                
                doc_num = cells[1].strip()
                file_date = cells[2].strip()
                grantor = cells[4].strip().upper()
                grantee = cells[5].strip().upper()
                legal = cells[6].strip().upper()

                records.append({
                    "id": f"RP-{doc_num}",
                    "doc_num": doc_num,
                    "date": file_date,
                    "type": doc_code,
                    "owner": grantor if grantor else "UNKNOWN OWNER",
                    "grantee": grantee if grantee else "UNKNOWN LENDER",
                    "prop_address": "HOUSTON, TX",
                    "legal": legal,
                    "score": 30 if cat == "deed" else 15,
                    "clerk_url": f"https://www.cclerk.hctx.net/applications/websearch/ViewECDocs.aspx?f=RP-{doc_num}"
                })
        except Exception as e:
            log.error("Error scraping standard instrument type %s: %s", doc_code, e)
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

                            # If it's a scanned image file, run OCR
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

async def main():
    from playwright.async_api import async_playwright
    
    lookback = int(os.environ.get("LOOKBACK_DAYS", "14"))
    scraper = HarrisScraper(days_lookback=lookback)
    
    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=True)
        context = await browser.new_context()
        page = await context.new_page()
        
        log.info("Starting Harris County lead retrieval session...")
        all_leads = await scraper.fetch_all_on_page(page)
        log.info("Retrieved a total of %d raw items across structural fields.", len(all_leads))
        
        # Format output payload tracking structures
        total_count = len(all_leads)
        with_address = sum(1 for r in all_leads if r.get("prop_address") and "HOUSTON, TX" not in r.get("prop_address"))
        
        output = {
            "total": total_count,
            "with_address": with_address,
            "fetched_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "records": all_leads
        }
        
        os.makedirs("dashboard", exist_ok=True)
        os.makedirs("data", exist_ok=True)
        
        with open("dashboard/records.json", "w") as f:
            json.dump(output, f, indent=2)
        with open("data/records.json", "w") as f:
            json.dump(output, f, indent=2)
            
        log.
