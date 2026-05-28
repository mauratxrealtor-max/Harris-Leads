import os
import re
import io
import gzip
import csv
import json
import logging
import asyncio
from datetime import datetime, timedelta

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("harris_scraper")

class HarrisScraper:
    def __init__(self, days_lookback: int = 60):
        now = datetime.now()
        self.date_to = now.strftime("%m/%d/%Y")
        self.date_from = (now - timedelta(days=days_lookback)).strftime("%m/%d/%Y")
        log.info("Starting scraper session looking back from %s to %s", self.date_from, self.date_to)
        self.hcad_map = self.load_hcad_database()

    def load_hcad_database(self) -> dict:
        """Dynamically unzips and parses the HCAD reference tables to match legal data to physical addresses."""
        hcad_data = {}
        log.info("Scanning repository for HCAD lookup files...")
        for i in range(1, 4):
            filename = f"data/hcad_lookup_part{i}.csv.gz"
            if os.path.exists(filename):
                try:
                    log.info(f"Decompressing and indexing {filename}...")
                    with gzip.open(filename, 'rt', encoding='utf-8') as f:
                        reader = csv.DictReader(f)
                        for row in reader:
                            owner_key = str(row.get('owner', '')).strip().upper()
                            if owner_key:
                                hcad_data[owner_key] = row.get('site_addr', 'HOUSTON, TX')
                except Exception as e:
                    log.error(f"Error parsing local database file part {i}: {e}")
        log.info(f"HCAD initialization completed. Indexed {len(hcad_data)} regional property records.")
        return hcad_data

    async def login_to_clerk_office(self, page) -> bool:
        """Secure login layer for authenticated county document searches."""
        username = os.environ.get("CLERK_USER", "YOUR_USERNAME_HERE")
        password = os.environ.get("CLERK_PASS", "YOUR_PASSWORD_HERE")
        
        if username == "YOUR_USERNAME_HERE":
            log.info("Running in public access mode. No clerk credentials detected.")
            return False
            
        try:
            log.info("Attempting secure login to Harris County Clerk portal...")
            await page.goto("https://www.cclerk.hctx.net/Login.aspx", wait_until="domcontentloaded")
            await page.fill("input[id*='txtUsername']", username)
            await page.fill("input[id*='txtPassword']", password)
            await page.click("input[id*='btnLogin']")
            await asyncio.sleep(3)
            log.info("Clerk authentication successfully established!")
            return True
        except Exception as e:
            log.error(f"Authentication channel failed: {e}. Defaulting to public sandbox.")
            return False

    async def fetch_all(self, page) -> list[dict]:
        records = []
        await self.login_to_clerk_office(page)
        
        instrument_codes = ["DB", "MTG", "NTC", "NOT", "TXD", "LP"]
        for code in instrument_codes:
            log.info("Navigating straight to search results for instrument: %s", code)
            try:
                direct_url = f"https://www.cclerk.hctx.net/applications/websearch/RP.aspx?i={code}&f={self.date_from}&t={self.date_to}"
                
                await page.goto(direct_url, wait_until="domcontentloaded", timeout=45_000)
                await asyncio.sleep(4)
                
                rows = await page.locator("table[id*='gvDocList'] tr").all()
                if len(rows) <= 1:
                    log.info("No records found for %s in this date range.", code)
                    continue
                
                log.info("Found %d rows for %s. Extracting text...", len(rows) - 1, code)
                for row in rows[1:]:
                    cells = await row.locator("td").all_contents()
                    if len(cells) < 7:
                        continue
                        
                    doc_num = cells[1].strip()
                    file_date = cells[2].strip()
                    doc_type = cells[3].strip().upper() if cells[3].strip() else code
                    grantor = cells[4].strip().upper()
                    grantee = cells[5].strip().upper()
                    legal = cells[6].strip().upper()

                    matched_address = self.hcad_map.get(grantor, "View clerk file for property description summary metadata")

                    score = 50
                    if any(x in doc_type for x in ["MTG", "DEED", "TRUST"]): score = 85
                    elif any(x in doc_type for x in ["LP", "PENDENS"]): score = 75
                    elif any(x in doc_type for x in ["TXD", "LIEN"]): score = 90
                    elif any(x in doc_type for x in ["JUDG", "JUD"]): score = 70
                    elif any(x in doc_type for x in ["PROB", "WILL"]): score = 65

                    records.append({
                        "id": f"RP-{doc_num}",
                        "doc_num": doc_num,
                        "date": file_date,
                        "type": doc_type,
                        "owner": grantor if grantor else "UNKNOWN OWNER",
                        "grantee": grantee if grantee else "UNKNOWN LENDER",
                        "prop_address": matched_address,
                        "legal": legal,
                        "score": score,
                        "clerk_url": f"https://www.cclerk.hctx.net/applications/websearch/ViewECDocs.aspx?f=RP-{doc_num}"
                    })
            except Exception as e:
                log.error("Failed to extract data for instrument %s: %s", code, e)
                
        return records

async def main():
    from playwright.async_api import async_playwright
    
    lookback = int(os.environ.get("LOOKBACK_DAYS", "60"))
    scraper = HarrisScraper(days_lookback=lookback)
    
    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=True)
        context = await browser.new_context(user_agent="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36")
        page = await context.new_page()
        
        all_leads = await scraper.fetch_all(page)
        log.info("Scraper sequence finished. Retrieved a total of %d items.", len(all_leads))
        
        enriched_count = sum(1 for r in all_leads if r["prop_address"] != "View clerk file for property description summary metadata")

        output = {
            "total": len(all_leads),
            "with_address": enriched_count,
            "fetched_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "records": all_leads
        }
        
        with open("records.json", "w") as f:
            json.dump(output, f, indent=2)
            
        log.info("Root directory database updates completed successfully.")
        await browser.close()

if __name__ == "__main__":
    asyncio.run(main())
