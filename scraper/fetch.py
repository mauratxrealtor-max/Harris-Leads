import os
import re
import io
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

    async def fetch_all(self, page) -> list[dict]:
        records = []
        
        # We will loop through the core instrument codes you need
        for code in ["DB", "MTG", "NTC", "NOT", "TXD"]:
            log.info("Navigating straight to search results for instrument: %s", code)
            try:
                # Build the direct query URL string so we don't have to fill out text boxes or dropdowns
                direct_url = f"https://www.cclerk.hctx.net/applications/websearch/RP.aspx?i={code}&f={self.date_from}&t={self.date_to}"
                
                # Use the browser to load it so the county site doesn't block the request
                await page.goto(direct_url, wait_until="domcontentloaded", timeout=45_000)
                await asyncio.sleep(4)
                
                # Check if a results table loaded onto the page
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
                    grantor = cells[4].strip().upper()
                    grantee = cells[5].strip().upper()
                    legal = cells[6].strip().upper()

                    records.append({
                        "id": f"RP-{doc_num}",
                        "doc_num": doc_num,
                        "date": file_date,
                        "type": code,
                        "owner": grantor if grantor else "UNKNOWN OWNER",
                        "grantee": grantee if grantee else "UNKNOWN LENDER",
                        "prop_address": "HOUSTON, TX",
                        "legal": legal,
                        "score": 30 if code == "DB" else 15,
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
        
        output = {
            "total": len(all_leads),
            "with_address": 0,
            "fetched_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "records": all_leads
        }
        
        # Crucial fix: We make sure the dashboard folder is ALWAYS created even if records are 0
        os.makedirs("dashboard", exist_ok=True)
        os.makedirs("data", exist_ok=True)
        
        with open("dashboard/records.json", "w") as f:
            json.dump(output, f, indent=2)
        with open("data/records.json", "w") as f:
            json.dump(output, f, indent=2)
            
        # Create a dummy index file so the website host never breaks on deployment
        with open("dashboard/index.html", "w") as f:
            f.write("<html><body><h1>Harris County Leads Dashboard</h1></body></html>")
            
        log.info("All output directories populated successfully.")
        await browser.close()

if __name__ == "__main__":
    asyncio.run(main())
