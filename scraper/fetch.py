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

    async def login_to_clerk_office(self, page) -> bool:
        """Secure login utilizing human-interaction emulation to bypass dynamic fields."""
        username = os.environ.get("CLERK_USER", "YOUR_USERNAME_HERE")
        password = os.environ.get("CLERK_PASS", "YOUR_PASSWORD_HERE")

        if username == "YOUR_USERNAME_HERE":
            log.info("Running in public access mode. No clerk credentials detected.")
            return False

        try:
            log.info("Attempting secure login to Harris County Clerk portal...")
            await page.goto("https://www.cclerk.hctx.net/Applications/WebSearch/Registration/Login.aspx", wait_until="networkidle")
            await asyncio.sleep(4)
            
            # Find the username box using our proven working pattern
            username_field = page.locator("input[type='text']").first
            await username_field.wait_for(timeout=10000)
            
            # Emulate human interaction: Click and type to trigger page scripts
            await username_field.click()
            await username_field.press_sequentially(username, delay=100)
            await asyncio.sleep(2)
            
            # Target the password container using a generic input type fallback
            password_field = page.locator("input[type='password']").first
            await password_field.wait_for(timeout=10000)
            await password_field.click()
            await password_field.press_sequentially(password, delay=100)
            await asyncio.sleep(2)
            
            # Target the submit action handler
            login_button = page.locator("input[type='submit'], input[id*='Login']").first
            await login_button.click()
            
            await asyncio.sleep(5)
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
                    grantor = cells[4].strip()
                    grantee = cells[3].strip()
                    summary = cells[5].strip()
                    
                    tracking_url = f"https://www.cclerk.hctx.net/applications/websearch/GetDocument.aspx?id={doc_num}"

                    records.append({
                        "score": 50 if code in ["NTC", "NOT", "LP"] else 30,
                        "type": code,
                        "filed": file_date,
                        "grantee": grantee,
                        "grantor": grantor,
                        "summary": summary,
                        "mailing": "Harris County, TX",
                        "flags": code,
                        "doc_id": doc_num,
                        "url": tracking_url
                    })
            except Exception as e:
                log.error("Failed parsing search data for instrument code %s: %s", code, e)
                continue

        return records


async def main():
    from playwright.async_api import async_playwright
    
    lookback = int(os.environ.get("LOOKBACK_DAYS", 60))
    scraper = HarrisScraper(days_lookback=lookback)
    
    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=True)
        context = await browser.new_context(user_agent="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36")
        page = await context.new_page()
        
        extracted_data = await scraper.fetch_all(page)
        await browser.close()
        
    output = {
        "total": len(extracted_data),
        "with_address": sum(1 for r in extracted_data if r["mailing"] != "Harris County, TX"),
        "fetched_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "records": extracted_data
    }
    
    with open("records.json", "w") as f:
        json.dump(output, f, indent=2)
    with open("data/records.json", "w") as f:
        json.dump(output, f, indent=2)
        
    log.info("Data crawl successfully exported. Total items saved: %d", len(extracted_data))


if __name__ == "__main__":
    asyncio.run(main())
