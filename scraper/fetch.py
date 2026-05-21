import os
import re
import io
import json
import logging
import asyncio
from datetime import datetime, timedelta
import requests
from bs4 import BeautifulSoup

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
log = logging.getLogger("harris_scraper")

CLERK_RP_URL = "https://www.cclerk.hctx.net/applications/websearch/RP.aspx"
CLERK_FRCL_URL = "https://www.cclerk.hctx.net/applications/websearch/FRCL_R.aspx"

class HarrisScraper:
    def __init__(self, days_lookback: int = 60):
        now = datetime.now()
        self.date_to = now.strftime("%m/%d/%Y")
        self.date_from = (now - timedelta(days=days_lookback)).strftime("%m/%d/%Y")
        log.info("Direct Parameter Scraper active: %s to %s", self.date_from, self.date_to)

    async def fetch_all(self) -> list[dict]:
        records = []
        session = requests.Session()
        session.headers.update({
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"
        })

        # Directly query the structural data engine endpoints
        for code in ["NOFC", "DB", "MTG", "NTC", "NOT", "TXD"]:
            log.info("Requesting raw rows for instrument: %s", code)
            try:
                # Bypass UI elements by pinging public search indices directly
                resp = session.get(f"{CLERK_RP_URL}?i={code}&f={self.date_from}&t={self.date_to}", timeout=30)
                if resp.status_code == 200:
                    soup = BeautifulSoup(resp.text, "lxml")
                    rows = soup.select("table[id*='gvDocList'] tr")
                    
                    for row in rows[1:]:
                        cells = [td.get_text(strip=True) for td in row.find_all("td")]
                        if len(cells) < 5:
                            continue
                        
                        doc_num = cells[1]
                        file_date = cells[2]
                        grantor = cells[4].upper() if len(cells) > 4 else "UNKNOWN"
                        grantee = cells[5].upper() if len(cells) > 5 else "UNKNOWN"
                        legal = cells[6].upper() if len(cells) > 6 else ""

                        records.append({
                            "id": f"RP-{doc_num}",
                            "doc_num": doc_num,
                            "date": file_date,
                            "type": code,
                            "owner": grantor,
                            "grantee": grantee,
                            "prop_address": "HOUSTON, TX",
                            "legal": legal,
                            "score": 50 if code == "NOFC" else 20,
                            "clerk_url": f"https://www.cclerk.hctx.net/applications/websearch/ViewECDocs.aspx?f=RP-{doc_num}"
                        })
            except Exception as e:
                log.error("Endpoint bypass exception on %s: %s", code, e)
                
        return records

async def main():
    scraper = HarrisScraper(days_lookback=60)
    all_leads = await scraper.fetch_all()
    
    log.info("Retrieved a total of %d items across parameters.", len(all_leads))
    
    output = {
        "total": len(all_leads),
        "with_address": 0,
        "fetched_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "records": all_leads
    }
    
    os.makedirs("dashboard", exist_ok=True)
    os.makedirs("data", exist_ok=True)
    
    with open("dashboard/records.json", "w") as f:
        json.dump(output, f, indent=2)
    with open("data/records.json", "w") as f:
        json.dump(output, f, indent=2)
        
    log.info("Master data objects saved successfully.")

if __name__ == "__main__":
    asyncio.run(main())
