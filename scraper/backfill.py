"""
Harris County Motivated Seller Lead Scraper — Historical Backfill
Scrapes in 14-day chunks with delays to avoid portal rate-limiting.
Saves to dashboard/backfill.json — separate from daily records.json.
Usage: python scraper/backfill.py
"""
import asyncio
import csv
import json
import logging
import os
import re
import sys
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path

# Reuse all helpers from fetch.py
sys.path.insert(0, str(Path(__file__).parent))
from fetch import (
    ClerkScraper, StaticClerkScraper, ParcelLookup,
    _deduplicate, compute_score, export_ghl_csv,
    HAS_PW, TARGET_CODES, CLERK_FRCL_URL, CLERK_RP_URL,
    log,
)

try:
    from playwright.async_api import async_playwright
except ImportError:
    pass

# ---------------------------------------------------------------------------
# Backfill uses its OWN output files — never touches daily records.json
# ---------------------------------------------------------------------------
ROOT          = Path(__file__).resolve().parent.parent
BACKFILL_JSON = ROOT / "dashboard" / "backfill.json"
BACKFILL_DATA = ROOT / "data"      / "backfill.json"
BACKFILL_CSV  = ROOT / "data"      / "backfill_ghl_export.csv"

LOOKBACK_DAYS = int(os.getenv("LOOKBACK_DAYS", "365"))
CHUNK_DAYS    = 14   # portal max reliable window
CHUNK_DELAY   = 45   # seconds between chunks to avoid rate-limiting


# ---------------------------------------------------------------------------
# Save backfill output (separate files)
# ---------------------------------------------------------------------------
def _save_backfill(records: list[dict], date_from: str, date_to: str):
    with_addr = sum(1 for r in records if r.get("prop_address"))
    payload = {
        "fetched_at":   datetime.utcnow().isoformat() + "Z",
        "source":       "Harris County Clerk (backfill)",
        "date_range":   {"from": date_from, "to": date_to},
        "total":        len(records),
        "with_address": with_addr,
        "records":      records,
    }
    for dest in [BACKFILL_JSON, BACKFILL_DATA]:
        dest.parent.mkdir(parents=True, exist_ok=True)
        with open(dest, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, indent=2, default=str)
        log.info("Saved: %s (%d records)", dest, len(records))
    export_ghl_csv(records, BACKFILL_CSV)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
async def main():
    now       = datetime.now(timezone.utc)
    date_to   = now.strftime("%Y-%m-%d")
    date_from = (now - timedelta(days=LOOKBACK_DAYS)).strftime("%Y-%m-%d")

    log.info("=" * 60)
    log.info("Harris County Backfill Scraper")
    log.info("Date range : %s -> %s  (%d days)", date_from, date_to, LOOKBACK_DAYS)
    log.info("Chunk size : %d days, delay: %ds", CHUNK_DAYS, CHUNK_DELAY)
    log.info("=" * 60)

    # Build non-overlapping 14-day chunks
    chunks = []
    cur = datetime.strptime(date_from, "%Y-%m-%d").replace(tzinfo=timezone.utc)
    end = datetime.strptime(date_to,   "%Y-%m-%d").replace(tzinfo=timezone.utc)
    while cur <= end:
        nxt = min(cur + timedelta(days=CHUNK_DAYS), end)
        chunks.append((cur.strftime("%Y-%m-%d"), nxt.strftime("%Y-%m-%d")))
        cur = nxt + timedelta(days=1)

    log.info("Total chunks: %d", len(chunks))

    all_raw: list[dict] = []

    if HAS_PW:
        from playwright.async_api import async_playwright
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
                    log.info("Chunk %d: %d records (total so far: %d)",
                             i, len(recs), len(all_raw) + len(recs))
                    all_raw.extend(recs)
                except Exception as exc:
                    log.warning("Chunk %d failed: %s — skipping", i, exc)

                if i < len(chunks):
                    log.info("Waiting %ds before next chunk...", CHUNK_DELAY)
                    try:
                        await page.goto("about:blank", wait_until="domcontentloaded", timeout=10_000)
                    except Exception:
                        pass
                    await asyncio.sleep(CHUNK_DELAY)

            await browser.close()
    else:
        for i, (c_from, c_to) in enumerate(chunks, 1):
            log.info("--- Chunk %d/%d: %s -> %s ---", i, len(chunks), c_from, c_to)
            scraper = StaticClerkScraper(c_from, c_to)
            recs = scraper.fetch_all()
            log.info("Chunk %d: %d records", i, len(recs))
            all_raw.extend(recs)
            if i < len(chunks):
                time.sleep(CHUNK_DELAY)

    log.info("Raw records fetched: %d", len(all_raw))

    # Dedup
    records = _deduplicate(all_raw)
    log.info("After dedup: %d", len(records))

    # HCAD enrichment
    log.info("Loading HCAD parcel data...")
    parcel_db = ParcelLookup()
    parcel_db.load()
    enriched = 0
    for rec in records:
        owner = rec.get("owner", "")
        if not owner:
            continue
        hit = parcel_db.lookup(owner)
        if hit and hit.get("prop_address"):
            rec.update({k: v for k, v in hit.items() if v})
            enriched += 1
    log.info("Parcel enrichment: %d/%d matched", enriched, len(records))

    # Score
    for rec in records:
        score, flags = compute_score(rec)
        rec["score"] = score
        rec["flags"] = flags
    records.sort(key=lambda r: r.get("score", 0), reverse=True)

    # Save to backfill files only — never touches records.json
    _save_backfill(records, date_from, date_to)

    log.info("=" * 60)
    log.info("DONE — %d total leads", len(records))
    log.info("=" * 60)
    return 0


if __name__ == "__main__":
    sys.exit(asyncio.run(main()))
