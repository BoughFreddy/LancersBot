#!/usr/bin/env python3
"""
Lancers.jp -> Telegram new-job alert bot.

Polls Lancers search pages, detects jobs that haven't been seen before,
and sends a Telegram message for each new one.
"""
import html
import json
import logging
import os
import random
import re
import signal
import sys
import time
from dataclasses import dataclass
from datetime import datetime
from urllib.parse import urljoin

import requests
from bs4 import BeautifulSoup
from dotenv import load_dotenv

load_dotenv()

# ---------------------------------------------------------------- config ----
SEARCH_URLS = [
    "https://www.lancers.jp/work/search/system?open=1&type%5B%5D=project&work_rank%5B%5D=0&work_rank%5B%5D=1&work_rank%5B%5D=2&work_rank%5B%5D=3",
    "https://www.lancers.jp/work/search/web?open=1&type%5B%5D=project&work_rank%5B%5D=0&work_rank%5B%5D=1&work_rank%5B%5D=2&work_rank%5B%5D=3",
]

BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
CHAT_IDS = [c.strip() for c in os.getenv("TELEGRAM_CHAT_ID", "").split(",") if c.strip()]
CHECK_INTERVAL = max(30, int(os.getenv("CHECK_INTERVAL", "180")))
SKIP_EXISTING = os.getenv("SKIP_EXISTING_ON_FIRST_RUN", "true").lower() in ("1", "true", "yes")
SEEN_FILE = os.getenv("SEEN_FILE", "seen_jobs.json")
# Keep only the newest N job ids in the file so it never grows forever
MAX_SEEN = int(os.getenv("MAX_SEEN", "5000"))
CONNECT_TIMEOUT = int(os.getenv("CONNECT_TIMEOUT", "15"))
READ_TIMEOUT = int(os.getenv("READ_TIMEOUT", "90"))
MAX_RETRIES = int(os.getenv("MAX_RETRIES", "4"))
# Alert on Telegram if every URL fails this many checks in a row (0 = never)
FAIL_ALERT_AFTER = int(os.getenv("FAIL_ALERT_AFTER", "5"))

BASE_URL = "https://www.lancers.jp"
HEADERS = {
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                   "(KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36"),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "ja,en-US;q=0.8,en;q=0.6",
    "Accept-Encoding": "gzip, deflate",
    "Referer": "https://www.lancers.jp/work/search/system",
    "Connection": "keep-alive",
    "Upgrade-Insecure-Requests": "1",
}
DETAIL_RE = re.compile(r"/work/detail/(\d+)")

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.StreamHandler(sys.stdout)],
)
log = logging.getLogger("lancers-bot")


# ------------------------------------------------------------------ model ---
@dataclass
class Job:
    id: str
    title: str
    url: str
    price: str = ""
    deadline: str = ""
    proposals: str = ""
    category: str = ""
    description: str = ""
    client: str = ""


# --------------------------------------------------------------- storage ----
class Store:
    """Remembers already-seen job ids in a JSON file, e.g. ["5123456", "5123457"]"""

    def __init__(self, path: str):
        self.path = path
        self.ids: set[str] = set()
        if os.path.exists(path):
            try:
                with open(path, encoding="utf-8") as f:
                    data = json.load(f)
                # accept the old {"id": {...}} format too
                self.ids = {str(i) for i in (data.keys() if isinstance(data, dict) else data)}
                log.info("Loaded %d seen job ids from %s", len(self.ids), path)
            except (json.JSONDecodeError, OSError) as e:
                backup = path + ".broken"
                log.error("Could not read %s (%s); moved it to %s and starting fresh", path, e, backup)
                try:
                    os.replace(path, backup)
                except OSError:
                    pass
                self.ids = set()

    def is_empty(self) -> bool:
        return not self.ids

    def has(self, job_id: str) -> bool:
        return job_id in self.ids

    def add(self, job: Job):
        self.ids.add(job.id)

    def save(self) -> bool:
        """Write the JSON file. Never raises: on failure the data stays in memory
        and is written on the next save."""
        ids = sorted(self.ids, key=int)
        if len(ids) > MAX_SEEN:  # drop the oldest (lowest) job ids
            ids = ids[-MAX_SEEN:]
            self.ids = set(ids)
        text = json.dumps(ids)
        tmp = self.path + ".tmp"

        # On Windows, antivirus / search indexer / OneDrive / an open editor can
        # lock the file for a moment, so retry the swap a few times.
        for attempt in range(10):
            try:
                with open(tmp, "w", encoding="utf-8") as f:
                    f.write(text)
                os.replace(tmp, self.path)  # atomic swap
                return True
            except PermissionError:
                time.sleep(0.2 * (attempt + 1))
            except OSError as e:
                log.warning("Saving %s failed: %s", self.path, e)
                time.sleep(0.5)

        # Last resort: write the file directly instead of swapping
        try:
            with open(self.path, "w", encoding="utf-8") as f:
                f.write(text)
            try:
                os.remove(tmp)
            except OSError:
                pass
            return True
        except OSError as e:
            log.error("Could not save %s (%s) - will retry on next save. "
                      "Is the file open in another program or another bot running?", self.path, e)
            return False

# --------------------------------------------------------------- scraper ----
def _clean(text: str) -> str:
    return re.sub(r"\s+", " ", text or "").strip()


def _find_card(link):
    """Walk up from a job link to the element that holds a single job card."""
    node = link
    for _ in range(8):
        parent = node.parent
        if parent is None or parent.name in ("body", "html"):
            break
        ids = {m.group(1) for a in parent.find_all("a", href=True)
               if (m := DETAIL_RE.search(a["href"]))}
        if len(ids) > 1:          # parent contains several jobs -> node is the card
            break
        node = parent
    return node


def _first(card, selectors):
    for sel in selectors:
        el = card.select_one(sel)
        if el and _clean(el.get_text()):
            return _clean(el.get_text(" "))
    return ""


def parse_jobs(page_html: str) -> list[Job]:
    soup = BeautifulSoup(page_html, "lxml")
    jobs: dict[str, Job] = {}

    for a in soup.find_all("a", href=True):
        m = DETAIL_RE.search(a["href"])
        if not m:
            continue
        job_id = m.group(1)
        title = _clean(a.get("title") or a.get_text(" "))
        # ignore links like "提案する" / "詳細を見る" when a real title exists
        if job_id in jobs:
            if len(title) > len(jobs[job_id].title) and len(title) < 200:
                jobs[job_id].title = title
            continue
        if not title:
            continue

        card = _find_card(a)
        text = _clean(card.get_text(" "))

        price = _first(card, ['[class*="price"]', '[class*="reward"]', '[class*="budget"]'])
        if not price:
            pm = re.search(r"[\d,]+\s*円(?:\s*[~〜～]\s*[\d,]+\s*円)?", text)
            price = pm.group(0) if pm else ""

        deadline = _first(card, ['[class*="limit"]', '[class*="deadline"]', '[class*="date"]'])
        if not deadline:
            dm = re.search(r"(?:あと|残り)\s*\d+\s*(?:日|時間|分)", text)
            deadline = dm.group(0) if dm else ""

        pr = re.search(r"提案\s*(\d+)\s*件?|(\d+)\s*件の提案", text)
        proposals = (pr.group(1) or pr.group(2)) if pr else ""

        category = _first(card, ['[class*="category"]', '[class*="tag"]'])
        description = _first(card, ['[class*="description"]', '[class*="detail"]', '[class*="text"]'])
        client = _first(card, ['[class*="client"]', '[class*="user-name"]', '[class*="author"]'])

        jobs[job_id] = Job(
            id=job_id,
            title=title[:200],
            url=urljoin(BASE_URL, f"/work/detail/{job_id}"),
            price=price[:80],
            deadline=deadline[:60],
            proposals=proposals,
            category=category[:80],
            description=description[:300],
            client=client[:60],
        )
    return list(jobs.values())


def make_session() -> requests.Session:
    s = requests.Session()
    s.headers.update(HEADERS)
    try:  # visit the top page once to get normal cookies, like a browser would
        s.get(BASE_URL + "/", timeout=(CONNECT_TIMEOUT, READ_TIMEOUT))
    except requests.RequestException as e:
        log.warning("Warm-up request failed (continuing): %s", e)
    return s


def fetch(session: requests.Session, url: str, retries: int = MAX_RETRIES) -> str | None:
    short = url.split("?")[0]
    for attempt in range(1, retries + 1):
        try:
            r = session.get(url, timeout=(CONNECT_TIMEOUT, READ_TIMEOUT))
            if r.status_code == 200:
                r.encoding = r.apparent_encoding or "utf-8"
                return r.text
            log.warning("HTTP %s for %s (attempt %d/%d)", r.status_code, short, attempt, retries)
        except requests.Timeout:
            log.warning("Timeout for %s (attempt %d/%d)", short, attempt, retries)
        except requests.RequestException as e:
            log.warning("Request error for %s (attempt %d/%d): %s", short, attempt, retries, e)
        if attempt < retries:
            time.sleep(10 * 2 ** (attempt - 1) + random.uniform(0, 5))  # ~10s, 20s, 40s...
    log.error("Giving up on %s for this round after %d attempts", short, retries)
    return None


# -------------------------------------------------------------- telegram ----
class Telegram:
    def __init__(self, token: str, chat_ids: list[str]):
        self.api = f"https://api.telegram.org/bot{token}"
        self.chat_ids = chat_ids
        self.s = requests.Session()

    def send(self, text: str):
        for chat_id in self.chat_ids:
            for _ in range(5):
                try:
                    r = self.s.post(f"{self.api}/sendMessage", timeout=30, data={
                        "chat_id": chat_id,
                        "text": text,
                        "parse_mode": "HTML",
                        "disable_web_page_preview": "true",
                    })
                    if r.status_code == 429:  # rate limited
                        wait = r.json().get("parameters", {}).get("retry_after", 5)
                        time.sleep(wait + 1)
                        continue
                    if not r.ok:
                        log.error("Telegram error %s: %s", r.status_code, r.text)
                    break
                except requests.RequestException as e:
                    log.error("Telegram request failed: %s", e)
                    time.sleep(3)
            time.sleep(0.5)  # stay well below Telegram limits

    def check(self) -> bool:
        try:
            r = self.s.get(f"{self.api}/getMe", timeout=15)
            if r.ok:
                log.info("Telegram bot: @%s", r.json()["result"]["username"])
                return True
            log.error("Telegram getMe failed: %s", r.text)
        except requests.RequestException as e:
            log.error("Telegram unreachable: %s", e)
        return False


def format_job(job: Job) -> str:
    e = html.escape
    lines = ["🆕 <b>New Lancers job</b>", "", f"<b>{e(job.title)}</b>"]
    if job.price:
        lines.append(f"💰 {e(job.price)}")
    if job.deadline:
        lines.append(f"⏰ {e(job.deadline)}")
    if job.proposals:
        lines.append(f"📨 提案 {e(job.proposals)}件")
    if job.category:
        lines.append(f"🏷 {e(job.category)}")
    if job.client:
        lines.append(f"👤 {e(job.client)}")
    if job.description and job.description != job.title:
        lines += ["", e(job.description)]
    lines += ["", f'🔗 <a href="{e(job.url)}">{e(job.url)}</a>']
    return "\n".join(lines)


# ------------------------------------------------------------------ main ----
_running = True


def _stop(*_):
    global _running
    log.info("Stopping...")
    _running = False


def run_once(session, store: Store, tg: Telegram, silent: bool) -> tuple[int, bool]:
    """Returns (alerts_sent, all_urls_failed)."""
    found: dict[str, Job] = {}
    ok = 0
    for i, url in enumerate(SEARCH_URLS):
        if i:
            time.sleep(random.uniform(5, 10))  # don't hit both pages at once
        page = fetch(session, url)
        if page is None:
            continue
        ok += 1
        jobs = parse_jobs(page)
        log.info("%d jobs parsed from %s", len(jobs), url.split("?")[0])
        if not jobs:
            log.warning("No jobs parsed - page layout may have changed or request was blocked")
        for j in jobs:
            found.setdefault(j.id, j)

    new = [j for j in found.values() if not store.has(j.id)]
    # oldest first (lower id = older) so messages arrive in posting order
    new.sort(key=lambda j: int(j.id))
    sent = 0
    for job in new:
        if not silent:
            tg.send(format_job(job))
            sent += 1
        store.add(job)
        store.save()  # save after each job so a crash never causes repeats
    if new:
        log.info("%d new jobs (%d alerted%s)", len(new), sent, ", silent first run" if silent else "")
    return sent, ok == 0


def main():
    if not BOT_TOKEN or not CHAT_IDS:
        log.error("Set TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID (see .env.example)")
        sys.exit(1)

    signal.signal(signal.SIGINT, _stop)
    signal.signal(signal.SIGTERM, _stop)

    tg = Telegram(BOT_TOKEN, CHAT_IDS)
    if not tg.check():
        sys.exit(1)

    store = Store(SEEN_FILE)
    session = make_session()
    first_run_silent = SKIP_EXISTING and store.is_empty()

    tg.send(f"✅ Lancers bot started. Checking every {CHECK_INTERVAL}s.")
    log.info("Started. interval=%ss urls=%d", CHECK_INTERVAL, len(SEARCH_URLS))

    fails = 0
    while _running:
        try:
            _, all_failed = run_once(session, store, tg, silent=first_run_silent)
            if all_failed:
                fails += 1
                log.error("Could not reach lancers.jp (%d check(s) in a row)", fails)
                if fails >= 2:
                    session.close()
                    session = make_session()  # fresh connection + cookies
                if FAIL_ALERT_AFTER and fails == FAIL_ALERT_AFTER:
                    tg.send(f"⚠️ lancers.jp has not responded for {fails} checks in a row. "
                            "Still retrying...")
            else:
                if FAIL_ALERT_AFTER and fails >= FAIL_ALERT_AFTER:
                    tg.send("✅ lancers.jp is reachable again.")
                fails = 0
                first_run_silent = False  # only drop silence after a successful fetch
        except Exception:
            log.exception("Unexpected error in check loop")
        for _ in range(CHECK_INTERVAL):
            if not _running:
                break
            time.sleep(1)


if __name__ == "__main__":
    main()