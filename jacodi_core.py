#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Digikala Jacodi (Prize Catcher) Core Engine
===========================================
- Keycloak OIDC PKCE (S256) password login -> api.digikala.com/v1/user/login/
- Landing page HTML parser (server clock sync, round countdowns, current prize list)
- Strict Whitelist Prize Matcher (pre-configured with the 5 checked prizes from user's screenshot)
- Prize list change detection & persistent state
"""

from __future__ import annotations

import base64
import csv
import hashlib
import html as html_lib
import json
import re
import secrets
import time
import urllib.parse
import uuid
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from html.parser import HTMLParser
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple

import requests


TEHRAN_TZ = timezone(timedelta(hours=3, minutes=30))

AUTH_BASE = "https://auth.digikala.com/realms/dk-group"
OIDC_AUTH_URL = f"{AUTH_BASE}/protocol/openid-connect/auth"
OIDC_TOKEN_URL = f"{AUTH_BASE}/protocol/openid-connect/token"
OIDC_CLIENT_ID = "digikala-web-public"
OIDC_REDIRECT_URI = "https://www.digikala.com/sso-redirect/?back-url=%2Fprofile%2F"

DK_API_LOGIN_URL = "https://api.digikala.com/v1/user/login/"
LANDING_URL = "https://www.digikala.com/landings/prize-catcher/"
PRIZE_API_BASE = "https://api.digikala.com/prize-catcher/api/v1"
WIDGET_ME_URL = f"{PRIZE_API_BASE}/widget/me"
CLAIMS_URL = f"{PRIZE_API_BASE}/claims"
CLAIMS_ME_URL = f"{PRIZE_API_BASE}/claims/me"

DEFAULT_UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/131.0.0.0 Safari/537.36"
)

# Exact 5 wanted prizes (checked with green/red tick in user's screenshot)
DEFAULT_WANTED_PRIZES = [
    "۵۰۰ میلیون تومان تخفیف برای ۵ نفر",
    "۳ میلیون تومان تخفیف برای خرید بالای ۱۰ میلیون تومان",
    "۷۰۰ هزار تومان تخفیف برای خرید بالای ۲.۵ میلیون تومان",
    "۵۰۰ هزار تومان تخفیف برای خرید بالای ۲ میلیون تومان",
    "تا ۳۰۰ هزار تومان طلای دیجیتال دیجی‌کالا",
]

# Exact 2 unwanted prizes (crossed out in user's screenshot)
DEFAULT_UNWANTED_PRIZES = [
    "۳۰۰ هزار تومان تخفیف برای خرید بالای ۱ میلیون تومان",
    "کلی تخفیف از بازار دیجی‌کالا، سوپرمارکت، خودرو",
]

# Extra unwanted patterns explicitly mentioned by user's friend (e.g. 200k/800k, 400k/1M)
DEFAULT_UNWANTED_KEYWORDS = [
    "کلی تخفیف",
    "خرید بالای ۱ میلیون",
    "خرید بالای 1 میلیون",
    "خرید بالای ۸۰۰ هزار",
    "خرید بالای 800 هزار",
]

_PERSIAN_DIGITS = str.maketrans("۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩", "01234567890123456789")


def normalize_fa(text: str) -> str:
    if not text:
        return ""
    s = html_lib.unescape(text).translate(_PERSIAN_DIGITS)
    s = s.replace("ي", "ی").replace("ك", "ک").replace("ة", "ه").replace("أ", "ا").replace("إ", "ا")
    s = s.replace("\u200c", " ").replace("\u200f", "").replace("\u200e", "")
    s = re.sub(r"[،,;؛:.!؟?()\[\]«»\"'ـ]+", " ", s)
    s = re.sub(r"\s+", " ", s).strip().lower()
    return s


def normalize_phone(phone: str) -> str:
    p = phone.strip().translate(_PERSIAN_DIGITS)
    p = re.sub(r"[\s\-()]+", "", p)
    if p.startswith("+98"):
        p = "0" + p[3:]
    elif p.startswith("0098"):
        p = "0" + p[4:]
    elif p.startswith("98") and len(p) == 12:
        p = "0" + p[2:]
    elif p.startswith("9") and len(p) == 10:
        p = "0" + p
    return p


def parse_iso_utc(iso_str: Optional[str]) -> Optional[float]:
    if not iso_str:
        return None
    try:
        s = iso_str.strip()
        if s.endswith("Z"):
            s = s[:-1] + "+00:00"
        return datetime.fromisoformat(s).timestamp()
    except Exception:
        return None


def fmt_tehran(ts: Optional[float]) -> str:
    if ts is None:
        return "نامشخص"
    return datetime.fromtimestamp(ts, tz=TEHRAN_TZ).strftime("%Y-%m-%d %H:%M:%S")


def fmt_duration(seconds: float) -> str:
    sec = max(0, int(round(seconds)))
    h, rem = divmod(sec, 3600)
    m, s = divmod(rem, 60)
    if h > 0:
        return f"{h} ساعت و {m} دقیقه و {s} ثانیه"
    if m > 0:
        return f"{m} دقیقه و {s} ثانیه"
    return f"{s} ثانیه"


# ==============================================================================
# HTML Parsers
# ==============================================================================

class _FormParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.forms: List[Dict[str, Any]] = []
        self._current_form: Optional[Dict[str, Any]] = None
        self.error_messages: List[str] = []

    def handle_starttag(self, tag: str, attrs: List[Tuple[str, Optional[str]]]) -> None:
        t = tag.lower()
        attr_map = {k.lower(): (v or "") for k, v in attrs}
        if "data-error-message" in attr_map and attr_map["data-error-message"].strip():
            self.error_messages.append(attr_map["data-error-message"].strip())
        if t == "form":
            self._current_form = {
                "action": html_lib.unescape(attr_map.get("action", "")),
                "method": attr_map.get("method", "post").lower(),
                "id": attr_map.get("id", ""),
                "inputs": [],
            }
            self.forms.append(self._current_form)
        elif t in ("input", "button") and self._current_form is not None:
            self._current_form["inputs"].append(attr_map)

    def handle_endtag(self, tag: str) -> None:
        if tag.lower() == "form":
            self._current_form = None


def parse_html_forms(html_text: str) -> Tuple[List[Dict[str, Any]], List[str]]:
    parser = _FormParser()
    parser.feed(html_text or "")
    return parser.forms, parser.error_messages


@dataclass
class LandingState:
    round_status: str
    round_ends_at: Optional[float]
    next_round_starts_at: Optional[float]
    prizes: List[str]
    server_now: Optional[float]
    clock_offset_sec: float = 0.0


def extract_server_now(headers: Dict[str, str], local_now: Optional[float] = None) -> Tuple[Optional[float], float]:
    local_ts = local_now if local_now is not None else time.time()
    lower_headers = {k.lower(): v for k, v in headers.items()}

    st = lower_headers.get("server-timing", "")
    m = re.search(r"now\s*;\s*dur\s*=\s*([0-9]+(?:\.[0-9]+)?)", st)
    if m:
        server_ts = float(m.group(1))
        return server_ts, server_ts - local_ts

    date_hdr = lower_headers.get("date", "")
    if date_hdr:
        try:
            server_ts = parsedate_to_datetime(date_hdr).timestamp()
            return server_ts, server_ts - local_ts
        except Exception:
            pass

    return None, 0.0


def parse_landing_html(
    html_text: str,
    headers: Optional[Dict[str, str]] = None,
    local_now: Optional[float] = None,
) -> LandingState:
    server_now, offset = extract_server_now(headers or {}, local_now=local_now)

    m_round = re.search(r'<dk-prize-catcher[^>]*data-round="([^"]+)"', html_text, re.I)
    round_status = m_round.group(1).strip().lower() if m_round else "unknown"

    round_ends_at: Optional[float] = None
    m_curr_block = re.search(r'data-live="current-prizes".*?</section>', html_text, re.S | re.I)
    if m_curr_block:
        m_cd = re.search(r'data-countdown="([^"]+)"', m_curr_block.group(0), re.I)
        if m_cd:
            round_ends_at = parse_iso_utc(m_cd.group(1))
    if round_ends_at is None:
        m_cd_fallback = re.search(
            r'aria-label="[^"]*پایان این دور[^"]*"[^>]*data-countdown="([^"]+)"',
            html_text,
            re.I,
        )
        if m_cd_fallback:
            round_ends_at = parse_iso_utc(m_cd_fallback.group(1))

    next_round_starts_at: Optional[float] = None
    m_next = re.search(
        r'data-ref="next-round"[^>]*data-starts-at="([^"]+)"|data-starts-at="([^"]+)"[^>]*data-ref="next-round"',
        html_text,
        re.I,
    )
    if m_next:
        next_round_starts_at = parse_iso_utc(m_next.group(1) or m_next.group(2))

    prizes: List[str] = []
    block_html = ""
    m_ul = re.search(r'<ul[^>]*id="current-other-prizes"[^>]*>(.*?)</ul>', html_text, re.S | re.I)
    if m_ul:
        block_html = m_ul.group(1)
    else:
        m_spot = re.search(r'data-live="spotlight-prizes"[^>]*>.*?<ul[^>]*>(.*?)</ul>', html_text, re.S | re.I)
        if m_spot:
            block_html = m_spot.group(1)

    if block_html:
        raw_titles = re.findall(r'<span[^>]*class="[^"]*_title_[^"]*"[^>]*>(.*?)</span>', block_html, re.S | re.I)
        if not raw_titles:
            raw_titles = re.findall(r"<li[^>]*>(.*?)</li>", block_html, re.S | re.I)
        for t in raw_titles:
            clean = html_lib.unescape(re.sub(r"<[^>]+>", " ", t))
            clean = re.sub(r"\s+", " ", clean).strip()
            if clean and clean not in prizes:
                prizes.append(clean)

    return LandingState(
        round_status=round_status,
        round_ends_at=round_ends_at,
        next_round_starts_at=next_round_starts_at,
        prizes=prizes,
        server_now=server_now,
        clock_offset_sec=offset,
    )


# ==============================================================================
# Prize Preferences & Strict Whitelist Matcher
# ==============================================================================

@dataclass
class PrizePreferences:
    known_landing_prizes: List[str] = field(default_factory=lambda: list(DEFAULT_WANTED_PRIZES + DEFAULT_UNWANTED_PRIZES))
    wanted_prizes: List[str] = field(default_factory=lambda: list(DEFAULT_WANTED_PRIZES))
    unwanted_prizes: List[str] = field(default_factory=lambda: list(DEFAULT_UNWANTED_PRIZES))
    wanted_keywords: List[str] = field(default_factory=lambda: ["طلای دیجیتال", "500 میلیون", "3 میلیون", "700 هزار", "500 هزار"])
    unwanted_keywords: List[str] = field(default_factory=lambda: list(DEFAULT_UNWANTED_KEYWORDS))
    seen_claim_titles: Dict[str, str] = field(default_factory=dict)  # normalized_title -> "accept" | "dismiss"
    auto_accept_big_prize: bool = True
    auto_accept_hunt: bool = True
    updated_at: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return {
            "known_landing_prizes": self.known_landing_prizes,
            "wanted_prizes": self.wanted_prizes,
            "unwanted_prizes": self.unwanted_prizes,
            "wanted_keywords": self.wanted_keywords,
            "unwanted_keywords": self.unwanted_keywords,
            "seen_claim_titles": self.seen_claim_titles,
            "auto_accept_big_prize": self.auto_accept_big_prize,
            "auto_accept_hunt": self.auto_accept_hunt,
            "updated_at": self.updated_at,
        }

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> "PrizePreferences":
        return cls(
            known_landing_prizes=list(d.get("known_landing_prizes") or (DEFAULT_WANTED_PRIZES + DEFAULT_UNWANTED_PRIZES)),
            wanted_prizes=list(d.get("wanted_prizes") or []),
            unwanted_prizes=list(d.get("unwanted_prizes") or []),
            wanted_keywords=list(d.get("wanted_keywords") or []),
            unwanted_keywords=list(d.get("unwanted_keywords") or DEFAULT_UNWANTED_KEYWORDS),
            seen_claim_titles=dict(d.get("seen_claim_titles") or {}),
            auto_accept_big_prize=bool(d.get("auto_accept_big_prize", True)),
            auto_accept_hunt=bool(d.get("auto_accept_hunt", True)),
            updated_at=str(d.get("updated_at") or ""),
        )

    def save(self, path: Path) -> None:
        self.updated_at = datetime.now(TEHRAN_TZ).isoformat()
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(self.to_dict(), ensure_ascii=False, indent=2), encoding="utf-8")

    @classmethod
    def load_or_default(cls, path: Path) -> "PrizePreferences":
        if path.exists():
            try:
                return cls.from_dict(json.loads(path.read_text(encoding="utf-8")))
            except Exception:
                pass
        prefs = cls()
        prefs.save(path)
        return prefs

    def is_wanted_landing_prize(self, prize_title: str) -> bool:
        nt = normalize_fa(prize_title)
        return any(normalize_fa(w) == nt for w in self.wanted_prizes)

    def toggle_landing_prize(self, prize_title: str) -> bool:
        """Toggle a landing prize between wanted and unwanted. Returns new is_wanted state."""
        nt = normalize_fa(prize_title)
        if self.is_wanted_landing_prize(prize_title):
            self.wanted_prizes = [w for w in self.wanted_prizes if normalize_fa(w) != nt]
            if not any(normalize_fa(u) == nt for u in self.unwanted_prizes):
                self.unwanted_prizes.append(prize_title)
            return False
        else:
            self.unwanted_prizes = [u for u in self.unwanted_prizes if normalize_fa(u) != nt]
            self.wanted_prizes.append(prize_title)
            return True


def detect_prize_list_changes(old_prizes: List[str], new_prizes: List[str]) -> Tuple[List[str], List[str]]:
    old_map = {normalize_fa(p): p for p in old_prizes}
    new_map = {normalize_fa(p): p for p in new_prizes}
    added = [orig for norm, orig in new_map.items() if norm not in old_map]
    removed = [orig for norm, orig in old_map.items() if norm not in new_map]
    return added, removed


def decide_prize_action(prize_title: str, prize_kind: str, prefs: PrizePreferences) -> Tuple[str, str, bool]:
    """
    Strict Whitelist decision:
    Returns (decision, reason, is_unknown_title)
      - decision: 'accept' or 'dismiss'
      - is_unknown_title: True if title was never explicitly matched (so bot alerts user in Telegram)
    """
    kind = (prize_kind or "").lower()
    if kind == "big_prize" and prefs.auto_accept_big_prize:
        return "accept", "جایزه بزرگ (big_prize)", False
    if kind == "hunt" and prefs.auto_accept_hunt:
        return "accept", "جایزه شکار گنج (hunt)", False

    norm_title = normalize_fa(prize_title)

    # 1. Explicit user decision on this exact claim title
    if norm_title in prefs.seen_claim_titles:
        dec = prefs.seen_claim_titles[norm_title]
        return dec, f"انتخاب قبلی کاربر ({dec})", False

    # 2. Explicit unwanted keywords (protect 3/day quota first)
    for kw in prefs.unwanted_keywords:
        nkw = normalize_fa(kw)
        if nkw and nkw in norm_title:
            return "dismiss", f"کلیدواژه غیر‌دلخواه: «{kw}»", False

    # 3. Exact or substring match with unwanted landing prizes
    for up in prefs.unwanted_prizes:
        nup = normalize_fa(up)
        if nup and (nup == norm_title or nup in norm_title or norm_title in nup):
            return "dismiss", f"در لیست غیر‌دلخواه: «{up}»", False

    # 4. Exact or substring match with wanted landing prizes
    for wp in prefs.wanted_prizes:
        nwp = normalize_fa(wp)
        if nwp and (nwp == norm_title or nwp in norm_title or norm_title in nwp):
            return "accept", f"در لیست دلخواه: ��{wp}»", False

    # 5. Wanted keywords (only if title corresponds to a wanted prize category, e.g. طلای دیجیتال)
    for kw in prefs.wanted_keywords:
        nkw = normalize_fa(kw)
        if nkw and nkw in norm_title:
            return "accept", f"کلیدواژه دلخواه: «{kw}»", False

    # 6. STRICT WHITELIST: Anything outside the selected prizes is DISMISSED automatically
    return "dismiss", "خارج از لیست جوایز انتخاب‌شده (حفظ سهمیه ۳تایی)", True


# ==============================================================================
# Digikala Account Client (Keycloak OIDC PKCE Password Login)
# ==============================================================================

def generate_pkce_pair() -> Tuple[str, str]:
    verifier = secrets.token_urlsafe(72)[:96]
    digest = hashlib.sha256(verifier.encode("ascii")).digest()
    challenge = base64.urlsafe_b64encode(digest).rstrip(b"=").decode("ascii")
    return verifier, challenge


def extract_code_from_redirect(location: str) -> Optional[str]:
    if not location:
        return None
    parsed = urllib.parse.urlparse(location)
    for part in (parsed.fragment, parsed.query):
        if part:
            qs = urllib.parse.parse_qs(part)
            if "code" in qs and qs["code"]:
                return qs["code"][0]
    return None


class DigikalaAuthError(Exception):
    pass


class DigikalaAccount:
    def __init__(self, phone: str, password: str, sessions_dir: Path, timeout: float = 20.0) -> None:
        self.phone = normalize_phone(phone)
        self.password = password
        self.sessions_dir = sessions_dir
        self.timeout = timeout
        self.session_file = sessions_dir / f"{self.phone}.json"

        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": DEFAULT_UA,
            "Accept-Language": "fa-IR,fa;q=0.9,en-US;q=0.8,en;q=0.7",
        })
        self.access_token: Optional[str] = None
        self.refresh_token: Optional[str] = None

        self.next_eligible_at: float = 0.0
        self.daily_reset_at: float = 0.0
        self.claims_today: int = 0
        self.daily_limit: int = 3
        self.remaining_today: int = 3
        self.last_status: str = "آماده"

        self._load_session()

    def _load_session(self) -> None:
        if not self.session_file.exists():
            return
        try:
            data = json.loads(self.session_file.read_text(encoding="utf-8"))
            self.access_token = data.get("access_token")
            self.refresh_token = data.get("refresh_token")
            for c in data.get("cookies") or []:
                self.session.cookies.set(
                    c["name"], c["value"], domain=c.get("domain"), path=c.get("path", "/")
                )
        except Exception:
            pass

    def _save_session(self) -> None:
        self.sessions_dir.mkdir(parents=True, exist_ok=True)
        cookies = [
            {"name": c.name, "value": c.value, "domain": c.domain, "path": c.path}
            for c in self.session.cookies
        ]
        payload = {
            "phone": self.phone,
            "access_token": self.access_token,
            "refresh_token": self.refresh_token,
            "cookies": cookies,
            "saved_at": datetime.now(TEHRAN_TZ).isoformat(),
        }
        self.session_file.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")

    @staticmethod
    def _prize_headers(json_body: bool = False) -> Dict[str, str]:
        h = {
            "Accept": "application/json",
            "Origin": "https://www.digikala.com",
            "Referer": "https://www.digikala.com/",
            "Sec-Fetch-Dest": "empty",
            "Sec-Fetch-Mode": "cors",
            "Sec-Fetch-Site": "same-site",
        }
        if json_body:
            h["Content-Type"] = "application/json"
        return h

    def _establish_digikala_cookies(self, access_token: str, refresh_token: str) -> None:
        resp = self.session.post(
            DK_API_LOGIN_URL,
            headers={
                "Accept": "application/json, text/plain, */*",
                "Authorization": f"Bearer {access_token}",
                "Content-Type": "application/json",
                "Origin": "https://www.digikala.com",
                "Referer": "https://www.digikala.com/",
                "X-Web-Client": "desktop",
                "X-Web-Client-Id": "web",
                "X-Web-Optimize-Response": "1",
            },
            json={"access_token": access_token, "refresh_token": refresh_token},
            timeout=self.timeout,
        )
        if resp.status_code != 200:
            raise DigikalaAuthError(f"خطا در ثبت سشن دیجی‌کالا: HTTP {resp.status_code}")
        self.access_token = access_token
        self.refresh_token = refresh_token
        self._save_session()

    def try_refresh_token(self) -> bool:
        if not self.refresh_token:
            return False
        try:
            resp = self.session.post(
                OIDC_TOKEN_URL,
                headers={
                    "Accept": "application/json",
                    "Content-Type": "application/x-www-form-urlencoded;charset=UTF-8",
                    "Origin": "https://www.digikala.com",
                    "Referer": "https://www.digikala.com/",
                },
                data={
                    "grant_type": "refresh_token",
                    "client_id": OIDC_CLIENT_ID,
                    "refresh_token": self.refresh_token,
                },
                timeout=self.timeout,
            )
            if resp.status_code != 200:
                return False
            tok = resp.json()
            if not tok.get("access_token"):
                return False
            self._establish_digikala_cookies(tok["access_token"], tok.get("refresh_token") or self.refresh_token)
            return True
        except Exception:
            return False

    def login_with_password(self) -> None:
        self.session.cookies.clear()
        verifier, challenge = generate_pkce_pair()
        auth_params = {
            "client_id": OIDC_CLIENT_ID,
            "redirect_uri": OIDC_REDIRECT_URI,
            "state": str(uuid.uuid4()),
            "response_mode": "fragment",
            "response_type": "code",
            "scope": "openid",
            "nonce": str(uuid.uuid4()),
            "code_challenge": challenge,
            "code_challenge_method": "S256",
        }
        nav_headers = {
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Upgrade-Insecure-Requests": "1",
        }

        r1 = self.session.get(
            OIDC_AUTH_URL, params=auth_params, headers=nav_headers, allow_redirects=True, timeout=self.timeout
        )
        forms, _ = parse_html_forms(r1.text)
        if not forms or not forms[0].get("action"):
            raise DigikalaAuthError(f"فرم ورود شماره پیدا نشد (HTTP {r1.status_code})")

        action_url = urllib.parse.urljoin(r1.url, forms[0]["action"])
        r2 = self.session.post(
            action_url,
            headers={**nav_headers, "Content-Type": "application/x-www-form-urlencoded"},
            data={"username": self.phone, "rememberMe": "on"},
            allow_redirects=False,
            timeout=self.timeout,
        )
        if r2.status_code in (301, 302, 303, 307, 308):
            loc = r2.headers.get("Location", "")
            if "sso-redirect" not in loc:
                r2 = self.session.get(urllib.parse.urljoin(r2.url, loc), headers=nav_headers, timeout=self.timeout)

        forms2, errs2 = parse_html_forms(r2.text)
        if errs2:
            raise DigikalaAuthError(f"خطا پس از ارسال شماره: {' | '.join(errs2)}")
        if not forms2:
            raise DigikalaAuthError(f"فرم مرحله دوم ورود پیدا نشد (HTTP {r2.status_code})")

        pwd_form = forms2[0]
        has_password_input = any(
            inp.get("name") == "password" or inp.get("id") == "password" for inp in pwd_form["inputs"]
        )
        if not has_password_input:
            alt_exec = None
            for inp in pwd_form["inputs"]:
                inp_id = (inp.get("id") or "").lower()
                inp_name = (inp.get("name") or "").lower()
                if "password" in inp_id and inp.get("value"):
                    alt_exec = inp["value"]
                    break
                if inp_name == "authenticationexecution" and inp.get("value"):
                    alt_exec = inp["value"]
            if alt_exec:
                sw_url = urllib.parse.urljoin(r2.url, pwd_form["action"])
                r_sw = self.session.post(
                    sw_url,
                    headers={**nav_headers, "Content-Type": "application/x-www-form-urlencoded"},
                    data={"authenticationExecution": alt_exec},
                    allow_redirects=True,
                    timeout=self.timeout,
                )
                forms2, errs_sw = parse_html_forms(r_sw.text)
                if errs_sw:
                    raise DigikalaAuthError(f"خطا هنگام سوییچ به رمز عبور: {' | '.join(errs_sw)}")
                if not forms2:
                    raise DigikalaAuthError("پس از سوییچ به رمز عبور، فرم رمز پیدا نشد.")
                pwd_form = forms2[0]
                r2 = r_sw
                has_password_input = any(
                    inp.get("name") == "password" or inp.get("id") == "password" for inp in pwd_form["inputs"]
                )
            if not has_password_input:
                raise DigikalaAuthError("صفحه رمز عبور نمایش داده نشد (رمز تنظیم نشده یا کپچا فعال است).")

        pwd_action = urllib.parse.urljoin(r2.url, pwd_form["action"])
        resp = self.session.post(
            pwd_action,
            headers={**nav_headers, "Content-Type": "application/x-www-form-urlencoded"},
            data={"password": self.password},
            allow_redirects=False,
            timeout=self.timeout,
        )

        auth_code: Optional[str] = None
        for _ in range(4):
            if resp.status_code in (301, 302, 303, 307, 308):
                loc = resp.headers.get("Location", "")
                code = extract_code_from_redirect(loc)
                if code:
                    auth_code = code
                    break
                resp = self.session.get(
                    urllib.parse.urljoin(resp.url, loc),
                    headers=nav_headers,
                    allow_redirects=False,
                    timeout=self.timeout,
                )
                continue

            next_forms, next_errs = parse_html_forms(resp.text)
            if next_errs:
                raise DigikalaAuthError(f"خطای رمز عبور: {' | '.join(next_errs)}")
            if not next_forms:
                break

            nf = next_forms[0]
            if any(inp.get("name") == "password" for inp in nf["inputs"]):
                raise DigikalaAuthError("رمز عبور اشتباه است.")

            payload: Dict[str, str] = {}
            has_accept = False
            for inp in nf["inputs"]:
                name = inp.get("name", "")
                val = inp.get("value", "")
                itype = (inp.get("type") or "").lower()
                if name == "accept":
                    has_accept = True
                    payload["accept"] = val or "true"
                elif itype == "hidden" and name:
                    payload[name] = val
            if not payload or (not has_accept and "login-actions/authenticate" in nf.get("action", "")):
                payload.setdefault("accept", "true")

            next_action = urllib.parse.urljoin(resp.url, nf["action"])
            resp = self.session.post(
                next_action,
                headers={**nav_headers, "Content-Type": "application/x-www-form-urlencoded"},
                data=payload,
                allow_redirects=False,
                timeout=self.timeout,
            )

        if not auth_code:
            raise DigikalaAuthError("کد OIDC دریافت نشد (احتمال کپچا یا نیاز به تایید اضافه).")

        r_tok = self.session.post(
            OIDC_TOKEN_URL,
            headers={
                "Accept": "application/json",
                "Content-Type": "application/x-www-form-urlencoded;charset=UTF-8",
                "Origin": "https://www.digikala.com",
                "Referer": "https://www.digikala.com/",
            },
            data={
                "code": auth_code,
                "grant_type": "authorization_code",
                "client_id": OIDC_CLIENT_ID,
                "redirect_uri": OIDC_REDIRECT_URI,
                "code_verifier": verifier,
            },
            timeout=self.timeout,
        )
        if r_tok.status_code != 200:
            raise DigikalaAuthError(f"خطا در دریافت توکن OIDC: HTTP {r_tok.status_code}")
        tok_data = r_tok.json()
        if not tok_data.get("access_token") or not tok_data.get("refresh_token"):
            raise DigikalaAuthError("پاسخ توکن OIDC ناقص است.")
        self._establish_digikala_cookies(tok_data["access_token"], tok_data["refresh_token"])

    def ensure_authenticated(self) -> Dict[str, Any]:
        status, data = self.get_widget_me()
        if status == 200 and isinstance(data, dict) and "remaining" in data:
            return data
        if self.try_refresh_token():
            status, data = self.get_widget_me()
            if status == 200 and isinstance(data, dict) and "remaining" in data:
                return data
        self.login_with_password()
        status, data = self.get_widget_me()
        if status != 200 or not isinstance(data, dict):
            raise DigikalaAuthError(f"پس از ورود، دسترسی به /widget/me ناموفق بود (HTTP {status}).")
        return data

    def _safe_json(self, resp: requests.Response) -> Dict[str, Any]:
        try:
            return resp.json()
        except Exception:
            return {"raw_text": resp.text[:300]}

    def get_widget_me(self) -> Tuple[int, Dict[str, Any]]:
        r = self.session.get(WIDGET_ME_URL, headers=self._prize_headers(), timeout=self.timeout)
        data = self._safe_json(r)
        if r.status_code == 200 and isinstance(data, dict):
            self.claims_today = int(data.get("claims_today", 0))
            self.daily_limit = int(data.get("limit", 3))
            self.remaining_today = int(data.get("remaining", 0))
            resets = parse_iso_utc(data.get("resets_at"))
            if resets:
                self.daily_reset_at = resets
        return r.status_code, data

    def get_claims_me(self) -> Tuple[int, Dict[str, Any]]:
        r = self.session.get(CLAIMS_ME_URL, headers=self._prize_headers(), timeout=self.timeout)
        return r.status_code, self._safe_json(r)

    def submit_code(self, code: str) -> Tuple[int, Dict[str, Any]]:
        r = self.session.post(
            CLAIMS_URL,
            headers=self._prize_headers(json_body=True),
            json={"code": code.strip().upper()},
            timeout=self.timeout,
        )
        return r.status_code, self._safe_json(r)

    def accept_claim(self, claim_id: str) -> Tuple[int, Dict[str, Any]]:
        r = self.session.post(f"{CLAIMS_URL}/{claim_id}/accept", headers=self._prize_headers(), timeout=self.timeout)
        return r.status_code, self._safe_json(r)

    def dismiss_claim(self, claim_id: str) -> Tuple[int, Dict[str, Any]]:
        r = self.session.post(f"{CLAIMS_URL}/{claim_id}/dismiss", headers=self._prize_headers(), timeout=self.timeout)
        return r.status_code, self._safe_json(r)


def save_won_prize(
    data_dir: Path,
    phone: str,
    input_code: str,
    claim_id: str,
    prize_kind: str,
    prize_title: str,
    voucher_code: str,
    expires_at: Optional[str],
) -> Dict[str, Any]:
    data_dir.mkdir(parents=True, exist_ok=True)
    record = {
        "won_at_tehran": datetime.now(TEHRAN_TZ).strftime("%Y-%m-%d %H:%M:%S"),
        "phone": phone,
        "input_code": input_code,
        "claim_id": claim_id,
        "prize_kind": prize_kind,
        "prize_title": prize_title,
        "voucher_code": voucher_code,
        "expires_at": expires_at or "",
    }
    csv_path = data_dir / "won_prizes.csv"
    write_header = not csv_path.exists()
    with csv_path.open("a", encoding="utf-8-sig", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(record.keys()))
        if write_header:
            writer.writeheader()
        writer.writerow(record)

    json_path = data_dir / "won_prizes.json"
    existing: List[Dict[str, Any]] = []
    if json_path.exists():
        try:
            existing = json.loads(json_path.read_text(encoding="utf-8"))
        except Exception:
            existing = []
    existing.append(record)
    json_path.write_text(json.dumps(existing, ensure_ascii=False, indent=2), encoding="utf-8")
    return record
