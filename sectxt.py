#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
================================================================================
 SECURITY.TXT CHECKER (SECTXT)
 Does this domain tell researchers how to report a vulnerability? - CLI + Web App
--------------------------------------------------------------------------------
 Author  : Karanam Shrivasta
 GitHub  : https://github.com/mrshrivasta
 LinkedIn: https://www.linkedin.com/in/karanam-shrivasta/
 Version : 1.0.0
--------------------------------------------------------------------------------
 WHAT security.txt IS FOR
   A researcher finds a flaw in your site at two in the morning. Who do they
   tell? Without an answer they guess: an abuse@ address that bounces, a support
   form that routes to someone who thinks it is spam, a tweet. Reports get lost,
   and the ones that get through arrive slowly.

   RFC 9116 defines a plain text file at /.well-known/security.txt that answers
   the question in one place. This tool fetches it, checks it against the RFC
   clause by clause, and explains what each field is actually for.

 WHAT IT CHECKS
   - That the file is where the RFC says it must be, over HTTPS, with the right
     media type, and that what came back is genuinely a security.txt rather than
     a site's catch-all HTML page returned with a 200.
   - Every field RFC 9116 defines: Contact and Expires are required, Expires must
     be a real RFC 3339 timestamp in the future, Preferred-Languages may appear
     at most once, Canonical should match where the file actually lives.
   - Whether it is signed with OpenPGP, and whether the signature is even
     structurally intact.
   - The things that are technically valid but practically useless: an expiry
     ten years out, a Contact pointing at a form that says "sales enquiries", a
     Canonical that points somewhere else entirely.

 WHAT A PASS DOES NOT MEAN
   *** A perfect security.txt does not mean anyone reads the inbox. ***
   This checks a text file. It cannot tell you whether the address accepts mail,
   whether a human triages it, or whether a report will ever be answered. A
   flawless file in front of an unmonitored mailbox is worse than no file at all,
   because it makes a researcher believe they have done their part.

   Equally, a domain with NO security.txt is not insecure and is not doing
   anything wrong. The RFC is a recommendation, adoption is voluntary, and plenty
   of well-run organisations publish contact details elsewhere.

 IT MAKES REAL NETWORK REQUESTS
   Checking a domain means fetching from it. That is the point of the tool, and
   it is ordinary, unremarkable traffic - the file is published to be read. But
   it does mean the target sees your address, and every check is a request
   against someone else's server. Requests are capped, redirects are limited, the
   body is size-limited, and addresses on private or loopback ranges are refused
   so this cannot be pointed at internal services.

 LEGAL DISCLAIMER
   Provided "as is" with no warranty. Fetching a published file is not an attack,
   but automated checking at volume against domains you do not own may breach
   terms of service. The author accepts no liability for any loss or damage.
================================================================================
"""

from __future__ import annotations

import argparse
import csv
import html as _html
import io
import ipaddress
import json
import math
import os
import platform
import re
import shutil
import socket
import sqlite3
import ssl
import sys
import textwrap
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timedelta, timezone

APP_NAME = "security.txt Checker"
APP_SHORT = "SECTXT"
VERSION = "1.0.0"
AUTHOR = "Karanam Shrivasta"
GITHUB = "https://github.com/mrshrivasta"
LINKEDIN = "https://www.linkedin.com/in/karanam-shrivasta/"
DEFAULT_DB = os.environ.get("SECTXT_DB", "sectxt.db")
USER_AGENT = f"sectxt/{VERSION} (RFC 9116 checker; +{GITHUB})"

NOT_A_GUARANTEE = (
    "A perfect security.txt does not mean anyone reads the inbox. This checks a text file - "
    "it cannot tell you whether the address accepts mail, whether a human triages it, or "
    "whether a report is ever answered. And a domain with NO security.txt is not insecure: "
    "the RFC is a recommendation and adoption is voluntary."
)
DISCLAIMER_SHORT = (
    "Fetches a published file and checks it against RFC 9116. A pass means the file is "
    "correct, not that anyone reads the inbox. No security.txt is not a vulnerability."
)
DISCLAIMER_LONG = textwrap.dedent(
    """\
    THIS CHECKS A TEXT FILE, NOT AN ORGANISATION. It fetches /.well-known/security.txt and
    validates it against RFC 9116 clause by clause.

    A clean result means the file is well-formed and complete. It does NOT mean the contact
    address accepts mail, that a human triages what arrives, or that a report will be
    answered. A flawless file in front of an unmonitored mailbox is arguably worse than no
    file at all, because it convinces a researcher they have done their part.

    A domain with no security.txt is not insecure and is not doing anything wrong. RFC 9116
    is a recommendation, adoption is voluntary, and many well-run organisations publish
    contact details elsewhere.

    Checking a domain makes real requests to it. That is ordinary traffic - the file exists
    to be read - but the target sees your address. Requests are capped, redirects limited,
    the body size-limited, and private, loopback and link-local addresses are refused so
    this cannot be aimed at internal services.

    Provided "as is" with no warranty. Automated checking at volume against domains you do
    not own may breach terms of service. The author accepts no liability for any loss or
    damage."""
)

SEVERITIES = ["critical", "high", "medium", "low", "info"]
SEV_WEIGHT = {"critical": 0.0, "high": 0.0, "medium": 0.0, "low": 0.0, "info": 0.0}
SEV_COLOR = {"critical": "#e5484d", "high": "#f76808", "medium": "#ffb224",
             "low": "#3e9dd8", "info": "#8b8f9b"}

# Scoring is by RFC conformance, not by severity weight: a file either meets the
# specification or it does not, and the grade should say which.
GRADE_BANDS = [(95, "A", "fully conformant", "#30a46c"),
               (85, "B", "conformant with minor issues", "#5bb98b"),
               (70, "C", "usable, but with real problems", "#ffb224"),
               (50, "D", "significant problems", "#f76808"),
               (0, "F", "not usable as published", "#e5484d")]


def grade_for(score: float) -> tuple[str, str, str]:
    for cut, letter, label, colour in GRADE_BANDS:
        if score >= cut:
            return letter, label, colour
    return "F", "not usable as published", "#e5484d"


WELL_KNOWN_PATH = "/.well-known/security.txt"
LEGACY_PATH = "/security.txt"
MAX_BODY_BYTES = 256 * 1024
MAX_REDIRECTS = 5


# =============================================================================
# SECTION 1 - Utilities
# =============================================================================

def now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def ts_pretty(iso: str | None) -> str:
    if not iso:
        return "-"
    try:
        return datetime.fromisoformat(iso).strftime("%Y-%m-%d %H:%M:%S")
    except Exception:
        return iso


def clamp(v, lo, hi):
    return max(lo, min(hi, v))


def html_escape(s) -> str:
    return _html.escape("" if s is None else str(s), quote=True)


def fmt_bytes(n) -> str:
    if n is None:
        return "-"
    n = float(n)
    for unit in ("B", "KiB", "MiB"):
        if n < 1024 or unit == "MiB":
            return f"{n:.{0 if unit == 'B' else 1}f} {unit}"
        n /= 1024.0
    return f"{n:.1f} MiB"


def fmt_days(days) -> str:
    if days is None:
        return "-"
    days = int(days)
    if abs(days) >= 730:
        return f"{days / 365.0:.1f} years"
    if abs(days) >= 60:
        return f"{days / 30.4:.0f} months"
    return f"{days} day(s)"


def F(category, title, severity, description, evidence="", advice="", rfc=""):
    """One finding. 'rfc' cites the clause, so a disagreement can be settled."""
    return {"category": category, "title": title, "severity": severity,
            "description": description, "evidence": str(evidence)[:1200],
            "advice": advice, "rfc": rfc}


class Result:
    def __init__(self, name: str):
        self.name = name
        self.data = None
        self.status = "ok"
        self.detail = ""

    def unavailable(self, detail):
        self.status, self.detail = "unavailable", detail
        return self

    def partial(self, detail):
        self.status = "partial"
        self.detail = " ".join((self.detail + "; " + detail).strip("; ").split())[:400]
        return self


# =============================================================================
# SECTION 2 - Fetching, with a guard against being aimed inwards
# =============================================================================

def resolve_and_guard(host: str, allow_private: bool = False) -> tuple[bool, str, list]:
    """Refuse to fetch from addresses that are not on the public internet.

    Without this, a checker is a convenient way to make a server request internal
    URLs on an attacker's behalf. The guard runs on every hop, not just the first,
    because a redirect is the obvious way around a one-time check.
    """
    try:
        infos = socket.getaddrinfo(host, None, proto=socket.IPPROTO_TCP)
    except socket.gaierror as e:
        return False, f"could not resolve '{host}': {e}", []
    addrs = sorted({i[4][0] for i in infos})
    if allow_private:
        return True, "", addrs
    for a in addrs:
        try:
            ip = ipaddress.ip_address(a)
        except ValueError:
            continue
        if (ip.is_private or ip.is_loopback or ip.is_link_local or ip.is_reserved
                or ip.is_multicast or ip.is_unspecified):
            return False, (f"'{host}' resolves to {a}, which is not a public address. "
                           f"Refusing, so this tool cannot be used to reach internal "
                           f"services. Use --allow-private if you are deliberately "
                           f"checking your own internal host."), addrs
    return True, "", addrs


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    """Follow redirects manually so every hop can be recorded and re-guarded."""

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def fetch_once(url: str, timeout: float, allow_private: bool,
               method: str = "GET") -> dict:
    out = {"url": url, "status": None, "headers": {}, "body": b"", "error": None,
           "elapsed_ms": None, "final_url": url, "addresses": [], "truncated": False}
    parts = urllib.parse.urlsplit(url)
    if parts.scheme not in ("http", "https"):
        out["error"] = f"unsupported scheme '{parts.scheme}'"
        return out
    ok, why, addrs = resolve_and_guard(parts.hostname or "", allow_private)
    out["addresses"] = addrs
    if not ok:
        out["error"] = why
        return out
    req = urllib.request.Request(url, method=method, headers={
        "User-Agent": USER_AGENT, "Accept": "text/plain, */*;q=0.5"})
    opener = urllib.request.build_opener(_NoRedirect)
    t0 = time.perf_counter()
    try:
        with opener.open(req, timeout=timeout) as resp:
            out["status"] = resp.status
            out["headers"] = {k.lower(): v for k, v in resp.headers.items()}
            if method != "HEAD":
                body = resp.read(MAX_BODY_BYTES + 1)
                if len(body) > MAX_BODY_BYTES:
                    out["truncated"] = True
                    body = body[:MAX_BODY_BYTES]
                out["body"] = body
            out["final_url"] = resp.geturl()
    except urllib.error.HTTPError as e:
        out["status"] = e.code
        out["headers"] = {k.lower(): v for k, v in (e.headers or {}).items()}
        try:
            out["body"] = e.read(MAX_BODY_BYTES)
        except Exception:
            out["body"] = b""
    except urllib.error.URLError as e:
        reason = getattr(e, "reason", e)
        if isinstance(reason, ssl.SSLError):
            out["error"] = (f"TLS failed: {reason}. A security.txt served over a broken "
                            f"certificate is not trustworthy, which rather defeats the "
                            f"purpose.")
        elif isinstance(reason, socket.timeout):
            out["error"] = f"no response within {timeout}s"
        else:
            out["error"] = f"could not connect: {reason}"
    except socket.timeout:
        out["error"] = f"no response within {timeout}s"
    except Exception as e:
        out["error"] = f"{type(e).__name__}: {e}"
    out["elapsed_ms"] = round((time.perf_counter() - t0) * 1000, 1)
    return out


def fetch_with_redirects(url: str, timeout: float = 10.0, allow_private: bool = False,
                         max_redirects: int = MAX_REDIRECTS) -> dict:
    """Follow redirects by hand, recording and re-guarding every hop."""
    chain = []
    current = url
    for hop in range(max_redirects + 1):
        r = fetch_once(current, timeout, allow_private)
        chain.append({"url": current, "status": r["status"], "error": r["error"],
                      "location": r["headers"].get("location"),
                      "elapsed_ms": r["elapsed_ms"],
                      "content_type": r["headers"].get("content-type")})
        if r["error"]:
            r["chain"] = chain
            return r
        if r["status"] in (301, 302, 303, 307, 308):
            loc = r["headers"].get("location")
            if not loc:
                r["error"] = f"HTTP {r['status']} with no Location header"
                r["chain"] = chain
                return r
            if hop >= max_redirects:
                r["error"] = (f"more than {max_redirects} redirects - a security.txt should "
                              f"not need a redirect chain this long")
                r["chain"] = chain
                return r
            current = urllib.parse.urljoin(current, loc)
            continue
        r["chain"] = chain
        r["redirects"] = len(chain) - 1
        return r
    return {"url": url, "status": None, "error": "redirect loop", "chain": chain,
            "headers": {}, "body": b"", "addresses": []}


WAF_MARKERS = (b"just a moment", b"cf_chl_opt", b"challenge-platform", b"cf-browser-verification",
               b"attention required", b"enable javascript and cookies",
               b"ddos protection by", b"incapsula incident", b"access denied",
               b"request unsuccessful", b"perimeterx", b"captcha-delivery",
               b"akamai", b"_imperva", b"radware")


def looks_like_challenge(body: bytes, status: int | None) -> tuple[bool, str]:
    """A bot challenge is not an absent file.

    A WAF interposing a challenge page, or a 403, means the checker could not SEE
    the file. Reporting that as "no security.txt" would be a plain lie about
    someone else's site, so the two are kept separate.
    """
    low = body[:4096].lower()
    hits = [mk.decode() for mk in WAF_MARKERS if mk in low]
    if hits:
        return True, (f"the response is a bot-protection challenge page (matched "
                      f"{', '.join(hits[:3])}), not the file itself")
    if status in (401, 403, 429):
        return True, (f"the server answered HTTP {status}, so it refused to serve the file "
                      f"to this client")
    return False, ""


def looks_like_html(body: bytes, content_type: str | None) -> tuple[bool, str]:
    """A 200 does not mean the file exists.

    Single-page applications and custom error pages routinely return their HTML
    shell with a 200 for any unknown path. A checker that trusts the status code
    reports a security.txt that is not there.
    """
    ct = (content_type or "").lower()
    head = body[:2048].lstrip().lower()
    if head.startswith((b"<!doctype html", b"<html", b"<?xml")):
        return True, ("the body starts with an HTML or XML document, so this is a web page, "
                      "not a security.txt")
    if b"<html" in head or b"<head>" in head or b"<body" in head:
        return True, "the body contains HTML tags, so this is a web page"
    if "text/html" in ct:
        return True, (f"the server declared Content-Type '{content_type}', which is HTML - "
                      f"whatever this is, it is not a security.txt")
    return False, ""


# =============================================================================
# SECTION 3 - Parsing RFC 9116
# =============================================================================

# field name -> (required, max occurrences or None, must be a URI, what it is for)
RFC_FIELDS = {
    "contact": (True, None, True,
                "Where to send a report. At least one is REQUIRED. Should be a URI: a "
                "mailto:, a tel:, or an https: link to a form."),
    "expires": (True, 1, False,
                "When this file stops being authoritative. Exactly one is REQUIRED, as an "
                "RFC 3339 timestamp. It exists so a stale file can be recognised as stale."),
    "encryption": (False, None, True,
                   "A key researchers can use to encrypt their report. A URI pointing to "
                   "the key - never the key itself inline."),
    "acknowledgments": (False, None, True,
                        "A page thanking researchers who have reported issues. Note the "
                        "US spelling: the RFC defines 'Acknowledgments'."),
    "preferred-languages": (False, 1, False,
                            "Which languages you can read reports in, as a comma-separated "
                            "list of language tags. At most one of this field."),
    "canonical": (False, None, True,
                  "Where this file officially lives. Lets a researcher confirm they are "
                  "reading the real file and not a copy."),
    "policy": (False, None, True,
               "Your vulnerability disclosure policy - what you promise, and what you ask "
               "of researchers."),
    "hiring": (False, None, True, "A link to security-related job openings."),
    "csaf": (False, None, True,
             "A link to a CSAF provider-metadata.json for machine-readable advisories."),
}
URI_SCHEMES_OK = ("mailto:", "https:", "tel:", "http:")
LANG_RE = re.compile(r"^[a-z]{2,3}(-[A-Za-z0-9]{2,8})*$", re.I)

PGP_BEGIN = "-----BEGIN PGP SIGNED MESSAGE-----"
PGP_SIG_BEGIN = "-----BEGIN PGP SIGNATURE-----"
PGP_SIG_END = "-----END PGP SIGNATURE-----"


def parse_security_txt(text: str) -> dict:
    """Parse the file into fields, keeping every line's number for the report."""
    out = {"fields": {}, "lines": [], "comments": [], "malformed": [], "empty_values": [],
           "signed": False, "signature_intact": False, "signature_detail": "",
           "signed_body": None, "byte_order_mark": False, "line_endings": None,
           "raw_line_count": 0}

    if text.startswith("\ufeff"):
        out["byte_order_mark"] = True
        text = text.lstrip("\ufeff")

    if "\r\n" in text:
        out["line_endings"] = "CRLF"
    elif "\r" in text:
        out["line_endings"] = "CR"
    elif "\n" in text:
        out["line_endings"] = "LF"

    body = text
    if PGP_BEGIN in text:
        out["signed"] = True
        try:
            after = text.split(PGP_BEGIN, 1)[1]
            # a clearsigned message has headers, a blank line, then the content
            if "\n\n" in after:
                content = after.split("\n\n", 1)[1]
            elif "\r\n\r\n" in after:
                content = after.split("\r\n\r\n", 1)[1]
            else:
                content = after
            if PGP_SIG_BEGIN in content:
                body = content.split(PGP_SIG_BEGIN, 1)[0]
                out["signature_intact"] = PGP_SIG_END in text
                out["signature_detail"] = (
                    "a clearsigned message with both signature delimiters present"
                    if out["signature_intact"] else
                    "the signature block starts but never ends - the file is truncated "
                    "or was edited after signing")
            else:
                body = content
                out["signature_detail"] = ("the file claims to be signed but contains no "
                                           "signature block at all")
        except Exception as e:
            out["signature_detail"] = f"the signature block could not be read: {e}"
        out["signed_body"] = body

    for i, raw in enumerate(body.splitlines(), 1):
        out["raw_line_count"] += 1
        line = raw.rstrip()
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("#"):
            out["comments"].append({"line": i, "text": stripped[1:].strip()})
            continue
        if stripped.startswith("- ") or stripped.startswith("Hash:"):
            continue
        if ":" not in stripped:
            out["malformed"].append({"line": i, "text": stripped[:160],
                                     "why": "no colon, so this is not a field"})
            continue
        name, _, value = stripped.partition(":")
        key = name.strip().lower()
        value = value.strip()
        if not key or " " in name.strip():
            out["malformed"].append({"line": i, "text": stripped[:160],
                                     "why": "the field name contains a space"})
            continue
        if not value:
            out["empty_values"].append({"line": i, "field": name.strip()})
            continue
        out["fields"].setdefault(key, []).append(
            {"line": i, "name": name.strip(), "value": value})
        out["lines"].append({"line": i, "field": key, "value": value})
    return out


def parse_rfc3339(value: str) -> tuple[datetime | None, str]:
    """Parse an Expires value. Returns (datetime, complaint)."""
    v = (value or "").strip()
    if not v:
        return None, "the value is empty"
    candidate = v
    # RFC 3339 permits 'Z' or 'z' - literal strings in ABNF are case-insensitive
    if candidate.endswith(("z", "Z")):
        candidate = candidate[:-1] + "+00:00"
    try:
        dt = datetime.fromisoformat(candidate)
    except ValueError:
        for fmt in ("%Y-%m-%dT%H:%M:%S%z", "%Y-%m-%dT%H:%M:%S.%f%z", "%Y-%m-%d"):
            try:
                dt = datetime.strptime(candidate, fmt)
                break
            except ValueError:
                continue
        else:
            return None, (f"'{v}' is not an RFC 3339 timestamp. It should look like "
                          f"2027-01-31T23:59:59Z")
    if dt.tzinfo is None:
        return dt.replace(tzinfo=timezone.utc), ("no timezone offset was given, so UTC was "
                                                 "assumed - RFC 3339 requires an offset")
    return dt, ""


def classify_contact(value: str) -> dict:
    """What kind of contact is this, and is it any use to a researcher?"""
    v = (value or "").strip()
    low = v.lower()
    out = {"value": v, "kind": "unknown", "is_uri": False, "secure": None, "note": ""}
    if low.startswith("mailto:"):
        out.update(kind="email", is_uri=True)
        addr = v[7:].strip()
        out["address"] = addr
        if "@" not in addr:
            out["note"] = "the mailto: URI does not contain an @ sign"
    elif low.startswith("tel:"):
        out.update(kind="telephone", is_uri=True)
    elif low.startswith("https://"):
        out.update(kind="web form or page", is_uri=True, secure=True)
    elif low.startswith("http://"):
        out.update(kind="web form or page", is_uri=True, secure=False,
                   note="served over plain HTTP, so a report submitted through it can be "
                        "read and altered in transit")
    elif "@" in v and " " not in v:
        out.update(kind="email", is_uri=False,
                   note="this is a bare address, not a URI. RFC 9116 asks for a URI, so "
                        "write it as mailto:" + v)
        out["address"] = v
    elif re.match(r"^\+?[0-9 ()\-]{6,}$", v):
        out.update(kind="telephone", is_uri=False,
                   note="this is a bare phone number, not a URI. Write it as tel:" + v)
    return out


ROLE_ADDRESSES = ("security", "security-team", "secure", "psirt", "cert", "soc",
                  "vulnerability", "vulnerabilities", "disclosure", "abuse")
PERSONAL_HINTS = ("gmail.com", "yahoo.com", "hotmail.com", "outlook.com", "protonmail.com",
                  "icloud.com", "me.com", "aol.com", "mail.com", "gmx.com")


# =============================================================================
# SECTION 4 - The checks
#   Each finding cites the clause it comes from, so a disagreement can be settled
#   by reading the RFC rather than by trusting this tool.
# =============================================================================

def check_location(fetches: dict, domain: str) -> tuple[list[dict], dict]:
    """Where the file was found, and whether that is where it belongs."""
    findings = []
    chosen = None
    wk = fetches.get("well_known")
    legacy = fetches.get("legacy")
    http_wk = fetches.get("http_well_known")

    def usable(f):
        if not f or f.get("error") or f.get("status") != 200:
            return False
        html, _why = looks_like_html(f.get("body", b""), f["headers"].get("content-type"))
        return not html

    if usable(wk):
        chosen = wk
        findings.append(F("Location", "Found at /.well-known/security.txt", "info",
                          "This is where RFC 9116 says the file must be.",
                          f"{wk['url']} returned {wk['status']} in {wk['elapsed_ms']} ms",
                          "", "RFC 9116 section 3"))
    elif usable(legacy):
        chosen = legacy
        findings.append(F("Location", "Found only at the legacy /security.txt path", "high",
                          "The file is served from the top level, not from "
                          "/.well-known/security.txt.",
                          f"{legacy['url']} returned {legacy['status']}",
                          "Move it to /.well-known/security.txt. The RFC says it MUST be "
                          "there; the top-level path is tolerated for compatibility only, "
                          "and tools that follow the specification will not find it where "
                          "it is now.", "RFC 9116 section 3"))
    else:
        detail = []
        blocked = []
        for name, f in (("/.well-known/security.txt", wk), ("/security.txt", legacy)):
            if not f:
                continue
            chal, cwhy = looks_like_challenge(f.get("body", b""), f.get("status"))
            if chal:
                blocked.append(f"{name}: {cwhy}")
                continue
            if f.get("error"):
                detail.append(f"{name}: {f['error']}")
            elif f.get("status") != 200:
                detail.append(f"{name}: HTTP {f['status']}")
            else:
                html, why = looks_like_html(f.get("body", b""),
                                            f["headers"].get("content-type"))
                if html:
                    detail.append(f"{name}: HTTP 200 but {why}")
        if blocked:
            findings.append(F("Location", "Blocked before the file could be read", "info",
                              "A bot-protection layer answered instead of the server, so "
                              "this check could not see whether a security.txt exists.",
                              "; ".join(blocked),
                              "This is NOT a finding about the domain - it is a limit of "
                              "this check. Open the URL in a browser to see the real "
                              "answer. Nothing below should be read as a statement about "
                              "whether the file exists.", "RFC 9116 section 3"))
            return findings, {"found": False, "source": None, "blocked": True}
        findings.append(F("Location", "No security.txt was found", "high",
                          f"Neither path on {domain} returned a usable file.",
                          "; ".join(detail),
                          "This is NOT a vulnerability and the domain is not doing anything "
                          "wrong - RFC 9116 is a recommendation and adoption is voluntary. "
                          "But a researcher who finds a flaw here has to guess who to tell, "
                          "and reports get lost that way.", "RFC 9116 section 3"))
        return findings, {"found": False, "source": None}

    # a 200 that is really the site's HTML shell
    for name, f in (("/.well-known/security.txt", wk), ("/security.txt", legacy)):
        if f and not f.get("error") and f.get("status") == 200 and f is not chosen:
            html, why = looks_like_html(f.get("body", b""),
                                        f["headers"].get("content-type"))
            if html:
                findings.append(F("Location", f"{name} returns a web page, not a file",
                                  "low",
                                  "That path answers 200, but the body is HTML.",
                                  why,
                                  "Common when a single-page app serves its shell for every "
                                  "unknown path. It means an automated checker can be "
                                  "fooled into reporting a file that is not there - return "
                                  "404 for paths that do not exist.", "RFC 9116 section 3"))

    if chosen is wk and usable(legacy):
        findings.append(F("Location", "Also served at the legacy /security.txt path", "info",
                          "Both paths return a usable file.", "",
                          "Harmless, and helpful for older tools. Keep them identical, or "
                          "redirect the legacy path to the canonical one.",
                          "RFC 9116 section 3"))

    scheme = urllib.parse.urlsplit(chosen["url"]).scheme
    if scheme != "https":
        findings.append(F("Transport", "Not served over HTTPS", "high",
                          "The file was retrieved over plain HTTP.",
                          chosen["url"],
                          "Anyone on the path can rewrite the contact address and redirect "
                          "reports to themselves. The RFC requires HTTPS.",
                          "RFC 9116 section 3"))
    elif http_wk and not http_wk.get("error") and http_wk.get("status") == 200:
        findings.append(F("Transport", "Also reachable over plain HTTP", "low",
                          "The same path answers over http:// as well as https://.",
                          f"http://{domain}{WELL_KNOWN_PATH} returned "
                          f"{http_wk['status']}",
                          "Redirect HTTP to HTTPS instead of serving the file over both. "
                          "A researcher who fetches the HTTP version gets a document anyone "
                          "on the path could have altered.", "RFC 9116 section 3"))

    redirects = chosen.get("redirects", 0)
    if redirects:
        hops = " -> ".join(h["url"] for h in chosen.get("chain", []))
        findings.append(F("Location", f"Reached after {redirects} redirect(s)",
                          "low" if redirects <= 2 else "medium",
                          "The file is not served directly from the requested URL.",
                          hops,
                          "Allowed, but each hop is a chance for the file to be served from "
                          "somewhere you did not intend. Set Canonical so a researcher can "
                          "confirm where it really lives."))

    ct = (chosen["headers"].get("content-type") or "").lower()
    if not ct:
        findings.append(F("Media type", "No Content-Type header", "medium",
                          "The server did not declare a media type.", "",
                          "Serve it as 'text/plain; charset=utf-8'. Without a type, browsers "
                          "and tools guess, and some will download it instead of showing it.",
                          "RFC 9116 section 3"))
    elif "text/plain" not in ct:
        findings.append(F("Media type", f"Wrong Content-Type: {ct}", "medium",
                          "RFC 9116 requires the file to be served as plain text.",
                          f"Content-Type: {chosen['headers'].get('content-type')}",
                          "Serve it as 'text/plain; charset=utf-8'.",
                          "RFC 9116 section 3"))
    elif "charset=utf-8" not in ct.replace(" ", ""):
        findings.append(F("Media type", "Content-Type does not declare charset=utf-8",
                          "low",
                          f"The type is plain text but no character set is given.",
                          f"Content-Type: {chosen['headers'].get('content-type')}",
                          "Serve it as 'text/plain; charset=utf-8'. Without it, a file "
                          "containing non-ASCII characters may be decoded wrongly.",
                          "RFC 9116 section 3"))

    return findings, {"found": True, "source": chosen}


def check_fields(parsed: dict, chosen_url: str, now: datetime | None = None) -> list[dict]:
    """Every field RFC 9116 defines, plus the things that are legal but useless."""
    findings = []
    now = now or datetime.now(timezone.utc)
    fields = parsed["fields"]

    # ---- Contact (REQUIRED) ----
    contacts = fields.get("contact", [])
    if not contacts:
        findings.append(F("Contact", "No Contact field", "critical",
                          "Contact is REQUIRED, and it is the entire point of the file - "
                          "without it, a researcher still has nowhere to send a report.",
                          "", "Add at least one: 'Contact: mailto:security@example.com'.",
                          "RFC 9116 section 2.5.3"))
    else:
        classified = [classify_contact(c["value"]) for c in contacts]
        non_uri = [c for c in classified if not c["is_uri"]]
        for c in non_uri:
            findings.append(F("Contact", "A Contact value is not a URI", "medium",
                              c["note"] or "The value should be a URI.",
                              f"Contact: {c['value']}",
                              "Use a scheme: mailto: for email, tel: for a phone number, "
                              "https: for a form.", "RFC 9116 section 2.5.3"))
        insecure = [c for c in classified if c.get("secure") is False]
        for c in insecure:
            findings.append(F("Contact", "A Contact link uses plain HTTP", "medium",
                              c["note"], f"Contact: {c['value']}",
                              "Serve the reporting form over HTTPS - a vulnerability report "
                              "is exactly the sort of thing that should not travel in "
                              "clear text.", "RFC 9116 section 2.5.3"))
        emails = [c for c in classified if c["kind"] == "email" and c.get("address")]
        personal = [c for c in emails
                    if any(c["address"].lower().endswith("@" + d) for d in PERSONAL_HINTS)]
        for c in personal:
            findings.append(F("Contact", "A Contact address is on a personal mail provider",
                              "low",
                              f"{c['address']} is at a consumer email provider.", "",
                              "It works, but it ties disclosure to one individual's "
                              "account. A role address on your own domain survives people "
                              "changing jobs."))
        role = [c for c in emails
                if any(c["address"].lower().split("@")[0].startswith(r)
                       for r in ROLE_ADDRESSES)]
        if emails and not role and not personal:
            findings.append(F("Contact", "No role-based email address", "info",
                              "The email contacts do not look like a shared security "
                              "mailbox.",
                              ", ".join(c["address"] for c in emails[:3]),
                              "A role address such as security@ is easier to keep monitored "
                              "than a named individual's inbox."))
        kinds = sorted({c["kind"] for c in classified})
        findings.append(F("Contact", f"{len(contacts)} contact method(s): "
                          f"{', '.join(kinds)}", "info",
                          "Contacts are listed in the order you prefer to be reached.",
                          "; ".join(c["value"] for c in classified[:5]),
                          "This tool cannot tell you whether any of them are monitored. "
                          "Send a test report to your own file occasionally - a contact "
                          "that bounces is worse than none, because the researcher believes "
                          "they have told you.", "RFC 9116 section 2.5.3"))

    # ---- Expires (REQUIRED, exactly one) ----
    expires = fields.get("expires", [])
    if not expires:
        findings.append(F("Expires", "No Expires field", "high",
                          "Expires is REQUIRED. Without it there is no way to tell a "
                          "current file from one abandoned three years ago.",
                          "",
                          "Add one, no more than a year out: "
                          "'Expires: 2027-01-31T23:59:59Z'.",
                          "RFC 9116 section 2.5.5"))
    else:
        if len(expires) > 1:
            findings.append(F("Expires", f"{len(expires)} Expires fields", "high",
                              "The RFC allows exactly one. A file with several has no "
                              "defined expiry at all.",
                              "; ".join(f"line {e['line']}: {e['value']}"
                                        for e in expires),
                              "Keep one and delete the rest.", "RFC 9116 section 2.5.5"))
        dt, complaint = parse_rfc3339(expires[0]["value"])
        if dt is None:
            findings.append(F("Expires", "Expires is not a valid timestamp", "high",
                              complaint, f"Expires: {expires[0]['value']}",
                              "Use RFC 3339: 2027-01-31T23:59:59Z.",
                              "RFC 9116 section 2.5.5"))
        else:
            days = (dt - now).total_seconds() / 86400.0
            if days < 0:
                findings.append(F("Expires", f"The file expired {fmt_days(-days)} ago",
                                  "critical",
                                  "RFC 9116 says a file past its Expires date should not be "
                                  "used.",
                                  f"Expires: {expires[0]['value']} "
                                  f"({dt.isoformat()})",
                                  "A researcher following the RFC will treat this file as "
                                  "void and go looking elsewhere - which is exactly the "
                                  "situation the file was meant to prevent. Update the date "
                                  "and re-check the contacts while you are there.",
                                  "RFC 9116 section 2.5.5"))
            elif days < 30:
                findings.append(F("Expires", f"Expires in {fmt_days(days)}", "medium",
                                  "The file is close to expiry.",
                                  f"Expires: {expires[0]['value']}",
                                  "Renew it now. Put a calendar reminder at the same time - "
                                  "the usual failure is that nobody remembers this file "
                                  "exists until it has been void for months.",
                                  "RFC 9116 section 2.5.5"))
            elif days > 400:
                findings.append(F("Expires", f"Expires {fmt_days(days)} from now", "low",
                                  "The RFC recommends less than a year.",
                                  f"Expires: {expires[0]['value']}",
                                  "A long expiry defeats the purpose: the date exists to "
                                  "force a periodic review, and one ten years out never "
                                  "prompts anybody to check whether the contacts still "
                                  "work.", "RFC 9116 section 2.5.5"))
            else:
                findings.append(F("Expires", f"Valid for another {fmt_days(days)}", "info",
                                  f"Expires {dt.strftime('%Y-%m-%d')}.",
                                  f"Expires: {expires[0]['value']}",
                                  "Within the recommended year.", "RFC 9116 section 2.5.5"))
            if complaint:
                findings.append(F("Expires", "Expires has no timezone offset", "low",
                                  complaint, f"Expires: {expires[0]['value']}",
                                  "Add an offset - 'Z' for UTC.", "RFC 9116 section 2.5.5"))

    # ---- fields that may appear at most once ----
    for key, (required, maxcount, _uri, _desc) in RFC_FIELDS.items():
        rows = fields.get(key, [])
        if maxcount and len(rows) > maxcount and key != "expires":
            findings.append(F("Fields", f"{len(rows)} '{rows[0]['name']}' fields",
                              "medium",
                              f"RFC 9116 allows at most {maxcount}.",
                              "; ".join(f"line {r['line']}: {r['value']}" for r in rows),
                              f"Keep one and delete the rest.",
                              "RFC 9116 section 2.5.4"))

    # ---- URI-valued fields ----
    for key in ("encryption", "acknowledgments", "policy", "hiring", "csaf", "canonical"):
        for r in fields.get(key, []):
            v = r["value"]
            if not v.lower().startswith(URI_SCHEMES_OK):
                findings.append(F("Fields", f"{r['name']} is not a URI", "medium",
                                  f"'{v[:70]}' does not begin with a scheme.",
                                  f"line {r['line']}",
                                  "Use an absolute URI beginning https://.",
                                  "RFC 9116 section 2.5"))
            elif v.lower().startswith("http://"):
                findings.append(F("Fields", f"{r['name']} uses plain HTTP", "low",
                                  "The link is not encrypted in transit.",
                                  f"{r['name']}: {v}",
                                  "Use https://.", "RFC 9116 section 2.5"))

    # ---- Encryption must not be an inline key ----
    for r in fields.get("encryption", []):
        if "BEGIN PGP PUBLIC KEY" in r["value"] or r["value"].strip().startswith("-----"):
            findings.append(F("Fields", "Encryption contains a key instead of a link",
                              "medium",
                              "The field must be a URI pointing to the key, not the key "
                              "itself.", f"line {r['line']}",
                              "Publish the key at a URL and link to it.",
                              "RFC 9116 section 2.5.4"))

    # ---- Preferred-Languages ----
    for r in fields.get("preferred-languages", []):
        tags = [t.strip() for t in r["value"].split(",") if t.strip()]
        bad = [t for t in tags if not LANG_RE.match(t)]
        if bad:
            findings.append(F("Fields", "Preferred-Languages contains invalid tags",
                              "low",
                              f"{', '.join(bad[:5])} are not language tags.",
                              f"Preferred-Languages: {r['value']}",
                              "Use tags such as 'en, fr, de' - not language names.",
                              "RFC 9116 section 2.5.8"))

    # ---- Canonical ----
    canon = fields.get("canonical", [])
    if not canon:
        findings.append(F("Fields", "No Canonical field", "low",
                          "Nothing states where this file officially lives.", "",
                          "Add 'Canonical: https://example.com/.well-known/security.txt'. "
                          "It lets a researcher confirm they are reading your file and not "
                          "a copy someone else published about you.",
                          "RFC 9116 section 2.5.2"))
    else:
        values = [c["value"].rstrip("/") for c in canon]
        if chosen_url and not any(v.rstrip("/") == chosen_url.rstrip("/") for v in values):
            findings.append(F("Fields", "Canonical does not match where the file was found",
                              "medium",
                              "The file claims to live somewhere other than where it was "
                              "just retrieved from.",
                              f"fetched: {chosen_url}\nCanonical: "
                              + "; ".join(values[:3]),
                              "If the file is served on several domains, list a Canonical "
                              "for each. A mismatch otherwise suggests the file was copied "
                              "from somewhere else and never updated - which means the "
                              "contacts may belong to a different organisation entirely.",
                              "RFC 9116 section 2.5.2"))

    # ---- unknown fields ----
    unknown = [k for k in fields if k not in RFC_FIELDS]
    if unknown:
        findings.append(F("Fields", f"{len(unknown)} unrecognised field(s)", "low",
                          "These are not defined by RFC 9116.",
                          ", ".join(fields[k][0]["name"] for k in unknown[:8]),
                          "Not an error - the format allows extensions, and parsers must "
                          "ignore what they do not know. Check for a typo though: "
                          "'Acknowledgements' with an E is the usual one, since the RFC "
                          "spells it 'Acknowledgments'.", "RFC 9116 section 2.4"))
        for k in unknown:
            if k in ("acknowledgements", "aknowledgments", "acknowledgment"):
                findings.append(F("Fields", f"'{fields[k][0]['name']}' is a misspelling",
                                  "medium",
                                  "The RFC defines 'Acknowledgments' (US spelling, no 'e' "
                                  "before the 'm').",
                                  f"line {fields[k][0]['line']}",
                                  "Rename it to Acknowledgments, or conforming parsers will "
                                  "ignore it.", "RFC 9116 section 2.5.1"))

    # ---- structural problems ----
    for mal in parsed["malformed"]:
        findings.append(F("Syntax", f"Line {mal['line']} is not a valid field", "medium",
                          mal["why"], mal["text"],
                          "Every line must be 'Name: value', a comment starting with #, or "
                          "blank.", "RFC 9116 section 2.2"))
    for emp in parsed["empty_values"]:
        findings.append(F("Syntax", f"{emp['field']} on line {emp['line']} has no value",
                          "medium", "The field name is present but the value is empty.", "",
                          "Give it a value or delete the line.", "RFC 9116 section 2.2"))
    if parsed["byte_order_mark"]:
        findings.append(F("Syntax", "The file begins with a byte order mark", "low",
                          "A UTF-8 BOM precedes the first field.", "",
                          "Strip it. Some parsers read the first field name as "
                          "'\\ufeffContact' and fail to recognise it.",
                          "RFC 9116 section 2.3"))

    # ---- signature ----
    if parsed["signed"]:
        if parsed["signature_intact"]:
            findings.append(F("Signature", "Signed with OpenPGP", "info",
                              parsed["signature_detail"], "",
                              "Good practice - it lets a researcher verify the file was not "
                              "altered. NOTE: this tool checks only that the signature "
                              "block is structurally complete. It does NOT verify the "
                              "signature cryptographically, so it cannot tell you the file "
                              "is authentic. Use gpg --verify for that.",
                              "RFC 9116 section 2.3"))
        else:
            findings.append(F("Signature", "The signature block is broken", "medium",
                              parsed["signature_detail"], "",
                              "Re-sign the file. A malformed signature is worse than none: "
                              "it looks verified at a glance and fails when anyone checks.",
                              "RFC 9116 section 2.3"))
    else:
        findings.append(F("Signature", "Not signed", "info",
                          "The file is plain text with no OpenPGP signature.", "",
                          "Optional. Signing lets a researcher confirm the contacts were "
                          "not tampered with - worth doing if you also publish an "
                          "Encryption key.", "RFC 9116 section 2.3"))

    present = [k for k in RFC_FIELDS if k in fields]
    missing_optional = [k for k in RFC_FIELDS
                        if k not in fields and not RFC_FIELDS[k][0]]
    findings.append(F("Summary", f"{len(present)} of {len(RFC_FIELDS)} defined field(s) "
                      f"present", "info",
                      ", ".join(fields[k][0]["name"] for k in present),
                      "not used: " + ", ".join(missing_optional) if missing_optional else "",
                      "Only Contact and Expires are required; the rest are there if they "
                      "help. Policy is the one most worth adding - it tells a researcher "
                      "what you promise and what you ask of them."))
    return findings


def conformance_score(findings: list[dict], found: bool) -> float:
    """Score by RFC conformance: the file either meets the specification or not."""
    if not found:
        return 0.0
    penalty = {"critical": 45.0, "high": 22.0, "medium": 8.0, "low": 3.0, "info": 0.0}
    total = sum(penalty[f["severity"]] for f in findings)
    return round(clamp(100.0 - total, 0.0, 100.0), 1)


def check_domain(domain: str, timeout: float = 10.0, allow_private: bool = False,
                 check_http: bool = True, progress=None) -> dict:
    """Fetch and check one domain. Returns everything needed for the report."""
    host = domain.strip().lower()
    host = re.sub(r"^[a-z]+://", "", host).split("/")[0].strip()
    if not host:
        return {"domain": domain, "error": "no domain given", "findings": [], "found": False}
    out = {"domain": host, "checked_at": now_iso(), "error": None, "findings": [],
           "found": False, "parsed": None, "body": None, "fetches": {}, "source_url": None,
           "score": 0.0, "grade": "F", "grade_label": "", "grade_colour": "#e5484d",
           "elapsed_ms": None, "addresses": []}
    t0 = time.time()

    targets = [("well_known", f"https://{host}{WELL_KNOWN_PATH}"),
               ("legacy", f"https://{host}{LEGACY_PATH}")]
    if check_http:
        targets.append(("http_well_known", f"http://{host}{WELL_KNOWN_PATH}"))
    for name, url in targets:
        if progress:
            progress(name, url)
        out["fetches"][name] = fetch_with_redirects(url, timeout, allow_private)
        if out["fetches"][name].get("addresses"):
            out["addresses"] = out["fetches"][name]["addresses"]

    wk = out["fetches"]["well_known"]
    if wk.get("error") and "not a public address" in (wk["error"] or ""):
        out["error"] = wk["error"]
        out["findings"] = [F("Refused", "Refused to fetch", "info", wk["error"], "",
                             "This guard exists so the checker cannot be used to reach "
                             "services on an internal network.")]
        out["elapsed_ms"] = int((time.time() - t0) * 1000)
        return out

    loc_findings, loc = check_location(out["fetches"], host)
    out["findings"].extend(loc_findings)
    out["found"] = loc["found"]

    if loc["found"]:
        chosen = loc["source"]
        out["source_url"] = chosen["url"]
        out["status"] = chosen["status"]
        out["content_type"] = chosen["headers"].get("content-type")
        out["size_bytes"] = len(chosen.get("body", b""))
        try:
            text = chosen["body"].decode("utf-8")
            out["encoding"] = "utf-8"
        except UnicodeDecodeError:
            text = chosen["body"].decode("latin-1", "replace")
            out["encoding"] = "not valid UTF-8"
            out["findings"].append(F("Syntax", "The file is not valid UTF-8", "medium",
                                     "Some bytes could not be decoded as UTF-8.", "",
                                     "Save it as UTF-8. The RFC requires it.",
                                     "RFC 9116 section 2.3"))
        out["body"] = text
        parsed = parse_security_txt(text)
        out["parsed"] = parsed
        out["findings"].extend(check_fields(parsed, chosen["url"]))
        if chosen.get("truncated"):
            out["findings"].append(F("Syntax", "The file is unusually large", "low",
                                     f"More than {fmt_bytes(MAX_BODY_BYTES)}; only the "
                                     f"first part was read.", "",
                                     "A security.txt should be a few lines. Something else "
                                     "is being served from that path."))

    out["blocked"] = loc.get("blocked", False)
    if out["blocked"]:
        # grading a domain we were never allowed to read would be dishonest
        out["score"] = None
        out["grade"], out["grade_label"] = "?", "could not be checked"
        out["grade_colour"] = "#8b8f9b"
    else:
        out["score"] = conformance_score(out["findings"], out["found"])
        out["grade"], out["grade_label"], out["grade_colour"] = grade_for(out["score"])
    out["elapsed_ms"] = int((time.time() - t0) * 1000)
    out["counts"] = {s: sum(1 for f in out["findings"] if f["severity"] == s)
                     for s in SEVERITIES}
    return out


# =============================================================================
# SECTION 5 - Database
# =============================================================================

SCHEMA = """
CREATE TABLE IF NOT EXISTS checks (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    ts TEXT NOT NULL, domain TEXT NOT NULL, found INTEGER DEFAULT 0,
    blocked INTEGER DEFAULT 0, source_url TEXT, status INTEGER, content_type TEXT,
    size_bytes INTEGER, encoding TEXT, score REAL, grade TEXT, grade_label TEXT,
    signed INTEGER DEFAULT 0, expires TEXT, expires_days REAL, contacts INTEGER DEFAULT 0,
    elapsed_ms INTEGER, error TEXT, body TEXT, fetches TEXT, addresses TEXT,
    critical INTEGER DEFAULT 0, high INTEGER DEFAULT 0, medium INTEGER DEFAULT 0,
    low INTEGER DEFAULT 0, info INTEGER DEFAULT 0, note TEXT
);
CREATE TABLE IF NOT EXISTS findings (
    id INTEGER PRIMARY KEY AUTOINCREMENT, check_id INTEGER NOT NULL,
    category TEXT, title TEXT, severity TEXT, description TEXT, evidence TEXT,
    advice TEXT, rfc TEXT, FOREIGN KEY (check_id) REFERENCES checks(id)
);
CREATE TABLE IF NOT EXISTS fields (
    id INTEGER PRIMARY KEY AUTOINCREMENT, check_id INTEGER NOT NULL,
    line INTEGER, name TEXT, value TEXT,
    FOREIGN KEY (check_id) REFERENCES checks(id)
);
CREATE TABLE IF NOT EXISTS audit_log (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    ts TEXT NOT NULL, level TEXT NOT NULL, source TEXT, message TEXT, check_id INTEGER
);
CREATE INDEX IF NOT EXISTS idx_checks_domain ON checks(domain);
CREATE INDEX IF NOT EXISTS idx_find_check ON findings(check_id);
CREATE INDEX IF NOT EXISTS idx_fields_check ON fields(check_id);
CREATE INDEX IF NOT EXISTS idx_audit_ts ON audit_log(ts);
"""

_DB_PATH = DEFAULT_DB


def set_db_path(p: str) -> None:
    global _DB_PATH
    _DB_PATH = p


def db_path() -> str:
    return _DB_PATH


def connect(path: str | None = None) -> sqlite3.Connection:
    conn = sqlite3.connect(path or _DB_PATH, timeout=30.0)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA busy_timeout=30000")
    conn.execute("PRAGMA foreign_keys=ON")
    return conn


def init_db(conn=None) -> None:
    own = conn is None
    conn = conn or connect()
    try:
        conn.executescript(SCHEMA)
        conn.commit()
    finally:
        if own:
            conn.close()


def q(sql: str, args: tuple = (), conn=None) -> list[sqlite3.Row]:
    own = conn is None
    conn = conn or connect()
    try:
        return conn.execute(sql, args).fetchall()
    finally:
        if own:
            conn.close()


def q1(sql: str, args: tuple = (), conn=None):
    rows = q(sql, args, conn)
    return rows[0] if rows else None


def log_event(level: str, source: str, message: str, check_id=None, conn=None) -> None:
    own = conn is None
    conn = conn or connect()
    try:
        conn.execute("INSERT INTO audit_log (ts, level, source, message, check_id) "
                     "VALUES (?,?,?,?,?)",
                     (now_iso(), level.upper(), source,
                      " ".join(str(message).split())[:1000], check_id))
        conn.commit()
    except Exception:
        pass
    finally:
        if own:
            conn.close()


def save_check(result: dict, note: str = "") -> int:
    conn = connect()
    try:
        init_db(conn)
        parsed = result.get("parsed") or {}
        fields = parsed.get("fields", {})
        expires_val, expires_days = None, None
        if fields.get("expires"):
            expires_val = fields["expires"][0]["value"]
            dt, _c = parse_rfc3339(expires_val)
            if dt:
                expires_days = round((dt - datetime.now(timezone.utc)).total_seconds()
                                     / 86400.0, 2)
        counts = result.get("counts") or {s: 0 for s in SEVERITIES}
        cur = conn.execute(
            "INSERT INTO checks (ts, domain, found, blocked, source_url, status,"
            " content_type, size_bytes, encoding, score, grade, grade_label, signed,"
            " expires, expires_days, contacts, elapsed_ms, error, body, fetches,"
            " addresses, critical, high, medium, low, info, note)"
            " VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (result.get("checked_at") or now_iso(), result["domain"],
             int(bool(result.get("found"))), int(bool(result.get("blocked"))),
             result.get("source_url"), result.get("status"), result.get("content_type"),
             result.get("size_bytes"), result.get("encoding"), result.get("score"),
             result.get("grade"), result.get("grade_label"),
             int(bool(parsed.get("signed"))), expires_val, expires_days,
             len(fields.get("contact", [])), result.get("elapsed_ms"), result.get("error"),
             result.get("body"),
             json.dumps({k: {"status": v.get("status"), "error": v.get("error"),
                             "content_type": v.get("headers", {}).get("content-type"),
                             "redirects": v.get("redirects"),
                             "elapsed_ms": v.get("elapsed_ms")}
                         for k, v in (result.get("fetches") or {}).items()}, default=str),
             json.dumps(result.get("addresses", [])),
             counts["critical"], counts["high"], counts["medium"], counts["low"],
             counts["info"], note))
        cid = cur.lastrowid
        for f in result.get("findings", []):
            conn.execute("INSERT INTO findings (check_id, category, title, severity,"
                         " description, evidence, advice, rfc) VALUES (?,?,?,?,?,?,?,?)",
                         (cid, f["category"], f["title"], f["severity"], f["description"],
                          f["evidence"], f.get("advice", ""), f.get("rfc", "")))
        for key, rows in fields.items():
            for r in rows:
                conn.execute("INSERT INTO fields (check_id, line, name, value) "
                             "VALUES (?,?,?,?)", (cid, r["line"], r["name"], r["value"]))
        conn.commit()
        log_event("INFO", "check",
                  f"Checked {result['domain']}: grade {result.get('grade')} "
                  f"({result.get('score')})", cid, conn)
        return cid
    finally:
        conn.close()


def latest_check_id(domain: str | None = None, conn=None):
    if domain:
        row = q1("SELECT id FROM checks WHERE domain=? ORDER BY id DESC LIMIT 1",
                 (domain,), conn)
    else:
        row = q1("SELECT id FROM checks ORDER BY id DESC LIMIT 1", (), conn)
    return row["id"] if row else None


def check_summary(cid: int, conn=None):
    row = q1("SELECT * FROM checks WHERE id=?", (cid,), conn)
    if not row:
        return None
    d = dict(row)
    for key in ("fetches", "addresses"):
        try:
            d[key] = json.loads(d[key] or "{}")
        except json.JSONDecodeError:
            d[key] = {}
    d["grade_colour"] = grade_for(d["score"])[2] if d["score"] is not None else "#8b8f9b"
    return d


# =============================================================================
# SECTION 6 - Charts (hand-drawn SVG: no CDN, no JS library, works offline)
# =============================================================================

def svg_gauge(score, grade, label, colour, size=170, title="RFC 9116 conformance") -> str:
    if score is None:
        return (f'<figure class="chart"><figcaption>{html_escape(title)}</figcaption>'
                f'<div class="chart-empty">not graded - the file could not be read, and '
                f'grading a domain we were never allowed to see would be dishonest</div>'
                f'</figure>')
    cx = cy = size / 2
    r = size / 2 - 16
    frac = clamp(score / 100.0, 0, 1)
    start, sweep = -210.0, 240.0 * frac
    def arc(a0, a1, colr, w):
        r0, r1 = math.radians(a0), math.radians(a1)
        x0, y0 = cx + r * math.cos(r0), cy + r * math.sin(r0)
        x1, y1 = cx + r * math.cos(r1), cy + r * math.sin(r1)
        lg = 1 if (a1 - a0) > 180 else 0
        return (f'<path d="M {x0:.2f} {y0:.2f} A {r:.2f} {r:.2f} 0 {lg} 1 {x1:.2f} '
                f'{y1:.2f}" fill="none" stroke="{colr}" stroke-width="{w}" '
                f'stroke-linecap="round"/>')
    return (f'<figure class="chart"><figcaption>{html_escape(title)}</figcaption>'
            f'<svg viewBox="0 0 {size} {size}" width="{size}" height="{size}" role="img" '
            f'aria-label="{html_escape(title)}: {score}">'
            f'{arc(start, start + 240, "#1e222a", 13)}'
            f'{arc(start, start + sweep, colour, 13) if sweep > 0.5 else ""}'
            f'<text x="{cx}" y="{cy + 4}" text-anchor="middle" '
            f'style="fill:{colour};font:700 34px ui-monospace,monospace">'
            f'{html_escape(grade)}</text>'
            f'<text x="{cx}" y="{cy + 24}" text-anchor="middle" class="bl">'
            f'{html_escape(str(score))}/100</text>'
            f'<text x="{cx}" y="{size - 4}" text-anchor="middle" class="bl">'
            f'{html_escape(label[:30])}</text></svg></figure>')


def svg_pie(items, size=180, title="Findings by severity", fmt=lambda v: f"{v:g}"):
    items = [(l, float(v), c) for (l, v, c) in items if v and v > 0]
    total = sum(v for _, v, _ in items)
    if total <= 0:
        return f'<div class="chart-empty">{html_escape(title)}: nothing to show</div>'
    cx = cy = size / 2
    r_out, r_in = size / 2 - 10, size / 2 - 42
    parts, legend, angle = [], [], -90.0
    for label, value, color in items:
        sweep = 360.0 * value / total
        if abs(sweep - 360.0) < 1e-9:
            parts.append(f'<circle cx="{cx}" cy="{cy}" r="{(r_out + r_in) / 2:.2f}" '
                         f'fill="none" stroke="{color}" stroke-width="{r_out - r_in:.2f}"/>')
        else:
            a0, a1 = math.radians(angle), math.radians(angle + sweep)
            x0, y0 = cx + r_out * math.cos(a0), cy + r_out * math.sin(a0)
            x1, y1 = cx + r_out * math.cos(a1), cy + r_out * math.sin(a1)
            x2, y2 = cx + r_in * math.cos(a1), cy + r_in * math.sin(a1)
            x3, y3 = cx + r_in * math.cos(a0), cy + r_in * math.sin(a0)
            lg = 1 if sweep > 180 else 0
            parts.append(f'<path d="M {x0:.2f} {y0:.2f} A {r_out:.2f} {r_out:.2f} 0 {lg} 1 '
                         f'{x1:.2f} {y1:.2f} L {x2:.2f} {y2:.2f} A {r_in:.2f} {r_in:.2f} 0 '
                         f'{lg} 0 {x3:.2f} {y3:.2f} Z" fill="{color}">'
                         f'<title>{html_escape(label)}: {html_escape(fmt(value))}</title>'
                         f'</path>')
        angle += sweep
        legend.append(f'<div class="lg"><i style="background:{color}"></i>'
                      f'<span>{html_escape(label)}</span><b>{html_escape(fmt(value))}</b>'
                      f'</div>')
    return (f'<figure class="chart"><figcaption>{html_escape(title)}</figcaption>'
            f'<div class="chart-row"><svg viewBox="0 0 {size} {size}" width="{size}" '
            f'height="{size}" role="img" aria-label="{html_escape(title)}">{"".join(parts)}'
            f'<text x="{cx}" y="{cy + 5}" text-anchor="middle" class="pie-n">'
            f'{html_escape(fmt(total))}</text></svg>'
            f'<div class="legend">{"".join(legend)}</div></div></figure>')


def svg_checklist(parsed: dict, width=430, title="RFC 9116 fields") -> str:
    """Every field the RFC defines, present or not - absence is the information."""
    fields = (parsed or {}).get("fields", {})
    rows = list(RFC_FIELDS.items())
    row_h, gap = 26, 5
    height = len(rows) * (row_h + gap) + 12
    parts = []
    for i, (key, (required, _mx, _uri, _desc)) in enumerate(rows):
        y = 6 + i * (row_h + gap)
        present = key in fields
        n = len(fields.get(key, []))
        if present:
            colour, mark = "#30a46c", "\u2713"
        elif required:
            colour, mark = "#e5484d", "\u2717"
        else:
            colour, mark = "#3a3f4a", "\u00b7"
        parts.append(f'<rect x="6" y="{y}" width="{width - 12}" height="{row_h}" rx="5" '
                     f'fill="#1a1e26" stroke="{colour}" stroke-width="1"/>')
        parts.append(f'<text x="18" y="{y + 18}" style="fill:{colour};'
                     f'font:700 14px ui-monospace,monospace">{mark}</text>')
        parts.append(f'<text x="38" y="{y + 18}" class="bv">'
                     f'{html_escape(key.title())}</text>')
        tag = ("REQUIRED" if required else "optional") if not present else (
            f"{n} value(s)")
        parts.append(f'<text x="{width - 18}" y="{y + 18}" text-anchor="end" class="bl">'
                     f'{html_escape(tag)}</text>')
    return (f'<figure class="chart"><figcaption>{html_escape(title)} &middot; '
            f'green present, red required and missing</figcaption>'
            f'<svg viewBox="0 0 {width} {height}" width="{width}" height="{height}" '
            f'role="img" aria-label="{html_escape(title)}">{"".join(parts)}</svg></figure>')


def svg_history(rows: list[dict], width=440, height=150,
                title="Grade over time") -> str:
    pts = [r for r in rows if r.get("score") is not None]
    if len(pts) < 2:
        return (f'<div class="chart-empty">{html_escape(title)}: needs at least two graded '
                f'checks ({len(pts)} so far)</div>')
    pad = 30
    step = (width - pad * 2) / max(len(pts) - 1, 1)
    coords = [(pad + i * step, height - pad - (height - pad * 2) * (r["score"] / 100.0))
              for i, r in enumerate(pts)]
    d = " ".join(f"{'M' if i == 0 else 'L'} {x:.1f} {y:.1f}"
                 for i, (x, y) in enumerate(coords))
    dots = "".join(
        f'<circle cx="{x:.1f}" cy="{y:.1f}" r="3.5" '
        f'fill="{grade_for(pts[i]["score"])[2]}">'
        f'<title>{html_escape(str(pts[i].get("ts", ""))[:19])}: {pts[i]["score"]} '
        f'({grade_for(pts[i]["score"])[0]})</title></circle>'
        for i, (x, y) in enumerate(coords))
    grid = "".join(
        f'<line x1="{pad}" y1="{height - pad - (height - pad * 2) * f:.1f}" '
        f'x2="{width - pad}" y2="{height - pad - (height - pad * 2) * f:.1f}" class="gl"/>'
        f'<text x="{pad - 6}" y="{height - pad - (height - pad * 2) * f + 4:.1f}" '
        f'text-anchor="end" class="bl">{100 * f:.0f}</text>' for f in (0, 0.5, 1.0))
    return (f'<figure class="chart"><figcaption>{html_escape(title)}</figcaption>'
            f'<svg viewBox="0 0 {width} {height}" width="{width}" height="{height}" '
            f'role="img" aria-label="{html_escape(title)}">{grid}'
            f'<path d="{d}" fill="none" stroke="#5b8def" stroke-width="2"/>{dots}'
            f'</svg></figure>')


def svg_bar(items, width=440, title="", color="#5b8def", fmt=lambda v: f"{v:g}",
            colors=None):
    items = [(str(l), float(v or 0)) for l, v in items]
    if not items or all(v <= 0 for _, v in items):
        return f'<div class="chart-empty">{html_escape(title)}: nothing to show</div>'
    row_h, gap, pad_l, pad_t = 22, 7, 168, 8
    height = pad_t * 2 + len(items) * (row_h + gap)
    mx = max(v for _, v in items) or 1
    bw = width - pad_l - 66
    rows = []
    for i, (label, value) in enumerate(items):
        y = pad_t + i * (row_h + gap)
        w = max(2.0, bw * value / mx)
        c = (colors or {}).get(label, color)
        lbl = label if len(label) <= 23 else label[:22] + "\u2026"
        rows.append(
            f'<text x="{pad_l - 9}" y="{y + row_h * 0.7:.1f}" text-anchor="end" class="bl">'
            f'{html_escape(lbl)}</text>'
            f'<rect x="{pad_l}" y="{y}" width="{bw}" height="{row_h}" rx="4" class="btrack"/>'
            f'<rect x="{pad_l}" y="{y}" width="{w:.1f}" height="{row_h}" rx="4" fill="{c}">'
            f'<title>{html_escape(label)}: {html_escape(fmt(value))}</title></rect>'
            f'<text x="{pad_l + bw + 7:.1f}" y="{y + row_h * 0.7:.1f}" class="bv">'
            f'{html_escape(fmt(value))}</text>')
    return (f'<figure class="chart"><figcaption>{html_escape(title)}</figcaption>'
            f'<svg viewBox="0 0 {width} {height}" width="{width}" height="{height}" '
            f'role="img" aria-label="{html_escape(title)}">{"".join(rows)}</svg></figure>')


# =============================================================================
# SECTION 7 - Exports
# =============================================================================

def report_payload(cid=None, conn=None) -> dict:
    own = conn is None
    conn = conn or connect()
    try:
        cid = cid or latest_check_id(conn=conn)
        chk = check_summary(cid, conn) if cid else None
        return {
            "tool": APP_NAME, "version": VERSION, "author": AUTHOR,
            "generated_at": now_iso(), "specification": "RFC 9116",
            "disclaimer": DISCLAIMER_LONG,
            "what_a_pass_does_not_mean": NOT_A_GUARANTEE,
            "limitations": [
                "This checks a text file. It cannot tell you whether the contact address "
                "accepts mail, whether a human triages it, or whether a report is answered.",
                "A domain with no security.txt is not insecure - RFC 9116 is a "
                "recommendation and adoption is voluntary.",
                "An OpenPGP signature is checked only for structural completeness. It is "
                "NOT verified cryptographically, so a signed file is not proven authentic.",
                "A bot-protection challenge is reported as 'could not be checked', never as "
                "'no file' - being blocked is not evidence of absence.",
                "Links inside the file (Policy, Encryption, Acknowledgments) are validated "
                "as URIs but never fetched.",
            ],
            "check": chk,
            "findings": [dict(r) for r in q(
                "SELECT category,title,severity,description,evidence,advice,rfc FROM "
                "findings WHERE check_id=? ORDER BY CASE severity WHEN 'critical' THEN 0 "
                "WHEN 'high' THEN 1 WHEN 'medium' THEN 2 WHEN 'low' THEN 3 ELSE 4 END, id",
                (cid,), conn)] if cid else [],
            "fields": [dict(r) for r in q(
                "SELECT line,name,value FROM fields WHERE check_id=? ORDER BY line",
                (cid,), conn)] if cid else [],
            "history": [dict(r) for r in q(
                "SELECT id,ts,domain,grade,score,found FROM checks WHERE domain=? "
                "ORDER BY id", (chk["domain"],), conn)] if chk else [],
            "checks": [dict(r) for r in q("SELECT id,ts,domain,grade,score,found "
                                          "FROM checks ORDER BY id DESC LIMIT 50",
                                          (), conn)],
        }
    finally:
        if own:
            conn.close()


def export_json(cid=None) -> str:
    return json.dumps(report_payload(cid), indent=2, default=str)


def export_csv(cid=None) -> str:
    conn = connect()
    try:
        cid = cid or latest_check_id(conn=conn)
        chk = check_summary(cid, conn)
        buf = io.StringIO()
        w = csv.writer(buf, lineterminator="\n")
        w.writerow([f"# {APP_NAME} v{VERSION} by {AUTHOR} - checks against RFC 9116"])
        w.writerow([f"# check={cid} domain={chk['domain'] if chk else '-'} "
                    f"generated={now_iso()}"])
        w.writerow([f"# {DISCLAIMER_SHORT}"])
        if not chk:
            return buf.getvalue()
        w.writerow([])
        w.writerow(["## Result"])
        w.writerow(["domain", "found", "blocked", "grade", "score", "source_url",
                    "content_type", "expires", "contacts", "signed"])
        w.writerow([chk["domain"], chk["found"], chk["blocked"], chk["grade"],
                    chk["score"], chk["source_url"], chk["content_type"], chk["expires"],
                    chk["contacts"], chk["signed"]])
        w.writerow([])
        w.writerow(["## Fields as published"])
        w.writerow(["line", "name", "value"])
        for r in q("SELECT * FROM fields WHERE check_id=? ORDER BY line", (cid,), conn):
            w.writerow([r["line"], r["name"], r["value"]])
        w.writerow([])
        w.writerow(["## Findings"])
        w.writerow(["severity", "category", "title", "description", "advice", "rfc"])
        for r in q("SELECT * FROM findings WHERE check_id=? ORDER BY id", (cid,), conn):
            w.writerow([r["severity"], r["category"], r["title"], r["description"],
                        r["advice"], r["rfc"]])
        return buf.getvalue()
    finally:
        conn.close()


def export_html(cid=None) -> str:
    conn = connect()
    try:
        p = report_payload(cid, conn)
        chk, esc = p["check"], html_escape
        if not chk:
            return "<!doctype html><html><body><h1>No checks recorded</h1></body></html>"
        counts = {s: chk[s] or 0 for s in SEVERITIES}
        gauge = svg_gauge(chk["score"], chk["grade"], chk["grade_label"],
                          chk["grade_colour"])
        pie = svg_pie([(s, counts[s], SEV_COLOR[s]) for s in SEVERITIES])
        parsed = {"fields": {}}
        for f in p["fields"]:
            parsed["fields"].setdefault(f["name"].lower(), []).append(f)
        checklist = svg_checklist(parsed)
        hist = svg_history(p["history"])
        frows = "".join(
            f'<tr><td><span class="pill" style="background:{SEV_COLOR[f["severity"]]}">'
            f'{esc(f["severity"].upper())}</span></td>'
            f'<td><b>{esc(f["title"])}</b>'
            f'<div class="desc">{esc(f["description"])}</div>'
            + (f'<pre>{esc(f["evidence"])}</pre>' if f["evidence"] else "")
            + (f'<div class="means"><b>What to do:</b> {esc(f["advice"])}</div>'
               if f["advice"] else "")
            + (f'<div class="sub2">{esc(f["rfc"])}</div>' if f["rfc"] else "")
            + "</td></tr>" for f in p["findings"])
        rows = "".join(f'<tr><td class="num">{f["line"]}</td>'
                       f'<td class="mono">{esc(f["name"])}</td>'
                       f'<td class="mono">{esc(f["value"])}</td></tr>'
                       for f in p["fields"])
        limits = "".join(f"<li>{esc(x)}</li>" for x in p["limitations"])
        body_block = (f'<h2>The file as published</h2><pre>{esc(chk["body"])}</pre>'
                      if chk.get("body") else "")
        return f"""<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{APP_SHORT} - {esc(chk['domain'])}</title><style>
 body{{font:14px/1.55 ui-sans-serif,system-ui,'Segoe UI',Roboto,sans-serif;margin:0;
      background:#0f1115;color:#e6e8ee}}
 .wrap{{max-width:1080px;margin:0 auto;padding:28px 20px 60px}}
 h1{{font-size:22px;margin:0 0 4px}} .meta{{color:#8b8f9b;font-size:12.5px}}
 h2{{font-size:12px;text-transform:uppercase;letter-spacing:.15em;color:#8b8f9b;
     margin:30px 0 12px;border-bottom:1px solid #262a33;padding-bottom:8px}}
 table{{width:100%;border-collapse:collapse;background:#171a21;border:1px solid #262a33;
        border-radius:10px;overflow:hidden;font-size:12.7px}}
 th{{text-align:left;font-size:10.5px;letter-spacing:.11em;text-transform:uppercase;
     color:#8b8f9b;padding:9px 11px;border-bottom:1px solid #262a33;background:#1c2029}}
 td{{padding:8px 11px;border-bottom:1px solid #1e222a;vertical-align:top}}
 .mono{{font-family:ui-monospace,Menlo,monospace;font-size:11.5px;word-break:break-word}}
 .num{{font-family:ui-monospace,monospace;text-align:right}}
 .sub2{{color:#6f7685;font-size:11px;margin-top:4px;font-family:ui-monospace,monospace}}
 .pill{{color:#0f1115;font-weight:700;font-size:10px;padding:2px 8px;border-radius:20px}}
 .desc{{color:#b6bac4;margin-top:4px;max-width:82ch}}
 .means{{margin-top:6px;color:#8fd3b0;font-size:12.4px;max-width:82ch}}
 pre{{background:#0f1115;border:1px solid #262a33;border-radius:6px;padding:9px;
      font-family:ui-monospace,monospace;font-size:11.5px;margin:6px 0 0;overflow:auto;
      white-space:pre-wrap;color:#b6bac4;max-height:420px}}
 .warn{{background:#231a12;border:1px solid #5a3b1c;color:#ffcf9e;padding:12px 14px;
        border-radius:10px;font-size:12.5px;margin:14px 0;white-space:pre-wrap}}
 .note{{background:#12202a;border:1px solid #1c4a5e;color:#a8d8e8;padding:11px 14px;
        border-radius:10px;font-size:12.5px;margin:14px 0}}
 .note ul{{margin:6px 0 0 18px;padding:0}} .note li{{margin:3px 0}}
 .charts{{display:flex;gap:18px;flex-wrap:wrap;align-items:flex-start;margin-bottom:14px}}
 .chart{{margin:0;background:#171a21;border:1px solid #262a33;border-radius:10px;
   padding:14px 16px}}
 .chart figcaption{{font-size:10.5px;letter-spacing:.12em;text-transform:uppercase;
   color:#8b8f9b;margin-bottom:10px;font-family:ui-monospace,monospace}}
 .chart-row{{display:flex;gap:16px;align-items:center;flex-wrap:wrap}}
 .chart-empty{{background:#171a21;border:1px dashed #31363f;border-radius:10px;padding:18px;
   color:#8b8f9b;font-size:12.5px}}
 .legend{{display:flex;flex-direction:column;gap:6px;min-width:130px}}
 .lg{{display:flex;align-items:center;gap:7px;font-size:12.5px}}
 .lg i{{width:11px;height:11px;border-radius:3px}} .lg span{{flex:1}}
 text.bl{{fill:#8b8f9b;font:10.5px ui-monospace,monospace}}
 text.bv{{fill:#e6e8ee;font:11.5px ui-monospace,monospace}}
 text.pie-n{{fill:#e6e8ee;font:700 16px ui-monospace,monospace}}
 rect.btrack{{fill:#1e222a}} line.gl{{stroke:#262a33;stroke-width:1}}
 footer{{margin-top:36px;color:#6f7685;font-size:12px;border-top:1px solid #262a33;
   padding-top:14px}}
</style></head><body><div class="wrap">
<h1>security.txt report - {esc(chk['domain'])}</h1>
<div class="meta">{esc(chk['source_url'] or 'no file found')} &middot;
 {ts_pretty(chk['ts'])} &middot; {chk['elapsed_ms']} ms &middot; checked against RFC 9116</div>
<div class="note"><b>What a pass does not mean.</b> {esc(p['what_a_pass_does_not_mean'])}
 <ul>{limits}</ul></div>
<div class="warn">{esc(DISCLAIMER_LONG)}</div>
<div class="charts">{gauge}{checklist}{pie}</div>
{f'<div class="charts">{hist}</div>' if len(p['history']) > 1 else ''}
{'<h2>Fields as published (' + str(len(p['fields'])) + ')</h2><table><tr><th>Line</th>'
 '<th>Field</th><th>Value</th></tr>' + rows + '</table>' if rows else ''}
<h2>Findings ({len(p['findings'])})</h2>
{'<table><tr><th>Severity</th><th>Detail</th></tr>' + frows + '</table>'
 if frows else '<div class="chart-empty">No findings.</div>'}
{body_block}
<footer>Generated by {APP_NAME} v{VERSION} &middot; {AUTHOR} &middot; {GITHUB}<br>
 This report describes a text file. It says nothing about whether anyone reads the inbox
 behind it.</footer></div></body></html>"""
    finally:
        conn.close()


# =============================================================================
# SECTION 8 - Web application (no CDN, no JS libraries)
# =============================================================================

CSS = """
:root{--bg:#0f1115;--panel:#171a21;--panel-2:#1c2029;--line:#262a33;--line-2:#31363f;
 --tx:#e6e8ee;--tx-dim:#8b8f9b;--tx-mid:#b6bac4;--accent:#5b8def;--ok:#30a46c;
 --warn:#ffb224;--crit:#e5484d;--good:#8fd3b0;
 --mono:ui-monospace,SFMono-Regular,'JetBrains Mono',Menlo,Consolas,'Courier New',monospace;}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--tx);
 font:14px/1.55 ui-sans-serif,system-ui,-apple-system,'Segoe UI',Roboto,Helvetica,Arial,sans-serif}
a{color:var(--accent);text-decoration:none} a:hover{text-decoration:underline}
:focus-visible{outline:2px solid var(--accent);outline-offset:2px;border-radius:4px}
header.top{border-bottom:1px solid var(--line);background:var(--panel);position:sticky;top:0;z-index:9}
.hd{max-width:1200px;margin:0 auto;padding:11px 20px;display:flex;align-items:center;gap:14px;
 flex-wrap:wrap}
.brand{font-family:var(--mono);font-weight:700;letter-spacing:-.4px;font-size:15px}
.brand b{color:var(--accent)}
.brand small{display:block;font-weight:400;font-size:10px;letter-spacing:.14em;
 text-transform:uppercase;color:var(--tx-dim)}
nav{display:flex;gap:2px;margin-left:auto;flex-wrap:wrap}
nav a{font-family:var(--mono);font-size:11.5px;letter-spacing:.05em;text-transform:uppercase;
 padding:6px 10px;border-radius:6px;color:var(--tx-dim)}
nav a:hover{background:var(--panel-2);color:var(--tx);text-decoration:none}
nav a.on{background:var(--accent);color:#0b0d10;font-weight:600}
.wrap{max-width:1200px;margin:0 auto;padding:20px 20px 70px}
.banner{background:#12202a;border:1px solid #1c4a5e;color:#a8d8e8;padding:10px 14px;
 border-radius:9px;font-size:12.3px;margin-bottom:12px;line-height:1.5}
.banner.warn{background:#231a12;border-color:#5a3b1c;color:#ffcf9e}
.banner.bad{background:#2a1216;border-color:#6b2229;color:#ffc9cd}
.banner b{color:#fff} .banner ul{margin:6px 0 0 18px;padding:0} .banner li{margin:3px 0}
h1{font-size:19px;margin:0 0 3px;letter-spacing:-.3px}
h2{font-family:var(--mono);font-size:11.5px;letter-spacing:.16em;text-transform:uppercase;
 color:var(--tx-dim);margin:24px 0 12px;padding-bottom:8px;border-bottom:1px solid var(--line)}
.sub{color:var(--tx-dim);font-size:12.5px;margin-bottom:14px}
.sub2{color:var(--tx-dim);font-size:11px;font-family:var(--mono)}
.bar{display:flex;gap:9px;align-items:center;flex-wrap:wrap;margin:0 0 16px}
.btn{font-family:var(--mono);font-size:12px;padding:8px 13px;border-radius:7px;cursor:pointer;
 border:1px solid var(--line-2);background:var(--panel-2);color:var(--tx);display:inline-block}
.btn:hover{border-color:var(--accent);text-decoration:none}
.btn.primary{background:var(--accent);border-color:var(--accent);color:#0b0d10;font-weight:700}
select,input[type=text]{font-family:var(--mono);font-size:12px;padding:8px 10px;
 background:var(--panel-2);color:var(--tx);border:1px solid var(--line-2);border-radius:7px}
input[type=text]{min-width:260px}
label.chk{font-family:var(--mono);font-size:12px;color:var(--tx-dim);display:flex;gap:5px;
 align-items:center}
.grid{display:grid;gap:12px;grid-template-columns:repeat(auto-fit,minmax(132px,1fr));margin:14px 0}
.card{background:var(--panel);border:1px solid var(--line);border-radius:11px;padding:13px 15px}
.card .l{font-family:var(--mono);font-size:10.5px;letter-spacing:.13em;text-transform:uppercase;
 color:var(--tx-dim)}
.card .n{font-size:21px;font-weight:700;line-height:1.3;font-family:var(--mono)}
.card .s{font-size:11.5px;color:var(--tx-dim)}
table{width:100%;border-collapse:collapse;background:var(--panel);border:1px solid var(--line);
 border-radius:11px;overflow:hidden;font-size:12.7px}
th{text-align:left;font-family:var(--mono);font-size:10.5px;letter-spacing:.11em;
 text-transform:uppercase;color:var(--tx-dim);padding:9px 11px;border-bottom:1px solid var(--line);
 background:var(--panel-2);white-space:nowrap}
td{padding:8px 11px;border-bottom:1px solid #1e222a;vertical-align:top}
tr:last-child td{border-bottom:none} tr:hover td{background:#1b1f27}
.mono{font-family:var(--mono);font-size:11.8px;word-break:break-word}
.num{font-family:var(--mono);font-size:11.8px;text-align:right}
.pill{display:inline-block;color:#0b0d10;font-weight:700;font-size:10px;padding:2px 8px;
 border-radius:20px;letter-spacing:.06em;font-family:var(--mono);white-space:nowrap}
.grade{display:inline-block;font-family:var(--mono);font-weight:700;font-size:13px;
 padding:2px 10px;border-radius:6px;color:#0b0d10}
.desc{color:var(--tx-mid);margin-top:4px;max-width:82ch}
.means{margin-top:6px;color:var(--good);font-size:12.4px;max-width:82ch}
pre{background:var(--bg);border:1px solid var(--line);border-radius:6px;padding:9px 11px;
 font-family:var(--mono);font-size:11.5px;margin:6px 0 0;max-height:420px;overflow:auto;
 white-space:pre-wrap;color:var(--tx-mid)}
.charts{display:flex;gap:18px;flex-wrap:wrap;align-items:flex-start;margin-bottom:14px}
.chart{margin:0;background:var(--panel);border:1px solid var(--line);border-radius:11px;
 padding:14px 16px}
.chart figcaption{font-family:var(--mono);font-size:10.5px;letter-spacing:.13em;
 text-transform:uppercase;color:var(--tx-dim);margin-bottom:10px}
.chart-row{display:flex;gap:16px;align-items:center;flex-wrap:wrap}
.chart-empty{background:var(--panel);border:1px dashed var(--line-2);border-radius:11px;
 padding:20px;color:var(--tx-dim);font-size:12.5px;flex:1;min-width:240px}
.legend{display:flex;flex-direction:column;gap:6px;min-width:130px}
.lg{display:flex;align-items:center;gap:7px;font-size:12.5px}
.lg i{width:11px;height:11px;border-radius:3px;flex:none} .lg span{flex:1}
.lg b{font-family:var(--mono)}
text.bl{fill:#8b8f9b;font:10.5px var(--mono)} text.bv{fill:#e6e8ee;font:11.5px var(--mono)}
text.pie-n{fill:#e6e8ee;font:700 16px var(--mono)}
rect.btrack{fill:#1e222a} line.gl{stroke:#262a33;stroke-width:1}
.empty{background:var(--panel);border:1px dashed var(--line-2);border-radius:11px;padding:28px;
 text-align:center;color:var(--tx-dim)}
.empty b{display:block;color:var(--tx);margin-bottom:6px;font-size:15px}
footer{max-width:1200px;margin:0 auto;padding:16px 20px 40px;color:#6f7685;font-size:11.5px;
 border-top:1px solid var(--line);line-height:1.7}
@media (max-width:640px){.hd{padding:10px 14px} .wrap{padding:14px 14px 50px}
 nav{margin-left:0;width:100%} .card .n{font-size:18px} table{font-size:12px}
 th,td{padding:7px 8px} input[type=text]{min-width:180px}}
"""

BASE_TPL = """<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{{ page }} - """ + APP_SHORT + """</title><style>""" + CSS + """</style></head><body>
<header class="top"><div class="hd">
 <div class="brand"><b>SECTXT</b> <small>RFC 9116 checker</small></div>
 <nav>
  <a href="{{ url_for('page_home') }}" class="{{ 'on' if nav=='home' }}">Check</a>
  <a href="{{ url_for('page_history') }}" class="{{ 'on' if nav=='history' }}">History</a>
  <a href="{{ url_for('page_learn') }}" class="{{ 'on' if nav=='learn' }}">Learn</a>
  <a href="{{ url_for('page_template') }}" class="{{ 'on' if nav=='template' }}">Template</a>
 </nav></div></header>
<div class="wrap">
 <div class="banner"><b>This checks a text file, not an organisation.</b>
  """ + NOT_A_GUARANTEE + """</div>
 {% if error %}<div class="banner bad"><b>That failed:</b> {{ error }}</div>{% endif %}
 {% block body %}{% endblock %}
</div>
<footer>""" + APP_NAME + """ v""" + VERSION + """ &middot; built by """ + AUTHOR + """ &middot;
 <a href=\"""" + GITHUB + """\" rel="noopener">GitHub</a> &middot;
 <a href=\"""" + LINKEDIN + """\" rel="noopener">LinkedIn</a><br>
 Checking a domain makes real requests to it. Private, loopback and link-local addresses are
 refused so this cannot be aimed at internal services. An OpenPGP signature is checked for
 structure only - it is never verified cryptographically.</footer>
</body></html>"""

FORM_TPL = """
<form method="post" action="{{ url_for('do_check') }}" class="bar">
 <input type="text" name="domain" value="{{ domain or '' }}"
  placeholder="example.com" autofocus>
 <label class="chk"><input type="checkbox" name="check_http" value="1" checked>
  also test plain HTTP</label>
 <button class="btn primary" type="submit">Check</button>
</form>"""

HOME_TPL = """{% extends 'base.html' %}{% block body %}
<h1>Check a domain</h1>
<div class="sub">Fetches /.well-known/security.txt and validates it against RFC 9116,
 clause by clause.</div>
""" + FORM_TPL + """
{% if not check %}
<div class="empty"><b>Enter a domain above</b>
 It will be fetched over HTTPS at both the required path and the legacy one, and every
 field checked against the specification.
 <div class="mono" style="margin-top:12px;color:var(--tx-dim)">
  from the terminal: python3 sectxt.py check example.com</div>
</div>
{% else %}
<div class="grid">
 <div class="card"><div class="l">Grade</div>
  <div class="n" style="color:{{ check.grade_colour }}">{{ check.grade }}</div>
  <div class="s">{{ check.grade_label }}</div></div>
 <div class="card"><div class="l">Score</div>
  <div class="n">{{ check.score if check.score is not none else '-' }}</div>
  <div class="s">out of 100</div></div>
 <div class="card"><div class="l">Found</div>
  <div class="n" style="font-size:15px">{{ 'yes' if check.found else
   ('blocked' if check.blocked else 'no') }}</div>
  <div class="s">{{ check.status or '' }}</div></div>
 <div class="card"><div class="l">Contacts</div><div class="n">{{ check.contacts }}</div></div>
 <div class="card"><div class="l">Signed</div>
  <div class="n" style="font-size:15px">{{ 'yes' if check.signed else 'no' }}</div></div>
{% for s in severities %}{% if check[s] %}
 <div class="card"><div class="l">{{ s }}</div>
  <div class="n" style="color:{{ sev[s] }}">{{ check[s] }}</div></div>
{% endif %}{% endfor %}
</div>
{% if check.blocked %}
<div class="banner warn"><b>Could not be checked.</b> A bot-protection layer answered
 instead of the server, so this check never saw whether a security.txt exists. Nothing here
 should be read as a statement about the domain - open the URL in a browser for the real
 answer.</div>
{% endif %}
<div class="charts">{{ gauge|safe }}{{ checklist|safe }}{{ pie|safe }}</div>
{% if history|length > 1 %}<div class="charts">{{ hist|safe }}</div>{% endif %}
{% if fields %}
<h2>Fields as published</h2>
<table><tr><th>Line</th><th>Field</th><th>Value</th></tr>
{% for f in fields %}<tr><td class="num">{{ f.line }}</td>
 <td class="mono">{{ f.name }}</td><td class="mono">{{ f.value }}</td></tr>{% endfor %}
</table>
{% endif %}
<h2>Findings ({{ findings|length }})</h2>
{% if findings %}
<table><tr><th>Severity</th><th>Detail</th></tr>
{% for f in findings %}
<tr><td><span class="pill" style="background:{{ sev[f.severity] }}">
 {{ f.severity|upper }}</span></td>
 <td><b>{{ f.title }}</b><div class="desc">{{ f.description }}</div>
  {% if f.evidence %}<pre>{{ f.evidence }}</pre>{% endif %}
  {% if f.advice %}<div class="means"><b>What to do:</b> {{ f.advice }}</div>{% endif %}
  {% if f.rfc %}<div class="sub2">{{ f.rfc }}</div>{% endif %}</td></tr>
{% endfor %}</table>
{% else %}<div class="empty">No findings.</div>{% endif %}
<div class="bar" style="margin-top:16px">
 <a class="btn" href="{{ url_for('export', fmt='html') }}?check={{ check.id }}">
  Export HTML</a>
 <a class="btn" href="{{ url_for('export', fmt='json') }}?check={{ check.id }}">JSON</a>
 <a class="btn" href="{{ url_for('export', fmt='csv') }}?check={{ check.id }}">CSV</a>
</div>
{% if check.body %}<h2>The file as published</h2><pre>{{ check.body }}</pre>{% endif %}
{% endif %}
{% endblock %}"""

HISTORY_TPL = """{% extends 'base.html' %}{% block body %}
<h1>History</h1><div class="sub">{{ rows|length }} check(s) stored locally.</div>
<div class="bar"><form method="get" style="display:flex;gap:8px;flex-wrap:wrap">
 <input type="text" name="qq" value="{{ f_q }}" placeholder="filter by domain">
 <button class="btn" type="submit">Filter</button>
 <a class="btn" href="{{ url_for('page_history') }}">Reset</a>
</form></div>
{% if rows %}
<table><tr><th>#</th><th>When</th><th>Domain</th><th>Grade</th><th>Score</th>
 <th>Found</th><th>Contacts</th><th>Expires</th><th></th></tr>
{% for r in rows %}<tr>
 <td class="mono">#{{ r.id }}</td>
 <td class="mono">{{ r.ts[:19].replace('T',' ') }}</td>
 <td class="mono">{{ r.domain }}</td>
 <td><span class="grade" style="background:{{ gradecol(r.score) }}">{{ r.grade }}</span></td>
 <td class="num">{{ r.score if r.score is not none else '-' }}</td>
 <td class="mono">{{ 'yes' if r.found else ('blocked' if r.blocked else 'no') }}</td>
 <td class="num">{{ r.contacts }}</td>
 <td class="mono">{{ (r.expires or '-')[:10] }}</td>
 <td><a class="btn" href="{{ url_for('page_home') }}?check={{ r.id }}">view</a></td>
</tr>{% endfor %}</table>
{% else %}<div class="empty"><b>Nothing checked yet</b></div>{% endif %}
{% endblock %}"""

LEARN_TPL = """{% extends 'base.html' %}{% block body %}
<h1>What security.txt is, and what it is not</h1>
<div class="banner"><b>The problem it solves.</b> A researcher finds a flaw in your site at
 two in the morning. Who do they tell? Without an answer they guess: an abuse@ address that
 bounces, a support form routed to someone who thinks it is spam, a public tweet. RFC 9116
 puts the answer in one predictable place.</div>
<h2>The two required fields</h2>
<div class="desc"><b>Contact</b> - where to send a report. At least one, and it should be a
 URI: <span class="mono">mailto:security@example.com</span>,
 <span class="mono">tel:+1-201-555-0123</span>, or an https: link to a form.<br><br>
 <b>Expires</b> - when the file stops being authoritative, as an RFC 3339 timestamp. Exactly
 one. It exists so a researcher can tell a current file from one abandoned three years ago,
 and so that somebody is forced to review the contacts periodically. Keep it under a
 year.</div>
<h2>The optional ones worth having</h2>
<div class="desc"><b>Policy</b> tells a researcher what you promise and what you ask of them -
 the single most useful addition after the required two. <b>Canonical</b> states where the
 file officially lives, so a researcher can tell your file from a copy someone else
 published. <b>Encryption</b> links to a key. <b>Acknowledgments</b> credits people who have
 reported issues - note the US spelling, without an 'e' before the 'm'; the misspelling is
 the most common error in real files. <b>Preferred-Languages</b>, <b>Hiring</b> and
 <b>CSAF</b> round out the set.</div>
<h2>Where it goes</h2>
<div class="desc">At <span class="mono">/.well-known/security.txt</span>, over HTTPS, served
 as <span class="mono">text/plain; charset=utf-8</span>. The top-level
 <span class="mono">/security.txt</span> is tolerated for compatibility but the RFC says the
 well-known path is where it MUST be.</div>
<h2>What a clean result does not mean</h2>
<div class="banner warn"><b>A perfect file does not mean anyone reads the inbox.</b>
 This tool checks a text file. It cannot tell you whether the address accepts mail, whether a
 human triages it, or whether a report is ever answered. A flawless file in front of an
 unmonitored mailbox is arguably worse than no file at all, because it convinces a researcher
 they have done their part. Send a test report to your own address occasionally.</div>
<h2>And no file is not a vulnerability</h2>
<div class="desc">A domain without a security.txt is not insecure and is not doing anything
 wrong. RFC 9116 is a recommendation, adoption is voluntary, and many well-run organisations
 publish contact details elsewhere. Reporting its absence as a finding - as some automated
 scanners do - misrepresents what the specification says.</div>
<h2>On signatures</h2>
<div class="desc">The file may be clearsigned with OpenPGP so a researcher can confirm the
 contacts were not tampered with. This tool checks only that the signature block is
 structurally complete; it does <b>not</b> verify the signature cryptographically, so a file
 marked signed here is not proven authentic. Use <span class="mono">gpg --verify</span> for
 that.</div>
{% endblock %}"""

TEMPLATE_TPL = """{% extends 'base.html' %}{% block body %}
<h1>A starting template</h1>
<div class="sub">Fill in the values, save it at /.well-known/security.txt, and serve it as
 text/plain; charset=utf-8 over HTTPS.</div>
<pre>{{ template }}</pre>
<div class="banner"><b>Two things people get wrong.</b>
 <ul>
  <li><b>Expires</b> is required and is a real date - not a duration. Set a calendar reminder
   for a month before it, because the usual failure is nobody noticing it lapsed.</li>
  <li><b>Acknowledgments</b> has no 'e' before the 'm'. The misspelling is the most common
   error in real files, and conforming parsers ignore the field entirely.</li>
 </ul></div>
<div class="banner warn"><b>Before you publish it.</b> Send a test report to the address you
 just listed and confirm a human sees it. A contact that bounces is worse than no file,
 because the researcher believes they have told you.</div>
{% endblock %}"""

TEMPLATES = {"base.html": BASE_TPL, "home.html": HOME_TPL, "history.html": HISTORY_TPL,
             "learn.html": LEARN_TPL, "template.html": TEMPLATE_TPL}


def starter_template() -> str:
    year = datetime.now(timezone.utc).year + 1
    return textwrap.dedent(f"""\
        # security.txt - RFC 9116
        # Save at: /.well-known/security.txt
        # Serve as: text/plain; charset=utf-8, over HTTPS

        # REQUIRED. Where to send a report. List them in the order you prefer.
        Contact: mailto:security@example.com
        Contact: https://example.com/security/report

        # REQUIRED. Exactly one, RFC 3339, under a year away.
        Expires: {year}-01-31T23:59:59Z

        # Recommended: what you promise, and what you ask of researchers.
        Policy: https://example.com/security/policy

        # Where this file officially lives, so a copy can be told from the original.
        Canonical: https://example.com/.well-known/security.txt

        # A key for encrypting reports. A LINK to the key, never the key itself.
        Encryption: https://example.com/pgp-key.txt

        # Note the spelling: no 'e' before the 'm'.
        Acknowledgments: https://example.com/security/thanks

        # Languages you can read reports in.
        Preferred-Languages: en

        Hiring: https://example.com/careers
        """)


try:
    from flask import (Flask, Response, jsonify, redirect, render_template, request, url_for)
    from jinja2 import ChoiceLoader, DictLoader
    HAVE_FLASK = True
except Exception:  # pragma: no cover
    HAVE_FLASK = False


def build_app():
    if not HAVE_FLASK:
        raise SystemExit("Flask is not installed. Install it with:  pip install flask\n"
                         "(The CLI works without Flask; only the web app needs it.)")
    app = Flask(__name__)
    app.jinja_loader = ChoiceLoader([DictLoader(TEMPLATES), app.jinja_loader])

    def gradecol(score):
        return grade_for(score)[2] if score is not None else "#8b8f9b"

    def ctx(nav, **kw):
        base = {"nav": nav, "page": nav.capitalize(), "sev": SEV_COLOR,
                "severities": SEVERITIES, "ts_pretty": ts_pretty, "gradecol": gradecol,
                "error": request.args.get("error"), "check": None, "domain": None}
        base.update(kw)
        return base

    @app.route("/")
    def page_home():
        conn = connect()
        try:
            init_db(conn)
            try:
                cid = int(request.args.get("check", "") or 0)
            except ValueError:
                cid = 0
            chk = check_summary(cid, conn) if cid else None
            if not chk:
                return render_template("home.html", **ctx("home"))
            p = report_payload(chk["id"], conn)
            parsed = {"fields": {}}
            for f in p["fields"]:
                parsed["fields"].setdefault(f["name"].lower(), []).append(f)
            counts = {s: chk[s] or 0 for s in SEVERITIES}
            return render_template("home.html", **ctx(
                "home", check=chk, domain=chk["domain"], fields=p["fields"],
                findings=p["findings"], history=p["history"],
                gauge=svg_gauge(chk["score"], chk["grade"], chk["grade_label"],
                                chk["grade_colour"]),
                checklist=svg_checklist(parsed),
                pie=svg_pie([(s, counts[s], SEV_COLOR[s]) for s in SEVERITIES]),
                hist=svg_history(p["history"])))
        finally:
            conn.close()

    @app.post("/check")
    def do_check():
        import urllib.parse as up
        domain = (request.form.get("domain") or "").strip()
        check_http = request.form.get("check_http") == "1"
        if not domain:
            return redirect(url_for("page_home") + "?error=" + up.quote("no domain given"))
        try:
            res = check_domain(domain, check_http=check_http)
            cid = save_check(res, note="from the web UI")
        except Exception as e:
            log_event("ERROR", "check", str(e))
            return redirect(url_for("page_home") + "?error=" + up.quote(str(e)))
        return redirect(url_for("page_home") + f"?check={cid}")

    @app.route("/history")
    def page_history():
        conn = connect()
        try:
            init_db(conn)
            term = request.args.get("qq", "").strip()
            sql, args = "SELECT * FROM checks WHERE 1=1", []
            if term:
                sql += " AND domain LIKE ?"
                args.append(f"%{term}%")
            sql += " ORDER BY id DESC LIMIT 200"
            return render_template("history.html", **ctx(
                "history", rows=q(sql, tuple(args), conn), f_q=term))
        finally:
            conn.close()

    @app.route("/learn")
    def page_learn():
        return render_template("learn.html", **ctx("learn"))

    @app.route("/template")
    def page_template():
        return render_template("template.html", **ctx("template",
                                                      template=starter_template()))

    @app.route("/export/<fmt>")
    def export(fmt):
        try:
            cid = int(request.args.get("check", "") or 0) or None
        except ValueError:
            cid = None
        fmt = fmt.lower()
        stamp = datetime.now(timezone.utc).strftime("%Y%m%d-%H%M%S")
        if fmt == "json":
            body, mime = export_json(cid), "application/json"
        elif fmt == "csv":
            body, mime = export_csv(cid), "text/csv"
        elif fmt == "html":
            body, mime = export_html(cid), "text/html"
        else:
            return Response("Unsupported format. Use json, csv or html.", 400,
                            mimetype="text/plain")
        log_event("INFO", "export", f"Exported the report as {fmt.upper()}", cid)
        return Response(body, mimetype=mime, headers={
            "Content-Disposition": f'attachment; filename="sectxt-{stamp}.{fmt}"'})

    @app.route("/api/check")
    def api_check():
        domain = (request.args.get("domain") or "").strip()
        if not domain:
            return jsonify({"error": "give ?domain="}), 400
        res = check_domain(domain, check_http=False)
        save_check(res, note="from the API")
        return jsonify({"tool": APP_NAME, "version": VERSION, "specification": "RFC 9116",
                        "not_a_guarantee": NOT_A_GUARANTEE,
                        "signature_not_cryptographically_verified": True,
                        "domain": res["domain"], "found": res["found"],
                        "blocked": res.get("blocked", False), "grade": res["grade"],
                        "score": res["score"], "source_url": res.get("source_url"),
                        "findings": res["findings"]})

    @app.errorhandler(404)
    def nf(_e):
        return Response("404 - page not found. Valid pages: / /history /learn /template",
                        404, mimetype="text/plain")

    return app


def serve(host: str, port: int, debug: bool = False):
    app = build_app()
    init_db()
    log_event("INFO", "web", f"Web app started on http://{host}:{port}")
    print(f"\n  {APP_NAME} v{VERSION} - by {AUTHOR}")
    print(f"  {'-' * 66}")
    print(f"  Web app : http://{'127.0.0.1' if host == '0.0.0.0' else host}:{port}")
    print(f"  Database: {os.path.abspath(db_path())}")
    print(f"  Checks against RFC 9116.")
    if host == "0.0.0.0":
        print("  WARNING : bound to 0.0.0.0 - anyone who reaches this UI can make this\n"
              "            machine fetch arbitrary domains. Use 127.0.0.1.")
    print(f"  {textwrap.fill(DISCLAIMER_SHORT, 66, subsequent_indent='  ')}")
    print(f"  {'-' * 66}\n  Press Ctrl+C to stop.\n")
    app.run(host=host, port=port, debug=debug, use_reloader=False)


# =============================================================================
# SECTION 9 - Command line interface
# =============================================================================

def line(char="-", n=78):
    print(char * n)


def banner():
    print(f"\n{APP_NAME} v{VERSION}  |  {AUTHOR}  |  checks against RFC 9116")
    line()
    print(textwrap.fill(DISCLAIMER_SHORT, 78))
    line()


def _print_findings(rows, limit=None, quiet_info=False):
    shown = [f for f in rows if not (quiet_info and f["severity"] == "info")]
    shown = shown[:limit] if limit else shown
    for f in shown:
        print(f"\n  [{f['severity'].upper():^8}] {f['title']}")
        for l in textwrap.wrap(f["description"], 70):
            print(f"      {l}")
        if f.get("evidence"):
            for l in str(f["evidence"]).splitlines()[:4]:
                for w in textwrap.wrap(l, 70):
                    print(f"      {w}")
        if f.get("advice"):
            for l in textwrap.wrap("what to do: " + f["advice"], 70):
                print(f"      {l}")
        if f.get("rfc"):
            print(f"      ({f['rfc']})")


def cmd_check(a):
    banner()
    domains = [a.domain] + list(a.also or [])
    if a.file:
        try:
            with open(a.file) as fh:
                domains += [l.strip() for l in fh
                            if l.strip() and not l.startswith("#")]
        except OSError as e:
            print(f"Could not read {a.file}: {e}")
            return 1
    domains = [d for d in domains if d]
    results = []
    for i, dom in enumerate(domains):
        if len(domains) > 1:
            print(f"[{i + 1}/{len(domains)}] {dom}")
        res = check_domain(dom, timeout=a.timeout, allow_private=a.allow_private,
                           check_http=not a.no_http)
        cid = save_check(res, note=a.note or "")
        res["id"] = cid
        results.append(res)
        if len(domains) == 1:
            _report_one(res, a)
        else:
            grade = res["grade"]
            print(f"      {grade:<2} {str(res['score']):>6}  "
                  f"{'found' if res['found'] else ('blocked' if res.get('blocked') else 'no file')}"
                  f"  {res.get('source_url') or ''}")
        if len(domains) > 1 and i < len(domains) - 1:
            time.sleep(a.delay)
    if len(domains) > 1:
        line("=")
        print(f"  {len(results)} domain(s) checked")
        for r in sorted(results, key=lambda x: (x["score"] is None, x["score"] or 0)):
            print(f"   {r['grade']:<2} {str(r['score']):>6}  {r['domain']}")
        line("=")
        print(textwrap.fill(
            "  A grade describes the FILE. It says nothing about whether anyone reads the "
            "inbox behind it, and a domain with no file is not insecure - RFC 9116 is a "
            "recommendation.", 78))
        line()
    worst = min((r["score"] for r in results if r["score"] is not None), default=None)
    if a.fail_under is not None and worst is not None and worst < a.fail_under:
        print(f"\n  Exiting non-zero: {worst} is below --fail-under {a.fail_under}")
        return 2
    return 0


def _report_one(res, a):
    print(f"Domain : {res['domain']}")
    if res.get("addresses"):
        print(f"Address: {', '.join(res['addresses'][:4])}")
    if res.get("source_url"):
        print(f"File   : {res['source_url']}  (HTTP {res.get('status')}, "
              f"{fmt_bytes(res.get('size_bytes'))}, {res.get('content_type')})")
    print(f"Time   : {res['elapsed_ms']} ms")
    line("=")
    if res.get("blocked"):
        print("  COULD NOT BE CHECKED - a bot-protection layer answered instead of the")
        print("  server. This is a limit of the check, NOT a finding about the domain.")
    else:
        print(f"  GRADE {res['grade']}   {res['score']}/100   {res['grade_label']}")
    line("=")
    if res.get("parsed"):
        fields = res["parsed"]["fields"]
        print("  RFC 9116 FIELDS")
        for key, (required, _mx, _uri, _desc) in RFC_FIELDS.items():
            rows = fields.get(key, [])
            if rows:
                mark, note = "[ok]", f"{len(rows)} value(s)"
            elif required:
                mark, note = "[XX]", "REQUIRED, missing"
            else:
                mark, note = "[  ]", "not used"
            print(f"   {mark} {key.title():<22} {note}")
        line()
    _print_findings(res["findings"], a.show, quiet_info=a.quiet)
    line()
    if res.get("body") and a.show_file:
        print("  THE FILE AS PUBLISHED")
        for l in res["body"].splitlines()[:40]:
            print(f"   {l}")
        line()
    print(textwrap.fill(
        "  Remember: this grades a text file. It cannot tell you whether the contact "
        "address accepts mail or whether a human reads it. Send a test report to your own "
        "file occasionally.", 78))
    line()


def cmd_template(a):
    body = starter_template()
    if a.out:
        with open(a.out, "w", encoding="utf-8") as fh:
            fh.write(body)
        print(f"Wrote {a.out}")
        print("Save it at /.well-known/security.txt and serve it as "
              "'text/plain; charset=utf-8' over HTTPS.")
        return 0
    print(body)
    return 0


def cmd_validate(a):
    """Check a local file without fetching anything."""
    banner()
    try:
        with open(a.file, encoding="utf-8") as fh:
            text = fh.read()
    except UnicodeDecodeError:
        print(f"{a.file} is not valid UTF-8. RFC 9116 requires UTF-8.")
        return 1
    except OSError as e:
        print(f"Could not read {a.file}: {e}")
        return 1
    print(f"Validating {a.file} ({len(text)} bytes) - nothing was fetched.\n")
    parsed = parse_security_txt(text)
    findings = check_fields(parsed, a.canonical or "")
    score = conformance_score(findings, True)
    grade, label, _c = grade_for(score)
    line("=")
    print(f"  GRADE {grade}   {score}/100   {label}")
    line("=")
    print("  Note: this checks the CONTENT only. Where the file is served from, over what")
    print("  transport, and with what media type are just as much a part of RFC 9116 - use")
    print("  'check <domain>' once it is published.")
    line()
    _print_findings(findings, a.show, quiet_info=a.quiet)
    line()
    return 0


def cmd_history(a):
    sql, args = "SELECT * FROM checks WHERE 1=1", []
    if a.domain:
        sql += " AND domain LIKE ?"
        args.append(f"%{a.domain}%")
    sql += " ORDER BY id DESC LIMIT ?"
    args.append(a.limit)
    rows = q(sql, tuple(args))
    if not rows:
        print("Nothing checked yet.")
        return 0
    print(f"{'ID':>4}  {'WHEN (UTC)':<20} {'GRADE':<6} {'SCORE':>6}  {'FOUND':<8} DOMAIN")
    line()
    for r in rows:
        found = "yes" if r["found"] else ("blocked" if r["blocked"] else "no")
        print(f"{r['id']:>4}  {r['ts'][:19].replace('T', ' '):<20} {r['grade']:<6} "
              f"{str(r['score']):>6}  {found:<8} {r['domain']}")
    return 0


def cmd_explain(_a):
    banner()
    print(textwrap.dedent("""\
        WHY security.txt EXISTS

          A researcher finds a flaw in your site at two in the morning. Who do
          they tell? Without an answer they guess: an abuse@ address that
          bounces, a support form routed to someone who thinks it is spam, a
          public tweet. Reports get lost, and the ones that arrive come slowly.

          RFC 9116 puts the answer in one predictable place:
          /.well-known/security.txt, over HTTPS, as text/plain.

        THE TWO REQUIRED FIELDS

          Contact   Where to send a report. At least one, as a URI:
                    mailto:security@example.com, tel:+1-201-555-0123, or an
                    https: link to a form.

          Expires   When the file stops being authoritative, as an RFC 3339
                    timestamp. Exactly one. It exists so a researcher can tell a
                    current file from one abandoned three years ago - and so that
                    somebody is forced to review the contacts periodically. Keep
                    it under a year; an expiry a decade out never prompts anyone
                    to check whether the address still works.

        THE ONES WORTH ADDING

          Policy    What you promise, and what you ask of researchers. The most
                    useful addition after the required two.
          Canonical Where this file officially lives, so your file can be told
                    apart from a copy someone else published about you.
          Encryption A LINK to a key - never the key inline.
          Acknowledgments  Credit for people who have reported issues. Note the
                    spelling: no 'e' before the 'm'. The misspelling is the most
                    common error in real files, and conforming parsers ignore the
                    field entirely.

        WHAT A GOOD GRADE DOES NOT MEAN

          This tool checks a TEXT FILE. It cannot tell you whether the address
          accepts mail, whether a human triages it, or whether a report is ever
          answered. A flawless file in front of an unmonitored mailbox is
          arguably worse than no file at all, because it convinces a researcher
          they have done their part and can stop trying.

          Send a test report to your own published address occasionally. It is
          the only check that matters and the only one no tool can do for you.

        AND NO FILE IS NOT A VULNERABILITY

          A domain without a security.txt is not insecure and is not doing
          anything wrong. RFC 9116 is a recommendation, adoption is voluntary,
          and plenty of well-run organisations publish contact details elsewhere.
          Automated scanners that report its absence as a finding misrepresent
          what the specification actually says.

        ON SIGNATURES

          The file may be clearsigned with OpenPGP. This tool checks only that
          the signature block is structurally complete - it does NOT verify the
          signature cryptographically, so a file reported as signed here is not
          proven authentic. Use 'gpg --verify' for that.

        ON BEING BLOCKED

          If a bot-protection layer answers instead of the server, this tool says
          "could not be checked" and refuses to grade. Being blocked is not
          evidence that a file is absent, and reporting it as such would be a
          plain lie about someone else's site.
        """))
    line()


def cmd_export(a):
    cid = a.check or latest_check_id()
    if not cid:
        print("Nothing to export yet.")
        return 1
    fmt = a.format.lower()
    body = {"json": export_json, "csv": export_csv, "html": export_html}[fmt](cid)
    out = a.out or f"sectxt-{datetime.now(timezone.utc).strftime('%Y%m%d-%H%M%S')}.{fmt}"
    with open(out, "w", encoding="utf-8") as fh:
        fh.write(body)
    log_event("INFO", "export", f"Exported check #{cid} as {fmt.upper()} to {out}", cid)
    print(f"Wrote {out} ({len(body):,} bytes)")
    return 0


def cmd_logs(a):
    sql, args = "SELECT * FROM audit_log WHERE 1=1", []
    if a.level:
        sql += " AND level=?"
        args.append(a.level.upper())
    sql += " ORDER BY id DESC LIMIT ?"
    args.append(a.limit)
    rows = q(sql, tuple(args))
    if not rows:
        print("No log entries.")
        return 0
    for e in reversed(rows):
        print(f"{e['ts'][:19].replace('T', ' ')}  {e['level']:<5} {e['source']:<8} "
              f"{e['message']}")
    return 0


def cmd_purge(a):
    conn = connect()
    try:
        if a.all:
            for t in ("findings", "fields", "checks", "audit_log"):
                conn.execute(f"DELETE FROM {t}")
            conn.commit()
            print("All checks, findings and logs deleted.")
            return 0
        rows = q("SELECT id FROM checks ORDER BY id DESC", (), conn)
        drop = [r["id"] for r in rows[a.keep:]]
        for cid in drop:
            conn.execute("DELETE FROM findings WHERE check_id=?", (cid,))
            conn.execute("DELETE FROM fields WHERE check_id=?", (cid,))
            conn.execute("DELETE FROM checks WHERE id=?", (cid,))
        conn.commit()
        print(f"Purged {len(drop)} check(s); kept the newest {a.keep}.")
        return 0
    finally:
        conn.close()


def cmd_serve(a):
    serve(a.host, a.port, a.debug)


def cmd_version(_a):
    banner()
    print(f"  Python     : {platform.python_version()} ({sys.platform})")
    print(f"  Flask      : {'yes' if HAVE_FLASK else 'NOT INSTALLED - web app unavailable'}")
    print(f"  Specification: RFC 9116")
    print(f"  Fields known : {len(RFC_FIELDS)}")
    print(f"  User agent : {USER_AGENT}")
    print(f"  Database   : {os.path.abspath(db_path())}")
    print(f"  GitHub     : {GITHUB}")
    line()
    print(DISCLAIMER_LONG)
    line()


# =============================================================================
# SECTION 10 - Self test
#   The RFC logic is checked against fixture files, so it passes or fails without
#   depending on any domain being reachable. Live checks run only when the
#   network is available, and are skipped honestly when it is not.
# =============================================================================

GOOD_FILE = """\
Contact: mailto:security@example.com
Contact: https://example.com/report
Expires: {expires}
Policy: https://example.com/policy
Canonical: https://example.com/.well-known/security.txt
Encryption: https://example.com/pgp-key.txt
Acknowledgments: https://example.com/thanks
Preferred-Languages: en, fr
Hiring: https://example.com/jobs
"""

SIGNED_FILE = """\
-----BEGIN PGP SIGNED MESSAGE-----
Hash: SHA512

Contact: mailto:security@example.com
Expires: {expires}
-----BEGIN PGP SIGNATURE-----

iQIzBAEBCgAdFiEEexampleexampleexample
-----END PGP SIGNATURE-----
"""


def cmd_selftest(_a=None) -> int:
    import tempfile
    passed, failed, skipped = [], [], []

    def check(name, cond, detail=""):
        (passed if cond else failed).append(name)
        print(f"  [{'PASS' if cond else 'FAIL'}] {name}"
              f"{'  <- ' + str(detail) if detail and not cond else ''}")

    def skip(name, why):
        skipped.append(name)
        print(f"  [SKIP] {name}  ({why})")

    banner()
    print("SELF TEST - RFC logic against fixtures; live checks only if the network "
          "allows.\n")
    original = db_path()
    tmp = tempfile.mkdtemp(prefix="sectxt-selftest-")
    set_db_path(os.path.join(tmp, "selftest.db"))
    future = (datetime.now(timezone.utc) + timedelta(days=180)).strftime(
        "%Y-%m-%dT%H:%M:%SZ")
    past = (datetime.now(timezone.utc) - timedelta(days=30)).strftime(
        "%Y-%m-%dT%H:%M:%SZ")
    try:
        print(" Timestamps")
        for v, ok_ in (("2027-01-31T23:59:59Z", True), ("2027-01-31T23:59:59z", True),
                       ("2027-01-31T23:59:59+05:30", True), ("not-a-date", False)):
            dt, _c = parse_rfc3339(v)
            check(f"'{v}' parses" if ok_ else f"'{v}' is rejected", (dt is not None) == ok_)
        _dt, complaint = parse_rfc3339("2027-01-31T23:59:59")
        check("a timestamp with no offset is accepted but complained about",
              _dt is not None and "offset" in complaint, complaint)
        check("lowercase 'z' is NOT reported as an error (ABNF is case-insensitive)",
              parse_rfc3339("2027-01-31T23:59:59z")[1] == "")

        print("\n Contact classification")
        for v, kind, is_uri in (("mailto:a@b.com", "email", True),
                                ("https://x.com/f", "web form or page", True),
                                ("tel:+15551234", "telephone", True),
                                ("a@b.com", "email", False),
                                ("+1 555 1234", "telephone", False)):
            c = classify_contact(v)
            check(f"'{v}' is a {kind}" + ("" if is_uri else " but not a URI"),
                  c["kind"] == kind and c["is_uri"] == is_uri, c)
        check("a bare address is told how to fix it",
              "mailto:" in classify_contact("a@b.com")["note"])
        check("a plain-HTTP contact is flagged as insecure",
              classify_contact("http://x.com/f")["secure"] is False)

        print("\n Parsing")
        p = parse_security_txt(GOOD_FILE.format(expires=future))
        check("every field is parsed", len(p["fields"]) == 8, list(p["fields"]))
        check("repeated fields are kept as a list", len(p["fields"]["contact"]) == 2)
        check("line numbers are recorded",
              all(r["line"] > 0 for rows in p["fields"].values() for r in rows))
        check("a clean file has no malformed lines", not p["malformed"])
        p2 = parse_security_txt("# a comment\nContact: mailto:a@b.c\nnonsense line\n"
                                "Empty:\nExpires: " + future + "\n")
        check("comments are separated from fields", len(p2["comments"]) == 1)
        check("a line with no colon is reported as malformed",
              len(p2["malformed"]) == 1 and "no colon" in p2["malformed"][0]["why"])
        check("a field with no value is reported",
              len(p2["empty_values"]) == 1 and p2["empty_values"][0]["field"] == "Empty")
        pb = parse_security_txt("\ufeffContact: mailto:a@b.c\n")
        check("a byte order mark is detected and stripped",
              pb["byte_order_mark"] and "contact" in pb["fields"])
        ps = parse_security_txt(SIGNED_FILE.format(expires=future))
        check("a clearsigned file is recognised", ps["signed"] and ps["signature_intact"])
        check("fields inside a signed file are still parsed",
              "contact" in ps["fields"] and "expires" in ps["fields"], list(ps["fields"]))
        broken = SIGNED_FILE.format(expires=future).replace(PGP_SIG_END, "")
        pbk = parse_security_txt(broken)
        check("a truncated signature block is detected",
              pbk["signed"] and not pbk["signature_intact"])

        print("\n Required fields")
        f = check_fields(parse_security_txt(f"Expires: {future}\n"), "")
        check("a missing Contact is CRITICAL",
              any(x["severity"] == "critical" and "Contact" in x["title"] for x in f),
              [x["title"] for x in f])
        f = check_fields(parse_security_txt("Contact: mailto:a@b.c\n"), "")
        check("a missing Expires is HIGH",
              any(x["severity"] == "high" and "Expires" in x["title"] for x in f),
              [x["title"] for x in f])
        f = check_fields(parse_security_txt(
            f"Contact: mailto:a@b.c\nExpires: {past}\n"), "")
        check("an expired file is CRITICAL",
              any(x["severity"] == "critical" and "expired" in x["title"] for x in f),
              [x["title"] for x in f])
        f = check_fields(parse_security_txt(
            f"Contact: mailto:a@b.c\nExpires: {future}\nExpires: {future}\n"), "")
        check("two Expires fields are reported",
              any("2 Expires fields" in x["title"] for x in f), [x["title"] for x in f])
        far = (datetime.now(timezone.utc) + timedelta(days=3650)).strftime(
            "%Y-%m-%dT%H:%M:%SZ")
        f = check_fields(parse_security_txt(f"Contact: mailto:a@b.c\nExpires: {far}\n"), "")
        check("an expiry a decade out is flagged",
              any("Expires" in x["title"] and "from now" in x["title"] for x in f),
              [x["title"] for x in f])
        check("and it explains WHY a long expiry is bad",
              any("force a periodic review" in x["advice"] for x in f))
        soon = (datetime.now(timezone.utc) + timedelta(days=10)).strftime(
            "%Y-%m-%dT%H:%M:%SZ")
        f = check_fields(parse_security_txt(f"Contact: mailto:a@b.c\nExpires: {soon}\n"), "")
        check("an expiry within a month is flagged",
              any("Expires in" in x["title"] for x in f), [x["title"] for x in f])

        print("\n A good file stays clean")
        good = parse_security_txt(GOOD_FILE.format(expires=future))
        f = check_fields(good, "https://example.com/.well-known/security.txt")
        bad = [x for x in f if x["severity"] in ("critical", "high", "medium")]
        check("a conformant file produces no critical, high or medium findings",
              not bad, [x["title"] for x in bad])
        check("its score is a clean 100", conformance_score(f, True) == 100.0,
              conformance_score(f, True))
        check("the grade is A", grade_for(conformance_score(f, True))[0] == "A")

        print("\n The details people get wrong")
        f = check_fields(parse_security_txt(
            f"Contact: mailto:a@b.c\nExpires: {future}\n"
            f"Acknowledgements: https://x.com/t\n"), "")
        check("the 'Acknowledgements' misspelling is caught specifically",
              any("misspelling" in x["title"] for x in f), [x["title"] for x in f])
        f = check_fields(parse_security_txt(
            f"Contact: a@b.c\nExpires: {future}\n"), "")
        check("a bare email Contact is flagged as not a URI",
              any("not a URI" in x["title"] for x in f), [x["title"] for x in f])
        f = check_fields(parse_security_txt(
            f"Contact: mailto:a@b.c\nExpires: {future}\nPolicy: /policy\n"), "")
        check("a relative URI in Policy is flagged",
              any("Policy is not a URI" in x["title"] for x in f), [x["title"] for x in f])
        f = check_fields(parse_security_txt(
            f"Contact: mailto:a@b.c\nExpires: {future}\n"
            f"Encryption: -----BEGIN PGP PUBLIC KEY BLOCK-----\n"), "")
        check("an inline key in Encryption is flagged",
              any("key instead of a link" in x["title"] for x in f), [x["title"] for x in f])
        f = check_fields(parse_security_txt(
            f"Contact: mailto:a@b.c\nExpires: {future}\n"
            f"Preferred-Languages: English, French\n"), "")
        check("language names instead of tags are flagged",
              any("invalid tags" in x["title"] for x in f), [x["title"] for x in f])
        f = check_fields(parse_security_txt(
            f"Contact: mailto:a@b.c\nExpires: {future}\n"
            f"Preferred-Languages: en\nPreferred-Languages: fr\n"), "")
        check("two Preferred-Languages fields are flagged",
              any("Preferred-Languages' fields" in x["title"] for x in f),
              [x["title"] for x in f])
        f = check_fields(parse_security_txt(
            f"Contact: mailto:a@b.c\nExpires: {future}\n"
            f"Canonical: https://elsewhere.example/.well-known/security.txt\n"),
            "https://example.com/.well-known/security.txt")
        check("a Canonical that does not match where the file was found is flagged",
              any("Canonical does not match" in x["title"] for x in f),
              [x["title"] for x in f])
        f = check_fields(parse_security_txt(
            f"Contact: mailto:a@gmail.com\nExpires: {future}\n"), "")
        check("a consumer mail provider is noted",
              any("personal mail provider" in x["title"] for x in f), [x["title"] for x in f])
        f = check_fields(parse_security_txt(
            f"Contact: mailto:security@example.com\nExpires: {future}\n"), "")
        check("a role address is NOT complained about",
              not any("role-based" in x["title"] for x in f), [x["title"] for x in f])

        print("\n The honest limits")
        f = check_fields(parse_security_txt(SIGNED_FILE.format(expires=future)), "")
        sig = [x for x in f if x["category"] == "Signature"]
        check("a signature is reported as structurally checked ONLY",
              sig and "NOT verify" in sig[0]["advice"], sig)
        f = check_fields(parse_security_txt(
            f"Contact: mailto:a@b.c\nExpires: {future}\n"), "")
        contact_note = [x for x in f if "contact method" in x["title"]]
        check("the contact summary warns that a monitored inbox cannot be checked",
              contact_note and "cannot tell you" in contact_note[0]["advice"],
              contact_note)

        print("\n Detecting what is NOT a security.txt")
        html = b"<!DOCTYPE html><html><head><title>404</title></head><body>x</body></html>"
        is_html, why = looks_like_html(html, "text/plain")
        check("an HTML body is detected even when the header claims text/plain",
              is_html and "HTML" in why, why)
        check("a real file is not mistaken for HTML",
              not looks_like_html(b"Contact: mailto:a@b.c\n", "text/plain")[0])
        cf = b"<!DOCTYPE html><html><title>Just a moment...</title>cf_chl_opt</html>"
        is_ch, cwhy = looks_like_challenge(cf, 200)
        check("a bot-protection challenge is recognised", is_ch and "challenge" in cwhy)
        check("a 403 counts as blocked, not absent", looks_like_challenge(b"x", 403)[0])
        check("a normal 200 is not called a challenge",
              not looks_like_challenge(b"Contact: mailto:a@b.c", 200)[0])

        print("\n The guard against being aimed inwards")
        for host, allowed in (("localhost", False), ("127.0.0.1", False),
                              ("169.254.169.254", False), ("10.0.0.1", False),
                              ("192.168.1.1", False)):
            ok, why, _a = resolve_and_guard(host)
            check(f"{host} is refused", ok == allowed, why)
        ok, _w, _a = resolve_and_guard("127.0.0.1", allow_private=True)
        check("--allow-private lets a deliberate internal check through", ok)
        r = fetch_once("ftp://example.com/x", 2.0, False)
        check("a non-HTTP scheme is refused", "unsupported scheme" in (r["error"] or ""))

        print("\n Grading")
        check("a domain with no file scores zero", conformance_score([], False) == 0.0)
        crit = [F("x", "y", "critical", "z")]
        check("one critical finding drops the grade below C",
              grade_for(conformance_score(crit, True))[0] in ("D", "F"),
              conformance_score(crit, True))
        check("info findings never reduce the score",
              conformance_score([F("x", "y", "info", "z")] * 20, True) == 100.0)
        check("the score never goes below zero",
              conformance_score([F("x", "y", "critical", "z")] * 10, True) == 0.0)

        print("\n Local validation, with nothing fetched")
        fixture = os.path.join(tmp, "security.txt")
        with open(fixture, "w") as fh:
            fh.write(GOOD_FILE.format(expires=future))
        ns = argparse.Namespace(file=fixture, canonical="", show=None, quiet=True)
        buf, old = io.StringIO(), sys.stdout
        sys.stdout = buf
        try:
            rc = cmd_validate(ns)
        finally:
            sys.stdout = old
        out = buf.getvalue()
        check("validating a local file works offline", rc == 0 and "GRADE A" in out,
              out[:120])
        check("it says plainly that nothing was fetched", "nothing was fetched" in out)
        check("it warns that transport and location are not covered",
              "CONTENT only" in out)

        print("\n The starter template is itself conformant")
        tpl = starter_template()
        tp = parse_security_txt(tpl)
        tf = check_fields(tp, "https://example.com/.well-known/security.txt")
        tbad = [x for x in tf if x["severity"] in ("critical", "high", "medium")]
        check("the template produces no serious findings", not tbad,
              [x["title"] for x in tbad])
        check("the template includes both required fields",
              "contact" in tp["fields"] and "expires" in tp["fields"])
        check("the template spells Acknowledgments correctly",
              "acknowledgments" in tp["fields"] and "acknowledgements" not in tp["fields"])

        print("\n Persistence")
        init_db()
        fake = {"domain": "example.com", "checked_at": now_iso(), "found": True,
                "blocked": False, "source_url": "https://example.com/.well-known/security.txt",
                "status": 200, "content_type": "text/plain; charset=utf-8",
                "size_bytes": len(GOOD_FILE), "encoding": "utf-8",
                "parsed": good, "body": GOOD_FILE.format(expires=future),
                "findings": f, "fetches": {}, "addresses": ["93.184.216.34"],
                "elapsed_ms": 42, "error": None,
                "counts": {s: sum(1 for x in f if x["severity"] == s) for s in SEVERITIES}}
        fake["score"] = conformance_score(f, True)
        fake["grade"], fake["grade_label"], fake["grade_colour"] = grade_for(fake["score"])
        cid = save_check(fake, note="selftest")
        chk = check_summary(cid)
        check("a check is stored and read back", chk and chk["domain"] == "example.com")
        check("the fields are stored individually",
              q1("SELECT COUNT(*) c FROM fields WHERE check_id=?", (cid,))["c"]
              == sum(len(v) for v in good["fields"].values()))
        check("findings are stored",
              q1("SELECT COUNT(*) c FROM findings WHERE check_id=?", (cid,))["c"] == len(f))
        check("Expires is extracted into its own column for querying",
              chk["expires"] is not None and chk["expires_days"] > 0)
        check("the contact count is stored", chk["contacts"] == 2, chk["contacts"])

        print("\n Charts")
        check("the gauge renders a grade", "A" in svg_gauge(100.0, "A", "x", "#30a46c"))
        check("the gauge REFUSES to grade an unreadable domain",
              "dishonest" in svg_gauge(None, "?", "x", "#888"))
        check("the checklist draws a row per defined field",
              svg_checklist(good).count("<rect") == len(RFC_FIELDS))
        check("a missing required field is drawn in red",
              "#e5484d" in svg_checklist(parse_security_txt("Policy: https://x.com\n")))
        check("pie renders slices",
              svg_pie([("a", 2, "#fff"), ("b", 1, "#000")]).count("<path") == 2)
        check("the history chart needs two graded checks and says so",
              "needs at least two" in svg_history([{"score": 100, "ts": "x"}]))
        check("the history chart draws with enough points",
              "<path" in svg_history([{"score": 100, "ts": "a"}, {"score": 80, "ts": "b"}]))
        check("every chart guards against empty input",
              all("nothing to show" in x or "needs at least" in x or "not graded" in x
                  for x in (svg_pie([]), svg_history([]), svg_gauge(None, "?", "", "#888"))))

        print("\n Exports")
        j = json.loads(export_json(cid))
        check("JSON export names the specification", j["specification"] == "RFC 9116")
        check("JSON export states what a pass does not mean",
              "does not mean anyone reads the inbox" in j["what_a_pass_does_not_mean"])
        check("JSON export lists the limitations", len(j["limitations"]) >= 5)
        check("JSON export says the signature is not cryptographically verified",
              any("NOT verified cryptographically" in x for x in j["limitations"]))
        check("JSON export says absence is not a vulnerability",
              any("not insecure" in x for x in j["limitations"]))
        c = export_csv(cid)
        check("CSV export has a section per table", c.count("##") >= 3)
        check("CSV export carries the disclaimer",
              any(l.lstrip('"').startswith("#") for l in c.splitlines()[:4]))
        h = export_html(cid)
        check("HTML export is a complete document",
              h.startswith("<!doctype html") and h.rstrip().endswith("</html>"))
        check("HTML export contains charts, the caveat and the author",
              "<svg" in h and "reads the inbox" in h and AUTHOR in h)

        print("\n Web application")
        if not HAVE_FLASK:
            check("Flask installed", False, "pip install flask")
        else:
            app = build_app()
            app.config["TESTING"] = True
            cl = app.test_client()
            for path, must in (("/", "Check a domain"), ("/history", "History"),
                               ("/learn", "what it is not"), ("/template", "template")):
                r = cl.get(path)
                body = r.get_data(as_text=True)
                check(f"page {path} renders",
                      r.status_code == 200 and must.lower() in body.lower(), r.status_code)
            check("every page carries the 'not an organisation' banner",
                  "not an organisation" in cl.get("/").get_data(as_text=True))
            check("the learn page says no file is not a vulnerability",
                  "not a vulnerability" in cl.get("/learn").get_data(as_text=True))
            check("the template page offers a conformant starting point",
                  "Expires:" in cl.get("/template").get_data(as_text=True))
            check("a stored check renders with its findings",
                  cl.get(f"/?check={cid}").status_code == 200
                  and "GRADE" in cl.get(f"/?check={cid}").get_data(as_text=True).upper())
            check("history filters apply", cl.get("/history?qq=example").status_code == 200)
            r = cl.post("/check", data={"domain": ""})
            check("an empty domain is rejected rather than crashing",
                  r.status_code == 302 and "error" in r.headers["Location"])
            r = cl.post("/check", data={"domain": "127.0.0.1"})
            check("the web form refuses an internal address", r.status_code == 302)
            for fmt, ctype in (("json", "application/json"), ("csv", "text/csv"),
                               ("html", "text/html")):
                r = cl.get(f"/export/{fmt}?check={cid}")
                check(f"export /{fmt} downloads",
                      r.status_code == 200 and ctype in r.headers["Content-Type"]
                      and "attachment" in r.headers.get("Content-Disposition", ""))
            check("bad export format is rejected", cl.get("/export/exe").status_code == 400)
            check("unknown route returns a helpful 404", cl.get("/nope").status_code == 404)
            check("the API requires a domain", cl.get("/api/check").status_code == 400)

        print("\n Live check (network permitting)")
        live = check_domain("github.com", timeout=8.0, check_http=False)
        if live.get("error") and "could not" in (live["error"] or "").lower():
            skip("a real domain is checked end to end", "no network access")
        elif live.get("blocked"):
            skip("a real domain is checked end to end", "blocked by bot protection")
        else:
            check("a real domain is fetched and graded",
                  live["found"] and live["score"] is not None,
                  (live["found"], live.get("error")))
            check("the file was found at the well-known path",
                  WELL_KNOWN_PATH in (live.get("source_url") or ""), live.get("source_url"))
            check("real fields were parsed",
                  live.get("parsed") and "contact" in live["parsed"]["fields"])
            check("every finding cites a clause or is a summary",
                  all(x.get("rfc") or x["category"] == "Summary" for x in live["findings"]),
                  [x["title"] for x in live["findings"] if not x.get("rfc")])

        print("\n Retention")
        cmd_purge(argparse.Namespace(all=False, keep=1))
        check("purge keeps exactly the newest check",
              q1("SELECT COUNT(*) c FROM checks", ())["c"] == 1)
        check("purge removes orphaned findings and fields",
              all(q1(f"SELECT COUNT(*) c FROM {t} WHERE check_id NOT IN "
                     f"(SELECT id FROM checks)", ())["c"] == 0
                  for t in ("findings", "fields")))
        cmd_purge(argparse.Namespace(all=True, keep=1))
        check("purge --all clears everything",
              q1("SELECT COUNT(*) c FROM checks", ())["c"] == 0)
    finally:
        set_db_path(original)
        shutil.rmtree(tmp, ignore_errors=True)

    line("=")
    print(f"  {len(passed)} passed, {len(failed)} failed"
          + (f", {len(skipped)} skipped" if skipped else ""))
    if failed:
        print("  Failed: " + ", ".join(failed))
    if skipped:
        print("  Skipped: " + ", ".join(skipped))
    if not failed:
        print("  All checks passed. The temporary database has been removed.")
    line("=")
    return 0 if not failed else 1


# =============================================================================
# SECTION 11 - Entry point
# =============================================================================

def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog=os.path.basename(__file__),
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=f"{APP_NAME} v{VERSION} - checks a domain's security.txt against "
                    f"RFC 9116, by {AUTHOR}",
        epilog=textwrap.dedent(f"""\
            examples
              %(prog)s explain                  what security.txt is, and what it is not
              %(prog)s check example.com
              %(prog)s check example.com --show-file
              %(prog)s check a.com --also b.com c.com
              %(prog)s check --file domains.txt --fail-under 70
              %(prog)s validate ./security.txt  check a local file, fetching nothing
              %(prog)s template --out security.txt
              %(prog)s serve                    web app on http://127.0.0.1:5000

            {DISCLAIMER_LONG}
            """))
    p.add_argument("--db", default=DEFAULT_DB,
                   help=f"SQLite database file (default: {DEFAULT_DB}, env SECTXT_DB)")
    p.add_argument("--version", action="version", version=f"{APP_NAME} {VERSION}")
    sub = p.add_subparsers(dest="cmd")

    s = sub.add_parser("check", help="fetch and check a domain")
    s.add_argument("domain", nargs="?", default="")
    s.add_argument("--also", nargs="*", help="more domains to check")
    s.add_argument("--file", help="a file of domains, one per line")
    s.add_argument("--timeout", type=float, default=10.0)
    s.add_argument("--no-http", action="store_true",
                   help="skip the plain-HTTP reachability test")
    s.add_argument("--allow-private", action="store_true",
                   help="permit private and loopback addresses (for your own internal host)")
    s.add_argument("--delay", type=float, default=1.0,
                   help="seconds between domains when checking several")
    s.add_argument("--show", type=int, help="limit how many findings are printed")
    s.add_argument("--show-file", action="store_true", help="print the file itself")
    s.add_argument("--quiet", action="store_true", help="hide informational findings")
    s.add_argument("--fail-under", type=float,
                   help="exit non-zero if any score is below this, for CI")
    s.add_argument("--note")
    s.set_defaults(func=cmd_check)

    s = sub.add_parser("validate", help="check a local file, fetching nothing")
    s.add_argument("file")
    s.add_argument("--canonical", help="the URL it will be published at")
    s.add_argument("--show", type=int)
    s.add_argument("--quiet", action="store_true")
    s.set_defaults(func=cmd_validate)

    s = sub.add_parser("template", help="print a conformant starting template")
    s.add_argument("--out")
    s.set_defaults(func=cmd_template)

    s = sub.add_parser("explain", help="what security.txt is, and what it is not")
    s.set_defaults(func=cmd_explain)

    s = sub.add_parser("history", help="previous checks")
    s.add_argument("--domain")
    s.add_argument("--limit", type=int, default=25)
    s.set_defaults(func=cmd_history)

    s = sub.add_parser("serve", help="start the web app")
    s.add_argument("--host", default="127.0.0.1")
    s.add_argument("--port", type=int, default=5000)
    s.add_argument("--debug", action="store_true")
    s.set_defaults(func=cmd_serve)

    s = sub.add_parser("export", help="write a report to a file")
    s.add_argument("--check", type=int)
    s.add_argument("--format", choices=["json", "csv", "html"], default="html")
    s.add_argument("--out")
    s.set_defaults(func=cmd_export)

    s = sub.add_parser("logs", help="local event log")
    s.add_argument("--level", choices=["INFO", "WARN", "ERROR", "info", "warn", "error"])
    s.add_argument("--limit", type=int, default=50)
    s.set_defaults(func=cmd_logs)

    s = sub.add_parser("purge", help="delete stored checks")
    s.add_argument("--keep", type=int, default=50)
    s.add_argument("--all", action="store_true")
    s.set_defaults(func=cmd_purge)

    s = sub.add_parser("selftest", help="verify every component (temporary database)")
    s.set_defaults(func=cmd_selftest)

    s = sub.add_parser("version", help="versions and the disclaimer")
    s.set_defaults(func=cmd_version)
    return p


def main(argv=None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    set_db_path(args.db)
    if not getattr(args, "cmd", None):
        parser.print_help()
        return 0
    if args.cmd == "check" and not args.domain and not args.file:
        parser.parse_args([args.cmd, "--help"])
        return 1
    if args.cmd != "selftest":
        init_db()
    try:
        rc = args.func(args)
        return rc if isinstance(rc, int) else 0
    except BrokenPipeError:
        try:
            os.dup2(os.open(os.devnull, os.O_WRONLY), sys.stdout.fileno())
        except Exception:
            pass
        return 0
    except KeyboardInterrupt:
        print("\nInterrupted.")
        return 130
    except sqlite3.OperationalError as e:
        print(f"Database error: {e}\nIs another copy running against {db_path()}?")
        return 1


if __name__ == "__main__":
    sys.exit(main())
