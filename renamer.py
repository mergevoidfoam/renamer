#!/usr/bin/env python3
"""renamer: rename TV episode files into a Kodi-friendly, terminal-friendly form.

    Show-Name_S01E04_Episode-Title.mkv

Titles come from TVmaze unless a nameInfo file is given with --names. Every
run shows a preview and asks before changing anything.
"""

from __future__ import annotations

import argparse
import contextlib
import copy
import dataclasses
import difflib
import unicodedata
import errno
import hashlib
import html
import json
import os
import platform
import re
import shlex
import shutil
import stat
import subprocess
import sys
import tempfile
import textwrap
import threading
import time
import traceback
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable
from xml.etree import ElementTree
from xml.sax.saxutils import escape as xml_escape

VIDEO_EXTS = {".mkv", ".mp4", ".avi", ".m4v", ".mov", ".wmv", ".ts", ".m2ts",
              ".webm", ".mpg", ".mpeg", ".flv"}
SUB_EXTS = {".srt", ".ass", ".ssa", ".sub", ".idx", ".vtt"}
# Files that are never part of a show: release notes, links, checksums, programs (--clean).
JUNK_EXTS = {".txt", ".url", ".lnk", ".link", ".website", ".html", ".htm", ".sfv", ".md5", ".torrent",
             ".exe", ".bat", ".cmd", ".scr", ".ico"}
DOWNLOAD_EXT = ".!qb"           # qBittorrent's extension for an unfinished download
DOWNLOAD_EXTS = (".!qb", ".!ut")  # qBittorrent's and uTorrent's
# uTorrent's leftovers, what macOS and Windows leave behind ("._Episode 1.mkv"), and release groups' adverts.
_JUNK_NAME = re.compile(r"~utorrentpartfile_[0-9a-f]+\.dat|\._.*|\.ds_store|thumbs\.db|desktop\.ini"
                        r"|.*donation.*\.(?:png|jpe?g|gif)", re.I)


def is_junk(path: Path) -> bool:
    """A file that's never part of a show (--clean)."""
    return path.suffix.lower() in JUNK_EXTS or bool(_JUNK_NAME.fullmatch(path.name))
UNDO_LOG = ".rename_undo.json"
NFO_DIR = ".nfo"                # new .nfo files go here
NFO_OLD = ".nfo-old"            # inside NFO_DIR: every existing .nfo is moved here
JUNK_DIR = ".junk"              # --clean moves junk here
MULTI_TITLE_LIMIT = 150         # characters; past this a multi-episode file keeps only its first title
NAME_LIMIT = 255 - 20           # bytes; filesystem limit minus room for companions like ".en.forced.srt"
RECENT_SECONDS = 120            # a video changed this recently may still be copying
SMALL_VIDEO_BYTES = 20 * 1024 * 1024
TYPO_SIMILARITY = 0.85          # "Episode Titel" vs "Episode Title" is 0.97; different titles score far lower
FETCH_TIMEOUT = 60              # seconds to wait for one answer from TVmaze or Wikipedia
RETRY_DELAYS = (5, 10, 20)      # waits between attempts, so 4 attempts in all
TVMAZE = "https://api.tvmaze.com"
WIKIPEDIA = "https://en.wikipedia.org/w/api.php"
VERSION = "1.2.0"
LOG_DIR = Path.home() / ".logs"   # --verbose logs
# A folder here makes every run also write a long debug log, for finding bugs. None turns it off.
DEBUG_LOG_DIR: Path | None = None
USER_AGENT = f"renamer/{VERSION} (personal TV file renamer)"


class RenamerError(Exception):
    """A problem that stops the run. Raised before anything is changed."""


class FetchError(Exception):
    """One failed request. Transient ones (timeouts, 5xx, 429) are worth retrying."""

    def __init__(self, reason: str, transient: bool = True, retry_after: float | None = None):
        super().__init__(reason)
        self.reason = reason
        self.transient = transient
        self.retry_after = retry_after   # seconds the server asked us to wait (429), if it said


# ---------------------------------------------------------------- text

_UNSAFE = re.compile(r'[/\\:*?"<>|()\[\]{}!$;`,\x00-\x1f\x7f]')
_ANSI = re.compile(r"\x1b\[[0-9;]*m")
_KEY_CODES = re.compile(r"\x1b(?:\[[0-9;?]*[~A-Za-z]|O[A-Za-z]|.)?")
_SMALL_WORDS = {"a", "an", "the", "and", "but", "or", "nor", "for", "so", "yet",
                "of", "in", "on", "at", "to", "by", "as", "vs"}


def clean_text(text: str) -> str:
    """Turn a show name or title into one filename part: words joined by "-"."""
    s = text.replace("&", " and ")
    s = _UNSAFE.sub("", s)
    s = re.sub(r"\s*\+\s*", "+", s)   # "Title A + Title B" from a nameInfo line -> "Title-A+Title-B"
    s = re.sub(r"[\s._]+", "-", s)   # spaces, dots and underscores; a spaced dash collapses below
    s = re.sub(r"-+", "-", s)
    return s.strip("-_.")


def readable(text: str) -> str:
    """Spaced-out form of a folder or file name, for prompts and TVmaze searches."""
    s = re.sub(r"[._]+", " ", text)
    if " " not in s.strip():
        s = s.replace("-", " ")      # renamer's own format uses "-" for spaces
    if " " not in s.strip() and len(re.findall(r"[a-z][A-Z]", s)) >= 2:
        s = re.sub(r"(?<=[a-z])(?=[A-Z])", " ", s)   # "ExampleShowName"; "OneWord" stays one word
    return re.sub(r"\s+", " ", s).strip(" -,;:")


def title_case(text: str) -> str:
    """Conventional title case, used only for show names guessed from a folder."""
    words = text.split()
    out = []
    for i, word in enumerate(words):
        if 0 < i < len(words) - 1 and word.lower() in _SMALL_WORDS:
            out.append(word.lower())
        else:
            out.append("-".join(p[:1].upper() + p[1:].lower() for p in word.split("-")))
    return " ".join(out)


def normalize_title(text: str) -> str:
    """A title reduced to letters and digits, for comparing a filename's title with TVmaze's."""
    # NFKD: "Café" is "cafe", and "Example ½" and "Example 1⁄2" are "example12", as "Example.1.2" is (1.2.0).
    return re.sub(r"[\W_]+", "", unicodedata.normalize("NFKD", text.replace("&", " and ")).casefold())


def natural_key(name: str) -> list:
    """Sort key that compares digit runs as numbers, so ep2 sorts before ep10."""
    return [int(t) if t.isdigit() else t for t in re.split(r"(\d+)", name.casefold())]


def _code(season: int, episodes: list[int]) -> str:
    return f"S{season:02d}" + "".join(f"E{e:02d}" for e in episodes)


def _episode_list(episodes: list[int]) -> str:
    shown = ", ".join(f"E{e:02d}" for e in episodes[:10])
    return shown + (f" and {len(episodes) - 10} more" if len(episodes) > 10 else "")


def _plural(count: int, word: str) -> str:
    return f"{count} {word}{'' if count == 1 else 's'}"


# ------------------------------------------------------ name parsing

# S01E04, S1E4, S01 E04, S01.E04, S01_E04, S01-E04, plus extra episodes (S01E04E05, S01E04-E05).
# S01E04, and more episodes after it: S01E04E05, S01E04-E05, S01E04-S01E05, S01E01&E02 (EXAMPLE SHOW).
_SE_RE = re.compile(r"(?<![0-9])s(\d{1,3})[ ._-]?e(\d{1,4})((?:[ ._&+-]?(?:s\d{1,3}[ ._-]?)?e\d{1,4})*)(?:v\d)?(?![0-9])",
                    re.I)
# 1x04. The lookarounds stop it matching inside longer numbers, so 1920x1080 never counts.
_X_RE = re.compile(r"(?<![0-9a-z])(\d{1,2})x(\d{2,3})(?![0-9])", re.I)
_COPY_MARK = re.compile(r"(?<![a-z])copy(?![a-z])|\(\d{1,2}\)", re.I)
_SAMPLE = re.compile(r"(?<![a-z])sample(?![a-z])", re.I)
# Folders that commonly sit next to season folders without making a folder "not a show folder".
_SHOW_EXTRAS = re.compile(r"(?:extras?|featurettes?|bonus|behind[ ._-]the[ ._-]scenes|samples?|nc|ncop|nced|creditless"
                          r"|scans?|subs|subtitles|artwork|posters?)", re.I)
# Folders whose contents are bonus material: never renamed, and junk in them needs its own yes.
_EXTRAS_FOLDER = re.compile(r"extras?|featurettes?|bonus|behind[ ._-]the[ ._-]scenes|samples?|nc|ncop|nced|creditless"
                            r"|scans?", re.I)
# "Part 1 of 2" in a release name, or "-Part-1" at the end of renamer's own names.
_PART_OF = re.compile(r"[ ,._-]*(?<![a-z])part[ ._-]*(\d{1,2})[ ._-]*of[ ._-]*\d{1,2}(?![0-9])", re.I)
_OWN_PART = re.compile(r"-Part-(\d{1,2})$")
# A folder whose only job is to hold the seasons: Show.S01-S13/Series/Season 1 (1.1.0).
_SEASONS_LAYER = re.compile(r"series|seasons|episodes|shows|tv|tv[ ._-]series|complete", re.I)
_HAS_YEAR = re.compile(r"(?<!\d)(?:19|20)\d\d(?!\d)")
# A folder name that says what kind of thing is inside, not which show: Anime/Live-Action/EXAMPLE SHOW S02E04… (1.2.0).
_GENERIC_FOLDER = re.compile(r"live[ ._-]?action|anime|animated|cartoons?|tv[ ._-]shows?|downloads?", re.I)
_DUB = re.compile(r"(?<![a-z])(?:eng(?:lish)?[ ._-]*)?dub(?:bed)?(?![a-z])", re.I)
_SUB_WORD = re.compile(r"(?<![a-z])subs?(?![a-z])", re.I)
GROUP_MARKER = ".renamer-group"    # in a folder lib --group made: copies of one show, kept apart
LOOSE_EPISODES = "loose-episodes"  # in such a folder: the episode files that had no folder of their own
MAX_MOVIES_IN_SHOW = 3             # more dated folders than this beside the seasons are specials
_OWN_FORMAT = re.compile(r"_S\d+(?:E\d+)+_")


_DASH_NUMBER = re.compile(r"(?:^|\s)-\s*(\d{3,4})(?=\s*-\s|\s*$)")
_BARE_NUMBER = re.compile(r"(?<![0-9a-z])(\d{3,4})(?![0-9a-z])", re.I)
_NOT_EPISODES = {"480", "576", "720", "1080", "2160"}


def _number_code(stem: str, folder_season: int | None) -> tuple[int, int, int] | None:
    """A season-and-episode number like 205 (S02E05) or 1012 (S10E12): (season, episode, end).

    Only trusted between dashes ("Show - 205 - Title"), or when its leading digits match the
    season folder it's in ("Show.205.Title" in "Season 2"), so years and resolutions aren't misread."""
    candidates = [(m, True) for m in _DASH_NUMBER.finditer(stem)]
    if folder_season is not None:
        candidates += [(m, False) for m in _BARE_NUMBER.finditer(stem)]
    for m, dashed in candidates:
        digits = m.group(1)
        season, episode = digits[:-2], digits[-2:]
        if digits in _NOT_EPISODES or int(episode) == 0 or digits[0] == "0":
            continue   # 0623 is episode 623, never season 6 (Example Show, 1.2.0)
        if len(digits) == 4 and digits[:2] in ("19", "20") and str(folder_season) != season:
            continue   # a year
        if dashed or str(folder_season) == season:
            return int(season), int(episode), m.end(1)
    return None


def parse_episode(filename: str, folder_season: int | None = None) -> tuple[int, list[int]] | None:
    """Season and episode numbers from a filename, or None."""
    stem = Path(filename).stem
    m = _SE_RE.search(stem)
    if m:
        episodes = [int(m.group(2))] + [int(n) for n in re.findall(r"e(\d{1,4})", m.group(3), re.I)]
        return int(m.group(1)), list(dict.fromkeys(episodes))
    m = _X_RE.search(stem)
    if m:
        return int(m.group(1)), [int(m.group(2))]
    found = _number_code(stem, folder_season)
    return (found[0], [found[1]]) if found else None


@dataclass
class Plain:
    """What a filename with only a plain episode number says (1.2.0)."""
    numbers: list[int]       # one, or a range like 88-91
    before: str = ""         # the text in front of the number: "Example.Show - Season Three Name"
    title: str = ""          # the text after it, if any
    special: bool = False    # OVA 01, NCOP 02, Movie 1: not one of the show's numbered episodes


_NOT_EPISODE_WORD = re.compile(r"(?<![a-z])(?:ovas?|oads?|oavs?|specials?|movies?|films?|recap|preview|trailer|sample"
                               r"|nc|ncop\d*|nced\d*|op|ed)(?![a-z])", re.I)
_LEADING_NUMBER = re.compile(r"^\s*\[?(\d{1,4})\]?(?:\s+|\s*[.)-]\s+|(?<=\])\s*)(?=\S)(.*)$")
_EPISODE_WORD = re.compile(r"(?:^|(?<=[\s-]))(?:episodes?|ep)[ .]*(\d{1,4})(?:v\d)?(?![0-9a-z])(.*)$", re.I)
_DASH_PLAIN = re.compile(r"(?:^|\s)-\s*(\d{1,4})(?:v\d)?(?:\s*-\s*(\d{1,4})(?:v\d)?)?(?=\s|$)(.*)$")
_TRAILING_PLAIN = re.compile(r"^(.*\S)\s+(\d{1,4})(?:v\d)?$")
_NUMBERED_WORD = re.compile(r"(?<![a-z])(?:part|pt|vol|volume|chapter|book|disc|disk|cd)\s*$", re.I)


def plain_numbers(filename: str) -> Plain | None:
    """A plain episode number in a filename with no SxxEyy: "Show - 12", "Show - 0623 - Title",
    "Episode 10 Doubt", "Episode01", "[18] Title", "10 Title", "Example.Show 01". What it counts (the
    season, or the whole show) only shows once TVmaze's list is known (1.2.0)."""
    stem = Path(filename).stem
    if stem.startswith(".") or _SAMPLE.search(stem):
        return None
    s = re.sub(r"^\s*\[[^\]]*[^\]\d\s][^\]]*\]\s*", "", stem).replace("_", " ")   # "[ABC] …", but not "[18] …"
    if " " not in s.strip():
        s = s.replace(".", " ")
    s = _PART_OF.sub(" ", s)
    cut = len(s)
    for pattern in (re.compile(r"(?<=.)[(\[]"), _RELEASE_TAG, _TITLE_TAG, re.compile(r"(?<=\s)(?:19|20)\d\d(?!\d)")):
        m = pattern.search(s)
        if m and m.start() > 0:
            cut = min(cut, m.start())
    s = s[:cut].strip()
    found = None
    if m := _LEADING_NUMBER.match(s):
        found = Plain([int(m.group(1))], "", readable(m.group(2)))
    elif m := re.fullmatch(r"\[?(\d{1,4})\]?", s):
        found = Plain([int(m.group(1))])
    elif m := _EPISODE_WORD.search(s):
        found = Plain([int(m.group(1))], s[:m.start()].strip(" -"), readable(m.group(2)))
    elif m := _DASH_PLAIN.search(s):
        first, last = int(m.group(1)), int(m.group(2) or m.group(1))
        numbers = list(range(first, last + 1)) if first < last <= first + 12 else [first]
        found = Plain(numbers, s[:m.start()].strip(" -"), readable(m.group(3)))
    elif (m := _TRAILING_PLAIN.match(s)) and not _NUMBERED_WORD.search(m.group(1)):
        found = Plain([int(m.group(2))], m.group(1).strip(" -"))
    if not found or found.numbers[0] == 0:
        return None
    if str(found.numbers[0]) in _NOT_EPISODES and not re.search(r"(?i)(?:-|ep\w*)\s*0*" + str(found.numbers[0]), s):
        return None   # "Show 1080.mkv", but Example Show does have an episode 1080
    found.special = bool(_NOT_EPISODE_WORD.search(found.before)) or bool(
        not found.before and _NOT_EPISODE_WORD.match(found.title or "") and len(found.title.split()) == 1)
    if found.before and not re.search(r"[^\W\d_]", found.before):
        return None
    return found


def text_after_code(filename: str, folder_season: int | None = None) -> str:
    """Everything after a filename's SxxExx, brackets and all ("Episode Title (aka Other Title)")."""
    stem = Path(filename).stem
    m = _episode_match(stem)
    if m:
        return stem[m.end():]
    found = _number_code(stem, folder_season)
    return stem[found[2]:] if found else ""


def _episode_match(stem: str) -> re.Match | None:
    return _SE_RE.search(stem) or _X_RE.search(stem)


_SITE_PREFIX = re.compile(r"^\s*(?:[\[({]\s*(?:www\.)?[^\])}]*\.(?:com|org|net|to|me|cc|info|tv|in)\s*[\])}]"
                          r"|(?:www\.)\S+\.(?:com|org|net|to|me|cc|info|tv|in))\s*[-_.]*\s*", re.I)
_NUMBER_WORDS = {w: n for n, w in enumerate(
    "zero one two three four five six seven eight nine ten eleven twelve thirteen fourteen fifteen sixteen "
    "seventeen eighteen nineteen twenty".split())}
# Seasons some shows call something else: "Book One - Air" (Example Show), "Volume 2",
# "Chapter 3", "Series 4" (British). "Part" isn't one: movies use it too (1.0.0).
_SEASON_WORD = re.compile(r"(?<![a-z])(book|volume|vol|chapter|series)[ ._]*(\d{1,2}|"
                          + "|".join(_NUMBER_WORDS) + r")(?![0-9a-z])", re.I)


def season_word(name: str) -> tuple[str, int, str] | None:
    """("Book", 1, "Air") for "Book One - Air": a season folder that isn't called a season, with
    what comes after its number, so renaming keeps it (1.0.0)."""
    m = _SEASON_WORD.search(name)
    if not m:
        return None
    word = m.group(1).capitalize()
    word = "Volume" if word == "Vol" else word
    number = m.group(2).lower()
    rest = re.sub(r"\s*[(\[].*$", "", name[m.end():]).strip(" -_.")
    return word, int(number) if number.isdigit() else _NUMBER_WORDS[number], rest


def season_from_folder(name: str) -> int | None:
    """Season number found anywhere in a folder name, or None."""
    # A range like "S01-S07" describes a whole show, never one season.
    s = re.sub(r"(?<![0-9a-z])s\d{1,3}\s*[-_]\s*s?\d{1,3}(?![0-9])", " ", name, flags=re.I)
    s = re.sub(r"(?i)(?<![a-z])seasons?[ ._-]*\d{1,3}\s*(?:-|to|&|and)\s*\d{1,3}(?![0-9])", " ", s)   # "Season 1-5", "Seasons 16 to 21"
    if re.search(r"(?<![a-z])specials?(?![a-z])", re.sub(r"\+\s*specials?", " ", s, flags=re.I), re.I):
        return 0
    numbers = re.findall(r"(?i)(?<![a-z])(?:season|seizoen|staffel|saison|temporada)[ ._-]*(\d{1,3})(?![0-9])", s)
    if len({int(n) for n in numbers}) > 1:   # "(Season 01 + Season 02 + Movies)": a whole release
        return None
    if numbers:   # also Dutch, German, French and Spanish
        return int(numbers[0])
    m = re.search(r"(?<![a-z])season[ ._-]*(" + "|".join(_NUMBER_WORDS) + r")(?![a-z])", s, re.I)
    if m:   # "even stevens - season one", "Looking Season One"
        return _NUMBER_WORDS[m.group(1).lower()]
    if (word := season_word(s)) and word[1] > 0:
        return word[1]
    m = re.search(r"(?<![0-9a-z])s(\d{1,3})(?![0-9])(?![ ._-]?e\d)", s, re.I)
    if m:
        return int(m.group(1))
    m = re.fullmatch(r"\s*(\d{1,3})\s*", s)
    return int(m.group(1)) if m else None


_RELEASE_TAG = re.compile(
    r"(?<![0-9a-z])(?:480p|576p|720p|1080p|2160p|360p|240p|4k|uhd|x26[45]|h[ .]?26[45]|hevc|avc"
    r"|web[ .-]?dl|web[ .-]?rip|blu[ .-]?ray|bdrip|bd|brrip|dvdrip|hdtv|remux|complete"
    r"|proper|repack|dual[ .-]?audio)(?![0-9a-z])", re.I)
# More tags that only matter when reading a title out of a filename.
_TITLE_TAG = re.compile(
    r"(?<![0-9a-z])(?:web|amzn|nf|hmax|dsnp|hulu|atvp|pcok|ddp?[ .]?\d(?:[ .]\d)?|aac\d?(?:[ .]\d)?"
    r"|10bit|hdr|internal|multi|subbed|dubbed|xvid|divx|dvdscr|ac3|dts|mp3|limited|extended)(?![0-9a-z])", re.I)
_SHOW_CUTS = (
    re.compile(r"[(\[]"),
    re.compile(r"(?<![0-9a-z])s\d{1,3}(?![0-9])", re.I),
    re.compile(r"[ ._-](?:seasons?|seizoen|staffel|saison|temporada)[ ._-]*(?:\d|(?:one|two|three|four|five|six"
               r"|seven|eight|nine|ten)(?![a-z]))", re.I),   # "_Season_01", "Seizoen 4", "Season One"
    _RELEASE_TAG,
    re.compile(r"[ ._-]+(?:19|20)\d\d(?![0-9])"),
    re.compile(r"[ ._-]+(?:eng(?:lish)?[ ._-]*)?dub(?:bed)?(?![a-z])", re.I),    # the dub is noted separately (1.2.0)
    re.compile(r"[ ._-]+(?:og|original)[ ._-]+series(?![a-z])", re.I),
    re.compile(r"[ ._-]+anime(?![a-z])\s+(?=\d|$)", re.I),
    re.compile(r"[ ._-]+episodes?[ ._-]*\d", re.I),                               # "Show Episodes 01-26"
    re.compile(r"[ ._]+\d{1,3}\s*-\s*\d{1,3}(?![0-9])"),                         # "Show 1-26 Complete"
)
_GROUP_PREFIX = re.compile(r"^\s*\[\s*[^\]]*\]\s*[-_.]*\s*")   # "[ABC] Show…", "[ example-site.gy ] Show…" (1.2.0)


def show_from_folder(name: str, before_code: bool = False) -> str:
    """The show-name part of a messy folder or file name, before any year or release tag.
    before_code: name is what stands before a filename's SxxEyy, so a dash in it is part of the show."""
    # renamer's own season folders since 1.0.0 put the number first: "Season_01_Show-Name".
    name = re.sub(r"(?i)^season[ ._-]*\d{1,3}[ ._-]+(?=\D)", "", name)
    # Download sites' names in front ("www.example-site.org - Example.Show…") and extras after ("+Specials").
    name = _SITE_PREFIX.sub("", name)
    name = _GROUP_PREFIX.sub("", name)
    if name.lstrip().startswith("("):   # "Season 1 (1080p Mixed)": nothing but tags
        return ""
    name = re.sub(r"(?i)\s*\+\s*(?:specials?|extras?|movies?|shorts?|ovas?)\b.*$", "", name)
    cut = len(name)
    for pattern in _SHOW_CUTS:
        m = pattern.search(name)
        if m and m.start() > 0:
            cut = min(cut, m.start())
    # " - " usually ends the show's name ("Show - 205 - Title"), but one right before the season
    # is part of it: "Example Show - Spin-Off - Season 1" isn't Example Show (1.1.0, from a real run).
    dash = re.search(r"\s-\s", name[:cut])
    if dash and dash.start() > 0:
        head = name[:cut].rstrip(" ._")
        if before_code:
            return re.sub(r"\s+-\s+", " ", head.rstrip(" -"))
        # "Example Show - The Subtitle (2005 - 2008) [1080p]": a subtitle, when tags end the name right after it.
        subtitle = (cut < len(name) and not head.endswith("-") and len(re.findall(r"\s-\s", head)) == 1
                    and re.search(r"[^\W\d_]", head[dash.end():]) and not re.fullmatch(r"\s*\d+.*", head[dash.end():]))
        if subtitle:
            return re.sub(r"\s+-\s+", " ", head)
        if cut == len(name) or not head.endswith("-") or not re.search(r"\s-\s", head.rstrip(" -")):
            return name[:dash.start()]
        return re.sub(r"\s+-\s+", " ", head.rstrip(" -"))   # TVmaze finds nothing with the dash in it
    if name[:cut].rstrip(" ._").endswith(" -"):   # "Example Show - Season 2"
        return name[:cut].rstrip(" ._-")
    return name[:cut]


def title_from_filename(filename: str, folder_season: int | None = None) -> tuple[str, int | None]:
    """The episode title written in a filename after its SxxExx, and its "Part N", if any.

    "Show - S00 E02 - Episode Title (480p).mp4" -> ("Episode Title", None)
    "Show.S02E01.Episode.Title.1080p.BluRay.mkv"        -> ("Episode Title", None)
    "Show - S00 E01 - Big Adventure, Part 1 of 2.mp4"     -> ("Big Adventure", 1)
    "Show - S01 E05 (1080p - HMax Web-DL).mp4"            -> ("", None)"""
    stem = Path(filename).stem
    m = _episode_match(stem)
    if m:
        end = m.end()
    elif found := _number_code(stem, folder_season):
        end = found[2]
    else:
        return "", None
    rest = stem[end:]
    part = None
    pm = _PART_OF.search(rest)
    if pm:
        part, rest = int(pm.group(1)), rest[:pm.start()] + " " + rest[pm.end():]
    elif _OWN_FORMAT.search(stem) and (om := _OWN_PART.search(rest)):
        part, rest = int(om.group(1)), rest[:om.start()]
    rest = _COPY_MARK.sub(" ", rest)
    cut = len(rest)
    for pattern in (re.compile(r"[(\[]"), _RELEASE_TAG, _TITLE_TAG):
        found = pattern.search(rest)
        if found:
            cut = min(cut, found.start())
    return readable(rest[:cut]), part


_YEARS = r"((?:19|20)\d\d)(?:\s*[-–]\s*((?:19|20)\d\d|present))?"


def folder_years(name: str) -> str | None:
    """Years from a show folder name: "(2001-2008)" gives "2001-2008", "(2005)" gives "2005"."""
    m = re.search(r"\(" + _YEARS + r"\)", name, re.I)
    if not m:
        m = re.search(r"(?<=.)(?<![0-9])" + _YEARS + r"(?![0-9])", name, re.I)
    if not m:
        return None
    start, end = m.group(1), (m.group(2) or "").lower()
    return f"{start}-{end}" if end and end != start else start


def years_text(start: str, end: str, running: bool) -> str | None:
    if not start:
        return None
    if running:
        return f"{start}-present"
    return f"{start}-{end}" if end and end != start else start


# ------------------------------------------------------------ title data

@dataclass
class EpisodeInfo:
    title: str
    aired: str = ""
    plot: str = ""
    tvmaze_id: int | None = None
    source: str = ""                # for --verbose: where the title came from
    rating: float | None = None     # TVmaze's average, 0-10


@dataclass
class ShowInfo:
    name: str                       # readable form, e.g. "Example Show"
    year: int | None = None
    premiered: str = ""
    plot: str = ""
    genres: list[str] = field(default_factory=list)
    ids: dict[str, str] = field(default_factory=dict)   # tvmaze / imdb / tvdb
    years: str | None = None        # "2013-present", for --years
    years_how: str = ""
    network: str = ""               # "Example Network", or the streaming service
    language: str = ""              # "English"
    overall: bool = False           # numbered by overall episode, like Example Show: S16E0623 (1.2.0)
    season_names: dict[int, str] = field(default_factory=dict)   # "Season Name", from TVmaze or Wikipedia
    total: int = 0                  # with overall: how many episodes, for the width of the number
    season_raw: dict[int, str] = field(default_factory=dict)     # names as the source writes them, to match folders by
    notes: list[str] = field(default_factory=list)               # warnings for the preview


Titles = dict[tuple[int, int], EpisodeInfo]


def parse_names(path: Path) -> Titles:
    """Read a nameInfo file: "Sxx" lines start a season, other lines are titles in order."""
    try:
        lines = path.read_text(encoding="utf-8-sig").splitlines()
    except OSError as e:
        raise RenamerError(f"Can't read {path}: {e.strerror}") from None
    titles: Titles = {}
    season = None
    episode = 0
    for number, line in enumerate(lines, 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        m = re.fullmatch(r"[sS](\d{1,3})", line)
        if m:
            season, episode = int(m.group(1)), 0
            continue
        if season is None:
            raise RenamerError(f"{path.name} line {number}: a title comes before the first season line (like S01)")
        episode += 1
        titles[(season, episode)] = EpisodeInfo(title=line, source=f"{path.name} line {number}")
    return titles


def strip_html(text: str | None) -> str:
    return html.unescape(re.sub(r"<[^>]+>", "", text or "")).strip()


_OFFLINE_HINT = "Nothing was changed. Use --names to run offline."
_sleep = time.sleep   # replaced in tests


def http_get_json(url: str):
    """One request, no retries. Raises FetchError with a readable reason."""
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(request, timeout=FETCH_TIMEOUT) as response:
            return json.load(response)
    except urllib.error.HTTPError as e:
        try:
            wait = float(e.headers.get("Retry-After") or "") if e.code == 429 else None
        except ValueError:
            wait = None
        raise FetchError(f"answered {e.code} {e.reason}", transient=e.code == 429 or e.code >= 500,
                         retry_after=wait) from None
    except TimeoutError:
        raise FetchError(f"didn't answer within {FETCH_TIMEOUT}s") from None
    except urllib.error.URLError as e:
        if isinstance(e.reason, TimeoutError):
            raise FetchError(f"didn't answer within {FETCH_TIMEOUT}s") from None
        raise FetchError(f"couldn't be reached ({e.reason})") from None
    except OSError as e:
        raise FetchError(f"couldn't be reached ({e})") from None
    except ValueError:
        raise FetchError("sent a reply that isn't valid JSON") from None


class Waiting:
    """The line shown while a request is pending:

        Waiting for TVmaze (searching for "Example Show")… 0:12

    It appears only after the first second, so quick answers don't flash it, ticks every second,
    and is erased when the answer arrives. It's only drawn on a real terminal and is never
    written to the --verbose log."""

    def __init__(self, ui: UI, text: str):
        self.ui, self.text = ui, text
        self.started = time.monotonic()
        self.drawn = False
        self._stop = threading.Event()
        self._thread = threading.Thread(target=self._run, daemon=True) if ui.tty else None
        if self._thread:
            self._thread.start()

    def _run(self) -> None:
        while not self._stop.wait(1):
            columns = shutil.get_terminal_size((80, 24)).columns
            line = f"{self.text}… {_elapsed(time.monotonic() - self.started)}"
            self.ui.out.write("\r" + line[:columns - 1] + "\033[K")
            self.ui.out.flush()
            self.drawn = True

    def done(self) -> None:
        if self._thread:
            self._stop.set()
            self._thread.join()
            self._thread = None
        if self.drawn:
            self.ui.out.write("\r\033[K")
            self.ui.out.flush()
            self.drawn = False


class Getter:
    """Fetches JSON with retries: up to 4 attempts, with a warning and the reason after each
    failed one. Gives up at once on answers that won't change, like 404. Shows a waiting line
    while a request is pending, and keeps how long the last answer took, for --verbose."""

    def __init__(self, fetch: Callable[[str], object], ui: UI, quiet: bool = False):
        self.fetch, self.ui = fetch, ui
        self.seconds = 0.0
        self.attempts = 0
        self.quiet = quiet   # retries go to the debug log only (lib runs, under a progress bar)

    def __call__(self, url: str, service: str = "TVmaze", hint: str = _OFFLINE_HINT, what: str = ""):
        attempts = len(RETRY_DELAYS) + 1
        label = f"Waiting for {service}" + (f" ({what})" if what else "")
        told_to_wait = 0
        attempt = 0
        while attempt < attempts:
            attempt += 1
            waiting = Waiting(self.ui, label)
            try:
                data = self.fetch(url)
                self.seconds, self.attempts = time.monotonic() - waiting.started, attempt
                size = len(json.dumps(data, ensure_ascii=False))
                self.ui.debug(f"GET {url}: answered in {self.seconds:.2f}s, attempt {attempt}, {size} characters")
                self.ui.responses.append({"url": url, "seconds": round(self.seconds, 3), "data": data})
                return data
            except FetchError as e:
                self.ui.debug(f"GET {url}: attempt {attempt} failed: {e.reason}"
                              + (f" (asked to wait {e.retry_after:.0f}s)" if e.retry_after else ""))
                waiting.done()
                if e.retry_after and e.retry_after <= 120 and told_to_wait < 5:
                    # Wikimedia's way of pacing: wait as long as it says, without counting it as a failure.
                    told_to_wait += 1
                    attempt -= 1
                    pause = Waiting(self.ui, f"{label}, which asked to wait {e.retry_after:.0f}s")
                    try:
                        _sleep(e.retry_after + 1)
                    finally:
                        pause.done()
                    continue
                if not e.transient or attempt == attempts:
                    tries = f" (tried {attempt} times)" if attempt > 1 else ""
                    raise RenamerError(f"{service} {e.reason}{tries}. {hint}".strip()) from None
                delay = RETRY_DELAYS[attempt - 1]
                warning = f"{service} {e.reason} (attempt {attempt} of {attempts}); trying again in {delay}s…"
                if self.quiet:
                    self.ui.debug(warning)
                else:
                    self.ui.say(self.ui.paint("Warning: ", "WARN") + warning)
                _sleep(delay)
            finally:
                waiting.done()

    def took(self) -> str:
        """"in 23.4s", plus the number of attempts when it needed more than one, for --verbose."""
        return f"in {self.seconds:.1f}s" + (f" (attempt {self.attempts})" if self.attempts > 1 else "")


def parse_tvmaze_show(data: dict) -> tuple[ShowInfo, Titles]:
    premiered = data.get("premiered") or ""
    ended = data.get("ended") or ""
    status = data.get("status") or ""
    running = status in ("Running", "To Be Determined", "In Development") or (not ended and status != "Ended")
    externals = data.get("externals") or {}
    ids = {"tvmaze": str(data["id"])}
    if externals.get("imdb"):
        ids["imdb"] = str(externals["imdb"])
    if externals.get("thetvdb"):
        ids["tvdb"] = str(externals["thetvdb"])
    info = ShowInfo(
        name=data.get("name") or "",
        year=int(premiered[:4]) if premiered[:4].isdigit() else None,
        premiered=premiered,
        plot=strip_html(data.get("summary")),
        genres=list(data.get("genres") or []),
        ids=ids,
        years=years_text(premiered[:4], ended[:4], running),
        years_how=f"TVmaze: premiered {premiered or 'unknown'}, status {status or 'unknown'}"
                  + (f", ended {ended}" if ended else ""),
        network=((data.get("network") or data.get("webChannel") or {}).get("name") or ""),
        language=data.get("language") or "",
    )
    titles: Titles = {}
    for ep in (data.get("_embedded") or {}).get("episodes") or []:
        season, number = ep.get("season"), ep.get("number")
        if not season or number is None:
            continue   # specials are matched by title instead
        titles[(season, number)] = EpisodeInfo(
            title=ep.get("name") or "",
            aired=ep.get("airdate") or "",
            plot=strip_html(ep.get("summary")),
            tvmaze_id=ep.get("id"),
            source=f"TVmaze episode #{ep.get('id')}",
            rating=_rating(ep),
        )
    return info, titles


def _rating(ep: dict) -> float | None:
    average = (ep.get("rating") or {}).get("average")
    return float(average) if isinstance(average, (int, float)) else None


def parse_specials(episodes: list) -> list[EpisodeInfo]:
    """TVmaze's specials: they have no episode number, so they're matched by title."""
    return [EpisodeInfo(title=ep["name"], aired=ep.get("airdate") or "", plot=strip_html(ep.get("summary")),
                        tvmaze_id=ep.get("id"), source=f"TVmaze special #{ep.get('id')}", rating=_rating(ep))
            for ep in episodes or [] if ep.get("number") is None and ep.get("name")]


def wikipedia_guess(query: str, ui: UI, get: Getter) -> str | None:
    """The article Wikipedia's search finds for a show name, e.g. "EXAMPLE SHOW" -> "Example Show"."""
    url = (f"{WIKIPEDIA}?action=opensearch&format=json&limit=5&namespace=0&redirects=resolve"
           f"&search={urllib.parse.quote(query)}")
    ui.detail(f"Wikipedia request: {url}")
    try:
        data = get(url, "Wikipedia", hint="", what=f'looking up "{query}"')
    except RenamerError as e:
        ui.say(ui.paint("Warning: ", "WARN") + f"no suggestion from Wikipedia: {e}")
        return None
    names = data[1] if isinstance(data, list) and len(data) > 1 and isinstance(data[1], list) else []
    ui.detail(f"Wikipedia answered {get.took()}: " + (", ".join(map(str, names[:3])) or "no articles"))
    for name in names:
        if isinstance(name, str) and not name.lower().startswith("list of "):
            # "Example Show (TV series)" -> "Example Show"
            return re.sub(r"\s*\([^)]*\b(?:series|programme|program|show|cartoon)\)$", "", name, flags=re.I)
    return None


def _choose_show(query: str, shows: list[dict], ui: UI) -> tuple[dict | None, str]:
    """The show picked from TVmaze's matches, or None and a new name to search for."""
    ui.say(f'TVmaze matches for "{query}":')
    for i, show in enumerate(shows, 1):
        year = (show.get("premiered") or "")[:4] or "year unknown"
        ui.say(f"  {i}) {show.get('name')} ({year})")
    ui.say("  0) None of these, search for another name")
    while True:
        answer = ui.ask("Choose a show [1], or type a name to search for: ", "1")
        if not answer.isdigit():
            break
        if 1 <= int(answer) <= len(shows):
            ui.say()
            return shows[int(answer) - 1], ""
        if int(answer) == 0:
            answer = ui.ask("Type a name to search TVmaze for, or press Enter to stop: ")
            if not answer:
                raise RenamerError("No show chosen. Nothing was changed.")
            break
        ui.say(f"Type a number from 0 to {len(shows)}, or a name to search for.")
    ui.say()
    return None, answer


@dataclass
class Evidence:
    """What a folder's names say about which of several shows with one name it is (1.2.0)."""
    years: list[str] = field(default_factory=list)
    titles: list[str] = field(default_factory=list)
    top_season: int = 0
    top_number: int = 0


def evidence_from(layout: "Layout", groups: list["Group"]) -> Evidence:
    years: Counter = Counter()
    if start := folder_years(layout.show_dir.name):
        years[start[:4]] += 1000   # the folder's own year comes first
    ev = Evidence()
    for g in groups:
        for year in _HAS_YEAR.findall(g.video.stem):
            years[year] += 1
        title = g.file_title or (g.plain.title if g.plain else "")
        if title:
            ev.titles.append(title)
        if g.plain and not g.plain.special:
            ev.top_number = max(ev.top_number, *g.plain.numbers)
        ev.top_season = max(ev.top_season, g.folder_season or 0, g.season or 0)
    ev.years = [y for y, _ in years.most_common()]
    return ev


def _titles_of(get: Getter, show: dict) -> list[str]:
    """Every episode and special TVmaze lists for a show, reduced for comparing."""
    data = get(f"{TVMAZE}/shows/{show['id']}/episodes?specials=1", what=f"getting the episodes of {show.get('name')}")
    return [normalize_title(e.get("name") or "") for e in data or [] if isinstance(e, dict)]


def _title_hits(titles: list[str], listed: list[str]) -> int:
    """How many of a folder's titles are among a show's: Example ½'s dub is 159 of 161 for the 1989 show, 6 for 2024."""
    hits = 0
    known = set(listed)
    for title in titles:
        key = normalize_title(title)
        if key and (key in known or difflib.get_close_matches(key, listed, n=1, cutoff=0.7)):
            hits += 1
    return hits


def pick_twin(shows: list[dict], ev: Evidence | None, get: Getter) -> dict | None:
    """Of TVmaze's shows with the same name (Example Show 1999 and 2023), the one the folder is, going by
    the year in its name, then its episode titles, then whether its numbers fit; None when they don't
    tell (1.2.0)."""
    if not ev or not shows:
        return None
    twins = [s for s in shows if _same_name(s.get("name", ""), shows[0].get("name", ""))]
    if len(twins) < 2:
        return None
    for year in ev.years:
        exact = [s for s in twins if (s.get("premiered") or "")[:4] == year]
        if len(exact) == 1:
            return exact[0]
        fits = [s for s in twins if (s.get("premiered") or "9999")[:4] <= year <= ((s.get("ended") or "9999")[:4])]
        if len(fits) == 1:
            return fits[0]
    if not ev.titles and not ev.top_number and not ev.top_season:
        return None
    lists = {s["id"]: _titles_of(get, s) for s in twins}
    if ev.titles:
        scores = sorted(((_title_hits(ev.titles, lists[s["id"]]), i) for i, s in enumerate(twins)), reverse=True)
        if scores[0][0] and scores[0][0] >= 2 * scores[1][0] + 1:
            return twins[scores[0][1]]
    fits = [s for s in twins if len(lists[s["id"]]) >= ev.top_number]
    return fits[0] if len(fits) == 1 else None


def shorter_search(query: str, get: Getter) -> list[dict]:
    """TVmaze knows "Example Show", not "Example Show Season Four Name": shorter forms of the name, only
    trusting a show whose whole name begins the query (1.2.0)."""
    words = query.split()
    key = normalize_title(query)
    for size in range(len(words) - 1, max(0, len(words) - 5), -1):
        found = _search_tvmaze(get, " ".join(words[:size]))
        same = [s for s in found if len(normalize_title(s.get("name", ""))) >= 3
                and key.startswith(normalize_title(s.get("name", "")))]
        if same:
            return same
    return []


def tvmaze_lookup(query: str, ui: UI, get: Getter, with_specials: bool, evidence: Evidence | None = None
                  ) -> tuple[ShowInfo, Titles, list[EpisodeInfo], str]:
    """Find the show on TVmaze, asking for help when nothing matches. Returns the query that worked."""
    tried_wikipedia = False
    shortened = False
    while True:
        url = f"{TVMAZE}/search/shows?q={urllib.parse.quote(query)}"
        ui.detail(f"TVmaze request: {url}")
        shows = [r["show"] for r in (get(url, what=f'searching for "{query}"') or [])[:8] if r.get("show")]
        ui.detail(f"TVmaze answered {get.took()}: {_plural(len(shows), 'matching show')}")
        if not shows and not shortened:
            shortened = True
            shows = shorter_search(query, get)
        if len(shows) == 1:
            chosen = shows[0]
            break
        if twin := pick_twin(shows, evidence, get):
            ui.detail(f"Several shows are called {twin.get('name')}; the names here fit the one from "
                      f"{(twin.get('premiered') or '')[:4]}")
            chosen = twin
            break
        if shows:
            chosen, typed = _choose_show(query, shows, ui)
            if chosen:
                break
            query = typed
            continue
        if not ui.interactive:
            raise RenamerError(f'TVmaze has no show matching "{query}". Try another name with --show, '
                               "or use --names to run offline.")
        ui.say(f'TVmaze has no show matching "{query}".')
        if not tried_wikipedia:
            tried_wikipedia = True
            guess = wikipedia_guess(query, ui, get)
            if guess and normalize_title(guess) != normalize_title(query):
                if ui.ask(f"Wikipedia suggests: {guess}. Search TVmaze for that? [Y/n]: ", "y").lower() \
                        not in ("n", "no"):
                    query = guess
                    continue
        typed = ui.ask("Type a name to search for, or press Enter to stop: ")
        if not typed:
            raise RenamerError("No show chosen. Nothing was changed.")
        query = typed
    url = f"{TVMAZE}/shows/{chosen['id']}?embed=episodes"
    ui.detail(f"TVmaze request: {url}")
    info, titles = parse_tvmaze_show(get(url, what=f"getting the episodes of {chosen.get('name', 'the show')}"))
    seasons = sorted({s for s, _ in titles})
    ui.detail(f"TVmaze answered {get.took()}: {info.name}, {_plural(len(titles), 'episode')} in "
              f"{_plural(len(seasons), 'season')}"
              + (f" ({seasons[0]}–{seasons[-1]})" if len(seasons) > 1 else ""))
    specials: list[EpisodeInfo] = []
    if with_specials:
        url = f"{TVMAZE}/shows/{chosen['id']}/episodes?specials=1"
        ui.detail(f"TVmaze request: {url}")
        specials = parse_specials(get(url, what="getting the specials"))
        ui.detail(f"TVmaze answered {get.took()}: {_plural(len(specials), 'special')}")
    return info, titles, specials, query


# ---------------------------------------- seasons and numbering from the sources (1.2.0)

@dataclass
class WikiSeason:
    number: int
    episodes: int | None = None
    name: str = ""
    year: str = ""


def _wiki_clean(text: str) -> str:
    text = re.sub(r"<[^>]*>|\{\{[^}]*\}\}", "", text)
    text = re.sub(r"\[\[(?:[^\]|]*\|)?([^\]]*)\]\]", r"\1", text)
    return text.replace("''", "").strip()


def parse_series_overview(body: str) -> list[WikiSeason]:
    """The seasons in a Wikipedia "Series overview" table: their sizes, and names in an arc column
    (Example Show) or in the link to the section ("#Season 1: Season Name (2004–2005)")."""
    fields = dict(re.findall(r"\|\s*(\w+?)\s*=[ \t]*([^\n]*)", body))
    numbers = sorted({int(m.group(1)) for k in fields if (m := re.fullmatch(r"(?:link|auxA|episodes|start)(\d+)A?", k))})
    rows = []
    for n in numbers:
        count = fields.get(f"episodes{n}", "").strip()
        parts = [v.strip() for k, v in fields.items() if re.fullmatch(rf"episodes{n}[A-Z]", k)]
        episodes = int(count) if count.isdigit() else (
            sum(int(v) for v in parts if v.isdigit()) or None)
        name = _wiki_clean(fields.get(f"auxA{n}", ""))
        if not name:
            anchor = _wiki_clean(fields.get(f"link{n}", "")).rpartition("#")[2]
            if m := re.match(r"(?i)season \d+\s*(?::\s*|\")(.*?)\"?\s*(?:\(.*)?$", anchor):
                name = m.group(1)
        start = fields.get(f"start{n}") or fields.get(f"start{n}A") or fields.get(f"released{n}") or ""
        year = m.group(1) if (m := re.search(r"\|((?:19|20)\d\d)\|", start)) else ""
        rows.append(WikiSeason(n, episodes, name.strip(), year))
    return rows


def wikipedia_seasons(get: Getter, show: str, year: str) -> list[WikiSeason]:
    """The season table of a show's "List of … episodes" article; [] when there's none, or it's about
    another show of that name (List of Example ½ episodes is the 1989 series, not the 2024 one)."""
    pages = [f"List of {show} episodes"]
    if year:
        pages.append(f"List of {show} ({year} TV series) episodes")
    for page in pages:
        url = f"{WIKIPEDIA}?action=parse&prop=wikitext&format=json&redirects=1&page={urllib.parse.quote(page)}"
        try:
            data = get(url, "Wikipedia", hint="", what=f'reading "{page}"')
        except RenamerError as e:
            debug(f"Wikipedia seasons: {e}")
            return []
        text = ((data.get("parse") or {}).get("wikitext") or {}).get("*", "") if isinstance(data, dict) else ""
        found = re.search(r"\{\{\s*Series overview(.*?)\n\}\}", text, re.S | re.I)
        rows = parse_series_overview(found.group(1)) if found else []
        if rows and (not year or not rows[0].year or abs(int(rows[0].year) - int(year)) <= 1):
            return rows
    return []


def use_overall_numbers(info: ShowInfo, titles: Titles, get: Getter) -> Titles:
    """TVmaze lists some long shows by calendar year (Example Show's "season 2013": #579 - #626). Such a
    show counts its episodes overall, so episode 623 stays 623, and Wikipedia's table gives its
    seasons and arcs: the titles come back keyed as (16, 623) (1.2.0)."""
    seasons = {s for s, _ in titles if s > 0}
    if not seasons or min(seasons) < 1900:
        return titles
    order = sorted(k for k in titles if k[0] > 0)
    rows = wikipedia_seasons(get, info.name, (info.premiered or "")[:4])
    info.overall, info.total = True, len(order)
    if not rows:
        info.notes.append(f"Wikipedia has no season table for {info.name}, so every episode counts as season 1.")
    new: Titles = {k: v for k, v in titles.items() if k[0] == 0}
    row, left = 0, (rows[0].episodes if rows else None)
    for number, key in enumerate(order, 1):
        while rows and left is not None and left <= 0 and row < len(rows) - 1:
            row += 1
            left = rows[row].episodes
        if left is not None:
            left -= 1
        new[(rows[row].number if rows else 1, number)] = titles[key]
    for r in rows:
        if label := season_label(r.name, info.name):
            info.season_names[r.number] = info.season_raw[r.number] = label
    return new


def load_season_names(info: ShowInfo, titles: Titles, get: Getter, ask_wikipedia: bool) -> None:
    """Season names from TVmaze ("Season Two Name"), then Wikipedia for those it leaves empty (1.2.0)."""
    if info.overall or not info.ids.get("tvmaze"):
        return
    try:
        data = get(f"{TVMAZE}/shows/{info.ids['tvmaze']}/seasons", hint="", what="getting the season names")
    except RenamerError as e:
        debug(f"season names: {e}")
        return
    for season in data if isinstance(data, list) else []:
        number, raw = season.get("number"), season.get("name") or ""
        if number and raw:
            info.season_raw[number] = raw
            if label := season_label(raw, info.name):
                info.season_names[number] = label
    numbers = {s for s, _ in titles if s > 0}
    if ask_wikipedia and numbers and not numbers <= set(info.season_names):
        rows = wikipedia_seasons(get, info.name, (info.premiered or "")[:4])
        if {r.number for r in rows} == numbers:   # the same seasons, or the names would land on the wrong ones
            for r in rows:
                if r.number not in info.season_names and (label := season_label(r.name, info.name)):
                    info.season_names[r.number] = label


def named_season(text: str, info: ShowInfo) -> int | None:
    """The season whose name is in a folder or file name: "Example.Show - Season Three Name" is season 3. The
    longest name wins, so "Season Name - Part Two" isn't plain "Season Name"."""
    haystack = normalize_title(text)
    show_key = normalize_title(info.name)
    best: tuple[int, int] | None = None
    for number, raw in info.season_raw.items():
        for name in (raw, info.season_names.get(number, "")):
            key = normalize_title(name)
            if len(key) >= 4 and key != show_key and key in haystack and (not best or len(key) > best[0]):
                best = (len(key), number)
    return best[1] if best else None


_ROMAN = {"I": 1, "II": 2, "III": 3, "IV": 4, "V": 5, "VI": 6}


def _sequel_number(before: str, info: ShowInfo) -> int | None:
    """"Example Show 2" (before the 01 of "Example Show 2 01"): the show's name and a number."""
    if re.search(r"\d", normalize_title(info.name)):
        return None
    m = re.fullmatch(r"(.*\S)\s+(\d|[IVX]{1,3})", before.strip())
    if not m or not same_show_key(normalize_title(m.group(1)) or "-", normalize_title(info.name)):
        return None
    return int(m.group(2)) if m.group(2).isdigit() else _ROMAN.get(m.group(2))


def _special_named(text: str, number: int, specials: list[EpisodeInfo]) -> EpisodeInfo | None:
    """TVmaze's special for "Example Show Director's Cut - 01": a name that starts "Director's Cut - 1 -"."""
    words = readable(text).split()
    for i in range(len(words)):
        key = normalize_title(" ".join(words[i:]))
        if len(key) < 4:
            break
        for sp in specials:
            if (m := re.search(r"(\d+)", sp.title)) and int(m.group(1)) == number \
                    and normalize_title(sp.title[:m.start()]) == key:
                return sp
    return None


def adopt_named_folders(layout: "Layout", info: ShowInfo, titles: Titles, specials: list[EpisodeInfo], get: Getter
                        ) -> bool:
    """Folders of plain-numbered episodes that are seasons though no number says so: "Example.Show - New
    World BD" by the season's name, "[Some Group] Example Show" as the first season when nothing but the
    show's name is left, "Example Show Director's Cut" as specials (1.2.0). True when any were found."""
    if not layout.trusted:
        return False
    found = []
    taken = {n for _, n in layout.seasons}
    show_key = normalize_title(info.name)
    for d in list(layout.ignored):
        if d.parent != layout.show_dir or _SHOW_EXTRAS.fullmatch(d.name):
            continue
        plain = [p for f in _entries(d, dirs=False) if f.suffix.lower() in VIDEO_EXTS and (p := plain_numbers(f.name))]
        if not plain or any(p.special for p in plain):
            continue
        name = readable(show_from_folder(d.name))
        number = named_season(d.name, info)
        if number is None and normalize_title(name) and same_show_key(normalize_title(name), show_key) \
                and 1 not in taken and any(s == 1 for s, _ in titles):
            number = 1
        if number is None:
            if not specials and info.ids.get("tvmaze"):
                try:
                    specials += parse_specials(get(f"{TVMAZE}/shows/{info.ids['tvmaze']}/episodes?specials=1", hint="",
                                                   what="getting the specials"))
                except RenamerError as e:
                    debug(f"specials: {e}")
            if _special_named(name, plain[0].numbers[0], specials):
                number = 0
        if number is not None:
            found.append((d, number))
            if number:
                taken.add(number)
    if not found:
        return False
    paths = {d for d, _ in found}
    ignored, subs = _split_season_subdirs(list(paths))
    layout.ignored = [d for d in layout.ignored if d not in paths] + ignored
    layout.subs.update(subs)
    layout.seasons = sorted(layout.seasons + found, key=lambda s: (s[1], natural_key(s[0].name)))
    layout.all_seasons = [n for _, n in layout.seasons]
    return True


def _set_numbers(g: "Group", season: int, episodes: list[int], plain: Plain | None, how: str) -> None:
    g.season, g.episodes, g.status, g.note = season, episodes, "", ""
    if plain:
        g.file_title, g.file_text = plain.title, plain.title
        if m := _PART_OF.search(g.video.stem):
            g.part = int(m.group(1))
    g.how = how


def _plain_season(g: "Group", info: ShowInfo) -> int | None:
    """The season a plain-numbered file says it's in: its folder, "Season 02" or "S1" in its name, a
    season's name, or a sequel number."""
    if g.folder_season is not None:
        return g.folder_season
    before = g.plain.before
    number = season_from_folder(before) if before else None
    if number:
        return number
    return named_season(f"{before} {g.folder.name}", info) or _sequel_number(before, info)


def settle_numbers(layout: "Layout", groups: list["Group"], titles: Titles, info: ShowInfo, specials: list[EpisodeInfo]
                   ) -> None:
    """Now that TVmaze's list is known: what the numbers in the filenames count. A plain number is
    the season's, or the whole show's when it runs past the season's end ("Season 02/… - 26"); S02E13
    in a 12-episode season carries on from season 1; a release whose seasons split TVmaze's differently
    is counted through (Example Show's S03E01 is TVmaze's S02E08) (1.2.0)."""
    if not titles:
        return
    order = sorted(k for k in titles if k[0] > 0)
    in_season: dict[int, list[int]] = {}
    for s, e in order:
        in_season.setdefault(s, []).append(e)
    for g in groups:
        if g.number_form and not g.status and g.file_code:
            n = g.file_code[0] * 100 + g.file_code[1][0]
            wrong_folder = g.folder_season is not None and g.file_code[0] != g.folder_season
            if info.overall or wrong_folder or ((g.season, g.episodes[0]) not in titles and n <= len(order)):
                g.plain = Plain([n], title=g.file_title)

    plain_groups = [g for g in groups if g.plain and g.status in ("", "UNMATCHED")]
    tops: dict[tuple[Path, int | None], int] = {}
    seasons_of = {id(g): _plain_season(g, info) if not g.plain.special else None for g in plain_groups}
    for g in plain_groups:
        if not g.plain.special:
            key = (g.folder, seasons_of[id(g)])
            tops[key] = max(tops.get(key, 0), *g.plain.numbers)
    for g in plain_groups:
        numbers, season = g.plain.numbers, seasons_of[id(g)]
        if g.plain.special or season == 0:
            sp = _special_named(f"{g.folder.name} {g.plain.before}", numbers[0], specials) \
                or _special_named(readable(show_from_folder(g.folder.name)), numbers[0], specials)
            if sp and not g.plain.special:
                _set_numbers(g, 0, numbers[:1], g.plain, f"special {numbers[0]}, by its folder's name: {sp.title}")
                g.overrides[numbers[0]] = sp
            else:
                g.status, g.note = "UNMATCHED", "a special or extra with only a number; left alone"
            continue
        listed = in_season.get(season or -1, [])
        if season and listed and tops[(g.folder, season)] <= (max(listed) if info.overall else len(listed)) \
                and (info.overall or all((season, n) in titles for n in numbers)):
            if all((season, n) in titles for n in numbers):
                keys = [(season, n) for n in numbers]
            else:
                keys = [(season, listed[0] + n - 1) for n in numbers]
        elif season and info.overall and all(n <= len(listed) for n in numbers):
            keys = [(season, listed[0] + n - 1) for n in numbers]   # Example Show's "Season 16/… - 01"
        else:
            keys = [order[n - 1] if n <= len(order) else None for n in numbers]
        if None in keys or len({k[0] for k in keys}) > 1:
            g.status, g.note = "UNMATCHED", (f"TVmaze's list has {len(order)} episodes, so episode "
                                             f"{numbers[-1]} isn't in it" if numbers[-1] > len(order)
                                             else "its episodes are in different seasons on TVmaze")
            continue
        new = [k[1] for k in keys]
        _set_numbers(g, keys[0][0], new, g.plain, f"{_code(keys[0][0], new)}, from the plain number {numbers[0]}")
        if new != numbers:
            g.warns_quiet.append(f"overall episode {numbers[0]}")

    coded = [g for g in groups if not g.status and g.file_code and not g.plain and g.season and g.season > 0]
    if info.overall:
        for g in coded:
            listed = in_season.get(g.season, [])
            if listed and not all((g.season, e) in titles for e in g.episodes) and all(e <= len(listed) for e in g.episodes):
                g.episodes = [listed[0] + e - 1 for e in g.episodes]   # S16E05: the fifth of season 16
                g.how += f"; season {g.season}'s episode, so {_code(g.season, g.episodes)} overall"
        return
    if _renumber_split_seasons(coded, order, in_season):
        return
    # Only when TVmaze's list has no gaps up to that season, so a missing number isn't taken for a count.
    whole = order == [(s, e) for s in sorted(in_season) for e in range(1, len(in_season[s]) + 1)]
    for g in coded:
        if not whole or all((g.season, e) in titles for e in g.episodes):
            continue
        keys = [order[e - 1] if e <= len(order) else None for e in g.episodes]
        if None not in keys and all(k[0] == g.season for k in keys):   # S02E13 carries on from a 12-episode season 1
            old = _code(g.season, g.episodes)
            g.episodes = [k[1] for k in keys]
            g.how += f"; {old} counts on from the seasons before it"
            g.warns_quiet.append(f"the filename says {old}, counting on from season {g.season - 1}")


def _renumber_split_seasons(coded: list["Group"], order: list[tuple[int, int]], in_season: dict[int, list[int]]) -> bool:
    """A release whose seasons add up to TVmaze's but split them differently: counted through. Every
    boundary of one must be a boundary of the other, so it never fires on seasons that merely differ."""
    mine: dict[int, set[int]] = {}
    for g in coded:
        mine.setdefault(g.season, set()).update(g.episodes)
    if not mine or sum(len(v) for v in mine.values()) != len(order) or any(v != set(range(1, len(v) + 1)) for v in mine.values()):
        return False
    start, total = {}, 0
    for season in sorted(mine):
        start[season] = total
        total += len(mine[season])
    file_ends = {start[s] + len(mine[s]) for s in mine}
    source_ends, total = set(), 0
    for season in sorted(in_season):
        total += len(in_season[season])
        source_ends.add(total)
    if file_ends == source_ends or not (file_ends < source_ends or source_ends < file_ends):
        return False
    for g in coded:
        keys = [order[start[g.season] + e - 1] for e in g.episodes]
        new_season, new = keys[0][0], [k[1] for k in keys]
        if (new_season, new) != (g.season, g.episodes):
            g.renumbered = (f"NOTE: renumbered; the filename says {_code(g.season, g.episodes)}, but this release splits "
                            f"its seasons differently from TVmaze, where it's {_code(new_season, new)}")
            g.how += f"; {_code(new_season, new)} counted through the seasons"
            g.season, g.episodes = new_season, new
    return True


def settle_show(args, layout: "Layout", groups: list["Group"], not_handled: list, ui: UI, info: ShowInfo, titles: Titles,
                specials: list[EpisodeInfo], get: Getter, only: Path | None = None) -> tuple[list["Group"], list]:
    """Everything that needs the show's episode list before titles are compared (1.2.0)."""
    if not getattr(args, "names", None):
        needed = getattr(args, "fix_folders", False) or any(g.plain for g in groups) or any(
            d.parent == layout.show_dir and not _SHOW_EXTRAS.fullmatch(d.name) for d in layout.ignored)
        if needed:
            load_season_names(info, titles, get, getattr(args, "fix_folders", False))
        if adopt_named_folders(layout, info, titles, specials, get):
            groups, not_handled = collect_groups(layout, ui, only)
            if only:
                groups = [g for g in groups if g.video == only]
    settle_numbers(layout, groups, titles, info, specials)
    return groups, not_handled


# --------------------------------------------------------------- .nfo

def _xml(tag: str, value, attrs: str = "") -> str:
    return f"    <{tag}{attrs}>{xml_escape(str(value))}</{tag}>"


def episode_nfo(show: ShowInfo, season: int, episodes: list[int], infos: list[EpisodeInfo | None]) -> bytes:
    """One <episodedetails> block per episode; Kodi reads several blocks for a multi-episode file."""
    blocks = ['<?xml version="1.0" encoding="UTF-8" standalone="yes"?>']
    for number, info in zip(episodes, infos):
        lines = ["<episodedetails>"]
        if info and info.title:
            lines.append(_xml("title", info.title))
        lines.append(_xml("showtitle", show.name))
        lines.append(_xml("season", season))
        lines.append(_xml("episode", number))
        if info and info.aired:
            lines.append(_xml("aired", info.aired))
        if info and info.plot:
            lines.append(_xml("plot", info.plot))
        if info and info.tvmaze_id:
            lines.append(_xml("uniqueid", info.tvmaze_id, ' type="tvmaze" default="true"'))
        lines.append("</episodedetails>")
        blocks.append("\n".join(lines))
    return ("\n".join(blocks) + "\n").encode("utf-8")


def tvshow_nfo(show: ShowInfo) -> bytes:
    lines = ['<?xml version="1.0" encoding="UTF-8" standalone="yes"?>', "<tvshow>", _xml("title", show.name)]
    if show.year:
        lines.append(_xml("year", show.year))
    if show.premiered:
        lines.append(_xml("premiered", show.premiered))
    if show.plot:
        lines.append(_xml("plot", show.plot))
    lines += [_xml("genre", g) for g in show.genres]
    for kind in ("tvmaze", "imdb", "tvdb"):
        if kind in show.ids:
            default = ' default="true"' if kind == "tvmaze" else ""
            lines.append(_xml("uniqueid", show.ids[kind], f' type="{kind}"{default}'))
    lines.append("</tvshow>")
    return ("\n".join(lines) + "\n").encode("utf-8")


# --------------------------------------------------------------- terminal

_COLORS = {"OK": "32", "MOVE": "32", "GUESS": "33", "MERGE": "32", "UNDO": "32", "CREATE": "32", "RESTORE": "32", "RENUMBERED": "36", "ARCHIVE": "36",
           "TAG": "36",
           "WARN": "33", "OTHER SHOW": "35",
           "LOOSE": "33", "JUNK": "33", "DELETE": "33", "REMOVE": "33", "SKIP": "2", "SKIPPED": "2",
           "IGNORED": "2", "KEEP": "2", "GONE": "2", "DUPLICATE": "31", "CONFLICT": "31", "UNMATCHED": "35"}


class _Page:
    shown = False


class UI:
    """All prompting and printing, so tests can script the answers. With --verbose it
    also copies everything to a log file in ~/.logs."""

    def __init__(self, interactive: bool, out=None, input_fn: Callable[[str], str] = input,
                 color: bool | None = None, verbose: bool = False, log_dir: Path | None = None, err=None,
                 pager: bool = True, debug_dir: Path | None | str = "default"):
        global _debug_ui
        self.interactive = interactive
        self.pager = pager
        self.changing = False          # set once changes start, for the Ctrl-C message
        self._page: list[str] | None = None
        self._log_off = False
        self.early_name = ""   # names the debug log of a run that ends before it has a show (help, errors)
        self.out = out or sys.stdout
        self.err = err or sys.stderr
        self.input_fn = input_fn
        self.tty = bool(getattr(self.out, "isatty", lambda: False)())
        if color is None:
            color = self.tty and "NO_COLOR" not in os.environ
        self.color = color
        self.verbose = verbose
        self.log_dir = log_dir or LOG_DIR
        self.log_path: Path | None = None
        self._log_file = None
        self._log_buffer: list[str] = []   # held until the show name, and so the log's name, is known
        self._log_failed = False
        self._stamp = time.strftime("%Y-%m-%d_%H%M%S")
        # The debug log: everything, on every run, while 0.8.x is tested.
        self.debug_dir = DEBUG_LOG_DIR if debug_dir == "default" else debug_dir
        self.debug_path: Path | None = None
        self._debug_file = None
        self._debug_buffer: list[str] = []
        self._debug_failed = self.debug_dir is None
        self._started = time.monotonic()
        self.responses: list[dict] = []   # TVmaze and Wikipedia answers, saved beside the debug log
        if self.debug_dir is not None:
            _debug_ui = self

    def _log(self, text: str) -> None:
        if not self.verbose or self._log_failed or self._log_off:
            return
        line = _ANSI.sub("", text)
        if self._log_file:
            self._log_file.write(line + "\n")
            self._log_file.flush()
        else:
            self._log_buffer.append(line)

    def say(self, text: str = "") -> None:
        if self._page is not None:
            self._page.append(text)
        else:
            print(text, file=self.out)
        self._log(text)
        self.debug(text)

    def debug(self, text: str) -> None:
        """A line for the debug log only, stamped with the seconds since the run started."""
        if self._debug_failed:
            return
        stamp = f"[{time.monotonic() - self._started:9.3f}] "
        lines = [stamp + line for line in _ANSI.sub("", str(text)).split("\n")]
        if self._debug_file:
            try:
                self._debug_file.write("\n".join(lines) + "\n")
                self._debug_file.flush()
            except OSError:
                self._debug_failed = True
        else:
            self._debug_buffer.extend(lines)

    def _start_debug(self, name: str) -> None:
        if self._debug_failed or self._debug_file:
            return
        try:
            self.debug_dir.mkdir(parents=True, exist_ok=True)
            self.debug_path = self.debug_dir / f"renamer_{name or 'run'}_{self._stamp}.log"
            self._debug_file = open(self.debug_path, "a", encoding="utf-8")
        except OSError as e:
            self._debug_failed = True
            print(f"renamer: can't write the debug log in {self.debug_dir} ({e.strerror}); "
                  "continuing without it.", file=self.err)
            return
        self._debug_file.write("\n".join(self._debug_buffer) + "\n")
        self._debug_buffer = []
        self._debug_file.flush()

    def _close_debug(self, fallback_name: str) -> None:
        self._start_debug(fallback_name)
        if not self._debug_file:
            return
        if self.responses:
            responses = self.debug_path.with_name(self.debug_path.stem + "_responses.json")
            try:
                responses.write_text(json.dumps(self.responses, indent=1, ensure_ascii=False), encoding="utf-8")
                self.debug(f"Saved {len(self.responses)} TVmaze/Wikipedia answers to {responses}")
            except OSError as e:
                self.debug(f"Couldn't save the answers to {responses}: {e}")
        self._debug_file.close()
        self._debug_file = None
        self._debug_failed = True   # closed for good; later lines have nowhere to go
        print(f"Debug log: {self.debug_path}", file=self.err)

    @contextlib.contextmanager
    def quiet_log(self):
        """Print without copying to the log (for lines the log already has)."""
        self._log_off = True
        try:
            yield
        finally:
            self._log_off = False

    @contextlib.contextmanager
    def paged(self, title: str = "renamer preview, q to go on to the question"):
        """Collect what's said and show it in a pager when it's taller than the terminal.
        The yielded object's .shown says afterwards whether the pager was used."""
        page = _Page()
        self._page = []
        try:
            yield page
        finally:
            lines, self._page = self._page, None
            page.shown = self._show_paged(lines, title)

    def _show_paged(self, lines: list[str], title: str) -> bool:
        rows = shutil.get_terminal_size((80, 24)).lines
        if not (self.pager and self.tty and self.interactive) or len(lines) <= rows - 4:
            for line in lines:
                print(line, file=self.out)
            return False
        env = dict(os.environ)
        env.setdefault("LESS", "-R")   # keep the colours
        cmd = shlex.split(os.environ.get("PAGER") or "") or ["less", "-R", "-Ps" + title]
        try:
            self.out.flush()
            subprocess.run(cmd, input="\n".join(lines) + "\n", text=True, env=env, check=False)
        except OSError:
            for line in lines:
                print(line, file=self.out)
            return False
        return True

    def detail(self, text: str) -> None:
        """A line shown only with --verbose. The debug log always gets it."""
        if self.verbose:
            self.say(text)
        else:
            self.debug("(verbose) " + text)

    def warn(self, text: str) -> None:
        self.say(self.paint("Warning: ", "WARN") + text)

    def error(self, text: str) -> None:
        print(text, file=self.err)
        self._log(text)
        self.debug(text)

    def ask(self, prompt: str, default: str = "") -> str:
        """The typed answer, or the default when Enter is pressed or nobody can answer."""
        if not self.interactive:
            self.debug(f"(not interactive) {prompt}-> {default!r}")
            return default
        try:
            answer = self.input_fn(prompt)
        except EOFError:
            answer = ""
            self.debug("(end of input)")
        self.debug(f"ASKED {prompt!r} ANSWERED {answer!r}")
        # Keys like Page Down or the arrows typed at the prompt arrive as escape codes ("y\x1b[6~")
        # and would turn a yes into a no (1.0.0, from a real run).
        answer = _KEY_CODES.sub("", answer)
        self._log(prompt + answer)
        return answer.strip() or default

    def paint(self, text: str, status: str) -> str:
        code = _COLORS.get(status)
        return f"\033[{code}m{text}\033[0m" if self.color and code else text

    def start_log(self, name: str) -> None:
        """Open ~/.logs/renamer_<name>_<date>_<time>.log and write what's been held so far."""
        self._start_debug(name)
        if not self.verbose or self._log_file or self._log_failed:
            return
        try:
            self.log_dir.mkdir(parents=True, exist_ok=True)
            self.log_path = self.log_dir / f"renamer_{name or 'run'}_{self._stamp}.log"
            self._log_file = open(self.log_path, "a", encoding="utf-8")
        except OSError as e:
            self._log_failed = True
            print(f"renamer: can't write the log file in {self.log_dir} ({e.strerror}); "
                  "continuing without it.", file=self.err)
            return
        for line in self._log_buffer:
            self._log_file.write(line + "\n")
        self._log_buffer = []
        self._log_file.flush()

    def close_log(self, fallback_name: str) -> None:
        if self.verbose:
            self.start_log(fallback_name)
            if self._log_file:
                self.say(f"Log saved to {self.log_path}")
                self._log_file.close()
                self._log_file = None
        self._close_debug(fallback_name)


_debug_ui: UI | None = None


def debug(text: str) -> None:
    """A line for the debug log, from code that has no UI at hand (tools, file reading)."""
    if _debug_ui is not None:
        _debug_ui.debug(text)


def debug_run_start(ui: UI, argv: list[str]) -> None:
    """Everything about the run that helps with fixing a bug later (debug log)."""
    if ui._debug_failed:
        return
    script = Path(__file__).resolve()
    try:
        digest = hashlib.sha256(script.read_bytes()).hexdigest()[:16]
    except OSError:
        digest = "unreadable"
    ui.debug(f"renamer {VERSION}, {script}, sha256 {digest}")
    ui.debug(f"command: renamer {shlex.join(argv)}")
    ui.debug(f"current folder: {os.getcwd()}")
    ui.debug(f"python {sys.version.split()[0]}, {platform.platform()}")
    for tool, flag in ((FFPROBE, "-version"), (FFMPEG, "-version"), (MKVMERGE, "--version"),
                       (MKVPROPEDIT, "--version"), (MKVEXTRACT, "--version")):
        where = shutil.which(tool)
        version = ""
        if where:
            try:
                out = subprocess.run([tool, flag], capture_output=True, text=True, timeout=10).stdout
                version = (out.splitlines() or [""])[0]
            except (OSError, subprocess.SubprocessError) as e:
                version = f"(couldn't ask: {e})"
        ui.debug(f"tool {tool}: {where or 'not installed'} {version}")
    size = shutil.get_terminal_size((0, 0))
    ui.debug(f"stdin terminal {sys.stdin.isatty()}, stdout terminal {sys.stdout.isatty()}, "
             f"size {size.columns}x{size.lines}, interactive {ui.interactive}, pager {ui.pager}")
    ui.debug("environment: " + ", ".join(f"{k}={os.environ.get(k)!r}" for k in
                                         ("PAGER", "LESS", "LANG", "LC_ALL", "TERM", "NO_COLOR", "SHELL")))


_OWN_HIDDEN = (".nfo", ".junk", ".duplicates")   # renamer's own hidden folders, listed in full


def looks_like_show(root: Path) -> bool:
    """Whether a folder holds something renamer could work on: a season folder, or a video with
    an episode number in it or in one of its folders. Looks two levels deep at most."""
    try:
        entries = list(os.scandir(root))
    except OSError:
        return False
    for e in entries:
        if e.name.startswith("."):
            continue
        if e.is_dir():
            if season_from_folder(e.name) is not None:
                return True
            try:
                inner = list(os.scandir(e.path))
            except OSError:
                continue
            if any(not f.name.startswith(".") and f.is_file() and Path(f.name).suffix.lower() in VIDEO_EXTS
                   and (parse_episode(f.name) or plain_numbers(f.name)) for f in inner):
                return True
        elif Path(e.name).suffix.lower() in VIDEO_EXTS and (parse_episode(e.name) or plain_numbers(e.name)):
            return True
    return False


def debug_tree(ui: UI, root: Path, limit: int = 5000) -> None:
    """The files and folders under the path, with size and date, for the debug log. Only a folder
    that looks like a show is listed in full; hidden folders other than renamer's own are named,
    never opened (0.8.1)."""
    if not root.exists():
        ui.debug(f"tree: {root} doesn't exist")
        return
    if root.is_file():
        st = root.stat()
        ui.debug(f"tree: {root} (a file, {st.st_size} bytes, {time.strftime('%Y-%m-%d %H:%M', time.localtime(st.st_mtime))})")
        return
    if not looks_like_show(root):
        names = sorted(os.listdir(root), key=natural_key) if os.access(root, os.R_OK) else []
        ui.debug(f"tree: {root} doesn't look like a show; its top level only: {len(names)} entries: "
                 + ", ".join(n + ("/" if (root / n).is_dir() else "") for n in names[:200]))
        return
    ui.debug(f"tree of {root}:")
    count = 0
    for folder, dirs, files in os.walk(root):
        hidden = sorted(d for d in dirs if d.startswith(".") and d not in _OWN_HIDDEN)
        dirs[:] = sorted((d for d in dirs if d not in hidden), key=natural_key)
        rel = os.path.relpath(folder, root)
        for d in hidden:
            ui.debug(f"  {'' if rel == '.' else rel + '/'}{d}/  (hidden folder, not listed)")
        for name in sorted(files, key=natural_key):
            count += 1
            if count > limit:
                ui.debug(f"tree: stopped after {limit} entries")
                return
            try:
                st = os.lstat(os.path.join(folder, name))
                info = f"{st.st_size} bytes, {time.strftime('%Y-%m-%d %H:%M', time.localtime(st.st_mtime))}"
            except OSError as e:
                info = f"({e.strerror})"
            ui.debug(f"  {'' if rel == '.' else rel + '/'}{name}  {info}")
        if not files and not dirs:
            ui.debug(f"  {rel}/  (empty)")


# ------------------------------------------------------------------ layout

def _entries(folder: Path, dirs: bool) -> list[Path]:
    """Visible files or folders in a folder, naturally sorted. Hidden ones are never touched."""
    with os.scandir(folder) as it:
        found = [Path(e.path) for e in it if not e.name.startswith(".") and e.is_dir() == dirs]
    return sorted(found, key=lambda p: natural_key(p.name))


def _hidden(folder: Path) -> list[str]:
    return sorted(n for n in os.listdir(folder)
                  if n.startswith(".") and n not in (UNDO_LOG, NFO_DIR, JUNK_DIR, DUPES_DIR)
                  and not n.endswith(".nfo"))


_SUBS_FOLDER = re.compile(r"subs|subtitles", re.I)


@dataclass
class Layout:
    show_dir: Path
    seasons: list[tuple[Path, int]]   # season folders being processed, and their numbers
    loose_dir: Path | None            # the show folder, when videos directly inside it are looked at
    ignored: list[Path]
    all_seasons: list[int] = field(default_factory=list)   # every season folder in the show folder
    trusted: bool = True              # False: the folder above a season folder doesn't look like a show folder
    subs: dict[Path, Path] = field(default_factory=dict)  # season folder -> its Subs folder

    @property
    def home(self) -> Path:
        """Where .nfo/ and .junk/ go: the show folder, or the season folder when there's no show folder."""
        return self.show_dir if self.trusted else self.seasons[0][0]

    def scan_roots(self) -> list[tuple[Path, bool]]:
        """Folders searched for old .nfo files and junk, and whether to search their subfolders."""
        if not self.trusted:
            return [(self.seasons[0][0], True)]
        if self.loose_dir:
            return [(self.show_dir, True)]
        return [(self.show_dir, False)] + [(d, True) for d, _ in self.seasons]


def _split_season_subdirs(season_dirs: list[Path]) -> tuple[list[Path], dict[Path, Path]]:
    """A season folder's subfolders: its Subs folder is handled, anything else is ignored."""
    ignored, subs = [], {}
    for season_dir in season_dirs:
        for d in _entries(season_dir, dirs=True):
            if _SUBS_FOLDER.fullmatch(d.name) and season_dir not in subs:
                subs[season_dir] = d
            else:
                ignored.append(d)
    return ignored, subs


def find_layout(path: Path) -> Layout:
    """Work out the show and season folders from where folders sit (folder roles)."""
    subdirs = _entries(path, dirs=True)
    seasons = [(d, n) for d in subdirs if (n := season_from_folder(d.name)) is not None]
    # "Example Show Season 2/" with its episodes and a Specials/ folder: one season, not a show folder (1.2.0).
    own_season = (season_from_folder(path.name) or 0) > 0 and bool(seasons) and all(n == 0 for _, n in seasons) \
        and any(f.suffix.lower() in VIDEO_EXTS for f in _entries(path, dirs=False))
    if seasons and not own_season:
        season_paths = {d for d, _ in seasons}
        ignored, subs = _split_season_subdirs([d for d, _ in seasons])
        ignored = [d for d in subdirs if d not in season_paths] + ignored
        seasons.sort(key=lambda s: (s[1], natural_key(s[0].name)))
        return Layout(path, seasons, path, ignored, [n for _, n in seasons], subs=subs)
    number = season_from_folder(path.name)
    if number is not None:
        parent = path.parent
        siblings = _entries(parent, dirs=True)
        sibling_seasons = [n for d in siblings if (n := season_from_folder(d.name)) is not None]
        # Anything else up there (other shows, a whole TV library) means the folder above is
        # not this show's folder, so it must never be renamed or get a tvshow.nfo.
        trusted = not (parent / GROUP_MARKER).is_file() and all(
            season_from_folder(d.name) is not None or _SHOW_EXTRAS.fullmatch(d.name) for d in siblings)
        ignored, subs = _split_season_subdirs([path])
        if trusted:
            return Layout(parent, [(path, number)], None, ignored, sibling_seasons, True, subs)
        # A season folder with no show folder around it (one season's release folder in a TV
        # library): it's its own show folder, so the undo log, .nfo/ and .junk/ stay inside it.
        return Layout(path, [(path, number)], None, ignored, [number], False, subs)
    return Layout(path, [], path, subdirs)


def find_downloads(root: Path) -> list[Path]:
    """Every unfinished qBittorrent download (.!qb) anywhere under root."""
    found = []
    for folder, subdirs, files in os.walk(root):
        # qBittorrent keeps deselected files in .unwanted/; they never finish, so they don't count.
        subdirs[:] = [d for d in subdirs if d != ".unwanted"]
        found += [Path(folder, f) for f in files if f.lower().endswith(DOWNLOAD_EXTS)]
    return sorted(found)


def _walk_files(layout: Layout) -> list[tuple[Path, bool]]:
    """Every file the .nfo sweep and --clean look at, and whether it sits in an extras folder.
    renamer's own .nfo/ and .junk/ folders and other hidden folders are skipped."""
    found: list[tuple[Path, bool]] = []
    seen: set[Path] = set()
    for root, recurse in layout.scan_roots():
        stack = [(root, False)]
        while stack:
            folder, in_extras = stack.pop()
            with os.scandir(folder) as it:
                entries = sorted(it, key=lambda e: natural_key(e.name))
            for e in entries:
                path = Path(e.path)
                if e.is_dir():
                    if recurse and not e.name.startswith(".") and path not in seen:
                        seen.add(path)
                        stack.append((path, in_extras or bool(_EXTRAS_FOLDER.fullmatch(e.name))))
                elif path not in seen:
                    seen.add(path)
                    found.append((path, in_extras))
    return found


# ---------------------------------------------------------------- planning

@dataclass
class Group:
    """A video plus everything that is renamed along with it."""
    folder: Path
    video: Path
    folder_season: int | None = None
    season: int | None = None
    episodes: list[int] = field(default_factory=list)
    file_code: tuple[int, list[int]] | None = None   # the numbers in the filename, before any --renumber
    file_title: str = ""             # the title written in the filename, if any
    file_text: str = ""              # everything after the filename's SxxExx, for "(aka …)"
    part: int | None = None          # "Part N of M"
    by_order: bool = False
    how: str = ""                    # for --verbose: how the season and episode were found
    size: int = 0
    mtime: float = 0.0
    status: str = ""                 # set once the group is SKIPPED, UNMATCHED, LOOSE, DUPLICATE or CONFLICT
    note: str = ""
    companions: list[tuple[Path, str]] = field(default_factory=list)   # (file, text after the video's stem)
    overrides: dict[int, EpisodeInfo] = field(default_factory=dict)    # episode -> title used instead of the source's
    renumbered: str = ""             # the NOTE shown when --renumber changed this file's number
    plain: Plain | None = None       # only a plain number in its name: settled once TVmaze's list is known (1.2.0)
    number_form: bool = False        # file_code came from a bare number ("Show - 205 - Title")
    warns_quiet: list[str] = field(default_factory=list)   # shown beside the new name without making it a WARN
    infos: list[EpisodeInfo | None] = field(default_factory=list)
    missing: list[int] = field(default_factory=list)
    warns: list[str] = field(default_factory=list)
    moves: list[tuple[Path, str]] = field(default_factory=list)       # (file, new name), video first


@dataclass
class Op:
    """One change. Paths are relative to the show folder."""
    kind: str            # rename, archive, junk, delete, mkdir, create, rename_show or tag
    src: str = ""
    dst: str = ""
    content: bytes = b""
    is_dir: bool = False
    junk: bool = False   # a folder made only for --clean's .junk/
    group: int | None = None   # the video this change belongs to; skipping a busy video skips them all
    tags: dict | None = None   # kind "tag": what write_tags changes, and the old values for --undo


@dataclass
class Row:
    status: str
    old: str = ""
    new: str = ""
    note: str = ""
    details: list[str] = field(default_factory=list)   # shown only with --verbose
    values: list[tuple[str, str, str | None]] = field(default_factory=list)   # TAG: (label, new, old)


@dataclass
class Plan:
    sections: dict[str, list[Row]] = field(default_factory=dict)
    folder_rows: list[Row] = field(default_factory=list)
    ignored: list[str] = field(default_factory=list)
    not_handled: list[tuple[str, str]] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    details: list[str] = field(default_factory=list)
    ops: list[Op] = field(default_factory=list)


def _ask_skip_sample(ui: UI, video: Path) -> bool:
    answer = ui.ask(f'"{video.name}" has "sample" in its name.\nSkip it? [Y/n]: ', "y")
    return answer.lower() not in ("n", "no")


def collect_groups(layout: Layout, ui: UI, only: Path | None = None) -> tuple[list[Group], list[tuple[Path, str]]]:
    """Find every video and give it a season and episodes. Also returns the
    files left alone, with the reason, for --verbose. With only (renamer meta on one file),
    the sample question is asked about that file alone; other samples are skipped silently."""
    folders: list[tuple[Path, int | None]] = list(layout.seasons)
    if layout.loose_dir:
        folders.append((layout.loose_dir, None))
    groups: list[Group] = []
    not_handled: list[tuple[Path, str]] = []
    for folder, season in folders:
        files = _entries(folder, dirs=False)
        videos = [f for f in files if f.suffix.lower() in VIDEO_EXTS]
        others = [f for f in files if f.suffix.lower() not in VIDEO_EXTS]
        folder_groups: list[Group] = []
        by_order: list[Group] = []
        loose = folder == layout.loose_dir and bool(layout.seasons)
        for video in videos:
            stat = video.stat()
            g = Group(folder=folder, video=video, folder_season=season, size=stat.st_size, mtime=stat.st_mtime)
            folder_groups.append(g)
            if loose:
                # A video next to season folders is left alone; it belongs in one of them.
                g.status, g.note = "LOOSE", "in the show folder, not a season folder; left alone"
                continue
            # Asked before numbering, so a skipped sample never takes an episode number.
            if _SAMPLE.search(video.stem) and (only not in (None, video) or _ask_skip_sample(ui, video)):
                g.status, g.note = "SKIPPED", "sample; you chose to skip it"
                continue
            parsed = parse_episode(video.name, season)
            if parsed:
                g.season, g.episodes = parsed
                g.file_code = (parsed[0], list(parsed[1]))
                g.file_title, g.part = title_from_filename(video.name, season)
                g.file_text = text_after_code(video.name, season)
                g.how = _code(g.season, g.episodes) + " from the filename"
                g.number_form = not _episode_match(video.stem)
            elif plain := plain_numbers(video.name):
                g.plain = plain
                g.status, g.note = "UNMATCHED", "only a plain episode number, and no list to compare it with"
            elif season is not None:
                by_order.append(g)
            else:
                g.status, g.note = "UNMATCHED", "no season/episode found"
        if by_order and any(g.file_code or g.plain for g in folder_groups):
            # Mixed with real episodes (e.g. movies or extras in a season folder): numbering these by
            # sort order would collide with the real ones, so they're left alone.
            for g in by_order:
                g.status, g.note = "UNMATCHED", "no season/episode in its name, unlike the other files here"
            by_order = []
        for number, g in enumerate(by_order, 1):
            g.season, g.episodes, g.by_order = season, [number], True
            g.how = f"numbered by sort order ({number} of {len(by_order)}); season {season} from the folder name"
        not_handled += _attach_companions(folder_groups, others)
        not_handled += [(folder / n, "hidden file") for n in _hidden(folder)]
        groups += folder_groups
    debug(f"layout: show folder {layout.show_dir}, trusted {layout.trusted}, loose {layout.loose_dir}, "
          f"seasons {[(str(d), n) for d, n in layout.seasons]}, all seasons {layout.all_seasons}, "
          f"ignored {[str(d) for d in layout.ignored]}, subs {[(str(a), str(b)) for a, b in layout.subs.items()]}")
    for g in groups:
        debug(f"group {g.video}: season {g.season} episodes {g.episodes} folder season {g.folder_season} "
              f"file code {g.file_code} title {g.file_title!r} part {g.part} by order {g.by_order} "
              f"status {g.status!r} note {g.note!r} how {g.how!r} size {g.size} "
              f"companions {[(str(p), t) for p, t in g.companions]}")
    for path, reason in not_handled:
        debug(f"not handled: {path} ({reason})")
    return groups, not_handled


def _attach_companions(groups: list[Group], others: list[Path]) -> list[tuple[Path, str]]:
    """Subtitles named after a video move with it. The longest matching stem wins. Returns
    the files that belong to no video. .nfo files are handled by the .nfo sweep."""
    leftover = []
    for f in others:
        ext = f.suffix.lower()
        if ext == ".nfo":
            continue
        if ext not in SUB_EXTS:
            leftover.append((f, "junk; --clean moves it to .junk/" if is_junk(f) else "not a video or subtitle"))
            continue
        best = None
        for g in groups:
            stem = g.video.stem
            if f.name.startswith(stem + ".") and (best is None or len(stem) > len(best.video.stem)):
                best = g
        if best is None:
            leftover.append((f, "subtitle with no matching video"))
        else:
            best.companions.append((f, f.name[len(best.video.stem):]))
    return leftover


def resolve_titles(groups: list[Group], titles: Titles, specials: list[EpisodeInfo],
                   from_tvmaze: bool, renumber: bool) -> int:
    """Compare each filename's own title with the title source.

    - A file with no title in its name takes the source's title for its number.
    - A filename title that matches the source's title for that number changes nothing.
    - A filename title that exactly matches TVmaze's title for another number is renumbered
      with --renumber, and otherwise keeps its number and title, with a NOTE.
    - Any other mismatch keeps the filename's title, with a NOTE.
    - Specials (S00) are matched against TVmaze's specials by title only.
    Returns how many files would be renumbered by --renumber."""
    index: dict[str, list[tuple[int, int]]] = {}
    for key, info in titles.items():
        if key[0] > 0 and normalize_title(info.title):
            index.setdefault(normalize_title(info.title), []).append(key)
    special_index = {normalize_title(sp.title): sp for sp in specials if normalize_title(sp.title)}
    suggested = 0
    for g in groups:
        if g.status or not g.file_title:
            continue
        if len(g.episodes) > 1:
            pieces = re.split(r"\s*\+\s*", g.file_title)
            if len(pieces) == len(g.episodes):
                for e, piece in zip(g.episodes, pieces):
                    known = titles.get((g.season, e))
                    if piece and not (known and clean_text(known.title)):
                        g.overrides[e] = EpisodeInfo(title=piece, source="the filename")
            continue
        e = g.episodes[0]
        key, wanted = (g.season, e), normalize_title(g.file_title)
        known = titles.get(key)
        if from_tvmaze and g.season == 0 and wanted in special_index:
            g.overrides[e] = special_index[wanted]
            continue
        if not (known and clean_text(known.title)):
            g.overrides[e] = EpisodeInfo(title=g.file_title, source="the filename")
            continue
        known_key = normalize_title(known.title)
        if not from_tvmaze or known_key == wanted:
            continue
        if len(known_key) >= 4 and wanted.startswith(known_key):
            continue   # "Episode Title - restored": TVmaze's clean title is used
        if len(wanted) >= 6 and known_key.endswith(wanted):
            g.overrides[e] = EpisodeInfo(title=g.file_title, source="the filename")
            continue   # TVmaze's "Book One: Water - Chapter One: Episode Title": the short form is kept (1.2.0)
        if len(known_key) >= 4 and known_key in normalize_title(g.file_text):
            g.how += f'; the filename also says "{known.title}" (e.g. "aka"), so TVmaze\'s title is used'
            continue   # "Episode Title (aka Other Title)"
        hits = [k for k in index.get(wanted, []) if k != key]
        if len(hits) == 1:
            new = hits[0]
            here, there = _code(key[0], [key[1]]), _code(new[0], [new[1]])
            if renumber:
                g.season, g.episodes = new[0], [new[1]]
                g.renumbered = f"NOTE: renumbered; the filename says {here}, the title matches TVmaze {there}"
                g.how += f"; renumbered to {there} by its title"
            else:
                g.overrides[e] = EpisodeInfo(title=g.file_title, source="the filename")
                g.warns.append(f"NOTE: the title matches TVmaze {there}, but the filename says {here}. "
                               "Run with --renumber to use TVmaze's number")
                suggested += 1
            continue
        if difflib.SequenceMatcher(None, wanted, known_key).ratio() >= TYPO_SIMILARITY:
            # Same episode number and nearly the same title: a misspelling in the filename.
            g.how += f'; the filename\'s "{g.file_title}" looks like a misspelling of TVmaze\'s "{known.title}"'
            continue
        g.overrides[e] = EpisodeInfo(title=g.file_title, source="the filename")
        note = f'NOTE: TVmaze calls {_code(key[0], [key[1]])} "{known.title}"; keeping the filename\'s title'
        close = difflib.get_close_matches(wanted, list(index), n=1, cutoff=0.8)
        if close and index[close[0]][0] != key:
            similar = index[close[0]][0]
            note += f' (similar to TVmaze {_code(similar[0], [similar[1]])} "{titles[similar].title}")'
        g.warns.append(note)
    return suggested


def mark_duplicates(groups: list[Group]) -> None:
    """Videos that share an episode: identical copies become DUPLICATE, the rest CONFLICT.
    Parts of one episode ("Part 1 of 2", "Part 2 of 2") don't count as sharing it."""
    by_episode: dict[tuple, list[Group]] = {}
    for g in groups:
        if not g.status:
            for e in g.episodes:
                by_episode.setdefault((g.season, e, g.part), []).append(g)
    handled: set[int] = set()
    for members in by_episode.values():
        if len(members) < 2 or id(members[0]) in handled:
            continue
        cluster = {id(g): g for g in members}
        stack = list(members)
        while stack:   # pull in anything overlapping, e.g. S01E01E02 next to S01E02
            g = stack.pop()
            for e in g.episodes:
                for other in by_episode[(g.season, e, g.part)]:
                    if id(other) not in cluster:
                        cluster[id(other)] = other
                        stack.append(other)
        handled.update(cluster)
        _resolve_cluster(list(cluster.values()))


def _resolve_cluster(members: list[Group]) -> None:
    copies = [g for g in members if _COPY_MARK.search(g.video.stem)]
    originals = [g for g in members if not _COPY_MARK.search(g.video.stem)]
    if len(originals) == 1 and copies:
        original = originals[0]
        if all(c.season == original.season and c.episodes == original.episodes and c.size == original.size
               for c in copies):
            for c in copies:
                c.status, c.note = "DUPLICATE", f"same size as {original.video.name}, left alone"
            return
    for g in members:
        others = ", ".join(o.video.name for o in members if o is not g)
        g.status, g.note = "CONFLICT", f"same episode as {others}; neither renamed"


def build_stem(show: str, season: int, episodes: list[int], titles: list[str], width: int, ext: str,
               part: int | None = None) -> str:
    """Show-Name_S01E04_Title, keeping only the first title of a too-long multi-episode name.
    A "Part N" goes at the end of the title: Show-Name_S00E01_Big-Adventure-Part-1."""
    base = f"{show}_S{season:02d}" + "".join(f"E{e:0{width}d}" for e in episodes)
    suffix = f"Part-{part}" if part else ""
    present = [t for t in titles if t]
    if not present:
        return f"{base}_{suffix}" if suffix else base
    if len(present) > 1 and len(f"{base}_{'+'.join(present)}{ext}") > MULTI_TITLE_LIMIT:
        present = present[:1]
    title = "+".join(present)
    tail = f"-{suffix}" if suffix else ""
    while len(f"{base}_{title}{tail}{ext}".encode()) > NAME_LIMIT:
        title = title.rsplit("-", 1)[0].rstrip("-+.") if "-" in title else ""
        if not title:
            return f"{base}_{suffix}" if suffix else base
    return f"{base}_{title}{tail}"


def _season_widths(groups: list[Group], titles: Titles) -> dict[int, int]:
    """2-digit episode numbers, or 3 when a season reaches 100."""
    highest: dict[int, int] = {}
    for g in groups:
        if g.season is not None and g.episodes:
            highest[g.season] = max(highest.get(g.season, 0), *g.episodes)
    for season, episode in titles:
        highest[season] = max(highest.get(season, 0), episode)
    return {s: 3 if top >= 100 else 2 for s, top in highest.items()}


class _Listing:
    """Case-insensitive names already in each folder, and write permission, read once."""

    def __init__(self):
        self._names: dict[Path, set[str]] = {}
        self._writable: dict[Path, bool] = {}

    def names(self, folder: Path) -> set[str]:
        if folder not in self._names:
            self._names[folder] = {n.casefold() for n in os.listdir(folder)} if folder.is_dir() else set()
        return self._names[folder]

    def writable(self, folder: Path) -> bool:
        while not folder.exists():   # a folder the plan will create: what matters is the one above it
            folder = folder.parent
        if folder not in self._writable:
            self._writable[folder] = os.access(folder, os.W_OK)
        return self._writable[folder]


class _Dirs:
    """Folders a plan creates (.nfo/, .nfo/Season_01/, .junk/...), each as a mkdir change, and
    names it claims in them, so two moves never pick the same name."""

    def __init__(self, show_dir: Path, listing: _Listing):
        self.show_dir, self.listing = show_dir, listing
        self.planned: set[Path] = set()
        self.ops: list[Op] = []

    def ensure(self, folder: Path, junk: bool = False) -> None:
        missing = []
        while not folder.is_dir() and folder not in self.planned:
            missing.append(folder)
            folder = folder.parent
        for d in reversed(missing):
            self.planned.add(d)
            self.ops.append(Op("mkdir", dst=Path(os.path.relpath(d, self.show_dir)).as_posix(), is_dir=True,
                               junk=junk))

    def free_name(self, folder: Path, name: str) -> str:
        """name, or name with a number before the extension if it's taken: old.nfo, old.1.nfo, ..."""
        taken = self.listing.names(folder)
        stem, ext = os.path.splitext(name)
        candidate, i = name, 1
        while candidate.casefold() in taken:
            candidate, i = f"{stem}.{i}{ext}", i + 1
        taken.add(candidate.casefold())
        return candidate


def _lower_ext(suffix: str) -> str:
    head, ext = os.path.splitext(suffix)
    return head + ext.lower()


def _size_text(size: int) -> str:
    return f"{size / (1024 * 1024):.1f} MB"


def find_junk(layout: Layout) -> tuple[list[Path], list[Path]]:
    """Junk files for --clean: (outside extras folders, inside extras folders)."""
    main, extras = [], []
    for path, in_extras in _walk_files(layout):
        if is_junk(path):
            (extras if in_extras else main).append(path)
    return main, extras


def build_plan(groups: list[Group], layout: Layout, show: str, info: ShowInfo, titles: Titles,
               nfo: bool, fix_folders: bool, years: str | None, junk: list[Path] | None = None,
               meta: bool = False, ui: UI | None = None) -> Plan:
    plan = Plan()
    show_dir, home = layout.show_dir, layout.home
    listing = _Listing()
    dirs = _Dirs(show_dir, listing)
    widths = _season_widths(groups, titles)
    if info.overall:   # every episode as wide as the show's total: S16E0623 (1.2.0)
        widths = {s: max(2, len(str(info.total))) for s in widths}
    now = time.time()

    def rel(p: Path) -> str:
        return p.relative_to(show_dir).as_posix()

    def label(folder: Path) -> str:
        if folder == show_dir:
            return "(show folder)" if layout.trusted else folder.name + "/"
        return rel(folder) + "/"

    def at_home(p: Path) -> str:
        return p.relative_to(home).as_posix()

    nfo_label, old_label, junk_label = (f"{NFO_DIR}/ (new .nfo files)",
                                        f"{NFO_DIR}/{NFO_OLD}/ (existing .nfo files moved here)",
                                        f"{JUNK_DIR}/ (--clean)")
    for folder, _ in layout.seasons:
        plan.sections[label(folder)] = []
        if folder in layout.subs:
            plan.sections[label(layout.subs[folder])] = []
    if layout.loose_dir:
        plan.sections[label(show_dir)] = []
    for name in (old_label, junk_label, nfo_label):
        plan.sections[name] = []

    # Pass 1: every group's new names, and the per-file checks.
    active = [g for g in groups if not g.status]
    for g in active:
        g.infos = [g.overrides.get(e) or titles.get((g.season, e)) for e in g.episodes]
        clean = [clean_text(i.title) if i else "" for i in g.infos]
        g.missing = [e for e, c in zip(g.episodes, clean) if not c]
        if now - g.mtime < RECENT_SECONDS:
            g.warns.append("changed recently; may still be copying")
        if g.size < SMALL_VIDEO_BYTES:
            g.warns.append(f"very small ({_size_text(g.size)}); possibly a sample")
        if g.folder_season is not None and not g.by_order and not g.renumbered and g.season != g.folder_season:
            g.warns.append(f"filename says season {g.season}, but it's in the season {g.folder_season} folder")
        ext = g.video.suffix.lower()
        stem = build_stem(show, g.season, g.episodes, clean, widths.get(g.season, 2), ext, g.part)
        g.moves = [(g.video, stem + ext)] + [(f, stem + _lower_ext(rest)) for f, rest in g.companions]

    # Pass 2: conflicts with files already there, between groups, or permissions.
    claimed: dict[tuple[Path, str], Group] = {}

    def conflict(g: Group, note: str) -> None:
        if not g.status:
            g.status, g.note = "CONFLICT", note

    for g in active:
        frees = {f.name.casefold() for f, _ in g.moves}
        targets = [new for f, new in g.moves if f.name != new]
        if targets and not listing.writable(g.folder):
            conflict(g, "no write permission in this folder")
        for t in targets:
            key = (g.folder, t.casefold())
            if t.casefold() in listing.names(g.folder) and t.casefold() not in frees:
                conflict(g, f"{t} already exists")
            other = claimed.get(key)
            if other is not None and other is not g:
                conflict(g, f"{t} is also the new name of {other.video.name}")
                conflict(other, f"{t} is also the new name of {g.video.name}")
            claimed[key] = g

    # Every existing .nfo outside .nfo/ moves to .nfo/.nfo-old/, with or without --nfo.
    archive_ops: list[Op] = []
    old_root = home / NFO_DIR / NFO_OLD
    for path, in_extras in _walk_files(layout):
        if path.suffix.lower() != ".nfo" or in_extras:
            continue
        shown = at_home(path)
        if not listing.writable(path.parent):
            plan.sections[old_label].append(Row("CONFLICT", shown, "", "no write permission in its folder"))
            continue
        dest_dir = old_root / Path(shown).parent
        dirs.ensure(dest_dir)
        name = dirs.free_name(dest_dir, path.name)
        plan.sections[old_label].append(Row("ARCHIVE", shown, at_home(dest_dir / name)))
        archive_ops.append(Op("archive", rel(path), rel(dest_dir / name)))

    # --clean: junk moves to .junk/, keeping its path.
    junk_ops: list[Op] = []
    for path in junk or []:
        shown = at_home(path)
        if not listing.writable(path.parent):
            plan.sections[junk_label].append(Row("CONFLICT", shown, "", "no write permission in its folder"))
            continue
        dest_dir = home / JUNK_DIR / Path(shown).parent
        dirs.ensure(dest_dir, junk=True)
        name = dirs.free_name(dest_dir, path.name)
        plan.sections[junk_label].append(Row("JUNK", shown, at_home(dest_dir / name)))
        junk_ops.append(Op("junk", rel(path), rel(dest_dir / name)))

    # Pass 3: rows and changes for the videos.
    rename_ops: list[Op] = []
    create_ops: list[Op] = []
    tag_items: list[tuple[Group, Path, str, str]] = []
    for g in groups:
        rows = plan.sections.setdefault(label(g.folder), [])
        details = [g.how] if g.how else []
        details += [f"E{e:02d} title: {i.source}" for e, i in zip(g.episodes, g.infos) if i and i.source]
        if g.status:
            rows.append(Row(g.status, g.video.name, "", g.note, details))
            continue
        video_new = g.moves[0][1]
        notes = []
        if g.renumbered:
            notes.append(g.renumbered)
        if g.missing:
            notes.append("no title" if len(g.missing) == len(g.episodes)
                         else "no title for " + _episode_list(g.missing))
        notes += g.warns + g.warns_quiet
        if g.by_order:
            notes.append("numbered by sort order")
        if g.video.name == video_new:
            rows.append(Row("SKIP", g.video.name, "", "already correct", details))
        else:
            status = "RENUMBERED" if g.renumbered else "WARN" if g.missing or g.warns else "OK"
            rows.append(Row(status, g.video.name, video_new, "; ".join(notes), details))
            rename_ops.append(Op("rename", rel(g.video), rel(g.folder / video_new), group=id(g)))
        for f, new in g.moves[1:]:
            if f.name != new:
                rows.append(Row("OK", f.name, new))
                rename_ops.append(Op("rename", rel(f), rel(g.folder / new), group=id(g)))
        if meta:
            # The tags are written after the renames, so to the file's new name.
            tag_items.append((g, g.video, rel(g.folder / video_new), rel(g.folder / video_new)))
        if nfo:
            season_dir = home / NFO_DIR / f"Season_{g.season:0{3 if g.season >= 100 else 2}d}"
            _plan_nfo_file(plan, dirs, season_dir, Path(video_new).stem + ".nfo",
                           episode_nfo(info, g.season, g.episodes, g.infos),
                           archive_ops, create_ops, rel, at_home, nfo_label, old_root, group=id(g))

    plan.ops = rename_ops
    _plan_subs(plan, groups, layout, listing, rel, label)
    rename_ops = plan.ops

    tag_ops: list[Op] = []
    if tag_items:
        if not shutil.which(FFPROBE):
            plan.warnings.append("--meta: ffprobe isn't installed (sudo apt install ffmpeg), so the tags inside "
                                 "the videos are left alone.")
        else:
            rows = plan.sections.setdefault(TAG_SECTION, [])
            for g, row, op in plan_tags(ui or UI(interactive=False), info, tag_items):
                if g.status:   # a conflict found after its tags were planned: it isn't renamed or tagged
                    continue
                rows.append(row)
                if op:
                    tag_ops.append(op)

    if nfo:
        if layout.trusted:
            _plan_nfo_file(plan, dirs, home / NFO_DIR, "tvshow.nfo", tvshow_nfo(info),
                           archive_ops, create_ops, rel, at_home, nfo_label, old_root)
        else:
            plan.warnings.append(f"tvshow.nfo isn't written: {show_dir.name}/ is a season folder with no show "
                                 "folder around it.")
    plan.ops = []
    if fix_folders:
        _plan_folders(plan, layout, show, years, listing, info, groups)
        if not nfo:
            plan.warnings.append("--fix-folders without --nfo: Kodi's TMDB scraper may not match the new "
                                 "show folder name. --nfo with \"Local information only\" avoids that.")
    folder_ops = plan.ops
    # Order matters: folders first, then moves out of the old paths, then renames, then new
    # files and tags, and the season and show folders last, so every path above is still valid.
    plan.ops = dirs.ops + archive_ops + junk_ops + rename_ops + create_ops + tag_ops + folder_ops
    plan.ignored = [rel(d) + "/" for d in layout.ignored]
    plan.sections = {k: v for k, v in plan.sections.items() if v}
    return plan


def _plan_nfo_file(plan: Plan, dirs: _Dirs, folder: Path, name: str, content: bytes, archive_ops: list[Op],
                   create_ops: list[Op], rel: Callable[[Path], str], at_home: Callable[[Path], str],
                   nfo_label: str, old_root: Path, group: int | None = None) -> None:
    """A new .nfo in .nfo/. One already there with the same content is left alone; one with
    different content moves to .nfo/.nfo-old/ first."""
    target = folder / name
    rows = plan.sections.setdefault(nfo_label, [])
    if target.is_file():
        if target.read_bytes() == content:
            rows.append(Row("SKIP", at_home(target), "", "already up to date"))
            return
        dest_dir = old_root / target.relative_to(old_root.parent).parent
        dirs.ensure(dest_dir)
        old_name = dirs.free_name(dest_dir, name)
        rows.append(Row("ARCHIVE", at_home(target), at_home(dest_dir / old_name), "replaced by a new one"))
        archive_ops.append(Op("archive", rel(target), rel(dest_dir / old_name)))
    else:
        dirs.ensure(folder)
    rows.append(Row("CREATE", "", at_home(target)))
    create_ops.append(Op("create", dst=rel(target), content=content, group=group))


def _sub_tag(f: Path, g: Group) -> str:
    """What tells a subtitle apart from its siblings, e.g. "5-English" from "5_English.srt"."""
    if f.name.startswith(g.video.stem + "."):            # named after the video's current name
        return f.stem[len(g.video.stem) + 1:]
    m = re.match(r"[^.]*_S\d+(?:E\d+)+[^.]*\.(.+)", f.stem)  # already renamed by renamer
    if m:
        return m.group(1)
    return clean_text(f.stem)


def _plan_subs(plan: Plan, groups: list[Group], layout: Layout, listing: _Listing,
               rel: Callable[[Path], str], label: Callable[[Path], str]) -> None:
    """Rename subtitles inside a season's Subs folder and keep them there.

    Episodes are matched by the SxxExx in a subfolder's or file's name, not by the video's
    name, because the video may already have been renamed by an earlier run. The numbers
    compared are the ones in the video's filename, so --renumber doesn't break the match."""
    for season_dir, subs_dir in layout.subs.items():
        rows = plan.sections.setdefault(label(subs_dir), [])
        by_episode = {}
        for g in groups:
            if g.folder == season_dir and not g.status and g.moves:
                season, episodes = g.file_code or (g.season, g.episodes)
                for e in episodes:
                    by_episode[(season, e)] = g

        def match(name: str) -> tuple[Group | None, str]:
            parsed = parse_episode(name + ".x")   # ".x" so parse_episode's stem keeps the whole name
            if not parsed:
                return None, "no season/episode in its name"
            g = by_episode.get((parsed[0], parsed[1][0]))
            return (g, "") if g else (None, "its video isn't being renamed")

        def stem_of(g: Group) -> str:
            return Path(g.moves[0][1]).stem

        file_moves: list[tuple[Path, Path, str, int]] = []    # (folder, file, new name, group)
        dir_moves: list[tuple[Path, str, int]] = []           # (episode subfolder, new name, group)
        for d in _entries(subs_dir, dirs=True):
            g, reason = match(d.name)
            if g is None:
                plan.not_handled.append((rel(d) + "/", reason))
                continue
            for f in _entries(d, dirs=False):
                if f.suffix.lower() in SUB_EXTS:
                    file_moves.append((d, f, _sub_name(stem_of(g), _sub_tag(f, g), f.suffix), id(g)))
                elif not is_junk(f) and f.suffix.lower() != ".nfo":
                    plan.not_handled.append((rel(f), "not a subtitle"))
            if d.name != stem_of(g):
                dir_moves.append((d, stem_of(g), id(g)))
        for f in _entries(subs_dir, dirs=False):
            if is_junk(f) or f.suffix.lower() == ".nfo":
                continue
            g, reason = match(f.name) if f.suffix.lower() in SUB_EXTS else (None, "not a subtitle")
            if g is None:
                plan.not_handled.append((rel(f), reason))
            else:
                file_moves.append((subs_dir, f, _sub_name(stem_of(g), _sub_tag(f, g), f.suffix), id(g)))

        # Never overwrite, and never let two subtitles end up with the same name.
        wanted = Counter((folder, new.casefold()) for folder, _, new, _ in file_moves)
        for folder, f, new, group in file_moves:
            shown = f.relative_to(subs_dir).as_posix()
            if f.name == new:
                continue
            if not listing.writable(folder):
                rows.append(Row("CONFLICT", shown, "", "no write permission in this folder"))
            elif wanted[(folder, new.casefold())] > 1:
                rows.append(Row("CONFLICT", shown, "", f"another subtitle would also be {new}"))
            elif new.casefold() in listing.names(folder) and new.casefold() != f.name.casefold():
                rows.append(Row("CONFLICT", shown, "", f"{new} already exists"))
            else:
                rows.append(Row("OK", shown, new))
                plan.ops.append(Op("rename", rel(f), rel(folder / new), group=group))
        dir_counts = Counter(new.casefold() for _, new, _ in dir_moves)
        for d, new, group in dir_moves:   # after the files, so the file paths above stay valid
            if not listing.writable(subs_dir):
                rows.append(Row("CONFLICT", d.name + "/", "", "no write permission in this folder"))
            elif dir_counts[new.casefold()] > 1:
                rows.append(Row("CONFLICT", d.name + "/", "", f"more than one folder would be {new}"))
            elif new.casefold() in listing.names(subs_dir) and new.casefold() != d.name.casefold():
                rows.append(Row("CONFLICT", d.name + "/", "", f"{new}/ already exists"))
            else:
                rows.append(Row("OK", d.name + "/", new + "/"))
                plan.ops.append(Op("rename", rel(d), rel(subs_dir / new), is_dir=True, group=group))


def _sub_name(stem: str, tag: str, suffix: str) -> str:
    return f"{stem}.{tag}{suffix.lower()}" if tag else f"{stem}{suffix.lower()}"


def show_folder_name(show: str, years: str | None, seasons: list[int], dub: bool = False) -> str:
    """Show-Name[_YEARS][_Season_01 | _Seasons_01-08][_Dub]. Specials count only when alone."""
    numbers = sorted({n for n in seasons if n > 0}) or sorted(set(seasons))
    part = ""
    if numbers:
        width = 3 if numbers[-1] >= 100 else 2
        lo, hi = numbers[0], numbers[-1]
        part = f"Season_{lo:0{width}d}" if lo == hi else f"Seasons_{lo:0{width}d}-{hi:0{width}d}"
    return "_".join(p for p in (show, years, part, "Dub" if dub else "") if p)


def season_folder_name(show: str, season: int, width: int, current: str = "", name: str = "") -> str:
    """Season_01_Show-Name: the number first, so it shows even when a file browser cuts long
    names short; never a year, which only the show folder gets. A season the show calls something
    else keeps that: "Book One - Air" -> Book_01_Air_Show-Name (1.0.0). A season with a name of
    its own takes that instead of the show's: Season_16_Season-Name (1.2.0)."""
    word = season_word(current) if current else None
    if word and word[1] == season:
        label, _, rest = word
        return "_".join(p for p in (f"{label}_{season:0{width}d}", clean_text(rest), show) if p)
    if not name and (m := re.match(r"(?i)^seasons?[ ._-]*\d{1,3}\s+-\s+(.+)$", current)):
        name = m.group(1)   # "Season 2 - Season Name"
    return f"Season_{season:0{width}d}_{clean_text(name) or show}"


def season_label(raw: str, show: str) -> str:
    """A season's own name, or "" when it says nothing the show's name doesn't: TVmaze's "#579 - #626",
    "Example Show II"; "Example Show: Season Name" -> "Season Name" (1.2.0)."""
    raw = (raw or "").strip()
    if not raw or raw.startswith("#"):
        return ""
    key = normalize_title(show)
    for i in range(1, len(raw) + 1):
        if normalize_title(raw[:i]) == key and not raw[i:i + 1].isalnum():
            raw = raw[i:].strip(" :-–—")
            break
    if not raw or re.fullmatch(r"(?i)\d{1,2}|[ivx]+|part \w+|season \d+", raw):
        return ""
    return raw


def is_dub(name: str) -> bool:
    """"English Dub" in a name, but not "Movies are Dub OVAs Sub", which is only partly dubbed (1.2.0)."""
    return bool(_DUB.search(name)) and not _SUB_WORD.search(name)


def _plan_folders(plan: Plan, layout: Layout, show: str, years: str | None, listing: _Listing,
                  info: ShowInfo | None = None, groups: list[Group] | None = None) -> None:
    """Season_01_Show-Name and Show-Name_Seasons_01-08 folder names. Done after every file change."""
    show_dir = layout.show_dir
    names = listing.names(show_dir)
    width = 3 if max(layout.all_seasons or [0]) >= 100 else 2
    season_names = info.season_names if info else {}
    active = [g for g in groups or [] if not g.status]

    def season_of(d: Path, n: int) -> int:
        """The season its files turned out to be: a release's "Season 3" can be TVmaze's season 2 (1.2.0)."""
        found = Counter(g.season for g in active if g.folder == d and g.renumbered)
        return found.most_common(1)[0][0] if found else n

    wanted = {d: season_folder_name(show, season_of(d, n), width, d.name, season_names.get(season_of(d, n), ""))
              for d, n in layout.seasons}
    counts = Counter(n.casefold() for n in wanted.values())
    videos = [g.video.name for g in groups or []]
    dub = is_dub(show_dir.name) or sum(1 for v in videos if is_dub(v)) * 2 > len(videos) > 0
    seasons_now = sorted({season_of(d, n) for d, n in layout.seasons} | set(layout.all_seasons)) \
        if not any(season_of(d, n) != n for d, n in layout.seasons) else sorted({season_of(d, n) for d, n in layout.seasons})
    if any(c > 1 for c in counts.values()):
        plan.warnings.append("Several season folders here hold one season (a release's parts, or seasons TVmaze counts "
                             "as one). They keep their names for now; renamer --sort puts their episodes together.")
    for d, new in wanted.items():
        if d == show_dir:   # a lone season folder is its own show folder, so it gets a show folder's name
            _plan_own_folder(plan, show_dir, show_folder_name(show, years, seasons_now, dub), listing)
            continue
        if d.name == new:
            plan.folder_rows.append(Row("SKIP", d.name + "/", "", "already correct"))
        elif counts[new.casefold()] > 1:
            plan.folder_rows.append(Row("CONFLICT", d.name + "/", "", f"more than one folder would be {new}"))
        elif new.casefold() in names and new.casefold() != d.name.casefold():
            plan.folder_rows.append(Row("CONFLICT", d.name + "/", "", f"{new}/ already exists"))
        else:
            plan.folder_rows.append(Row("OK", d.name + "/", new + "/"))
            plan.ops.append(Op("rename", d.name, new, is_dir=True))
    if not layout.trusted:
        return
    new_show = show_folder_name(show, years, seasons_now, dub)
    if show_dir.name == new_show:
        plan.folder_rows.append(Row("SKIP", show_dir.name + "/", "", "already correct"))
        return
    parent_names = {n.casefold() for n in os.listdir(show_dir.parent)}
    if not listing.writable(show_dir.parent):
        plan.folder_rows.append(Row("CONFLICT", show_dir.name + "/", "", "no write permission in the folder above"))
    elif new_show.casefold() in parent_names and new_show.casefold() != show_dir.name.casefold():
        plan.folder_rows.append(Row("CONFLICT", show_dir.name + "/", "", f"{new_show}/ already exists"))
    else:
        plan.folder_rows.append(Row("OK", show_dir.name + "/", new_show + "/"))
        plan.ops.append(Op("rename_show", show_dir.name, new_show, is_dir=True))
        plan.warnings.append("The show folder will be renamed. Kodi tracks shows by folder, so it will treat "
                             "this as a new show: watched status and resume points for it are lost.")


def _plan_own_folder(plan: Plan, show_dir: Path, new: str, listing: _Listing) -> None:
    """Renaming a lone season folder, which is also the folder the undo log is in."""
    if show_dir.name == new:
        plan.folder_rows.append(Row("SKIP", show_dir.name + "/", "", "already correct"))
        return
    parent_names = {n.casefold() for n in os.listdir(show_dir.parent)}
    if not listing.writable(show_dir.parent):
        plan.folder_rows.append(Row("CONFLICT", show_dir.name + "/", "", "no write permission in the folder above"))
    elif new.casefold() in parent_names and new.casefold() != show_dir.name.casefold():
        plan.folder_rows.append(Row("CONFLICT", show_dir.name + "/", "", f"{new}/ already exists"))
    else:
        plan.folder_rows.append(Row("OK", show_dir.name + "/", new + "/"))
        plan.ops.append(Op("rename_show", show_dir.name, new, is_dir=True))


def season_warnings(groups: list[Group], titles: Titles, layout: Layout, from_tvmaze: bool,
                    overall: bool = False) -> list[str]:
    """Sort-order counts, gaps, and episode counts that don't fit TVmaze."""
    warnings = []
    active = [g for g in groups if not g.status]
    for folder, season in layout.seasons:
        ordered = sum(1 for g in active if g.folder == folder and g.by_order)
        available = sum(1 for s, _ in titles if s == season)
        if ordered and ordered != available:
            warnings.append(f"{folder.name}: {ordered} files numbered by sort order, "
                            f"but {available} titles for season {season}.")
    by_season: dict[int, set[int]] = {}
    for g in active:
        by_season.setdefault(g.season, set()).update(g.episodes)
    for season in sorted(by_season):
        if season == 0:
            continue
        episodes = by_season[season]
        top = max(episodes)
        listed_here = [e for s, e in titles if s == season]
        first = min(listed_here) if from_tvmaze and listed_here else 1   # Example Show's season 16 starts at E579
        missing = [e for e in range(first, top + 1) if e not in episodes]
        if missing:
            warnings.append(f"Season {season}: no file for {_episode_list(missing)}.")
        if not from_tvmaze:
            continue
        listed = [e for s, e in titles if s == season]
        if not listed:
            warnings.append(f"TVmaze has no season {season}, so its files get no titles from TVmaze.")
        elif top > max(listed):
            warnings.append(f"Season {season}: the files go up to E{top:02d}, but TVmaze's season {season} "
                            f"ends at E{max(listed):02d}. The titles are probably wrong.")
        elif len(listed) >= 2 * len(episodes) and len(episodes) >= 3 and not overall:
            warnings.append(f"Season {season}: TVmaze lists {len(listed)} episodes, but there are only "
                            f"{len(episodes)} files. If each file is a full episode and TVmaze counts "
                            "segments, the titles are wrong; use --names for this show "
                            "(--make-names writes a starting file).")
    return warnings


# ----------------------------------------------------------------- preview

def _print_row(ui: UI, row: Row) -> None:
    ui.say(f"  {ui.paint(f'{row.status:<10}', row.status)} {row.old or row.new}")
    if row.old and row.new:
        ui.say(f"  {'':10}   → {row.new}")
    if row.note:
        ui.say(f"  {'':10}   ({row.note})")
    for detail in row.details:
        ui.detail(f"  {'':10}   · {detail}")


COLLAPSE = ("SKIP",)   # rows that are folded together when a season's files share a note


def _collapsed(section: str, rows: list[Row]) -> list[Row]:
    """Runs of three or more TAG or SKIP rows in one folder with the same note become one row:
    "TAG  Season 3/ (16 videos)  (adds 15 tags)". Only without --verbose."""
    def folder(row: Row) -> str:
        name = row.old or row.new
        return name.rsplit("/", 1)[0] + "/" if "/" in name else section
    out: list[Row] = []
    i = 0
    while i < len(rows):
        row = rows[i]
        j = i + 1
        if row.status in COLLAPSE:
            while j < len(rows) and (rows[j].status, rows[j].note, folder(rows[j])) == \
                    (row.status, row.note, folder(row)):
                j += 1
        if j - i >= 3:
            out.append(Row(row.status, f"{folder(row)} ({_plural(j - i, 'video')})", "", row.note))
        else:
            out.extend(rows[i:j])
        i = j
    return out


def _shared_tags(plan: Plan) -> dict[str, tuple[str, str | None]]:
    """The tag values every TAG row has in common (show, genre, network, IDs...), so the preview
    lists them once instead of on every file (0.8.1)."""
    rows = [row for rows in plan.sections.values() for row in rows if row.status == "TAG" and row.values]
    if len(rows) < 2:
        return {}
    shared = {label: (new, old) for label, new, old in rows[0].values}
    for row in rows[1:]:
        mine = {label: (new, old) for label, new, old in row.values}
        shared = {k: v for k, v in shared.items() if mine.get(k) == v}
    return shared


def _print_tag_row(ui: UI, row: Row, shared: dict) -> None:
    """A TAG row with the values it gets, except those listed once for every file (0.8.1)."""
    ui.say(f"  {ui.paint(f'{row.status:<10}', row.status)} {row.old or row.new}")
    width = max(50, shutil.get_terminal_size((100, 24)).columns - 16)
    values = sorted((v for v in row.values if v[0] not in shared), key=lambda v: "plot" in v[0])   # plot last
    texts = [_tag_text(label, new, old) for label, new, old in values]
    other = [n for n in row.note.split("; ") if n and not n.startswith(("adds ", "fixes "))]
    for line in textwrap.wrap(" · ".join(texts), width, break_on_hyphens=False):
        ui.say(f"  {'':10}   {line}")
    if other:
        ui.say(f"  {'':10}   ({'; '.join(other)})")
    if not texts and not other and row.note:
        ui.say(f"  {'':10}   ({row.note})")


def print_preview(ui: UI, header: list[str], plan: Plan) -> None:
    for section, rows in plan.sections.items():
        for row in rows:
            ui.debug(f"row [{section}] {row.status} | {row.old} | {row.new} | {row.note} | {row.details}")
    for op in plan.ops:
        ui.debug(f"planned {_op_text(op)}")
    flagged = [(section, row) for section, rows in plan.sections.items() for row in rows] \
        + [("Folders", row) for row in plan.folder_rows]
    with ui.paged() as page:
        for line in header:
            ui.say(line)
        for line in plan.details:
            ui.detail(line)
        for warning in plan.warnings:
            ui.warn(warning)
        shared = {} if ui.verbose else _shared_tags(plan)
        if shared:
            ui.say()
            ui.say("Tags for every file")
            width = max(50, shutil.get_terminal_size((100, 24)).columns - 4)
            for line in textwrap.wrap(" · ".join(_tag_text(k, *v) for k, v in shared.items()), width,
                                      break_on_hyphens=False):
                ui.say(f"  {line}")
        for section, rows in plan.sections.items():
            ui.say()
            ui.say(section)
            for row in rows if ui.verbose else _collapsed(section, rows):
                if row.status == "TAG" and row.values and not ui.verbose:
                    _print_tag_row(ui, row, shared)
                else:
                    _print_row(ui, row)
        if plan.folder_rows:
            ui.say()
            ui.say("Folders")
            for row in plan.folder_rows:
                _print_row(ui, row)
        if plan.ignored:
            ui.say()
            for d in plan.ignored:
                _print_row(ui, Row("IGNORED", d, "", "not a season folder"))
        if plan.not_handled and ui.verbose:
            ui.say()
            ui.say("Not handled")
            for name, reason in plan.not_handled:
                ui.say(f"  {name}  ({reason})")
        print_attention(ui, flagged, plan.warnings)
        ui.say()
    if page.shown:
        # The pager has closed: keep only what needs a look on screen, above the question.
        _print_after_pager(ui, flagged, plan.warnings)


def _print_after_pager(ui: UI, flagged: list[tuple[str, Row]], warnings: list[str]) -> None:
    with ui.quiet_log():
        print_attention(ui, flagged, warnings)
        ui.say()


ATTENTION = ("CONFLICT", "WARN", "UNMATCHED", "DUPLICATE", "LOOSE", "RENUMBERED", "OTHER SHOW", "SKIPPED")


def print_attention(ui: UI, rows: list[tuple[str, Row]], warnings: list[str]) -> None:
    """Everything that needs a look, repeated at the bottom so a long preview doesn't hide it
   : the warnings from the top, then every row that isn't a plain OK or expected action."""
    flagged = [(where, row) for where, row in rows if row.status in ATTENTION]
    if not flagged and not warnings:
        return
    ui.say()
    ui.say(ui.paint(f"Needs a look ({len(warnings) + len(flagged)})", "WARN"))
    for warning in warnings:
        ui.say(f"  {ui.paint('Warning', 'WARN')}  {warning}")
    order = {status: i for i, status in enumerate(ATTENTION)}
    for where, row in sorted(flagged, key=lambda item: order[item[1].status]):
        place = "" if where in ("(show folder)", "Folders", TAG_SECTION) or where.startswith((".", "..", "Left")) \
            or "  (" in where else where   # lib --sort's sections are explained; their rows are complete
        ui.say(f"  {ui.paint(f'{row.status:<10}', row.status)} {place}{row.old or row.new}"
               + (f"  ({row.note})" if row.note else ""))


def _summary(ops: list[Op]) -> str:
    kinds = Counter(o.kind for o in ops)
    files = sum(1 for o in ops if o.kind == "rename" and not o.is_dir)
    folders = sum(1 for o in ops if o.kind in ("rename", "rename_show") and o.is_dir)
    parts = []
    if kinds["lib"]:
        parts.append(f"move {kinds['lib']} into show folders or the movies library"
                     + (f", creating {_plural(kinds['mkdir'], 'folder')}" if kinds["mkdir"] else ""))
    if kinds["group"]:
        parts.append(f"move {kinds['group']} into folders of copies"
                     + (f", creating {_plural(kinds['mkdir'], 'folder')}" if kinds["mkdir"] else ""))
    if kinds["genre"]:
        made = kinds["mkdir"]
        parts.append(f"move {kinds['genre']} into genre folders"
                     + (f", creating {_plural(made, 'folder')}" if made else ""))
    if kinds["sort"]:
        parts.append(f"move {_plural(kinds['sort'], 'file')} into season folders")
    if kinds["duplicate"]:
        n = kinds["duplicate"]
        parts.append(f"move {n} worse {'copy' if n == 1 else 'copies'} to {DUPES_DIR}")
    if kinds["unsorted"]:
        parts.append(f"move {kinds['unsorted']} to ../{UNSORTED_DIR}")
    if files:
        parts.append("rename " + _plural(files, "file"))
    if kinds["archive"]:
        parts.append(f"move {kinds['archive']} old .nfo to {NFO_DIR}/{NFO_OLD}")
    if kinds["junk"]:
        parts.append(f"move {_plural(kinds['junk'], 'junk file')} to {JUNK_DIR}")
    nfos = sum(1 for o in ops if o.kind == "create" and Path(o.dst).name != GROUP_MARKER)
    if nfos:
        parts.append(f"create {nfos} .nfo")
    if kinds["tag"]:
        copies = sum(1 for o in ops if o.kind == "tag" and o.tags["container"] != "mkv")
        parts.append(f"update the tags in {_plural(kinds['tag'], 'video')}"
                     + (f" ({copies} rewritten by ffmpeg)" if copies else ""))
    if folders:
        parts.append("rename " + _plural(folders, "folder"))
    if kinds["rmdir"]:
        parts.append("remove " + _plural(kinds["rmdir"], "emptied folder"))
    if not parts and kinds["mkdir"] and not kinds["genre"] and not kinds["lib"] and not kinds["group"]:
        parts.append("create " + _plural(kinds["mkdir"], "folder"))
    text = ", ".join(parts)
    return text[0].upper() + text[1:]


def confirm(ui: UI, question: str, allow_delete: bool = False) -> str | None:
    """The Y/N step every run ends with. Returns "yes", "delete" (only offered with --clean
    junk) or None. No answer, or no terminal, means No."""
    if not ui.interactive:
        ui.say("Not running in an interactive terminal, so nothing was changed.")
        return None
    if allow_delete:
        answer = ui.ask(f"{question}? [y/n/DELETE]: ")
        if answer == "DELETE":
            return "delete"
        if answer.lower() == "delete":
            ui.say("To delete the junk for good, type DELETE in capitals. Nothing was changed.")
            return None
    else:
        answer = ui.ask(f"{question}? [y/N]: ")
    if answer.lower() in ("y", "yes"):
        return "yes"
    ui.say("Cancelled. Nothing was changed.")
    return None


def junk_to_delete(ops: list[Op]) -> list[Op]:
    """DELETE: junk is deleted instead of moved to .junk/, so .junk/ isn't created either."""
    return [Op("delete", src=o.src) if o.kind == "junk" else o
            for o in ops if not (o.kind == "mkdir" and o.junk)]


def report_downloads(ui: UI, root: Path, downloads: list[Path]) -> int:
    """Unfinished downloads stop the whole run."""
    ui.warn(f"unfinished downloads ({', '.join(DOWNLOAD_EXTS)}) under {root}:")
    for path in downloads:
        ui.say(f"  {path.relative_to(root).as_posix()}")
    ui.say("Nothing was changed. Run renamer again once the downloads have finished.")
    return 1


# ------------------------------------------------------------------- apply

def load_log(path: Path) -> dict:
    if not path.exists():
        return {"version": 1, "runs": []}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(data.get("runs"), list):
            raise ValueError
        return data
    except (ValueError, AttributeError, OSError):
        raise RenamerError(f"The undo log {path} is damaged; not touching anything.") from None


def save_log(path: Path, data: dict) -> None:
    """Write the log in one step, so an interruption never leaves it half-written."""
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(data, indent=1, ensure_ascii=False), encoding="utf-8")
    os.replace(tmp, path)


class Journal:
    """The undo log for one run, saved after every single change."""

    def __init__(self, show_dir: Path):
        self.path = show_dir / UNDO_LOG
        self.data = load_log(self.path)
        self.run = {"time": time.strftime("%Y-%m-%d %H:%M:%S"), "version": VERSION, "ops": []}
        self.data["runs"].append(self.run)
        save_log(self.path, self.data)   # fails here, before any change, if the folder isn't writable

    def record(self, entry: dict) -> None:
        debug(f"undo log: {json.dumps(entry, ensure_ascii=False, default=str)}")
        self.run["ops"].append(entry)
        save_log(self.path, self.data)

    def moved(self, new_show_dir: Path) -> None:
        self.path = new_show_dir / UNDO_LOG

    def finish(self) -> None:
        if not self.run["ops"]:
            self.data["runs"].remove(self.run)
        if self.data["runs"]:
            save_log(self.path, self.data)
        else:
            self.path.unlink(missing_ok=True)


def move(src: Path, dst: Path) -> None:
    """Rename without ever overwriting. Case-only changes go through a temporary name."""
    if src.parent == dst.parent and src.name != dst.name and src.name.casefold() == dst.name.casefold():
        tmp = src.with_name(f".renamer-tmp-{os.getpid()}-{dst.name}")
        os.rename(src, tmp)
        os.rename(tmp, dst)
        return
    if os.path.lexists(dst):
        raise FileExistsError(errno.EEXIST, "already exists", str(dst))
    os.rename(src, dst)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _elapsed(seconds: float) -> str:
    seconds = int(seconds)
    hours, rest = divmod(seconds, 3600)
    return f"{hours}:{rest // 60:02d}:{rest % 60:02d}" if hours else f"{rest // 60}:{rest % 60:02d}"


class Progress:
    """The one-line progress bar shown while changes are made:

        Renaming  [████████░░░░░░░░░░░░]  77/191 40%  0:12  Example-Show_S05E03_Episode-Title.mkv

    It redraws in place after every change and at least once a second, so the elapsed time keeps
    ticking even while one slow change is in progress. It's only drawn on a real terminal and is
    never copied to the --verbose log. A filename too long for the terminal is cut at the end, so
    the show and SxxExx stay visible."""

    def __init__(self, ui: UI, label: str, total: int):
        self.ui, self.label, self.total = ui, label, total
        self.enabled = ui.tty and total > 0
        self.done, self.name = 0, ""
        self.drawn = self.paused = False
        self.started = time.monotonic()
        self._lock = threading.Lock()
        self._stop = threading.Event()
        self._thread = None
        if self.enabled:
            self._thread = threading.Thread(target=self._tick, daemon=True)
            self._thread.start()

    def _draw(self) -> None:
        columns = shutil.get_terminal_size((80, 24)).columns
        width = max(10, min(30, columns // 4))
        filled = width * self.done // self.total
        percent = 100 * self.done // self.total   # rounded down, so 100% only shows when every change is done
        line = (f"{self.label}  [{'█' * filled}{'░' * (width - filled)}]  {self.done}/{self.total} {percent}%"
                f"  {_elapsed(time.monotonic() - self.started)}")
        room = columns - len(line) - 3
        if self.name and room >= 12:
            line += "  " + (self.name if len(self.name) <= room else self.name[:room - 1] + "…")
        self.ui.out.write("\r" + line[:columns - 1] + "\033[K")
        self.ui.out.flush()
        self.drawn = True

    def _tick(self) -> None:
        while not self._stop.wait(1):
            with self._lock:
                if not self.paused:
                    self._draw()

    def update(self, done: int, name: str = "") -> None:
        if not self.enabled:
            return
        with self._lock:
            self.done, self.name, self.paused = done, name, False
            self._draw()

    def pause(self) -> None:
        """End the bar's line and stop redrawing until the next update(), so a question can be asked."""
        with self._lock:
            self.paused = True
            if self.drawn:
                self.ui.out.write("\n")
                self.ui.out.flush()
                self.drawn = False

    def finish(self) -> None:
        """Stop ticking and end the bar's line, so whatever is printed next starts on its own line."""
        if self._thread:
            self._stop.set()
            self._thread.join()
            self._thread = None
        if self.drawn:
            self.ui.out.write("\n")
            self.ui.out.flush()
            self.drawn = False


_BUSY = {errno.EBUSY, errno.ETXTBSY}
# Over SMB, renaming a folder with an open file inside is refused as "Permission denied". Write
# permission was already checked before the preview, so at this point it almost always means a lock.
_LOCKED = {errno.EACCES, errno.EPERM}


def ask_busy(ui: UI, progress: Progress, error: OSError, name: str) -> str:
    """A file is open somewhere, e.g. playing in VLC on another machine. Returns "retry",
    "skip" or "stop". Without a terminal to ask, it's "stop", as before 0.4.2."""
    if error.errno not in _BUSY | _LOCKED or not ui.interactive:
        return "stop"
    progress.pause()
    if error.errno in _BUSY:
        reason = f"{name} is in use (open in a player or being scanned)."
    else:
        reason = (f"{name} can't be changed right now ({error.strerror}). Something in it is probably "
                  "open in a player or being scanned.")
    answer = ui.ask(f"{reason}\nClose it and press Enter to retry, s to skip it, or q to stop: ").lower()
    if answer in ("s", "skip"):
        return "skip"
    if answer in ("q", "quit", "stop"):
        return "stop"
    return "retry"


def _op_text(op: Op) -> str:
    return (f"{op.kind} {op.src!r} -> {op.dst!r}" + (" (folder)" if op.is_dir else "")
            + (f" tags {json.dumps(op.tags, ensure_ascii=False, default=str)}" if op.tags else "")
            + (f" {len(op.content)} bytes" if op.content else ""))


def apply_ops(ops: list[Op], show_dir: Path, ui: UI, label: str = "Renaming") -> int:
    try:
        journal = Journal(show_dir)
    except OSError as e:
        raise RenamerError(f"Can't write the undo log in {show_dir} ({e.strerror}). Nothing was changed.") from None
    ui.changing = True
    done = 0
    progress = Progress(ui, label, len(ops))
    skipped: list[str] = []
    skipped_groups: set[int] = set()
    failed: list[tuple[str, str]] = []   # videos whose tags couldn't be written

    def apply(op: Op) -> None:
        nonlocal show_dir
        ui.debug(f"doing {_op_text(op)}")
        if op.kind in ("rename", "archive", "junk", "sort", "duplicate", "unsorted", "genre", "lib", "group"):
            move(show_dir / op.src, show_dir / op.dst)
            entry = {"op": "rename", "src": op.src, "dst": op.dst, "dir": op.is_dir}
            if op.kind != "rename":
                entry["kind"] = op.kind   # "archive": --undo leaves it in .nfo/.nfo-old
            journal.record(entry)
        elif op.kind == "mkdir":
            if not (show_dir / op.dst).is_dir():
                os.mkdir(show_dir / op.dst)
                journal.record({"op": "mkdir", "path": op.dst})
        elif op.kind == "delete":
            os.remove(show_dir / op.src)
            journal.record({"op": "delete", "path": op.src})
        elif op.kind == "rmdir":
            os.rmdir(show_dir / op.dst)
            journal.record({"op": "rmdir", "path": op.dst})
        elif op.kind == "create":
            with open(show_dir / op.dst, "xb") as f:
                f.write(op.content)
            journal.record({"op": "create", "path": op.dst, "sha256": sha256(op.content)})
        elif op.kind == "rename_show":
            new_dir = show_dir.with_name(op.dst)
            move(show_dir, new_dir)
            show_dir = new_dir
            journal.moved(new_dir)
            journal.record({"op": "rename_show", "src": op.src, "dst": op.dst})
        elif op.kind == "tag":
            write_tags(show_dir / op.src, op.tags)
            journal.record({"op": "tag", "path": op.src, **op.tags})

    skipped_ops: list[Op] = []
    folder_moves: list[tuple[str, str]] = []   # season folders renamed, so a retry finds its files

    def run_ops(todo: list[Op]) -> None:
        nonlocal done
        for op in todo:
            if op.group is not None and op.group in skipped_groups:
                skipped_ops.append(op)
                continue   # its video was skipped, so its subtitles and .nfo keep matching the old name
            while True:
                progress.update(done, Path(op.dst or op.src).name)
                try:
                    apply(op)
                    done += 1
                    if op.kind == "rename" and op.is_dir:
                        folder_moves.append((op.src, op.dst))
                    break
                except ToolError as e:   # that video's tags stay as they were; the run goes on
                    failed.append((op.src, str(e)))
                    break
                except OSError as e:
                    action = ask_busy(ui, progress, e, Path(op.src or op.dst).name)
                    if action == "stop":
                        raise
                    if action == "skip":
                        skipped.append(op.src or op.dst)
                        skipped_ops.append(op)
                        if op.group is not None:
                            skipped_groups.add(op.group)
                        break

    def moved(path: str) -> str:
        for old, new in folder_moves:
            if path == old or path.startswith(old + "/"):
                path = new + path[len(old):]
        return path

    try:
        run_ops(ops)
        progress.update(done)
        # Files in use can be tried again straight away, in the same run, instead of later (0.8.1).
        while skipped and ui.interactive:
            progress.finish()
            ui.say(f"{_plural(len(skipped), 'file')} {'was' if len(skipped) == 1 else 'were'} skipped because "
                   f"{'it was' if len(skipped) == 1 else 'they were'} in use: {', '.join(skipped[:5])}"
                   + (", …" if len(skipped) > 5 else ""))
            if ui.ask("Try them again now? [y/N]: ").lower() not in ("y", "yes"):
                break
            todo = [dataclasses.replace(op, src=moved(op.src), dst=moved(op.dst)) for op in skipped_ops]
            skipped.clear()
            skipped_ops.clear()
            skipped_groups.clear()
            progress = Progress(ui, label, len(todo))
            done_before, done = done, 0
            run_ops(todo)
            progress.update(done)
            done += done_before
    except OSError as e:
        progress.finish()
        journal.finish()
        ui.say(ui.paint("Error: ", "CONFLICT") + f"{e.strerror or e}: {e.filename or ''}")
        ui.say(f"Stopped after {done} of {len(ops)} changes. Those {done} are in the undo log;"
               f" reverse them with: renamer {shlex.quote(str(show_dir))} --undo")
        return 1
    progress.finish()
    journal.finish()
    ui.say(f"Done: {_plural(done, 'change')}. To reverse them: renamer {shlex.quote(str(show_dir))} --undo")
    if skipped:
        ui.warn(f"skipped {_plural(len(skipped), 'file')} that {'was' if len(skipped) == 1 else 'were'} in use "
                "(with their subtitles and .nfo); run renamer again later to rename "
                f"{'it' if len(skipped) == 1 else 'them'}:")
        for path in skipped:
            ui.say(f"  {path}")
    if failed:
        ui.warn(f"couldn't update the tags in {_plural(len(failed), 'video')}; "
                f"{'it was' if len(failed) == 1 else 'they were'} left as before:")
        for path, reason in failed:
            ui.say(f"  {path}  ({reason})")
    return 0


# -------------------------------------------------------------- rename run

def _guess_show(layout: Layout, groups: list[Group]) -> tuple[str, str]:
    """The show-name text to start from, and where it came from (show name)."""
    candidates = []
    if layout.trusted:
        if _SEASONS_LAYER.fullmatch(layout.show_dir.name):   # release/Series/: the release names the show
            candidates.append((layout.show_dir.parent.name, "the folder above"))
        if not _GENERIC_FOLDER.fullmatch(layout.show_dir.name):
            candidates.append((layout.show_dir.name, "the show folder name"))
    else:
        candidates += [(d.name, "the season folder name") for d, _ in layout.seasons]
    for name, where in candidates:
        guess = show_from_folder(name)
        if clean_text(guess):
            return guess, where
    for g in groups:
        m = _episode_match(Path(g.video.name).stem)
        if m and m.start():
            return show_from_folder(g.video.name[:m.start()], True), f"the filename {g.video.name}"
    for g in groups:
        if g.plain and g.plain.before:
            return show_from_folder(g.plain.before, True), f"the filename {g.video.name}"
    return "", "nowhere"


TYPED = "a name you typed"


def _files_show(groups: list[Group]) -> tuple[str, int]:
    """The show name most of the filenames start with, and how many do (show name)."""
    counts: Counter = Counter()
    first: dict[str, str] = {}
    for g in groups:
        name = readable(show_from_folder(show_in_filename(g.video.name), True))
        key = normalize_title(name)
        if len(key) >= 4:   # "x.s01e01", "dl.s01e01": a short prefix, not a show name to go by
            counts[key] += 1
            first.setdefault(key, name)
    if not counts:
        return "", 0
    key, n = counts.most_common(1)[0]
    if n * 2 < sum(counts.values()) or (n < 2 < len(groups)):
        # No name most of them share: the text before SxxEyy is each file's own title
        # ("Looking at Your Browser History.S01E03.mkv"), not the show's (1.0.0, from a real library).
        return "", 0
    return first[key], n


def _check_guess(guess: str, guess_from: str, groups: list[Group], ui: UI, names_mode: bool
                 ) -> tuple[str, str]:
    """When the folder's name and the filenames name different shows (a show kept in a folder
    called "Scifi"), ask which to use; the filenames come first (show name)."""
    if guess_from.startswith("the filename"):
        return guess, guess_from
    files, n = _files_show(groups)
    folder_key, files_key = normalize_title(readable(guess)), normalize_title(files)
    if not files_key or (folder_key and same_show_key(files_key, folder_key)):
        return guess, guess_from
    files_from = f"{_plural(n, 'filename')}"
    if not folder_key:
        return files, files_from
    folder_text = readable(guess)
    ui.detail(f"Show name: {guess_from} says {folder_text!r}, {files_from} say {files!r}")
    if names_mode:
        return files, f"{files_from} (the folder name {folder_text!r} names a different show)"
    width = max(len(files), len(folder_text))
    ui.say("The folder and the files name different shows:")
    ui.say(f"  1) {files:<{width}}  (from {files_from})")
    ui.say(f"  2) {folder_text:<{width}}  ({guess_from})")
    while True:
        answer = ui.ask("Search TVmaze for [1], or type a name: ", "1")
        if answer == "1":
            chosen = files, files_from
            break
        if answer == "2":
            chosen = guess, guess_from
            break
        if not answer.isdigit():
            chosen = answer, TYPED
            break
        ui.say("Type 1, 2 or a name to search for.")
    ui.say()
    return chosen


def resolve_show(args, layout: Layout, groups: list[Group], ui: UI, get: Getter
                 ) -> tuple[str, ShowInfo, Titles, list[EpisodeInfo], str, str]:
    """Show name, show details, titles, TVmaze specials, where titles came from, and how the
    name was chosen."""
    guess, guess_from = _guess_show(layout, groups)
    debug(f"show name guesses: folder {guess!r} ({guess_from}), files {_files_show(groups)}, --show {args.show!r}")
    if not args.show:
        guess, guess_from = _check_guess(guess, guess_from, groups, ui, names_mode=bool(args.names))
    specials: list[EpisodeInfo] = []
    if args.names:
        titles = parse_names(args.names)
        source = f"nameInfo ({args.names.name})"
        if args.show:
            display, how = args.show, "from --show"
        else:
            suggestion = guess if guess_from == TYPED else title_case(readable(guess))
            display = ui.ask(f"Show name [{suggestion}]: ", suggestion)
            while not clean_text(display) and ui.interactive:
                display = ui.ask("Type the show name: ")
            how = f"suggested from {guess_from}" + ("" if display == suggestion else ", then typed")
        info = ShowInfo(name=display)
    else:
        query = args.show or readable(guess)
        if not query:
            raise RenamerError("Couldn't work out the show name to search TVmaze for; give it with --show.")
        with_specials = any(g.season == 0 for g in groups if not g.status)
        info, titles, specials, used = tvmaze_lookup(query, ui, get, with_specials, evidence_from(layout, groups))
        titles = use_overall_numbers(info, titles, get)
        source = f"TVmaze ({info.name}{f', {info.year}' if info.year else ''})"
        display = args.show or info.name
        how = ("from --show" if args.show
               else f'TVmaze show #{info.ids["tvmaze"]}, searched as "{used}" (from {guess_from})')
        if args.show:
            info.name = args.show
    show = clean_text(display)
    if not show:
        raise RenamerError("Couldn't work out the show name; give it with --show.")
    return show, info, titles, specials, source, how


def ask_missing_titles(groups: list[Group], titles: Titles, ui: UI) -> None:
    """Ask once per episode that has no title; Enter leaves it untitled."""
    if not ui.interactive:
        return
    asked: set[tuple[int, int]] = set()
    for g in groups:
        if g.status:
            continue
        for e in g.episodes:
            key = (g.season, e)
            existing = g.overrides.get(e) or titles.get(key)
            if key in asked or (existing and clean_text(existing.title)):
                continue
            asked.add(key)
            typed = ui.ask(f"No title for S{g.season:02d}E{e:02d} ({g.video.name})\n"
                           "Type a title, or press Enter to leave it untitled: ")
            if typed:
                if existing:
                    existing.title, existing.source = typed, "typed at the prompt"
                else:
                    titles[key] = EpisodeInfo(title=typed, source="typed at the prompt")


def ask_extras_junk(extras: list[Path], home: Path, ui: UI) -> list[Path]:
    """Junk inside extras folders is only cleaned when you say so."""
    if not extras:
        return []
    folders = sorted({p.relative_to(home).parts[0] for p in extras})
    ui.say(f"{', '.join(f + '/' for f in folders)} {'has' if len(folders) == 1 else 'have'} "
           f"{_plural(len(extras), 'junk file')}:")
    for path in extras:
        ui.say(f"  {path.relative_to(home).as_posix()}")
    if ui.ask("Include them with the rest? [y/N]: ").lower() in ("y", "yes"):
        return extras
    return []


def title_sources(groups: list[Group], titles: Titles) -> str:
    """One line for --verbose on how every episode got its title."""
    counts: Counter = Counter()
    for g in groups:
        if g.status:
            continue
        if g.renumbered:
            counts["renumbered by title"] += 1
        for e in g.episodes:
            info = g.overrides.get(e) or titles.get((g.season, e))
            source = info.source if info and clean_text(info.title) else ""
            if source.startswith("TVmaze episode"):
                counts["from TVmaze by episode number"] += 1
            elif source.startswith("TVmaze special"):
                counts["from TVmaze specials by title"] += 1
            elif source.startswith("the filename"):
                counts["from the filename"] += 1
            elif source.startswith("typed"):
                counts["typed"] += 1
            elif source:
                counts["from the nameInfo file"] += 1
            else:
                counts["without a title"] += 1
    return "Title sources: " + (", ".join(f"{n} {what}" for what, n in counts.most_common()) or "none needed")


def _undo_log_detail(show_dir: Path) -> str:
    path = show_dir / UNDO_LOG
    if not path.exists():
        return "Undo log: none yet"
    try:
        runs = len(load_log(path)["runs"])
    except RenamerError:
        return "Undo log: present but damaged"
    return f"Undo log: {runs} earlier run{'' if runs == 1 else 's'} recorded"


@dataclass
class SortOffer:
    """Videos renamer can't rename where they are, which --sort would gather (0.8.1)."""
    folder: Path                       # what --sort runs on
    lone: bool                         # a season folder with no show folder around it
    videos: list[tuple[str, str]]      # (where it is, its SxxEyy), for the question


def sort_offer(layout: Layout) -> SortOffer | None:
    show_dir = layout.show_dir
    if not layout.trusted:
        return SortOffer(show_dir, True, [])
    videos = []
    for d in layout.ignored:
        if _EXTRAS_FOLDER.fullmatch(d.name) or _SUBS_FOLDER.fullmatch(d.name):
            continue
        for folder, dirs, files in os.walk(d):
            dirs[:] = [x for x in dirs if not x.startswith(".")]
            for name in sorted(files, key=natural_key):
                found = parse_episode(name) if Path(name).suffix.lower() in VIDEO_EXTS else None
                if found and not _SAMPLE.search(Path(name).stem) and not name.startswith("."):
                    videos.append((d.relative_to(show_dir).as_posix() + "/", _code(*found)))
    if layout.seasons:   # with season folders, videos lying loose in the show folder aren't renamed either
        for p in _entries(show_dir, dirs=False):
            found = parse_episode(p.name) if p.suffix.lower() in VIDEO_EXTS else None
            if found:
                videos.append(("(loose in the show folder)", _code(*found)))
    return SortOffer(show_dir, False, videos) if videos else None


def _offer_text(offer: SortOffer) -> str:
    if offer.lone:
        return (f"{offer.folder.name}/ is one season with no show folder around it, in {offer.folder.parent}/. "
                f"Sorting puts its videos in a Season_NN folder inside it, so it becomes a proper show folder.")
    codes = sorted({c for _, c in offer.videos}, key=natural_key)
    shown = ", ".join(codes[:8]) + (", …" if len(codes) > 8 else "")
    return (f"{_plural(len(offer.videos), 'video')} {'is' if len(offer.videos) == 1 else 'are'} in release folders "
            f"or loose in {offer.folder.name}/, where renamer can't rename them ({shown}).")


def ask_sort(ui: UI, offer: SortOffer) -> bool:
    """The question a renaming run asks before anything else when --sort would help (0.8.1)."""
    ui.say(_offer_text(offer))
    if not offer.lone:
        width = max(len(w) for w, _ in offer.videos)
        for where, code in offer.videos[:20]:
            ui.say(f"  {where:<{width}}  {code}")
        if len(offer.videos) > 20:
            ui.say(f"  … and {len(offer.videos) - 20} more")
    answer = ui.ask("Sort them into season folders first (renamer --sort)? [Y/n]: ", "y")
    ui.say()
    return answer.lower() not in ("n", "no")


RENUMBER_NOTE = "NOTE: the title matches TVmaze "


def ask_renumber(ui: UI, groups: list[Group]) -> bool:
    """When titles belong to other TVmaze numbers, ask instead of telling the user to rerun with
    --renumber (0.8.1)."""
    found = [(g.video.name, w) for g in groups for w in g.warns if w.startswith(RENUMBER_NOTE)]
    ui.say(f"{_plural(len(found), 'file')} {'has a title' if len(found) == 1 else 'have titles'} that "
           "TVmaze gives a different episode number:")
    for name, note in found[:20]:
        m = re.search(r"TVmaze (S\d+E\d+), but the filename says (S\d+E\d+)", note)
        ui.say(f"  {name}" + (f"  (the filename says {m.group(2)}, TVmaze {m.group(1)})" if m else ""))
    answer = ui.ask("Use TVmaze's numbers for these (--renumber)? [y/N]: ")
    ui.say()
    return answer.lower() in ("y", "yes")


def refuse_group(folder: Path) -> None:
    """A folder lib --group made holds whole releases, each to be worked on by itself."""
    if (folder / GROUP_MARKER).is_file():
        raise RenamerError(f"{folder.name}/ holds several copies of one show (renamer lib --group), so it isn't one "
                           "show folder. Give one of the releases inside it.")


def seasons_layer(folder: Path) -> Path | None:
    """The folder between a release and its seasons (Show.S01-S13/Series/Season 1), when there's
    one: no seasons directly in the release, one subfolder holding them, and a generic name."""
    subs = _entries(folder, dirs=True)
    if any(season_from_folder(d.name) is not None for d in subs):
        return None
    holders = [d for d in subs if any(season_from_folder(x.name) is not None for x in _entries(d, dirs=True))]
    return holders[0] if len(holders) == 1 and _SEASONS_LAYER.fullmatch(holders[0].name) else None


def movies_in_show(show_dir: Path, layer: Path | None = None) -> list[Path]:
    """Movies beside a show's seasons: a folder or video with a year in its name and no episode
    numbers (Example Movie (2022)/ with its featurettes). Many of them are the show's
    specials, not movies (Example Special (1991)/ and nine more), so they stay."""
    subs = _entries(show_dir, dirs=True)
    if not layer and not any(season_from_folder(d.name) is not None for d in subs):
        return []
    found = []
    for d in subs:
        if (d == layer or season_from_folder(d.name) is not None or _SHOW_EXTRAS.fullmatch(d.name)
                or not _HAS_YEAR.search(d.name)):
            continue
        videos = [f for _, _, fs in os.walk(d) for f in fs if Path(f).suffix.lower() in VIDEO_EXTS and not f.startswith(".")]
        if videos and not any(parse_episode(f) for f in videos):
            found.append(d)
    for p in _entries(show_dir, dirs=False):
        if (p.suffix.lower() in VIDEO_EXTS and _HAS_YEAR.search(p.stem) and not parse_episode(p.name)
                and not _SAMPLE.search(p.stem)):
            found.append(p)
    return found if len(found) <= MAX_MOVIES_IN_SHOW else []


def unwrap_plan(show_dir: Path, layer: Path, base: Path) -> tuple[list[Op], list[Row]]:
    """Everything in a seasons layer up into the show folder, and the layer removed; paths relative
    to base. Anything in the way makes it one CONFLICT and no changes."""
    rel = lambda p: p.relative_to(base).as_posix()
    entries = sorted(os.listdir(layer), key=natural_key)
    taken = {n.casefold() for n in os.listdir(show_dir)}
    clash = [n for n in entries if n.casefold() in taken]
    if UNDO_LOG in entries:
        return [], [Row("CONFLICT", rel(layer) + "/", "", "it has an undo log of its own; undo that run first")]
    if clash:
        return [], [Row("CONFLICT", rel(layer) + "/", "", f"{rel(show_dir / clash[0])} is in the way")]
    ops, rows = [], []
    for name in entries:
        is_dir = (layer / name).is_dir()
        ops.append(Op("lib", rel(layer / name), rel(show_dir / name), is_dir=is_dir))
        slash = "/" if is_dir else ""
        rows.append(Row("MOVE", rel(layer / name) + slash, rel(show_dir / name) + slash, ""))
    ops.append(Op("rmdir", dst=rel(layer), is_dir=True))
    rows.append(Row("REMOVE", rel(layer) + "/", "", "empty by then"))
    return ops, rows


def tidy_release(target: Path, ui: UI) -> int | None:
    """Before a rename: offers to remove a seasons layer and to move movies out of the show.
    Returns None to carry on, or the exit code when the run should stop here."""
    layer = seasons_layer(target)
    movies = movies_in_show(target, layer)
    if not layer and not movies:
        return None
    if not ui.interactive:
        if layer:
            raise RenamerError(f"{target.name}/ keeps its season folders inside {layer.name}/. Run renamer in a "
                               "terminal to move them up. Nothing was changed.")
        return None
    downloads = find_downloads(target)
    if downloads:
        return report_downloads(ui, target, downloads) if layer else None
    if not os.access(target, os.W_OK):
        if layer:
            raise RenamerError(f"{target.name}/ keeps its season folders inside {layer.name}/, and there's no write "
                               "permission to move them up. Nothing was changed.")
        return None
    plan = Plan()
    if layer:
        ui.start_log(log_name_for(target))
        seasons = [d for d in _entries(layer, dirs=True) if season_from_folder(d.name) is not None]
        ui.say(f"{target.name}/ keeps its {_plural(len(seasons), 'season folder')} inside {layer.name}/.")
        answer = ui.ask(f"Move them up into the show folder and remove {layer.name}/? [Y/n]: ", "y")
        ui.say()
        if answer.lower() in ("n", "no"):
            ui.say("Nothing was changed.")
            return 0
        ops, rows = unwrap_plan(target, layer, target)
        if not ops:
            raise RenamerError(f"Can't move the seasons up out of {layer.name}/: {rows[0].note}. Nothing was changed.")
        plan.sections[f"Out of {layer.name}/"] = rows
        plan.ops += ops
    movies_dir = find_movies_dir(target.parent)
    on_disk = movies_dir.is_dir()
    same_disk = not on_disk or os.stat(movies_dir).st_dev == os.stat(target).st_dev
    taken = {n.casefold() for n in os.listdir(movies_dir)} if on_disk else set()
    for movie in movies:
        slash = "/" if movie.is_dir() else ""
        if not same_disk:
            ui.say(f"{movie.name}{slash} looks like a movie, but {movies_dir} is on another disk; it stays here.")
        elif movie.name.casefold() in taken:
            ui.say(f"{movie.name}{slash} looks like a movie, but {movies_dir} already has one by that name; it stays here.")
        else:
            ui.say(f"{movie.name}{slash} looks like a movie, not part of the show.")
            answer = ui.ask(f"Move it to {movies_dir}/? [Y/n]: ", "y")
            ui.say()
            if answer.lower() in ("n", "no"):
                continue
            if not on_disk and not any(o.kind == "mkdir" for o in plan.ops):
                plan.ops.append(Op("mkdir", dst=os.path.relpath(movies_dir, target)))
            dest = os.path.relpath(movies_dir / movie.name, target)
            plan.ops.append(Op("lib", movie.name, dest, is_dir=movie.is_dir()))
            plan.sections.setdefault(f"To {movies_dir}/", []).append(Row("MOVE", movie.name + slash, dest + slash, "a movie"))
    if not plan.ops:
        return None
    print_preview(ui, [f"Folder: {target}", "Mode:   tidying the release first (only moves folders; the rename "
                       "follows straight after)"], plan)
    if not confirm(ui, _summary(plan.ops)):
        return 0
    code = apply_ops(plan.ops, target, ui, "Moving")
    if code:
        return code
    ui.say()
    ui.say("Looking at the folder again for the rename…")
    ui.say()
    return None


def check_show_folder(folder: Path) -> None:
    """Stop before anything is searched for when there's nothing renamer could work on (0.8.1)."""
    refuse_group(folder)
    layer = seasons_layer(folder)
    if layer:
        raise RenamerError(f"{folder.name}/ keeps its season folders inside {layer.name}/. Give that folder, or run "
                           f"renamer {shlex.quote(str(folder))} to move them up.")
    if _is_bundle(folder):
        raise RenamerError(f"{folder.name}/ holds several shows or releases, each with its own seasons. Give one of "
                           "the folders inside it, or sort them out with renamer lib --sort on the folder above.")
    if is_movie_collection(folder):
        raise RenamerError(f"{folder.name}/ looks like a collection of movies, not a show: its videos have years and "
                           "no episode numbers. renamer lib --sort on the folder above moves it to your movies folder.")
    if not looks_like_show(folder):
        raise RenamerError(f"No season folders or episode videos in {folder}, so there's nothing to work on here. "
                           'Give a show folder, for example: renamer "/mnt/media/TV/Example Show"')


def run_rename(args, ui: UI, fetch: Callable[[str], object] = http_get_json) -> int:
    target = _full_path(args.path)
    if not target.is_dir():
        raise RenamerError(f"Not a folder: {target}")
    refuse_group(target)
    if seasons_layer(target.parent) == target:   # given release/Series/: the same as being given the release
        target = target.parent
        args.path = str(target)
    if not getattr(args, "tidied", False):
        args.tidied = True
        code = tidy_release(target, ui)
        if code is not None:
            return code
    check_show_folder(target)
    layout = find_layout(target)
    scan_root = layout.show_dir if layout.trusted else target
    downloads = find_downloads(scan_root)
    if downloads:
        return report_downloads(ui, scan_root, downloads)
    if not os.access(layout.show_dir, os.W_OK):
        raise RenamerError(f"No write permission in {layout.show_dir}, so the undo log can't be written there. "
                           "Nothing was changed.")
    offer = sort_offer(layout)
    if offer and ui.interactive and not getattr(args, "sorted_already", False):
        args.sorted_already = True
        if ask_sort(ui, offer):
            sort_args = argparse.Namespace(**{**vars(args), "path": str(offer.folder), "sort": True})
            try:
                run_sort(sort_args, ui, chained=True)
            except RenamerError as e:
                ui.say(f"The sort didn't run: {e}")
            ui.say()
            ui.say("Looking at the folder again for the rename…")
            ui.say()
            return run_rename(args, ui, fetch)

    groups, not_handled = collect_groups(layout, ui)
    get = Getter(fetch, ui)
    show, info, titles, specials, source, show_how = resolve_show(args, layout, groups, ui, get)
    ui.start_log(show)
    groups, not_handled = settle_show(args, layout, groups, not_handled, ui, info, titles, specials, get)
    renumber = getattr(args, "renumber", False)
    pristine = copy.deepcopy(groups)
    suggested = resolve_titles(groups, titles, specials, from_tvmaze=not args.names, renumber=renumber)
    if suggested and ui.interactive and not renumber and ask_renumber(ui, groups):
        groups = pristine
        resolve_titles(groups, titles, specials, from_tvmaze=True, renumber=True)
        suggested = 0
    mark_duplicates(groups)
    warnings = info.notes + season_warnings(groups, titles, layout, from_tvmaze=not args.names, overall=info.overall)
    in_releases = [v for v in offer.videos if not v[0].startswith("(loose")] if offer else []
    if in_releases:
        # The missing episodes are probably the ones in release folders, and the episode count
        # looks short for the same reason, so that warning would mislead. Loose videos already
        # have their own warning.
        warnings = [w + " Some may be the videos in release folders; see below." if "no file for" in w else w
                    for w in warnings if "TVmaze lists" not in w]
        warnings.append(_offer_text(SortOffer(offer.folder, False, in_releases))
                        + " renamer --sort gathers them into season folders.")
    if (not args.names and ui.interactive and not getattr(args, "names_offered", False)
            and any(k in w for w in warnings for k in NUMBERING)):
        args.names_offered = True
        path = ask_names_file(ui, show, info, titles, specials, warnings)
        if path:
            # The same run again, with the edited titles instead of TVmaze's (offline from here).
            args.names, args.show, args.renumber = path, show, False
            return run_rename(args, ui, fetch)
    loose = sum(1 for g in groups if g.status == "LOOSE")
    if loose:
        one = loose == 1
        warnings.append(f"{loose} video{' is' if one else 's are'} loose in the show folder and left alone. "
                        f"Move {'it' if one else 'them'} into a season folder to have "
                        f"{'it' if one else 'them'} renamed.")
    if suggested:
        warnings.append(f"{_plural(suggested, 'file')} {'has a title' if suggested == 1 else 'have titles'} "
                        "matching a different TVmaze episode number. They keep their own numbers; "
                        "run with --renumber to use TVmaze's.")
    junk: list[Path] = []
    if getattr(args, "clean", False):
        junk, extras_junk = find_junk(layout)
        junk += ask_extras_junk(extras_junk, layout.home, ui)
    ask_missing_titles(groups, titles, ui)

    years = None
    details = [f"Show name: {show_how}"]
    if args.years:
        if not args.names:
            years, years_how = info.years, info.years_how
        else:
            name = layout.show_dir.name if layout.trusted else layout.seasons[0][0].name
            years, years_how = folder_years(name), f"the folder name {name}"
        if years:
            details.append(f"Years: {years} (from {years_how})")
        else:
            warnings.append("--years: no years found, so they're left out of the show folder name.")
    details.append(title_sources(groups, titles))
    seasons_text = ", ".join(f"{d.name} (season {n})" for d, n in layout.seasons) or "none"
    details.append(f"Season folders: {seasons_text}")
    if not layout.trusted:
        details.append(f"{target.parent.name}/ holds other folders too, so it's treated as a plain "
                       f"parent folder, and {target.name}/ as its own show folder.")
        warnings.append(f"{target.name}/ sits directly in {target.parent.name}/. renamer --sort on it makes it a "
                        "show folder with a Season_NN folder inside, so tvshow.nfo can be written.")
    details.append(_undo_log_detail(layout.show_dir))

    plan = build_plan(groups, layout, show, info, titles, args.nfo, args.fix_folders, years, junk,
                      meta=getattr(args, "meta", False), ui=ui)
    plan.warnings = warnings + plan.warnings
    plan.details = details
    plan.not_handled = ([(p.relative_to(layout.show_dir).as_posix(), reason) for p, reason in not_handled
                         if not (junk and p in junk)] + plan.not_handled)
    print_preview(ui, [f"Show:   {show}", f"Titles: {source}", f"Folder: {layout.show_dir}"], plan)
    if not plan.ops:
        ui.say("Nothing to change.")
        return 0
    answer = confirm(ui, _summary(plan.ops), allow_delete=any(o.kind == "junk" for o in plan.ops))
    if answer is None:
        return 0 if ui.interactive else 1
    if answer == "delete":
        plan.ops = junk_to_delete(plan.ops)
    return apply_ops(plan.ops, layout.show_dir, ui)


def names_file_lines(info: ShowInfo, titles: Titles, specials: list[EpisodeInfo]) -> list[str]:
    """A nameInfo file of TVmaze's titles, to edit so each line matches one file."""
    lines = [f"# nameInfo for {info.name}, from TVmaze (renamer {VERSION}).",
             "# One line per video file, in order. When one file holds several TVmaze episodes,",
             "# join their titles on one line with \" + \", for example:  First Title + Second Title",
             "# Then run:  renamer <show folder> --names <this file>", ""]
    for season in sorted({s for s, _ in titles if s > 0}):
        lines.append(f"S{season:02d}")
        top = max(e for s, e in titles if s == season)
        for e in range(1, top + 1):
            info_e = titles.get((season, e))
            lines.append(info_e.title if info_e and info_e.title.strip() else f"Episode {e}")
        lines.append("")
    if specials:
        lines += ["# Specials: TVmaze doesn't number these, so reorder them to match your files.", "S00"]
        lines += [sp.title for sp in specials] + [""]
    return lines


# Titles files written for the editor (0.8.1), kept so the next run can use the same edits.
NAMES_DIR = Path(os.environ.get("XDG_DATA_HOME") or Path.home() / ".local" / "share") / "renamer" / "names"
# Warnings that mean TVmaze numbers the episodes differently from the files.
NUMBERING = ("TVmaze lists", "TVmaze has no season", "but TVmaze's season", "numbered by sort order")


def find_editor() -> list[str]:
    cmd = shlex.split(os.environ.get("VISUAL") or os.environ.get("EDITOR") or "")
    if cmd:
        return cmd
    return next(([e] for e in ("nano", "vi") if shutil.which(e)), [])


def open_in_editor(cmd: list[str], path: Path) -> bool:
    try:
        return subprocess.run([*cmd, str(path)]).returncode == 0
    except OSError:
        return False


def ask_names_file(ui: UI, show: str, info: ShowInfo, titles: Titles, specials: list[EpisodeInfo],
                   warnings: list[str]) -> Path | None:
    """When TVmaze's numbering doesn't fit the files, offer to write its titles to a file, open
    it in the editor, and rename from it, instead of saying to run --make-names and --names (0.8.1)."""
    editor = find_editor()
    if not editor:
        return None
    ui.say("TVmaze numbers this show differently from the files:")
    for w in warnings:
        if any(k in w for k in NUMBERING):
            ui.say(f"  {w}")
    path = NAMES_DIR / f"{show}.txt"
    if path.exists():
        question = f"Open the titles file from last time ({path}) in {editor[0]} and rename from it? [y/N]: "
    else:
        question = (f"Write TVmaze's titles to a file, open it in {editor[0]} so each line matches one of your "
                    "files, and rename from it? [y/N]: ")
    if ui.ask(question).lower() not in ("y", "yes"):
        ui.say()
        return None
    if not path.exists():
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("\n".join(names_file_lines(info, titles, specials)), encoding="utf-8")
        except OSError as e:
            ui.say(f"Can't write {path} ({e.strerror}); carrying on with TVmaze's numbers.")
            return None
    ui.say(f"Opening {path}. Save it and close the editor to carry on.")
    if not open_in_editor(editor, path):
        ui.say(f"{editor[0]} didn't finish normally; carrying on with TVmaze's numbers.")
        return None
    ui.say()
    return path


def run_make_names(args, ui: UI, fetch: Callable[[str], object] = http_get_json) -> int:
    """--make-names: write a nameInfo file from TVmaze's titles, to edit and use with --names."""
    out = Path(args.make_names).expanduser()
    if out.exists():
        raise RenamerError(f"{out} already exists; not overwriting it. Pick another name or move it first.")
    target = _full_path(args.path)
    if not target.is_dir():
        raise RenamerError(f"Not a folder: {target}")
    check_show_folder(target)
    layout = find_layout(target)
    guess, _ = _guess_show(layout, [])
    query = args.show or readable(guess)
    if not query:
        raise RenamerError("Couldn't work out the show name to search TVmaze for; give it with --show.")
    info, titles, specials, _ = tvmaze_lookup(query, ui, Getter(fetch, ui), with_specials=True)
    ui.start_log(clean_text(info.name) + "_names")
    lines = names_file_lines(info, titles, specials)
    seasons = sorted({s for s, _ in titles if s > 0})
    try:
        with open(out, "x", encoding="utf-8") as f:
            f.write("\n".join(lines))
    except OSError as e:
        raise RenamerError(f"Can't write {out} ({e.strerror}).") from None
    count = sum(1 for s, _ in titles if s > 0) + len(specials)
    ui.say(f"Wrote {out}: {_plural(len(seasons), 'season')}, {_plural(count, 'title')}.")
    ui.say("Edit it so each line matches one file, then run: "
           f"renamer {shlex.quote(str(target))} --names {shlex.quote(str(out))}")
    return 0


# ---------------------------------------------------------------- sort

DUPES_DIR = ".duplicates"       # worse copies of an episode go here, keeping their path
UNSORTED_DIR = "unsorted"       # next to the show folder: videos of a different show go here
_SAMPLE_FOLDER = re.compile(r"samples?", re.I)
_SCREENS_FOLDER = re.compile(r"screens?|screenshots?|screencaps?", re.I)
_QUALITY = (
    (re.compile(r"(?<![0-9a-z])(?:2160p|4k|uhd)(?![0-9a-z])", re.I), 4, "2160p"),
    (re.compile(r"(?<![0-9a-z])1080[pi](?![0-9a-z])", re.I), 3, "1080p"),
    (re.compile(r"(?<![0-9a-z])720p(?![0-9a-z])", re.I), 2, "720p"),
)


def quality(name: str) -> tuple[int, str]:
    """How good a copy looks from its name: 2160p > 1080p > 720p > anything else."""
    for pattern, rank, label in _QUALITY:
        if pattern.search(name):
            return rank, label
    return 1, "SD or unknown"


def show_in_filename(filename: str) -> str:
    """The show name written before a filename's SxxExx ("Example.Show.S03E01…" -> "Example Show")."""
    stem = Path(filename).stem
    m = _episode_match(stem)
    return readable(stem[:m.start()]) if m else ""


def same_show(filename: str, show_key: str) -> bool:
    """Whether a filename's own show name is this show. A filename without one counts as this
    show; release-group prefixes ("daa-example.show") and small spelling differences are allowed."""
    raw = show_in_filename(filename)
    return any(not (key := normalize_title(candidate)) or same_show_key(key, show_key)
               for candidate in (raw, raw.rsplit(" - ", 1)[-1]))


def same_show_key(key: str, show_key: str) -> bool:
    """Two normalized show names name the same show: one holds the other, or they're spelled
    almost alike."""
    return show_key in key or key in show_key or difflib.SequenceMatcher(None, key, show_key).ratio() >= 0.8


@dataclass
class SortVideo:
    path: Path
    season: int
    episodes: list[int]
    part: int | None
    size: int
    rank: int
    label: str
    subs: list[Path] = field(default_factory=list)


def _walk_show(show_dir: Path) -> list[tuple[Path, str]]:
    """Every file in the show folder with the kind of folder it's in: "", "extras", "sample" or
    "screens". Hidden folders (.nfo, .junk, .duplicates) are skipped; of hidden files only old
    .nfo backups are kept, for the .nfo sweep."""
    found = []
    stack = [(show_dir, "")]
    while stack:
        folder, area = stack.pop()
        with os.scandir(folder) as it:
            entries = sorted(it, key=lambda e: natural_key(e.name))
        for e in entries:
            path = Path(e.path)
            if e.is_dir():
                if e.name.startswith("."):
                    continue
                inner = area or ("sample" if _SAMPLE_FOLDER.fullmatch(e.name) else
                                 "screens" if _SCREENS_FOLDER.fullmatch(e.name) else
                                 "extras" if _EXTRAS_FOLDER.fullmatch(e.name) else "")
                stack.append((path, inner))
            elif e.name == UNDO_LOG or (e.name.startswith(".") and not e.name.lower().endswith(".nfo")
                                        and not is_junk(path)):
                continue
            else:
                found.append((path, area))
    return found


def build_sort_plan(show_dir: Path, ui: UI, clean: bool, prefer: list[str] | None = None) -> tuple[Plan, str]:
    """Plan for --sort: every video moves into its season folder, worse copies to .duplicates/,
    other shows to ../unsorted/, and with --clean junk to .junk/ and emptied folders are removed."""
    show_name = readable(show_from_folder(show_dir.name))
    show_key = normalize_title(show_name)
    if not show_key:
        raise RenamerError("Couldn't work out the show's name from its folder name. Nothing was changed.")
    plan = Plan()
    listing = _Listing()
    dirs = _Dirs(show_dir, listing)
    unsorted = show_dir.parent / UNSORTED_DIR

    def rel(p: Path) -> str:
        return Path(os.path.relpath(p, show_dir)).as_posix()

    def section(label: str) -> list[Row]:
        return plan.sections.setdefault(label, [])

    left_label = "Left alone"
    files = _walk_show(show_dir)
    videos = [(p, a) for p, a in files if p.suffix.lower() in VIDEO_EXTS and not p.name.startswith(".")]
    subtitles = [(p, a) for p, a in files if p.suffix.lower() in SUB_EXTS and not p.name.startswith(".")]
    others = [(p, a) for p, a in files if p.suffix.lower() not in VIDEO_EXTS | SUB_EXTS or p.name.startswith(".")]

    # 1. What each video is.
    mine: list[SortVideo] = []
    other: list[Path] = []
    samples: list[Path] = []
    for path, area in videos:
        if area == "extras":
            section(left_label).append(Row("IGNORED", rel(path), "", "in an extras folder"))
        elif area == "sample" or _SAMPLE.search(path.stem):
            samples.append(path)
        elif not (parsed := parse_episode(path.name, season_from_folder(path.parent.name))):
            note = ("only a plain episode number; renaming works it out from TVmaze's list" if plain_numbers(path.name)
                    else "no season/episode in its name")
            section(left_label).append(Row("UNMATCHED", rel(path), "", note))
        elif not same_show(path.name, show_key):
            other.append(path)
        else:
            tags = path.name if path.parent == show_dir else f"{path.name} {path.parent.name}"
            rank, label = quality(tags)
            mine.append(SortVideo(path, parsed[0], parsed[1],
                                  title_from_filename(path.name, season_from_folder(path.parent.name))[1],
                                  path.stat().st_size, rank, label))
    if len(other) > len(mine):
        raise RenamerError(f"Most videos here don't look like {show_name}. Run --sort on one show's folder, "
                           "not on a folder of several shows. Nothing was changed.")

    # 2. Release folders: a folder holding exactly one video belongs to that video.
    all_videos = [v.path for v in mine] + other

    def release_dir(video: Path) -> Path | None:
        d = video.parent
        if d == show_dir or sum(1 for q in all_videos if d in q.parents) != 1:
            return None
        return d

    # 3. Subtitles go with their video: named after it, or inside its release folder.
    other_subs: dict[Path, list[Path]] = {}
    orphan_subs: list[tuple[Path, int]] = []
    for sub, area in subtitles:
        if area == "extras":
            section(left_label).append(Row("IGNORED", rel(sub), "", "in an extras folder"))
            continue
        owner = next((v for v in mine if sub.parent == v.path.parent and sub.name.startswith(v.path.stem + ".")), None)
        owner = owner or next((v for v in mine if (d := release_dir(v.path)) and d in sub.parents), None)
        if owner:
            owner.subs.append(sub)
            continue
        loose_other = next((o for o in other if sub.parent == o.parent and sub.name.startswith(o.stem + ".")), None)
        if loose_other or any((d := release_dir(o)) and d in sub.parents for o in other):
            if loose_other:
                other_subs.setdefault(loose_other, []).append(sub)
            continue
        parsed = parse_episode(sub.name)
        if parsed and same_show(sub.name, show_key):
            orphan_subs.append((sub, parsed[0]))
        else:
            section(left_label).append(Row("IGNORED", rel(sub), "", "subtitle with no matching video"))

    # 4. Duplicates: the best copy of each episode stays; the rest go to .duplicates/.
    by_episode: dict[tuple, list[SortVideo]] = {}
    for v in mine:
        by_episode.setdefault((v.season, tuple(v.episodes), v.part), []).append(v)
    best: list[SortVideo] = []
    worse: list[tuple[SortVideo, SortVideo]] = []
    for copies in by_episode.values():
        copies.sort(key=lambda v: (v.rank, v.size), reverse=True)
        same_release = prefer_release(copies, prefer or [])   # the show's own release wins (1.0.0)
        if same_release:
            copies.remove(same_release)
            copies.insert(0, same_release)
        best.append(copies[0])
        worse += [(v, copies[0]) for v in copies[1:]]

    # 5. Season folders: reuse one that's already there, otherwise Season_NN.
    existing: dict[int, Path] = {}
    for d in _entries(show_dir, dirs=True):
        n = season_from_folder(d.name)
        if n is not None and (n not in existing or d.name == f"Season_{n:02d}"):
            existing[n] = d

    def season_dir(n: int) -> Path:
        return existing.get(n) or show_dir / f"Season_{n:0{3 if n >= 100 else 2}d}"

    def subs_dir(folder: Path) -> Path:
        found = next((d for d in _entries(folder, dirs=True) if _SUBS_FOLDER.fullmatch(d.name)), None) \
            if folder.is_dir() else None
        return found or folder / "Subs"

    moves: list[Op] = []
    moving: set[Path] = set()         # files leaving their folder, for removing emptied folders
    away: set[Path] = set()           # whole folders moving to ../unsorted
    claimed: set[tuple[Path, str]] = set()

    def free(folder: Path, name: str, src: Path) -> bool:
        key = (folder, name.casefold())
        if key in claimed or (name.casefold() in listing.names(folder) and src != folder / name):
            return False
        claimed.add(key)
        return True

    def move(kind: str, src: Path, folder: Path, name: str, rows: list[Row], status: str, note: str = "",
             group: int | None = None, details: list[str] | None = None, junk: bool = False) -> None:
        dirs.ensure(folder, junk=junk)
        moves.append(Op(kind, rel(src), rel(folder / name), group=group))
        moving.add(src)
        rows.append(Row(status, rel(src), rel(folder / name), note, details or []))

    for v in sorted(best, key=lambda v: (v.season, v.episodes, v.part or 0)):
        dest = season_dir(v.season)
        rows = section(rel(dest) + "/")
        details = [_code(v.season, v.episodes) + " from the filename", f"{v.label}, {_size_text(v.size)}"]
        if v.path.parent == dest:
            rows.append(Row("SKIP", rel(v.path), "", "already in its season folder", details))
        elif not listing.writable(v.path.parent):
            rows.append(Row("CONFLICT", rel(v.path), "", "no write permission in its folder", details))
            continue
        elif not free(dest, v.path.name, v.path):
            rows.append(Row("CONFLICT", rel(v.path), "", f"{rel(dest / v.path.name)} already exists", details))
            continue
        else:
            move("sort", v.path, dest, v.path.name, rows, "OK", group=id(v), details=details)
        target = subs_dir(dest)
        for sub in v.subs:
            folder = target if parse_episode(sub.name) else target / v.path.stem
            if sub.parent == folder:
                continue
            if not free(folder, sub.name, sub):
                rows.append(Row("CONFLICT", rel(sub), "", f"{rel(folder / sub.name)} already exists"))
                continue
            move("sort", sub, folder, sub.name, rows, "OK", group=id(v))
    for sub, season in orphan_subs:
        folder = subs_dir(season_dir(season))
        rows = section(rel(season_dir(season)) + "/")
        if sub.parent != folder and free(folder, sub.name, sub):
            move("sort", sub, folder, sub.name, rows, "OK", "subtitle without its video")

    for v, kept in worse:
        rows = section(f"{DUPES_DIR}/ (worse copies; the best one is kept)")
        if not listing.writable(v.path.parent):
            rows.append(Row("CONFLICT", rel(v.path), "", "no write permission in its folder"))
            continue
        note = f"{v.label}, {_size_text(v.size)}; kept the {kept.label} copy, {kept.path.name}"
        for path in [v.path] + v.subs:
            folder = show_dir / DUPES_DIR / Path(rel(path)).parent
            dirs.ensure(folder)
            move("duplicate", path, folder, dirs.free_name(folder, path.name), rows,
                 "DUPLICATE" if path == v.path else "OK", note if path == v.path else "", group=id(v))

    for video in other:
        rows = section(f"../{UNSORTED_DIR}/ (a different show)")
        note = f"looks like {title_case(show_in_filename(video.name)) or 'a different show'}, not {show_name}"
        d = release_dir(video)
        if not listing.writable(show_dir.parent):
            rows.append(Row("CONFLICT", rel(d or video), "", "no write permission in the folder above"))
        elif d:
            if d in away:
                continue
            dirs.ensure(unsorted)
            name = dirs.free_name(unsorted, d.name)
            moves.append(Op("unsorted", rel(d), rel(unsorted / name), is_dir=True))
            away.add(d)
            rows.append(Row("OTHER SHOW", rel(d) + "/", rel(unsorted / name) + "/", note + "; its whole folder moves"))
        else:
            for path in [video] + other_subs.get(video, []):
                dirs.ensure(unsorted)
                kind_note = note if path == video else ""
                move("unsorted", path, unsorted, dirs.free_name(unsorted, path.name), rows,
                     "OTHER SHOW" if path == video else "OK", kind_note, group=id(video))

    def gone_with_folder(path: Path) -> bool:
        return any(d in path.parents for d in away)

    # 6. Old .nfo files to .nfo/.nfo-old/ (every run); with --clean, samples and junk to .junk/.
    for path, area in others:
        if path.suffix.lower() != ".nfo" or area == "extras" or gone_with_folder(path):
            continue
        folder = show_dir / NFO_DIR / NFO_OLD / Path(rel(path)).parent
        dirs.ensure(folder)
        move("archive", path, folder, dirs.free_name(folder, path.name),
             section(f"{NFO_DIR}/{NFO_OLD}/ (existing .nfo files moved here)"), "ARCHIVE")
    if clean:
        removals = _plan_cleanup(plan, show_dir, ui, others, [x for x in samples if not gone_with_folder(x)],
                                 dirs, moves, moving, move, rel, section, gone_with_folder, away,
                                 "empty after sorting")
    else:
        removals = []
        for path in samples:
            if not gone_with_folder(path):
                section(left_label).append(Row("SKIPPED", rel(path), "", "sample; --clean moves it to .junk/"))

    # Warnings.
    if worse:
        n = len(worse)
        plan.warnings.append(f"{n} episode {'copy is' if n == 1 else 'copies are'} not the best one; "
                             f"{'it moves' if n == 1 else 'they move'} to {DUPES_DIR}/ so you can check and "
                             f"delete {'it' if n == 1 else 'them'}.")
    if other:
        plan.warnings.append(f"{_plural(len(other), 'video')} look{'s' if len(other) == 1 else ''} like a "
                             f"different show; {'it moves' if len(other) == 1 else 'they move'} to "
                             f"../{UNSORTED_DIR}/.")
    by_season: dict[int, set[int]] = {}
    for v in best:
        by_season.setdefault(v.season, set()).update(v.episodes)
    for season in sorted(n for n in by_season if n > 0):
        missing = [e for e in range(1, max(by_season[season]) + 1) if e not in by_season[season]]
        if missing:
            plan.warnings.append(f"Season {season}: no file for {_episode_list(missing)}.")
    plan.ops = dirs.ops + moves + removals
    order = sorted(plan.sections, key=lambda k: (k.startswith((".", "..", left_label)), natural_key(k)))
    plan.sections = {k: plan.sections[k] for k in order if plan.sections[k]}
    return plan, show_name


def _plan_cleanup(plan: Plan, show_dir: Path, ui: UI, others: list[tuple[Path, str]], samples: list[Path],
                  dirs: _Dirs, moves: list[Op], moving: set[Path], move: Callable, rel: Callable[[Path], str],
                  section: Callable[[str], list[Row]], gone: Callable[[Path], bool], away: set[Path],
                  why: str) -> list[Op]:
    """--clean's part of a sort or a clean-only run: samples, junk and screenshot folders
    move to .junk/ (keeping their path), then folders left completely empty are removed, deepest
    first. Returns the removals, which run after every move."""
    junk = [p for p, a in others if a != "extras" and not gone(p) and (is_junk(p) or a == "screens")]
    extras = [p for p, a in others if a == "extras" and is_junk(p)]
    junk += ask_extras_junk(extras, show_dir, ui)
    for path in samples + junk:
        folder = show_dir / JUNK_DIR / Path(rel(path)).parent
        move("junk", path, folder, dirs.free_name(folder, path.name), section(f"{JUNK_DIR}/ (--clean)"), "JUNK",
             "sample" if path in samples else "", junk=True)

    targets = {Path(os.path.normpath(show_dir / op.dst)) for op in moves}
    keep = {show_dir}
    for t in targets:
        keep.update(p for p in t.parents if show_dir in p.parents or p == show_dir)
    empty: set[Path] = set()
    removals: list[Op] = []
    all_dirs = [Path(f) for f, _, _ in os.walk(show_dir)]
    for d in sorted(all_dirs, key=lambda d: len(d.parts), reverse=True):
        if d in keep or any(part.startswith(".") for part in d.relative_to(show_dir).parts) \
                or d in away or gone(d):
            continue
        with os.scandir(d) as it:
            entries = list(it)
        if all((Path(e.path) in empty) if e.is_dir() else (Path(e.path) in moving) for e in entries):
            empty.add(d)
            removals.append(Op("rmdir", dst=rel(d), is_dir=True))
            plan.folder_rows.append(Row("REMOVE", rel(d) + "/", "", why))
    return removals


def build_clean_plan(folder: Path, ui: UI) -> Plan:
    """Clean-only mode: only samples, junk and screenshots move to .junk/, and folders left
    empty are removed. Videos, subtitles and .nfo files aren't touched, and TVmaze isn't asked."""
    plan = Plan()
    listing = _Listing()
    dirs = _Dirs(folder, listing)
    moves: list[Op] = []
    moving: set[Path] = set()

    def rel(p: Path) -> str:
        return Path(os.path.relpath(p, folder)).as_posix()

    def section(label: str) -> list[Row]:
        return plan.sections.setdefault(label, [])

    def move(kind: str, src: Path, dest: Path, name: str, rows: list[Row], status: str, note: str = "",
             group: int | None = None, details: list[str] | None = None, junk: bool = False) -> None:
        dirs.ensure(dest, junk=junk)
        moves.append(Op(kind, rel(src), rel(dest / name), group=group))
        moving.add(src)
        rows.append(Row(status, rel(src), rel(dest / name), note, details or []))

    files = _walk_show(folder)
    samples = []
    for path, area in files:
        if path.suffix.lower() not in VIDEO_EXTS or area == "extras":
            continue
        if area == "sample":
            samples.append(path)
        elif _SAMPLE.search(path.stem):
            # A real episode title can contain "sample", so a name alone is asked about.
            answer = ui.ask(f'"{path.name}" has "sample" in its name.\nMove it to .junk/? [Y/n]: ', "y")
            if answer.lower() not in ("n", "no"):
                samples.append(path)
    others = [(p, a) for p, a in files if p.suffix.lower() not in VIDEO_EXTS | SUB_EXTS | {".nfo"}]
    removals = _plan_cleanup(plan, folder, ui, others, samples, dirs, moves, moving, move, rel, section,
                             lambda p: False, set(), "empty after cleaning")
    plan.ops = dirs.ops + moves + removals
    return plan


def run_clean(args, ui: UI) -> int:
    """Clean-only mode: renamer PATH --clean, with no renaming options."""
    folder = _full_path(args.path)
    if not folder.is_dir():
        raise RenamerError(f"Not a folder: {folder}")
    ui.start_log(log_name_for(folder) + "_clean")
    downloads = find_downloads(folder)
    if downloads:
        return report_downloads(ui, folder, downloads)
    if not os.access(folder, os.W_OK):
        raise RenamerError(f"No write permission in {folder}, so the undo log can't be written there. "
                           "Nothing was changed.")
    plan = build_clean_plan(folder, ui)
    plan.details = [_undo_log_detail(folder)]
    print_preview(ui, ["Mode:   clean only (moves junk to .junk/; renames nothing)", f"Folder: {folder}"], plan)
    if not plan.ops:
        ui.say("Nothing to clean.")
        return 0
    answer = confirm(ui, _summary(plan.ops), allow_delete=True)
    if answer is None:
        return 0 if ui.interactive else 1
    if answer == "delete":
        plan.ops = junk_to_delete(plan.ops)
    return apply_ops(plan.ops, folder, ui)


def is_clean_only(args) -> bool:
    """--clean with no renaming options (and not --sort, --all, --undo...) only cleans."""
    return bool(args.clean) and not any((args.show, args.names, args.make_names, args.fix_folders, args.years,
                                         args.nfo, args.renumber, args.sort, args.undo, args.reset, args.all,
                                         getattr(args, "usual", False), getattr(args, "meta", False)))


def run_sort(args, ui: UI, chained: bool = False) -> int:
    """--sort: gather a show's videos from loose files and release folders into Season_NN
    folders. It only moves files; a normal run afterwards renames them. chained: a renaming run
    offered the sort and carries on by itself afterwards (0.8.1)."""
    show_dir = _full_path(args.path)
    if not show_dir.is_dir():
        raise RenamerError(f"Not a folder: {show_dir}")
    refuse_group(show_dir)
    ui.start_log(log_name_for(show_dir) + "_sort")
    downloads = find_downloads(show_dir)
    if downloads:
        return report_downloads(ui, show_dir, downloads)
    if not os.access(show_dir, os.W_OK):
        raise RenamerError(f"No write permission in {show_dir}, so the undo log can't be written there. "
                           "Nothing was changed.")
    plan, show_name = build_sort_plan(show_dir, ui, args.clean)
    plan.details = [_undo_log_detail(show_dir)]
    mode = ("sort (only moves files; the rename follows straight after)" if chained
            else "sort (only moves files; run renamer again afterwards to rename them)")
    print_preview(ui, [f"Show:   {show_name}", f"Mode:   {mode}", f"Folder: {show_dir}"], plan)
    if not plan.ops:
        ui.say("Nothing to sort.")
        return 0
    answer = confirm(ui, _summary(plan.ops), allow_delete=any(o.kind == "junk" for o in plan.ops))
    if answer is None:
        return 0 if ui.interactive else 1
    if answer == "delete":
        plan.ops = junk_to_delete(plan.ops)
    code = apply_ops(plan.ops, show_dir, ui)
    if code == 0 and not chained:
        ui.say(f"Next, rename them: renamer {shlex.quote(str(show_dir))} (with --fix-folders, --nfo and so on)")
    return code


# ---------------------------------------------------------------- tags

FFPROBE, FFMPEG = "ffprobe", "ffmpeg"
MKVMERGE, MKVPROPEDIT, MKVEXTRACT = "mkvmerge", "mkvpropedit", "mkvextract"
CONTAINERS = {".mkv": "mkv", ".mp4": "mp4", ".m4v": "mp4", ".avi": "avi"}
READ_TIMEOUT = 120              # seconds for ffprobe or mkvmerge to read one file's tags
FREE_SPACE_MARGIN = 64 * 1024 * 1024   # ffmpeg's copy needs the video's size plus this
TAG_SECTION = "Tags (--meta)"
_MKV_LEVELS = {"COLLECTION": 70, "SEASON": 60, "EPISODE": 50}   # Matroska's levels for a TV show
_MKV_UIDS = ("TrackUID", "EditionUID", "ChapterUID", "AttachmentUID")

# What each tag is called in the preview.
TAG_LABELS = {
    "title": "title", "COLLECTION/TITLE": "show", "COLLECTION/GENRE": "genre",
    "COLLECTION/DATE_RELEASED": "premiered", "COLLECTION/DISTRIBUTED_BY": "network", "COLLECTION/IMDB": "IMDb",
    "COLLECTION/TVDB2": "TVDB", "COLLECTION/TVMAZE": "TVmaze show", "SEASON/PART_NUMBER": "season",
    "EPISODE/TITLE": "episode title", "EPISODE/PART_NUMBER": "episode", "EPISODE/DATE_RELEASED": "aired",
    "EPISODE/SYNOPSIS": "plot", "EPISODE/RATING": "rating", "EPISODE/TVMAZE": "TVmaze episode",
    "show": "show", "season_number": "season", "episode_sort": "episode", "episode_id": "episode code",
    "date": "aired", "description": "short plot", "synopsis": "plot", "genre": "genre", "network": "network",
    "media_type": "media type", "comment": "comment",
}

# Language names (from TVmaze, or a track's name like "English SDH") and ISO 639-2 codes.
LANGUAGES = {
    "english": "eng", "spanish": "spa", "español": "spa", "castellano": "spa", "latino": "spa",
    "french": "fra", "français": "fra", "german": "deu", "deutsch": "deu", "italian": "ita", "italiano": "ita",
    "portuguese": "por", "português": "por", "japanese": "jpn", "korean": "kor", "chinese": "zho",
    "mandarin": "zho", "cantonese": "yue", "russian": "rus", "dutch": "nld", "nederlands": "nld",
    "swedish": "swe", "svenska": "swe", "norwegian": "nor", "norsk": "nor", "danish": "dan", "dansk": "dan",
    "finnish": "fin", "suomi": "fin", "polish": "pol", "polski": "pol", "czech": "ces", "hungarian": "hun",
    "greek": "ell", "turkish": "tur", "hebrew": "heb", "arabic": "ara", "hindi": "hin", "thai": "tha",
    "vietnamese": "vie", "indonesian": "ind", "ukrainian": "ukr", "romanian": "ron", "icelandic": "isl",
    "persian": "fas", "welsh": "cym", "irish": "gle", "tagalog": "tgl", "filipino": "fil",
}
# The older "bibliographic" codes Matroska uses, for the languages where they differ.
_BIBLIOGRAPHIC = {"fra": "fre", "deu": "ger", "zho": "chi", "nld": "dut", "ces": "cze", "ell": "gre",
                  "ron": "rum", "isl": "ice", "fas": "per", "cym": "wel", "msa": "may", "sqi": "alb",
                  "hye": "arm", "eus": "baq", "kat": "geo", "mkd": "mac", "mya": "bur", "slk": "slo", "bod": "tib"}
_TERMINOLOGIC = {b: t for t, b in _BIBLIOGRAPHIC.items()}
_NO_LANGUAGE = {"", "und", "unk", "mis", "mul", "zxx", "qaa"}


class ToolError(Exception):
    """ffprobe, ffmpeg or an mkvtoolnix program failed on one file. That file is left as it was."""


def _language(code: str) -> str:
    """A language code in one form for comparing: "fre" and "fra" are the same."""
    code = (code or "").strip().lower()
    return _TERMINOLOGIC.get(code, code)


def language_code(name: str) -> str:
    """ISO 639-2 code for a language name like "English" or a track name like "English SDH", or ""."""
    words = re.findall(r"[^\W\d_]+", (name or "").lower())
    if not words:
        return ""
    if words[0] in LANGUAGES:
        return LANGUAGES[words[0]]
    if len(words[0]) == 3 and _language(words[0]) in LANGUAGES.values():   # a track named "ENG"
        return _language(words[0])
    return ""


@dataclass
class Track:
    kind: str           # "audio" or "subtitles"
    number: int         # 1, 2, ... among the tracks of its kind, for the preview
    ref: str            # how the writing tool picks it: "track:@3" (mkvpropedit) or "a:0" (ffmpeg)
    language: str       # "und" when it isn't set
    default: bool
    name: str = ""


@dataclass
class Media:
    container: str      # "mkv", "mp4" or "avi"
    tags: dict[str, str]
    tracks: list[Track]
    streams: int
    duration: float


def _run_tool(cmd: list[str], timeout: float | None = None, ok: tuple[int, ...] = (0,)) -> str:
    """Run one program and return what it printed. mkvtoolnix exits with 1 for warnings only."""
    started = time.monotonic()
    try:
        done = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, stdin=subprocess.DEVNULL)
    except FileNotFoundError:
        debug(f"RUN {shlex.join(cmd)}: not installed")
        raise ToolError(f"{cmd[0]} isn't installed") from None
    except subprocess.TimeoutExpired:
        debug(f"RUN {shlex.join(cmd)}: timed out after {timeout:.0f}s")
        raise ToolError(f"{cmd[0]} didn't finish within {timeout:.0f}s") from None
    debug(f"RUN {shlex.join(cmd)}: exit {done.returncode} in {time.monotonic() - started:.2f}s, "
          f"{len(done.stdout or '')} characters out" + (f"; stderr: {done.stderr.strip()[-2000:]}"
                                                        if (done.stderr or "").strip() else ""))
    if done.returncode not in ok:
        lines = [line.strip() for line in (done.stderr or done.stdout or "").splitlines() if line.strip()]
        reason = lines[-1] if lines else f"exit code {done.returncode}"
        raise ToolError(f"{cmd[0]} failed: {reason}")
    return done.stdout


def _json_tool(cmd: list[str], ok: tuple[int, ...] = (0,)) -> dict:
    try:
        return json.loads(_run_tool(cmd, READ_TIMEOUT, ok))
    except ValueError:
        raise ToolError(f"{cmd[0]} printed something that isn't JSON") from None


def read_media(path: Path) -> Media:
    """The tags and audio/subtitle tracks in a video, read with ffprobe (and mkvmerge for MKV)."""
    container = CONTAINERS[path.suffix.lower()]
    probe = _json_tool([FFPROBE, "-v", "error", "-show_format", "-show_streams", "-of", "json", str(path)])
    debug(f"ffprobe of {path.name}: {json.dumps(probe, ensure_ascii=False)}")
    fmt = probe.get("format") or {}
    streams = probe.get("streams") or []
    found = fmt.get("tags") or {}
    tracks: list[Track] = []
    if container == "mkv":
        # mkvmerge gives the exact track numbers mkvpropedit needs, and the segment title.
        info = _json_tool([MKVMERGE, "-J", str(path)], ok=(0, 1))
        debug(f"mkvmerge -J of {path.name}: {json.dumps(info, ensure_ascii=False)}")
        tags = {k.upper(): str(v) for k, v in found.items() if "/" in k}
        title = ((info.get("container") or {}).get("properties") or {}).get("title")
        if title:
            tags["title"] = str(title)
        counts: Counter = Counter()
        for t in info.get("tracks") or []:
            kind, props = t.get("type"), t.get("properties") or {}
            if kind in ("audio", "subtitles") and props.get("number") is not None:
                counts[kind] += 1
                tracks.append(Track(kind, counts[kind], f"track:@{props['number']}", props.get("language") or "und",
                                    bool(props.get("default_track", True)), props.get("track_name") or ""))
    else:
        tags = {k.lower(): str(v) for k, v in found.items()}
        if container == "mp4":
            counts = Counter()
            for s in streams:
                kind = {"audio": "audio", "subtitle": "subtitles"}.get(s.get("codec_type"))
                if kind:
                    letter = "a" if kind == "audio" else "s"
                    stream_tags = s.get("tags") or {}
                    tracks.append(Track(kind, counts[kind] + 1, f"{letter}:{counts[kind]}",
                                        stream_tags.get("language") or "und",
                                        bool((s.get("disposition") or {}).get("default")),
                                        stream_tags.get("title") or ""))
                    counts[kind] += 1
    try:
        duration = float(fmt.get("duration") or 0)
    except ValueError:
        duration = 0.0
    return Media(container, tags, tracks, len(streams), duration)


def wanted_tags(container: str, show: ShowInfo, season: int, episodes: list[int],
                infos: list[EpisodeInfo | None]) -> dict[str, str]:
    """The tags a video should have, in its container's own names. Only what's known is listed,
    so a run with --names (titles only) never removes a plot or date that's already there."""
    known = [i for i in infos if i]
    title = " + ".join(i.title.strip() for i in known if i.title.strip())
    aired = next((i.aired for i in known if i.aired), "")
    plot = "\n\n".join(i.plot for i in known if i.plot)
    rating = next((i.rating for i in known if i.rating is not None), None)
    episode_id = next((i.tvmaze_id for i in known if i.tvmaze_id), None)
    code = _code(season, episodes)
    if container == "mkv":
        tags = {
            "title": title,
            "COLLECTION/TITLE": show.name,
            "COLLECTION/GENRE": ", ".join(show.genres),
            "COLLECTION/DATE_RELEASED": show.premiered,
            "COLLECTION/DISTRIBUTED_BY": show.network,
            "COLLECTION/IMDB": show.ids.get("imdb", ""),
            "COLLECTION/TVDB2": f"series/{show.ids['tvdb']}" if show.ids.get("tvdb") else "",
            "COLLECTION/TVMAZE": show.ids.get("tvmaze", ""),
            "SEASON/PART_NUMBER": str(season),
            "EPISODE/TITLE": title,
            "EPISODE/PART_NUMBER": str(episodes[0]),
            "EPISODE/DATE_RELEASED": aired,
            "EPISODE/SYNOPSIS": plot,
            # Matroska ratings go from 0 to 5; TVmaze's from 0 to 10.
            "EPISODE/RATING": f"{round(rating / 2, 2):g}" if rating is not None else "",
            "EPISODE/TVMAZE": str(episode_id or ""),
        }
    elif container == "mp4":
        tags = {
            "title": title, "show": show.name, "season_number": str(season), "episode_sort": str(episodes[0]),
            "episode_id": code, "date": aired, "description": plot[:255], "synopsis": plot,
            "genre": ", ".join(show.genres), "network": show.network, "media_type": "10",   # 10: TV show
        }
    else:   # AVI only has a few fields
        tags = {"title": title, "genre": ", ".join(show.genres), "date": aired,
                "comment": f"{show.name} {code}" if show.name else ""}
    return {k: v.strip() for k, v in tags.items() if v and v.strip()}


def track_changes(media: Media, show_language: str) -> tuple[list[tuple[Track, dict]], list[str]]:
    """Language and default-track fixes, and notes about tracks left alone.

    - A track with no language takes it from its name ("English SDH"), if the name is a language.
    - Otherwise an audio track takes the show's language from TVmaze when it's the only audio track
      without a language and no other audio track is already in that language (a dual-audio anime
      release with Japanese marked and the English dub not).
    - Audio: when no track, or several, are marked default, the first in the show's language
      (or the first one) becomes the only default."""
    changes: dict[int, dict] = {}
    notes: list[str] = []
    if media.container == "avi":
        return [], []
    languages = {id(t): t.language for t in media.tracks}
    audio = [t for t in media.tracks if t.kind == "audio"]
    show_code = language_code(show_language)
    untagged_audio = [t for t in audio if _language(t.language) in _NO_LANGUAGE and not language_code(t.name)]
    show_language_free = not any(_language(t.language) == show_code for t in audio)
    unknown_audio = []
    for t in media.tracks:
        if _language(t.language) not in _NO_LANGUAGE:
            continue
        code = language_code(t.name)
        if not code and untagged_audio == [t] and show_language_free:
            code = show_code
        if code:
            new = _BIBLIOGRAPHIC.get(code, code) if media.container == "mkv" else code
            changes.setdefault(id(t), {})["language"] = new
            languages[id(t)] = new
        elif t.kind == "audio":
            unknown_audio.append(t)
    if unknown_audio:
        notes.append(f"{_plural(len(unknown_audio), 'audio track')} with no language left alone")
    defaults = [t for t in audio if t.default]
    if audio and len(defaults) != 1:
        chosen = next((t for t in audio if show_code and _language(languages[id(t)]) == show_code), audio[0])
        for t in audio:
            if t.default != (t is chosen):
                changes.setdefault(id(t), {})["default"] = t is chosen
    return [(t, changes[id(t)]) for t in media.tracks if id(t) in changes], notes


def _short(text: str, limit: int = 60) -> str:
    text = " ".join(text.split())
    return text if len(text) <= limit else text[:limit - 1] + "…"


def _tag_values(change: dict) -> list[tuple[str, str, str | None]]:
    """(label, new value, old value or None) for each tag a file gets, for the preview (0.8.1)."""
    out = []
    for key, new in change["set"].items():
        label = TAG_LABELS.get(key, key)
        if key == "EPISODE/TITLE" and change["set"].get("title") == new:
            continue   # the same as the title, which players show
        old = change["old"].get(key)
        out.append((label, new, old.strip() if old and old.strip() else None))
    return out


def _tag_text(label: str, new: str, old: str | None) -> str:
    def show(v: str) -> str:
        v = _short(v, 70)
        return v if re.fullmatch(r"[\w.:/-]+", v) else f'"{v}"'
    return f"{label} {show(new)}" + (f" (was {show(old)})" if old else "")


def _tag_list(verb: str, labels: list[str]) -> str:
    """ "adds show, season, plot", or "adds 15 tags" when the list is long; --verbose lists each."""
    return f"{verb} {', '.join(labels)}" if len(labels) <= 3 else f"{verb} {len(labels)} tags"


def plan_file_tags(media: Media, wanted: dict[str, str], show_language: str
                   ) -> tuple[dict | None, list[str], list[str]]:
    """What write_tags must change in one file: (op.tags or None, the note's parts, verbose details)."""
    values, old = {}, {}
    added, fixed, details = [], [], []
    for key, new in wanted.items():
        current = media.tags.get(key)
        if current is not None and current.strip() == new:
            continue
        values[key], old[key] = new, current
        label = TAG_LABELS.get(key, key)
        if current is None or not current.strip():
            added.append(label)
            details.append(f'{label}: "{_short(new)}" (new)')
        else:
            fixed.append(label)
            details.append(f'{label}: "{_short(current)}" → "{_short(new)}"')
    parts = []
    if added:
        parts.append(_tag_list("adds", added))
    if fixed:
        parts.append(_tag_list("fixes", fixed))
    changes, notes = track_changes(media, show_language)
    tracks, old_tracks = [], []
    for t, change in changes:
        what = []
        if "language" in change:
            what.append(f"language {t.language} → {change['language']}")
        if "default" in change:
            what.append("made the default" if change["default"] else "no longer the default")
        parts.append(f"{'audio' if t.kind == 'audio' else 'subtitle'} {t.number}: {', '.join(what)}")
        tracks.append({"ref": t.ref, **change})
        old_tracks.append({"ref": t.ref, **{k: (t.language if k == "language" else t.default) for k in change}})
    if not values and not tracks:
        return None, notes, details
    tool = MKVPROPEDIT if media.container == "mkv" else FFMPEG
    return ({"container": media.container, "tool": tool, "set": values, "old": old,
             "tracks": tracks, "old_tracks": old_tracks}, parts + notes, details)


def tag_tools_missing(containers: set[str]) -> dict[str, str]:
    """{container: why it can't be tagged here} for the programs that aren't installed."""
    missing = {}
    if not shutil.which(FFPROBE):
        return {c: "ffprobe isn't installed (sudo apt install ffmpeg)" for c in containers}
    if "mkv" in containers and not all(shutil.which(t) for t in (MKVMERGE, MKVPROPEDIT, MKVEXTRACT)):
        missing["mkv"] = "mkvtoolnix isn't installed (sudo apt install mkvtoolnix)"
    for c in containers & {"mp4", "avi"}:
        if not shutil.which(FFMPEG):
            missing[c] = "ffmpeg isn't installed (sudo apt install ffmpeg)"
    return missing


def plan_tags(ui: UI, show: ShowInfo, items: list[tuple[Group, Path, str, str]]
              ) -> list[tuple[Group, Row, Op | None]]:
    """Read every video's tags and work out the changes. Each item is (group, the file
    now, its path relative to the show folder when the tags are written, the name shown)."""
    containers = {CONTAINERS[p.suffix.lower()] for _, p, _, _ in items if p.suffix.lower() in CONTAINERS}
    missing = tag_tools_missing(containers)
    readable_items = [it for it in items if CONTAINERS.get(it[1].suffix.lower()) not in (None, *missing)]
    results: list[tuple[Group, Row, Op | None]] = []
    progress = Progress(ui, "Reading tags", len(readable_items))
    done = 0
    try:
        for g, path, rel_after, shown in items:
            container = CONTAINERS.get(path.suffix.lower())
            if container is None:
                results.append((g, Row("SKIP", shown, "", f"renamer can't tag {path.suffix.lower()} files"), None))
                continue
            if container in missing:
                results.append((g, Row("CONFLICT", shown, "", f"tags left alone: {missing[container]}"), None))
                continue
            progress.update(done, path.name)
            try:
                media = read_media(path)
            except ToolError as e:
                results.append((g, Row("CONFLICT", shown, "", f"couldn't read its tags: {e}"), None))
                continue
            finally:
                done += 1
            wanted = wanted_tags(container, show, g.season, g.episodes, g.infos)
            change, parts, details = plan_file_tags(media, wanted, show.language)
            notes = list(parts)
            if change is None:
                status = "WARN" if notes else "SKIP"
                results.append((g, Row(status, shown, "", "; ".join(notes) or "tags already correct", details), None))
                continue
            if container != "mkv":
                need = g.size + FREE_SPACE_MARGIN
                try:
                    free = shutil.disk_usage(path.parent).free
                except OSError:
                    free = need
                if free < need:
                    results.append((g, Row("CONFLICT", shown, "", f"not enough free space for ffmpeg's copy "
                                                                  f"(needs {_size_text(need)})"), None))
                    continue
                notes.append("ffmpeg rewrites the file")
            results.append((g, Row("TAG", shown, "", "; ".join(notes), details, _tag_values(change)),
                            Op("tag", src=rel_after, group=id(g), tags=change)))
        progress.update(done)
    finally:
        progress.finish()
    return results


def _mkv_tag_xml(xml_text: str, values: dict[str, str | None]) -> str:
    """The file's full tag XML with renamer's tags set; None removes one. Tags renamer
    doesn't write (a release group's, mkvmerge's track statistics) stay as they are."""
    root = ElementTree.fromstring(xml_text) if xml_text.strip() else ElementTree.Element("Tags")
    for key, value in values.items():
        level_name, name = key.split("/", 1)
        level = _MKV_LEVELS[level_name]
        tag = None
        for candidate in root.findall("Tag"):
            targets = candidate.find("Targets")
            targets = targets if targets is not None else ElementTree.Element("Targets")
            if any(targets.find(u) is not None for u in _MKV_UIDS):
                continue
            if (int(targets.findtext("TargetTypeValue") or 50) == level
                    and (targets.findtext("TargetType") or "").upper() == level_name):
                tag = candidate
                break
        if tag is None:
            if value is None:
                continue
            tag = ElementTree.SubElement(root, "Tag")
            targets = ElementTree.SubElement(tag, "Targets")
            ElementTree.SubElement(targets, "TargetTypeValue").text = str(level)
            ElementTree.SubElement(targets, "TargetType").text = level_name
        for simple in tag.findall("Simple"):
            if (simple.findtext("Name") or "").upper() == name:
                tag.remove(simple)
        if value is not None:
            simple = ElementTree.SubElement(tag, "Simple")
            ElementTree.SubElement(simple, "Name").text = name
            ElementTree.SubElement(simple, "String").text = value
        if tag.find("Simple") is None:
            root.remove(tag)
    return '<?xml version="1.0" encoding="UTF-8"?>\n' + ElementTree.tostring(root, encoding="unicode") + "\n"


def _write_mkv(path: Path, values: dict[str, str | None], tracks: list[dict]) -> None:
    """mkvpropedit changes the tags in place, in seconds, without rewriting the video."""
    cmd = [MKVPROPEDIT, str(path)]
    if "title" in values:
        cmd += ["--edit", "info"] + (["--set", f"title={values['title']}"] if values["title"] else
                                     ["--delete", "title"])
    tag_values = {k: v for k, v in values.items() if k != "title"}
    with tempfile.TemporaryDirectory(prefix="renamer-") as tmp:
        if tag_values:
            current = Path(tmp, "current.xml")
            _run_tool([MKVEXTRACT, str(path), "tags", str(current)], READ_TIMEOUT, ok=(0, 1))
            text = current.read_text(encoding="utf-8-sig") if current.exists() else ""
            new = Path(tmp, "tags.xml")
            new.write_text(_mkv_tag_xml(text, tag_values), encoding="utf-8")
            cmd += ["--tags", f"all:{new}"]
        for t in tracks:
            cmd += ["--edit", t["ref"]]
            if "language" in t:
                cmd += ["--set", f"language={t['language']}"]
            if "default" in t:
                cmd += ["--set", f"flag-default={int(t['default'])}"]
        before = path.stat()
        _run_tool(cmd, ok=(0, 1))
    os.utime(path, ns=(before.st_atime_ns, before.st_mtime_ns))


def _write_ffmpeg(path: Path, container: str, values: dict[str, str | None], tracks: list[dict]) -> None:
    """MP4 and AVI: ffmpeg writes a tagged copy next to the video, checks it has the same streams
    and length, then swaps it in. The video is copied, never re-encoded."""
    tmp = path.with_name(f".renamer-tmp-{os.getpid()}-{path.name}")
    before = path.stat()
    cmd = [FFMPEG, "-nostdin", "-v", "error", "-y"]
    if container == "avi":
        cmd += ["-fflags", "+genpts"]   # old AVIs often lack timestamps that copying needs
    cmd += ["-i", str(path), "-map", "0", "-c", "copy", "-map_metadata", "0"]
    for key, value in values.items():
        cmd += ["-metadata", f"{key}={value or ''}"]   # an empty value removes the tag
    for t in tracks:
        if "language" in t:
            cmd += [f"-metadata:s:{t['ref']}", f"language={t['language']}"]
        if "default" in t:
            cmd += [f"-disposition:{t['ref']}", "+default" if t["default"] else "-default"]
    cmd += ["-f", container, str(tmp)]
    try:
        _run_tool(cmd)
        original, copy = read_media(path), read_media(tmp)
        if copy.streams != original.streams or abs(copy.duration - original.duration) > 1:
            raise ToolError("ffmpeg's copy doesn't match the original (streams or length differ); "
                            "the original is kept")
        os.chmod(tmp, stat.S_IMODE(before.st_mode))
        os.utime(tmp, ns=(before.st_atime_ns, before.st_mtime_ns))
        os.replace(tmp, path)
    finally:
        if tmp.exists():
            tmp.unlink()


def write_tags(path: Path, tags: dict, undo: bool = False) -> None:
    """Apply an op's tag changes, or with undo, put the old values back."""
    values = tags["old"] if undo else tags["set"]
    tracks = tags["old_tracks"] if undo else tags["tracks"]
    if tags["container"] == "mkv":
        _write_mkv(path, values, tracks)
    else:
        _write_ffmpeg(path, tags["container"], values, tracks)


def run_meta(args, ui: UI, fetch: Callable[[str], object] = http_get_json) -> int:
    """renamer meta: check the tags inside the videos against TVmaze and fix them. Renames nothing."""
    target = _full_path(args.path)
    only = None
    if target.is_file():
        if target.suffix.lower() not in VIDEO_EXTS:
            raise RenamerError(f"Not a video file: {target}")
        only, folder = target, target.parent
    elif target.is_dir():
        folder = target
        check_show_folder(folder)
    else:
        raise RenamerError(f"No such file or folder: {target}")
    if not shutil.which(FFPROBE):
        raise RenamerError("renamer meta reads tags with ffprobe, which isn't installed (sudo apt install ffmpeg).")
    if getattr(args, "view", False) or getattr(args, "compare", False):
        return run_view(args, ui, folder, only, fetch)
    layout = find_layout(folder)
    scan_root = layout.show_dir if layout.trusted else folder
    downloads = find_downloads(scan_root)
    if downloads:
        return report_downloads(ui, scan_root, downloads)
    if not os.access(layout.show_dir, os.W_OK):
        raise RenamerError(f"No write permission in {layout.show_dir}, so the undo log can't be written there. "
                           "Nothing was changed.")
    groups, _ = collect_groups(layout, ui, only)
    if only:
        groups = [g for g in groups if g.video == only]
        if not groups:
            raise RenamerError(f"{only.name} isn't in a season folder or show folder renamer can read.")
    get = Getter(fetch, ui)
    show, info, titles, specials, source, show_how = resolve_show(args, layout, groups, ui, get)
    groups, _ = settle_show(args, layout, groups, [], ui, info, titles, specials, get, only)
    ui.start_log(show + "_meta")
    resolve_titles(groups, titles, specials, from_tvmaze=not args.names, renumber=False)
    show_dir = layout.show_dir

    def label(folder: Path) -> str:
        if folder == show_dir:
            return "(show folder)" if layout.trusted else folder.name + "/"
        return folder.relative_to(show_dir).as_posix() + "/"

    plan = Plan()
    items = []
    for g in groups:
        if g.status:
            plan.sections.setdefault(label(g.folder), []).append(Row(g.status, g.video.name, "", g.note))
            continue
        g.infos = [g.overrides.get(e) or titles.get((g.season, e)) for e in g.episodes]
        items.append((g, g.video, g.video.relative_to(show_dir).as_posix(), g.video.name))
    for g, row, op in plan_tags(ui, info, items):
        row.note = "; ".join(n for n in [row.note, *g.warns] if n)
        row.details = [g.how] + row.details if g.how else row.details
        plan.sections.setdefault(label(g.folder), []).append(row)
        if op:
            plan.ops.append(op)
    plan.details = [f"Show name: {show_how}", title_sources(groups, titles), _undo_log_detail(show_dir)]
    if not args.names and not info.language:
        plan.warnings.append("TVmaze doesn't say what language the show is in, so untagged audio tracks "
                             "only get a language from their names.")
    offer = sort_offer(layout)
    if offer and not offer.lone and not only:
        plan.warnings.append(_offer_text(offer) + " renamer meta doesn't move files: renamer --sort "
                             f"{shlex.quote(str(show_dir))} gathers them, then run renamer meta again.")
    print_preview(ui, [f"Show:   {show}", f"Tags:   {source}",
                       "Mode:   meta (changes only the tags inside the videos; renames nothing)",
                       f"Folder: {show_dir}"], plan)
    if not plan.ops:
        ui.say("Nothing to change.")
        return 0
    if not confirm(ui, _summary(plan.ops)):
        return 0 if ui.interactive else 1
    return apply_ops(plan.ops, show_dir, ui, "Tagging")


# ------------------------------------------------- view and compare

# The order tags are listed in by --view, per container; plot last because it's long.
VIEW_KEYS = {
    "mkv": ["title", "COLLECTION/TITLE", "SEASON/PART_NUMBER", "EPISODE/PART_NUMBER", "EPISODE/TITLE",
            "EPISODE/DATE_RELEASED", "COLLECTION/GENRE", "COLLECTION/DISTRIBUTED_BY", "COLLECTION/DATE_RELEASED",
            "EPISODE/RATING", "COLLECTION/IMDB", "COLLECTION/TVDB2", "COLLECTION/TVMAZE", "EPISODE/TVMAZE",
            "EPISODE/SYNOPSIS"],
    "mp4": ["title", "show", "season_number", "episode_sort", "episode_id", "date", "genre", "network",
            "media_type", "description", "synopsis"],
    "avi": ["title", "genre", "date", "comment"],
}
_VIEW_WIDTH = 18


def _view_line(ui: UI, label: str, value: str, mark: str = "", status: str = "") -> None:
    """One "Label   value" line; long values (the plot) wrap under the value column."""
    lead = f"  {label[:1].upper() + label[1:]:<{_VIEW_WIDTH - 2}}"
    if mark:
        lead += ui.paint(f"{mark:<10}", status) + " "
    width = max(40, shutil.get_terminal_size((100, 24)).columns - 2)
    pad = " " * (_VIEW_WIDTH + (11 if mark else 0))
    lines = textwrap.wrap(" ".join(value.split()), width - len(pad), break_on_hyphens=False) or [""]
    ui.say(lead + lines[0])
    for line in lines[1:]:
        ui.say(pad + line)


def _track_text(t: Track) -> str:
    return f"{t.number}: {t.language or 'und'}" + (" (default)" if t.default else "") + \
        (f'  "{t.name}"' if t.name else "")


def _compare_summary(same: int, differ: int) -> str:
    return (f"{_plural(same, 'video')} {'matches' if same == 1 else 'match'} TVmaze, "
            f"{_plural(differ, 'video')} {'differs' if differ == 1 else 'differ'}")


def run_view(args, ui: UI, folder: Path, only: Path | None, fetch: Callable[[str], object]) -> int:
    """renamer meta --view: list the tags already in the videos; with --compare, beside what
    TVmaze has. Changes nothing, writes no undo log and needs no write permission."""
    layout = find_layout(folder)
    groups, _ = collect_groups(layout, ui, only)
    if only:
        groups = [g for g in groups if g.video == only]
        if not groups:
            raise RenamerError(f"{only.name} isn't in a season folder or show folder renamer can read.")
    show_dir = layout.show_dir
    header = [f"Folder: {show_dir}"]
    info = None
    if args.compare:
        get = Getter(fetch, ui)
        show, info, titles, specials, source, show_how = resolve_show(args, layout, groups, ui, get)
        groups, _ = settle_show(args, layout, groups, [], ui, info, titles, specials, get, only)
        ui.start_log(show + "_compare")
        resolve_titles(groups, titles, specials, from_tvmaze=not args.names, renumber=False)
        header = [f"Show:   {show}", f"Tags:   compared with {source}",
                  "Mode:   compare (reads the tags; changes nothing)"] + header
        ui.detail(f"Show name: {show_how}")
    else:
        ui.start_log(log_name_for(show_dir) + "_view")
        header = ["Mode:   view (reads the tags; changes nothing)"] + header

    readable_groups = [g for g in groups if g.video.suffix.lower() in CONTAINERS]
    read: dict[Path, Media | str] = {}
    progress = Progress(ui, "Reading tags", len(readable_groups))
    try:
        for done, g in enumerate(readable_groups):
            progress.update(done, g.video.name)
            try:
                read[g.video] = read_media(g.video)
            except ToolError as e:
                read[g.video] = f"couldn't read its tags: {e}"
        progress.update(len(readable_groups))
    finally:
        progress.finish()

    to_fix = same = 0
    counts: Counter = Counter()
    with ui.paged() as page:
        for line in header:
            ui.say(line)
        for g in groups:
            ui.say()
            ui.say(ui.paint(g.video.relative_to(show_dir).as_posix(), "TAG"))
            media = read.get(g.video)
            if media is None:
                ui.say(f"  (renamer can't read tags in {g.video.suffix.lower()} files)")
                continue
            if isinstance(media, str):
                ui.say(f"  ({media})")
                continue
            wanted: dict[str, str] = {}
            if info is not None and g.season is not None and g.episodes and not g.status:
                g.infos = [g.overrides.get(e) or titles.get((g.season, e)) for e in g.episodes]
                wanted = wanted_tags(media.container, info, g.season, g.episodes, g.infos)
            elif info is not None:
                ui.say(f"  (not compared: {g.note or 'no season and episode number'})")
            differs = False
            keys = VIEW_KEYS[media.container]
            if info is None and not any((media.tags.get(k) or "").strip() for k in keys):
                keys = []
                ui.say("  No title, show, episode or other tags.")
            for key in keys:
                label = TAG_LABELS.get(key, key)
                current = (media.tags.get(key) or "").strip()
                if info is None:
                    _view_line(ui, label, current or "–")
                    continue
                new = wanted.get(key, "")
                if not new:
                    _view_line(ui, label, current or "–", "not listed" if current else "", "SKIP")
                elif current == new:
                    _view_line(ui, label, current, "same", "OK")
                elif not current:
                    _view_line(ui, label, new, "missing", "TAG")
                    differs = True
                    counts["missing"] += 1
                else:
                    _view_line(ui, label, f"{_short(current)} → {new}", "different", "WARN")
                    differs = True
                    counts["different"] += 1
            others = {k: v for k, v in media.tags.items() if k not in VIEW_KEYS[media.container]}
            if others:
                _view_line(ui, "other tags", "; ".join(f"{k} = {_short(v, 40)}" for k, v in sorted(others.items())))
            changes = dict((id(t), c) for t, c in track_changes(media, info.language)[0]) if info is not None else {}
            for t in media.tracks:
                label = "audio" if t.kind == "audio" else "subtitles"
                change = changes.get(id(t))
                if change:
                    what = [f"language → {change['language']}"] if "language" in change else []
                    if "default" in change:
                        what.append("made the default" if change["default"] else "no longer the default")
                    _view_line(ui, label, f"{_track_text(t)} → {', '.join(what)}", "different", "WARN")
                    differs = True
                    counts["tracks"] += 1
                else:
                    _view_line(ui, label, _track_text(t), "same" if info is not None else "", "OK")
            if info is not None and wanted:
                to_fix += differs
                same += not differs
        ui.say()
        if info is None:
            ui.say(f"{_plural(len(groups), 'video')}. Nothing was changed.")
        else:
            ui.say(f"{_compare_summary(same, to_fix)} ({counts['missing']} missing, {counts['different']} "
                   f"different, {_plural(counts['tracks'], 'track')} to fix). Nothing was changed.")
            if to_fix:
                ui.say(f"To fix them: renamer meta {shlex.quote(str(only or folder))}")
    if page.shown and info is not None:
        with ui.quiet_log():
            ui.say(f"{_compare_summary(same, to_fix)}. Nothing was changed.")
    return 0


# ---------------------------------------------------------------- undo

class _Sim:
    """What the show folder will look like as undo steps run, so each step is checked first."""

    def __init__(self, show_dir: Path):
        self.show_dir = show_dir
        self.moves: list[tuple[str, str]] = []
        self.gone: set[str] = set()

    def disk(self, rel: str) -> Path:
        for frm, to in reversed(self.moves):
            if rel == to or rel.startswith(to + "/"):
                rel = frm + rel[len(to):]
        return self.show_dir / rel

    def exists(self, rel: str) -> bool:
        if any(rel == g or rel.startswith(g + "/") for g in self.gone):
            return False
        return os.path.lexists(self.disk(rel))

    def move(self, frm: str, to: str) -> None:
        self.moves.append((frm, to))
        self.gone.add(frm)
        self.gone.discard(to)


def _full_path(path) -> Path:
    """An absolute path with "a/../b" tidied, without following symlinks or mounts."""
    return Path(os.path.normpath(Path(path).expanduser().absolute()))


def log_name_for(path: Path) -> str:
    """Show-name part of a log file's name, worked out from a folder name alone."""
    return clean_text(readable(show_from_folder(path.name))) or "run"


def run_undo(path: Path, ui: UI, reset: bool = False) -> int:
    """--undo reverses a run but leaves old .nfo files in .nfo/.nfo-old; --reset also puts those
    back, restoring everything exactly."""
    word = "Reset" if reset else "Undo"
    path = _full_path(path)
    show_dir = path if (path / UNDO_LOG).is_file() else None
    if show_dir is None and (path.parent / UNDO_LOG).is_file():
        # The folder above only counts when its last run changed something in this folder (a lone
        # season folder whose log went to the library before 0.8.1); a library's log is about other
        # shows (1.0.0, from a real run).
        try:
            last = load_log(path.parent / UNDO_LOG)["runs"][-1]["ops"]
        except (IndexError, KeyError, RenamerError):
            last = []
        mine = path.name
        if any(str(op.get(k, "")).split("/")[0] == mine for op in last for k in ("src", "dst", "path")):
            show_dir = path.parent
        else:
            raise RenamerError(f"No undo log ({UNDO_LOG}) in {path}. The one in {path.parent} is about other "
                               f"folders; reverse that with: renamer --undo {shlex.quote(str(path.parent))}")
    if show_dir is None:
        raise RenamerError(f"No undo log ({UNDO_LOG}) in {path} or the folder above it.")
    ui.start_log(log_name_for(show_dir) + ("_reset" if reset else "_undo"))
    data = load_log(show_dir / UNDO_LOG)
    run = data["runs"][-1] if data["runs"] else {"ops": []}
    # Only downloads inside the folders this run touched matter: an undo changes nothing else, and a
    # library's other shows may well be downloading (1.0.0).
    touched = {str(op[k]).split("/")[0] for op in run["ops"] for k in ("src", "dst", "path") if op.get(k)}
    downloads = [d for d in find_downloads(show_dir) if d.relative_to(show_dir).parts[0] in touched]
    if downloads:
        return report_downloads(ui, show_dir, downloads)
    if not data["runs"]:
        raise RenamerError("The undo log is empty; there's nothing to undo.")
    sim = _Sim(show_dir)
    rows: list[Row] = []
    steps: list[tuple[int, dict]] = []
    kept = 0
    for index in range(len(run["ops"]) - 1, -1, -1):
        op = run["ops"][index]
        if op["op"] == "rename":
            src, dst = op["src"], op["dst"]
            if op.get("kind") == "archive" and not reset:
                rows.append(Row("KEEP", dst, "", f"old .nfo stays in {NFO_DIR}/{NFO_OLD}; --reset puts it back"))
                kept += 1
                continue
            case_only = src.casefold() == dst.casefold()
            if not sim.exists(dst):
                rows.append(Row("CONFLICT", dst, "", "missing; it was moved or renamed since"))
            elif not case_only and sim.exists(src):
                rows.append(Row("CONFLICT", dst, "", f"{src} exists again; not overwriting it"))
            else:
                rows.append(Row("UNDO", dst, src))
                sim.move(dst, src)
                steps.append((index, op))
        elif op["op"] == "create":
            rel = op["path"]
            if not sim.exists(rel):
                rows.append(Row("SKIP", rel, "", "already gone"))
            elif sha256(sim.disk(rel).read_bytes()) != op["sha256"]:
                rows.append(Row("CONFLICT", rel, "", "edited since it was created; kept"))
            else:
                rows.append(Row("DELETE", rel, "", "created by renamer"))
                sim.gone.add(rel)
                steps.append((index, op))
        elif op["op"] == "mkdir":
            rows.append(Row("REMOVE", op["path"] + "/", "", "folder renamer created; removed if it ends up empty"))
            sim.gone.add(op["path"])
            steps.append((index, op))
        elif op["op"] == "delete":
            rows.append(Row("GONE", op["path"], "", "deleted with DELETE; can't be restored"))
        elif op["op"] == "rmdir":
            rows.append(Row("RESTORE", op["path"] + "/", "", "folder --sort removed; it's made again"))
            sim.gone.discard(op["path"])
            steps.append((index, op))
        elif op["op"] == "tag":
            rel = op["path"]
            if not sim.exists(rel):
                rows.append(Row("CONFLICT", rel, "", "missing; it was moved or renamed since"))
            else:
                rows.append(Row("UNDO", rel, "", "tags put back as they were"
                                + (" (ffmpeg rewrites the file)" if op["container"] != "mkv" else "")))
                steps.append((index, op))
        elif op["op"] == "rename_show":
            if show_dir.name != op["dst"] or (show_dir.parent / op["src"]).exists():
                rows.append(Row("CONFLICT", op["dst"] + "/", "", "show folder was renamed or moved since"))
            else:
                rows.append(Row("UNDO", op["dst"] + "/", op["src"] + "/"))
                steps.append((index, op))
    ui.say(f"{word} the run from {run.get('time', 'an unknown time')} in {show_dir}")
    ui.detail(f"The undo log holds {len(data['runs'])} run{'' if len(data['runs']) == 1 else 's'}; "
              f"this {'resets' if reset else 'undoes'} the most recent one.")
    if kept:
        ui.say(f"{_plural(kept, 'old .nfo file')} stay in {NFO_DIR}/{NFO_OLD}. Use --reset instead to put "
               "them back too (after this undo, that run can't be reset any more).")
    with ui.paged() as page:
        ui.say()
        for row in rows:
            _print_row(ui, row)
        print_attention(ui, [("", row) for row in rows], [])
        ui.say()
    if page.shown:
        _print_after_pager(ui, [("", row) for row in rows], [])
    if not any(op["op"] != "mkdir" for _, op in steps):
        ui.say(f"Nothing can be {'reset' if reset else 'undone'}.")
        return 1
    if not confirm(ui, f"{word} {_plural(len(steps), 'change')}"):
        return 0 if ui.interactive else 1

    reverted: set[int] = set()
    skipped: list[str] = []
    left_folders = 0
    ui.changing = True
    progress = Progress(ui, "Resetting" if reset else "Undoing", len(steps))

    def revert(op: dict) -> None:
        nonlocal show_dir, left_folders
        if op["op"] == "rename":
            move(show_dir / op["dst"], show_dir / op["src"])
        elif op["op"] == "create":
            (show_dir / op["path"]).unlink()
        elif op["op"] == "mkdir":
            try:
                os.rmdir(show_dir / op["path"])
            except OSError:   # not empty (e.g. old .nfo files kept), or already gone
                left_folders += 1
        elif op["op"] == "rmdir":
            os.makedirs(show_dir / op["path"], exist_ok=True)
        elif op["op"] == "tag":
            write_tags(show_dir / op["path"], op, undo=True)
        elif op["op"] == "rename_show":
            new_dir = show_dir.with_name(op["src"])
            move(show_dir, new_dir)
            show_dir = new_dir

    try:
        for index, op in steps:
            name = Path(op.get("dst") or op.get("path", "")).name
            while True:
                progress.update(len(reverted), Path(op.get("src") or op.get("path", "")).name)
                try:
                    revert(op)
                    reverted.add(index)
                    break
                except ToolError as e:
                    progress.pause()
                    ui.warn(f"{op['path']}: {e}")
                    skipped.append(op["path"])
                    break
                except OSError as e:
                    action = ask_busy(ui, progress, e, name)
                    if action == "stop":
                        raise
                    if action == "skip":
                        skipped.append(op.get("dst") or op.get("path", ""))
                        break
        progress.update(len(reverted))
    except OSError as e:
        progress.finish()
        run["ops"] = [op for i, op in enumerate(run["ops"]) if i not in reverted]
        save_log(show_dir / UNDO_LOG, data)
        ui.say(ui.paint("Error: ", "CONFLICT") + f"{e.strerror or e}: {e.filename or ''}")
        ui.say(f"Stopped after {len(reverted)} of {len(steps)} changes; the rest stay in the undo log.")
        return 1
    progress.finish()
    if skipped:   # what couldn't be reverted stays in the log, so --undo can finish it later
        run["ops"] = [op for i, op in enumerate(run["ops"]) if i not in reverted]
        save_log(show_dir / UNDO_LOG, data)
        ui.say(f"{'Reset' if reset else 'Undone'}: {_plural(len(reverted) - left_folders, 'change')}.")
        ui.warn(f"skipped {_plural(len(skipped), 'file')} that couldn't be changed now; "
                f"{'it stays' if len(skipped) == 1 else 'they stay'} "
                f"in the undo log, so run --{'reset' if reset else 'undo'} again later to finish:")
        for path in skipped:
            ui.say(f"  {path}")
        return 0
    data["runs"].pop()
    if data["runs"]:
        save_log(show_dir / UNDO_LOG, data)
    else:
        (show_dir / UNDO_LOG).unlink(missing_ok=True)
    done = len(reverted) - left_folders
    ui.say(f"{'Reset' if reset else 'Undone'}: {_plural(done, 'change')}."
           + (f" {_plural(left_folders, 'folder')} kept because they aren't empty." if left_folders else ""))
    return 0


# --------------------------------------------------------------------- CLI

# ------------------------------------------------- library: genre folders

GENRE_CONFIG = Path(os.environ.get("XDG_CONFIG_HOME") or Path.home() / ".config") / "renamer" / "genres.conf"
WIKIDATA = "https://www.wikidata.org/w/api.php"

DEFAULT_GENRES = """\
# renamer lib --genre: which genre folder a show or movie goes to.
#
# Genre = folder name, one per line. The order is the priority when Wikipedia doesn't settle
# which genre is the main one: a show that's both Drama and Comedy goes to the one higher up.
# Change the folder names as you like. A folder already in the library whose name is a genre,
# a folder name or an alias below is used for that genre, whatever it's called.
Comedy = Comedy
Science-Fiction = Sci-Fi
Horror = Horror
Fantasy = Fantasy
Anime = Anime
Crime = Crime
Thriller = Thriller
Mystery = Mystery
Action = Action
Adventure = Adventure
War = War
Western = Western
Romance = Romance
Sports = Sports
Music = Music
History = History
Documentary = Documentary
Children = Kids
Family = Family
Supernatural = Supernatural
Espionage = Espionage
Legal = Legal
Medical = Medical
Nature = Nature
Food = Food
Travel = Travel
DIY = DIY
Adult = Adult
Drama = Drama

# Other words for a genre, as Wikipedia, Wikidata or folder names put it.
alias Comedy = sitcom, comedy, comedy-drama, black comedy, dark comedy, satire, satirical, parody, mockumentary, sketch comedy, comedy film
alias Science-Fiction = science fiction, sci-fi, scifi, space opera, cyberpunk, dystopian, science fiction film
alias Horror = horror, horror film, slasher, zombie
alias Fantasy = fantasy, fantasy film, sword and sorcery
alias Crime = crime, police procedural, crime film, gangster, heist
alias Thriller = thriller, psychological thriller, thriller film
alias Mystery = mystery, mystery film, whodunit
alias Action = action, action film, martial arts, superhero
alias Adventure = adventure, adventure film
alias War = war, war film
alias Western = western, western film
alias Romance = romance, romantic, romance film
alias Sports = sports, sport
alias Music = musical, music, musical film
alias History = historical, history, historical film
alias Documentary = documentary, docuseries, documentary film
alias Children = children's, kids, preschool
alias Supernatural = supernatural, paranormal
alias Drama = drama, drama film, teen drama, period drama
"""


@dataclass
class GenreConfig:
    folders: dict[str, str]                 # genre -> folder name, in priority order
    aliases: dict[str, list[str]]           # genre -> other words for it, lower case

    def words(self, genre: str) -> list[str]:
        return [genre.lower(), genre.lower().replace("-", " ")] + self.aliases.get(genre, [])

    def genre_for(self, word: str) -> str | None:
        """The genre a word (a TVmaze genre, a Wikidata label, a folder name) stands for."""
        key = normalize_title(word)
        for genre, folder in self.folders.items():
            if key in {normalize_title(w) for w in [folder, *self.words(genre)]}:
                return genre
        return None


def parse_genre_config(text: str) -> GenreConfig:
    folders: dict[str, str] = {}
    aliases: dict[str, list[str]] = {}
    for n, raw in enumerate(text.splitlines(), 1):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        if "=" not in line:
            raise RenamerError(f"{GENRE_CONFIG}, line {n}: expected 'Genre = Folder' or 'alias Genre = words'.")
        left, right = (part.strip() for part in line.split("=", 1))
        if left.lower().startswith("alias "):
            aliases.setdefault(left[6:].strip(), []).extend(w.strip().lower() for w in right.split(",") if w.strip())
        elif left and right:
            folders[left] = right
    return GenreConfig(folders, aliases)


def load_genre_config(ui: UI) -> GenreConfig:
    """~/.config/renamer/genres.conf, written with the defaults the first time."""
    if not GENRE_CONFIG.exists():
        try:
            GENRE_CONFIG.parent.mkdir(parents=True, exist_ok=True)
            GENRE_CONFIG.write_text(DEFAULT_GENRES, encoding="utf-8")
            ui.say(f"Wrote {GENRE_CONFIG} with the default genre folders; edit it to change their names.")
        except OSError as e:
            ui.say(f"Can't write {GENRE_CONFIG} ({e.strerror}); using the defaults.")
            return parse_genre_config(DEFAULT_GENRES)
    try:
        text = GENRE_CONFIG.read_text(encoding="utf-8")
    except OSError as e:
        raise RenamerError(f"Can't read {GENRE_CONFIG} ({e.strerror}).") from None
    config = parse_genre_config(text)
    debug(f"genre config {GENRE_CONFIG}: {config}")
    return config


@dataclass
class LibItem:
    """One show or movie at the top of a library, and where it goes."""
    path: Path
    kind: str                       # "show", "movie" or "skip"
    title: str = ""                 # what it was looked up as / found as
    found: str = ""                 # TVmaze's or Wikidata's name and year
    genres: list[str] = field(default_factory=list)   # the source's genres, mapped to config genres
    raw_genres: list[str] = field(default_factory=list)
    lead: str = ""                  # Wikipedia's description ("an American science fiction drama…")
    match_note: str = ""            # set when it isn't sure the right show or film was found
    tvmaze_id: str = ""
    in_genre: bool = False          # inside a genre folder: a place to merge into, not moved itself
    lone: bool = False              # one season's folder, with no show folder around it
    videos: int = 0
    files: list[Path] = field(default_factory=list)   # kind "loose": episode files at the library's top
    leave: bool = False             # the user said to leave it where it is
    genre: str | None = None
    folder: str | None = None
    sure: bool = False
    why: str = ""
    conflict: str = ""
    dub: bool = False               # an English dub: kept apart from other copies by lib --sort (1.2.0)
    split: "MixedFolder | None" = None   # several shows of one name in one folder (1.2.0)


_DESCRIPTOR_END = re.compile(r"\b(?:television series|tv series|web series|series|sitcom|show|programme|program"
                             r"|miniseries|anime|film|movie)\b", re.I)


def descriptor(lead: str) -> str:
    """The part of Wikipedia's first sentence that says what it is: "Another Show is an American
    science fiction drama television series created by…" -> "…science fiction drama television series"."""
    m = re.search(r"\b(?:is|was|are|were)\s+(?:an?|the)?\s*", lead)
    start = m.end() if m else 0
    end = _DESCRIPTOR_END.search(lead, start)
    return lead[start:end.end() if end else min(len(lead), start + 200)]


def genres_in(text: str, config: GenreConfig, among: list[str] | None = None) -> list[str]:
    """The genres a text names, in the order it names them."""
    low = re.sub(r"\badult[ -]animat\w*", "animated", text.lower())   # for grown-ups, not the Adult genre
    found: list[tuple[int, str]] = []
    for genre in (among if among is not None else list(config.folders)):
        hits = [m.start() for w in config.words(genre)
                for m in re.finditer(rf"(?<![a-z]){re.escape(w)}(?![a-z])", low)]
        if hits:
            found.append((min(hits), genre))
    return [g for _, g in sorted(found)]


def pick_genre(item: LibItem, config: GenreConfig) -> None:
    """The main genre: the item's genres cross-checked with Wikipedia's description. Sure when the
    description names exactly one of them."""
    named = genres_in(descriptor(item.lead), config, item.genres) if item.lead else []
    order = list(config.folders)
    if len(named) == 1:
        item.genre, item.sure = named[0], True
        item.why = f"Wikipedia: {descriptor(item.lead).strip()}"
    elif named:
        # Several named ("science fiction horror", "comedy-drama"): sure when the first one named is
        # also the first of them in the config's order, since then both say the same. Otherwise
        # the config's order makes the guess ("supernatural horror" -> Horror).
        item.genre = min(named, key=order.index)
        item.sure = named[0] == item.genre
        item.why = f"Wikipedia names {', '.join(named)}: {descriptor(item.lead).strip()}"
    elif item.genres:
        item.genre = min(item.genres, key=list(config.folders).index)
        item.sure = len(item.genres) == 1   # only one genre: nothing to decide
        item.why = "Wikipedia doesn't say" if item.lead else "no Wikipedia article found"
    else:
        other = genres_in(descriptor(item.lead), config) if item.lead else []
        item.genre = other[0] if other else None
        item.why = (f"no genres listed; Wikipedia: {descriptor(item.lead).strip()}" if other
                    else "no genres found")
    item.folder = config.folders.get(item.genre) if item.genre else None


class _Paced:
    """At most 20 requests to TVmaze in any 10 seconds, its documented limit; Wikipedia every 2
    seconds and Wikidata's API every second, each on its own, since they answer 429 to bursts.
    Wikidata's Special:EntityData pages come from a cache and aren't limited."""

    GAPS = {"wikipedia.org": 2.0, "www.wikidata.org/w/api.php": 1.0}   # seconds between requests

    def __init__(self, fetch: Callable[[str], object]):
        self.fetch, self.times, self.last = fetch, [], {}

    def __call__(self, url: str):
        for host, gap in self.GAPS.items():
            if host in url:
                wait = gap - (time.monotonic() - self.last.get(host, 0.0))
                if wait > 0:
                    _sleep(wait)
                self.last[host] = time.monotonic()
        if "tvmaze.com" in url:
            now = time.monotonic()
            self.times = [t for t in self.times if now - t < 10]
            if len(self.times) >= 20:
                _sleep(10 - (now - self.times[0]))
            self.times.append(time.monotonic())
        return self.fetch(url)


LIB_CACHE = Path(os.environ.get("XDG_CACHE_HOME") or Path.home() / ".cache") / "renamer" / "lib-lookups.json"
LIB_CACHE_DAYS = 30


def _cache_load() -> dict:
    try:
        data = json.loads(LIB_CACHE.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}
    cutoff = time.time() - LIB_CACHE_DAYS * 86400
    return {k: v for k, v in data.items() if isinstance(v, dict) and v.get("time", 0) > cutoff}


def _cache_save(cache: dict) -> None:
    try:
        LIB_CACHE.parent.mkdir(parents=True, exist_ok=True)
        LIB_CACHE.write_text(json.dumps(cache, ensure_ascii=False), encoding="utf-8")
    except OSError as e:
        debug(f"couldn't save the lookup cache {LIB_CACHE}: {e}")


_CACHED = ("title", "found", "raw_genres", "lead", "match_note", "why", "tvmaze_id")


def read_group_marker(folder: Path) -> dict | None:
    """What lib --group wrote in a folder of copies; None when it isn't one."""
    try:
        data = json.loads((folder / GROUP_MARKER).read_text(encoding="utf-8"))
    except FileNotFoundError:
        return None
    except (OSError, ValueError):
        return {}
    return data if isinstance(data, dict) else {}


def _known_tvmaze_id(folder: Path) -> str | None:
    """The TVmaze ID renamer wrote earlier: in lib --group's marker, in .nfo/tvshow.nfo, or in an
    MKV's tags."""
    marker = read_group_marker(folder)
    if marker:
        return marker.get("tvmaze_id") or None
    for nfo in (folder / NFO_DIR / "tvshow.nfo", folder / "tvshow.nfo"):
        try:
            m = re.search(r'<uniqueid type="tvmaze"[^>]*>(\d+)<', nfo.read_text(encoding="utf-8", errors="replace"))
        except OSError:
            continue
        if m:
            return m.group(1)
    if shutil.which(FFPROBE) and shutil.which(MKVMERGE):
        for root, dirs, files in os.walk(folder):
            dirs[:] = [d for d in dirs if not d.startswith(".")]
            mkv = next((f for f in sorted(files) if f.lower().endswith(".mkv")), None)
            if mkv:
                try:
                    return read_media(Path(root, mkv)).tags.get("COLLECTION/TVMAZE") or None
                except ToolError:
                    return None
    return None


def wikipedia_lead(get: Getter, query: str, want: str) -> str:
    """The first sentences of the Wikipedia article that best fits: its title must start with the
    name, and its text must say it's a series or a film."""
    url = (f"{WIKIPEDIA}?action=query&format=json&generator=search&gsrlimit=5&prop=extracts&exintro=1"
           f"&explaintext=1&exsentences=2&exlimit=max&redirects=1&gsrsearch={urllib.parse.quote(query)}")
    try:
        data = get(url, "Wikipedia", hint="", what=f'looking up "{query}"')
    except RenamerError as e:
        debug(f"Wikipedia: {e}")
        return ""
    pages = sorted(((data or {}).get("query") or {}).get("pages", {}).values(), key=lambda p: p.get("index", 99))
    key = normalize_title(want)
    for page in pages:
        title = re.sub(r"\s*\([^)]*\)$", "", page.get("title", ""))
        text = page.get("extract") or ""
        if normalize_title(title).startswith(key[:12]) and _DESCRIPTOR_END.search(text):
            return " ".join(text.split())
    return ""


def wikipedia_extract(get: Getter, title: str) -> str:
    url = (f"{WIKIPEDIA}?action=query&format=json&prop=extracts&exintro=1&explaintext=1&exsentences=2"
           f"&redirects=1&titles={urllib.parse.quote(title)}")
    try:
        data = get(url, "Wikipedia", hint="", what=f'reading "{title}"')
    except RenamerError:
        return ""
    pages = ((data or {}).get("query") or {}).get("pages", {})
    return " ".join(next(iter(pages.values()), {}).get("extract", "").split()) if pages else ""


def _search_tvmaze(get: Getter, name: str) -> list[dict]:
    results = get(f"{TVMAZE}/search/shows?q={urllib.parse.quote(name)}", what=f'searching for "{name}"') or []
    return [r["show"] for r in results if r.get("show")]


def _same_name(a: str, b: str) -> bool:
    def key(x: str) -> str:
        return normalize_title(re.sub(r"^the\s+", "", x, flags=re.I))
    return key(a) == key(b)


def lookup_show(item: LibItem, get: Getter) -> None:
    """Find the show on TVmaze without asking anything; doubtful matches get a match_note."""
    known = _known_tvmaze_id(item.path)
    show = None
    if known:
        try:
            show = get(f"{TVMAZE}/shows/{known}", what=f"show #{known}")
            item.title = f"TVmaze #{known} (from renamer's .nfo or tags)"
        except RenamerError as e:
            debug(f"TVmaze show #{known}: {e}")
    if show is None:
        layout = find_layout(item.path)
        groups, _ = collect_groups(layout, UI(interactive=False, debug_dir=None))
        guess, _ = _guess_show(layout, groups)
        files, _ = _files_show(groups)
        name = readable(guess)
        if files and not same_show_key(normalize_title(files), normalize_title(name) or "-"):
            name = files
        if not name or season_from_folder(name) is not None and len(normalize_title(re.sub(
                r"(?i)season|series|s\d+|\d+", "", name))) < 3:
            item.why = "can't tell which show it is: no show name in the folder or the filenames"
            return
        item.title = name
        shows = _search_tvmaze(get, name) or shorter_search(name, get)
        if not shows:
            suggestion = wikipedia_guess(name, UI(interactive=False, debug_dir=None), get)
            if suggestion and normalize_title(suggestion) != normalize_title(name):
                shows = _search_tvmaze(get, suggestion)
                if shows:
                    item.match_note = f'TVmaze has nothing for "{name}"; Wikipedia suggests {suggestion}'
        if not shows:
            item.why = f'TVmaze has no show matching "{name}"'
            return
        twin = pick_twin(shows, evidence_from(layout, groups), get)
        show = twin or shows[0]
        if not item.match_note and not _same_name(show.get("name", ""), name):
            item.match_note = f'TVmaze\'s best match for "{name}"'
        elif not twin and len([s for s in shows if _same_name(s.get("name", ""), show.get("name", ""))]) > 1:
            item.match_note = f"Several shows are called {show.get('name')}, and nothing here says which"
    item.found = f"{show.get('name')} ({(show.get('premiered') or '')[:4] or 'year unknown'})"
    item.tvmaze_id = str(show.get("id", ""))
    item.raw_genres = list(show.get("genres") or [])
    year = (show.get("premiered") or "")[:4]
    item.lead = (wikipedia_lead(get, f"{show.get('name')} {year} television series", show.get("name", ""))
                 or wikipedia_lead(get, f"{show.get('name')} TV series", show.get("name", "")))


def finish_item(item: LibItem, config: GenreConfig) -> None:
    """Map the source's genres to the config's and pick the main one."""
    item.genres = list(dict.fromkeys(g for g in (config.genre_for(x) or next(iter(genres_in(x, config)), None)
                                                 for x in item.raw_genres) if g))
    if not item.found:
        return
    pick_genre(item, config)
    if item.match_note:
        item.sure = False
        item.why = f"{item.match_note} is {item.found}; {item.why}"


_COLLECTION = re.compile(r"\b(?:trilogy|quadrilogy|duology|collection|anthology|box[ ._-]?set|saga"
                         r"|complete|\d{1,2}\s*-\s*\d{1,2}|\d{1,2}(?:\s*,\s*\d{1,2}){2,})\b.*$", re.I)


def _movie_title(name: str) -> tuple[str, str, bool]:
    """A movie's title, year, and whether it's a collection, from a folder or file name:
    "Example Movie (1985) [1080p]", "[ www.example-site.com ] - Example Movie (1992)",
    "Example Movie 1-3 Trilogy 1997-2002" -> ("Example Movie", "1997", True)."""
    stem = Path(name).stem if Path(name).suffix.lower() in VIDEO_EXTS else name
    stem = _SITE_PREFIX.sub("", stem)
    year = re.search(r"(?<![0-9])(19[0-9]{2}|20[0-9]{2})(?![0-9])", stem)
    title = readable(show_from_folder(stem)) or readable(stem)
    collection = bool(_COLLECTION.search(title) or _COLLECTION.search(readable(stem)))
    if collection:
        title = _COLLECTION.sub("", title).strip(" -,") or title
    return title, year.group(1) if year else "", collection


def _like(found: str, title: str) -> bool:
    """Whether a found film's name is close enough to the title looked for."""
    a = normalize_title(re.sub(r"\s*\([^)]*\)\s*$", "", found))
    b = normalize_title(title)
    return bool(a and b) and (a in b or b in a or difflib.SequenceMatcher(None, a, b).ratio() >= 0.6)


WIKIDATA_ENTITY = "https://www.wikidata.org/wiki/Special:EntityData/{}.json"
_genre_labels: dict[str, str] = {}   # Wikidata genre ID -> its English name, kept in the lookup cache


def _wikidata_entity(get: Getter, qid: str) -> dict:
    data = get(WIKIDATA_ENTITY.format(qid), "Wikidata", hint="", what=f"reading {qid}") or {}
    return (data.get("entities") or {}).get(qid) or next(iter((data.get("entities") or {}).values()), {})


def _wikidata_genres(get: Getter, qid: str) -> tuple[list[str], str]:
    """A Wikidata item's genre (P136) names, and its English Wikipedia article's title. Read from
    Special:EntityData, which isn't rate limited; genre names are remembered."""
    data = _wikidata_entity(get, qid)
    ids = [c["mainsnak"]["datavalue"]["value"]["id"] for c in (data.get("claims") or {}).get("P136", [])
           if c.get("mainsnak", {}).get("datavalue")][:20]
    labels = []
    for g in ids:
        if g not in _genre_labels:
            _genre_labels[g] = ((_wikidata_entity(get, g).get("labels") or {}).get("en") or {}).get("value", "")
        labels.append(_genre_labels[g])
    return [x for x in labels if x], ((data.get("sitelinks") or {}).get("enwiki") or {}).get("title", "")


def _wikipedia_film(get: Getter, title: str, year: str) -> tuple[str, str, str]:
    """When Wikidata's search doesn't find the film by name: Wikipedia's search, which matches
    looser names ("Example Movie Long Name" -> "Movie Long Name"). Returns
    (article title, its Wikidata ID, its first sentences)."""
    url = (f"{WIKIPEDIA}?action=query&format=json&generator=search&gsrlimit=5&prop=pageprops|extracts"
           f"&ppprop=wikibase_item&exintro=1&explaintext=1&exsentences=2&exlimit=max&redirects=1"
           f"&gsrsearch={urllib.parse.quote(f'{title} {year} film'.strip())}")
    try:
        data = get(url, "Wikipedia", hint="", what=f'looking up "{title}"')
    except RenamerError:
        return "", "", ""
    pages = sorted(((data or {}).get("query") or {}).get("pages", {}).values(), key=lambda p: p.get("index", 99))
    films = [(p, " ".join((p.get("extract") or "").split())) for p in pages]
    films = [(p, t) for p, t in films if re.search(r"\bfilm\b", descriptor(t))]
    # The year in the description itself ("a 2023 American … film") beats a year anywhere in the text,
    # which a sequel's article mentions too.
    for page, text in sorted(films, key=lambda pt: not (year and year in descriptor(pt[1]))):
        if not year or year in text:
            return page.get("title", ""), (page.get("pageprops") or {}).get("wikibase_item", ""), text
    return "", "", ""


config_for_names: GenreConfig | None = None   # set by run_lib_genre, for genre words in folder names


def lookup_movie(item: LibItem, get: Getter) -> None:
    """Find the film on Wikidata (or through Wikipedia) and its genres, and Wikipedia's
    description of it."""
    title, year, collection = _movie_title(item.path.name)
    item.title = f"{title} ({year})" if year else title
    url = (f"{WIKIDATA}?action=wbsearchentities&format=json&language=en&type=item&limit=10"
           f"&search={urllib.parse.quote(title)}")
    results = (get(url, "Wikidata", hint="", what=f'searching for "{title}"') or {}).get("search", [])
    films = [r for r in results if "film" in (r.get("description") or "").lower()
             and _like(r.get("label", ""), title)]
    if year:   # a film from another year is the wrong one (Example Movie for 1996)
        films = [r for r in films if year in (r.get("description") or "")]
    if films:
        film = films[0]
        if collection:
            item.match_note = "a collection; its first film on Wikidata"
        elif not (year and year in (film.get("description") or "") and _same_name(film.get("label", ""), title)):
            item.match_note = "Wikidata's best match"
        item.raw_genres, wiki_title = _wikidata_genres(get, film["id"])
        item.found = f"{film.get('label')} ({film.get('description')})"
        item.lead = wikipedia_extract(get, wiki_title) if wiki_title else ""
        return
    wiki_title, qid, lead = _wikipedia_film(get, title, year)
    if not qid or not _like(wiki_title, title):
        item.why = "no film found on Wikidata or Wikipedia" + (f" (Wikipedia's search gave {wiki_title})"
                                                              if wiki_title else "")
        named = genres_in(item.path.name, config_for_names) if config_for_names else []
        if collection and named:   # "Example Show Movie Collection - Sci-Fi …": the name says the genre
            item.found, item.raw_genres = item.title, named[:1]
            item.match_note = "a collection named for its genre"
        return
    item.raw_genres, _ = _wikidata_genres(get, qid)
    item.found, item.lead = wiki_title, lead
    if collection:
        item.match_note = "a collection; Wikipedia's best match"
    elif not (year and year in descriptor(lead) and _same_name(re.sub(r"\s*\([^)]*\)$", "", wiki_title), title)):
        item.match_note = "Wikipedia's best match"


def scan_library(root: Path, config: GenreConfig) -> tuple[list[LibItem], dict[str, str], list[str]]:
    """The items at the top of a library, its genre folders ({genre: folder name}), and warnings."""
    genre_dirs: dict[str, str] = {}
    items: list[LibItem] = []
    warnings: list[str] = []
    loose_episodes = 0
    for entry in sorted(os.scandir(root), key=lambda e: natural_key(e.name)):
        if entry.name.startswith(".") or entry.name == UNSORTED_DIR:
            continue
        path = Path(entry.path)
        if entry.is_dir():
            genre = config.genre_for(entry.name)
            if genre:
                genre_dirs.setdefault(genre, entry.name)
                continue
            if (path / GROUP_MARKER).is_file() or looks_like_show(path) or season_from_folder(entry.name) is not None:
                items.append(LibItem(path, "show"))
            elif any(Path(f).suffix.lower() in VIDEO_EXTS for _, _, fs in os.walk(path) for f in fs):
                items.append(LibItem(path, "movie"))
            else:
                items.append(LibItem(path, "skip", why="no videos in it"))
        elif path.suffix.lower() in VIDEO_EXTS:
            if parse_episode(path.name):
                loose_episodes += 1
            else:
                items.append(LibItem(path, "movie"))
    if loose_episodes:
        warnings.append(f"{_plural(loose_episodes, 'episode video')} lie loose in {root.name}/ and are left alone; "
                        "put them in a show folder first.")
    return items, genre_dirs, warnings


@dataclass
class _Wrap:
    genre_dir: str
    show: str
    seasons: list[str]


def wraps_needed(root: Path, genre_dirs: dict[str, str]) -> list[_Wrap]:
    """Genre folders holding a show's season folders directly, with no show folder (a
    TV/Scifi/ with EXAMPLE SHOW's seasons in it)."""
    found = []
    for folder in genre_dirs.values():
        seasons = [d for d in _entries(root / folder, dirs=True) if season_from_folder(d.name) is not None]
        if not seasons:
            continue
        counts: Counter = Counter()
        for d in seasons:
            for f in _entries(d, dirs=False):
                name = readable(show_from_folder(show_in_filename(f.name)))
                if len(normalize_title(name)) >= 4:
                    counts[name] += 1
        show = counts.most_common(1)[0][0] if counts else readable(show_from_folder(seasons[0].name))
        found.append(_Wrap(folder, clean_text(show) or "Show", [d.name for d in seasons]))
    return found


def lib_plan(root: Path, items: list[LibItem], genre_dirs: dict[str, str], wraps: list[_Wrap]) -> Plan:
    plan = Plan()
    existing = {n.casefold() for n in os.listdir(root)}
    made: set[str] = set()
    moves: list[Op] = []
    for w in wraps:
        target = f"{w.genre_dir}/{w.show}"
        rows = plan.sections.setdefault(f"{w.genre_dir}/ (its season folders go into a show folder)", [])
        if (root / target).exists():
            rows.append(Row("CONFLICT", f"{w.genre_dir}/", "", f"{target}/ already exists"))
            continue
        plan.ops.append(Op("mkdir", dst=target))
        for s in w.seasons:
            rows.append(Row("MOVE", f"{w.genre_dir}/{s}/", f"{target}/{s}/"))
            moves.append(Op("genre", f"{w.genre_dir}/{s}", f"{target}/{s}", is_dir=True))
    left = plan.sections.setdefault("Left where they are", [])
    for item in items:
        name = item.path.name + ("/" if item.path.is_dir() else "")
        if item.conflict:
            left.append(Row("CONFLICT", name, "", item.conflict))
            continue
        if item.kind == "skip" or not item.folder:
            left.append(Row("SKIP", name, "", item.why or "no genre found"))
            continue
        folder = item.folder
        target = root / folder / item.path.name
        label = f"{folder}/" + ("" if folder.casefold() in existing else "  (new folder)")
        rows = plan.sections.setdefault(label, [])
        if target.exists() or (root / folder).is_file():
            rows.append(Row("CONFLICT", name, "", f"{folder}/{item.path.name} already exists"))
            continue
        if folder.casefold() not in existing and folder not in made:
            plan.ops.append(Op("mkdir", dst=folder))
            made.add(folder)
        genres = ", ".join(item.raw_genres) or "no genres listed"
        rows.append(Row("MOVE" if item.sure else "GUESS", name, f"{folder}/{name}",
                        f"{item.found}: {genres}" if item.found else genres, [item.why] if item.why else []))
        moves.append(Op("genre", item.path.name, f"{folder}/{item.path.name}", is_dir=item.path.is_dir()))
    if not left:
        del plan.sections["Left where they are"]
    else:   # last in the preview
        plan.sections["Left where they are"] = plan.sections.pop("Left where they are")
    plan.ops += moves
    return plan


def _parse_numbers(text: str, top: int) -> list[int]:
    if text.strip().lower() == "all":
        return list(range(1, top + 1))
    return [int(n) for n in re.findall(r"\d+", text) if 1 <= int(n) <= top]


def ask_unsure(ui: UI, unsure: list[LibItem], config: GenreConfig, genre_dirs: dict[str, str],
               get: Getter) -> bool:
    """After the preview: the items renamer isn't sure about, and which to change.
    Returns whether anything changed."""
    ui.say(f"Not sure about {len(unsure)}:")
    width = min(40, max(len(i.path.name) for i in unsure))
    for n, item in enumerate(unsure, 1):
        genres = ", ".join(item.raw_genres) or "no genres"
        ui.say(f"  {n:>2}. {item.path.name[:width]:<{width}} | {genres} → {item.folder or '(left where it is)'}")
        if item.why:
            ui.say(f"      {'':<{width}}   {_short(item.why, 110)}")
    picked = _parse_numbers(ui.ask("Select which to change (numbers, all, Enter for none): "), len(unsure))
    changed = False
    for n in picked:
        item = unsure[n - 1]
        ui.say()
        ui.say(f"{item.path.name}" + (f"  ({item.found})" if item.found else ""))
        if item.why:
            ui.say(f"  {item.why}")
        choices = list(dict.fromkeys([config.folders[g] for g in item.genres if g in config.folders]
                                     + sorted(genre_dirs.values(), key=natural_key)))
        for i, folder in enumerate(choices, 1):
            ui.say(f"  {i}) {folder}" + ("" if folder in genre_dirs.values() else "  (new folder)"))
        ui.say("  0) leave it where it is")
        if item.kind == "show":
            ui.say("  s) search TVmaze for a different show")
        while True:
            answer = ui.ask(f"Folder [{1 if choices else 0}], or type a folder name: ", "1" if choices else "0")
            if answer.lower() == "s" and item.kind == "show":
                typed = ui.ask("Search TVmaze for: ")
                if typed:
                    found = get(f"{TVMAZE}/search/shows?q={urllib.parse.quote(typed)}",
                                what=f'searching for "{typed}"') or []
                    shows = [r["show"] for r in found if r.get("show")]
                    show = _choose_show(typed, shows, ui)[0] if len(shows) > 1 else (shows or [None])[0]
                    if show:
                        item.found = f"{show.get('name')} ({(show.get('premiered') or '')[:4]})"
                        item.raw_genres = list(show.get("genres") or [])
                        item.match_note, item.lead = "", wikipedia_lead(
                            get, f"{show.get('name')} TV series", show.get("name", ""))
                        finish_item(item, config)
                        ui.say(f"  {item.found}: {', '.join(item.raw_genres) or 'no genres'} → {item.folder}")
                        choices = list(dict.fromkeys([config.folders[g] for g in item.genres if g in config.folders]
                                                     + choices))
                continue
            if answer.isdigit() and 0 <= int(answer) <= len(choices):
                item.folder = choices[int(answer) - 1] if int(answer) else None
            elif answer and not answer.isdigit():
                existing = next((f for f in genre_dirs.values() if f.casefold() == answer.casefold()), None)
                item.folder = existing or clean_folder_name(answer)
            else:
                ui.say(f"Type a number from 0 to {len(choices)}, or a folder name.")
                continue
            break
        item.sure, item.why = True, "chosen"
        if not item.folder:
            item.why = "left where it is (chosen)"
        changed = True
    ui.say()
    return changed


def clean_folder_name(text: str) -> str:
    return re.sub(r'[/\\:*?"<>|]+', "-", text).strip(" .") or "Other"


def run_lib_genre(args, ui: UI, fetch: Callable[[str], object] = http_get_json) -> int:
    """renamer lib --genre: move each show or movie at the top of a library into a genre
    folder, as a whole; nothing inside it is touched."""
    root = _full_path(args.path)
    if not root.is_dir():
        raise RenamerError(f"Not a folder: {root}")
    subdirs = _entries(root, dirs=True)
    if subdirs and all(season_from_folder(d.name) is not None or _SHOW_EXTRAS.fullmatch(d.name) for d in subdirs):
        raise RenamerError(f"{root} is a show folder (it holds season folders). Give the library folder "
                           f"above it, for example: renamer lib --genre {shlex.quote(str(root.parent))}")
    if not os.access(root, os.W_OK):
        raise RenamerError(f"No write permission in {root}, so nothing can be moved. Nothing was changed.")
    ui.start_log(log_name_for(root) + "_lib")
    global config_for_names
    config = config_for_names = load_genre_config(ui)
    items, genre_dirs, warnings = scan_library(root, config)
    for genre, folder in genre_dirs.items():
        config.folders[genre] = folder   # an existing folder wins over the config's name for it
    wraps = wraps_needed(root, genre_dirs)
    if wraps and ui.interactive:
        for w in list(wraps):
            ui.say(f"{w.genre_dir}/ holds a show's season folders ({', '.join(w.seasons[:4])}"
                   + (", …" if len(w.seasons) > 4 else "") + f") with no show folder around them.")
            answer = ui.ask(f"Put them in a show folder, {w.genre_dir}/{w.show}/? [Y/n], or type its name: ", "y")
            if answer.lower() in ("n", "no"):
                wraps.remove(w)
            elif answer.lower() not in ("y", "yes"):
                w.show = clean_folder_name(answer)
            ui.say()
    elif wraps:
        warnings += [f"{w.genre_dir}/ holds a show's season folders with no show folder around them." for w in wraps]
        wraps = []

    get = Getter(_Paced(fetch), ui, quiet=True)
    cache = _cache_load()
    _genre_labels.update(cache.get("_genre_labels", {}).get("names", {}))
    todo = [i for i in items if i.kind in ("show", "movie")]
    progress = Progress(ui, "Looking up genres", len(todo))
    try:
        for done, item in enumerate(todo):
            progress.update(done, item.path.name)
            if find_downloads(item.path) if item.path.is_dir() else item.path.name.lower().endswith(DOWNLOAD_EXTS):
                item.conflict = "still downloading (.!qb)"
                continue
            key = f"{item.kind}:{item.path.name}"
            if key in cache:
                for name in _CACHED:
                    setattr(item, name, cache[key].get(name, getattr(item, name)))
                debug(f"lib item from the cache ({LIB_CACHE}): {key}")
            else:
                try:
                    (lookup_show if item.kind == "show" else lookup_movie)(item, get)
                    if item.found:
                        cache[key] = {name: getattr(item, name) for name in _CACHED} | {"time": time.time()}
                except RenamerError as e:
                    item.why = str(e)
            finish_item(item, config)
            debug(f"lib item {item}")
        progress.update(len(todo))
    finally:
        progress.finish()
        cache["_genre_labels"] = {"names": dict(_genre_labels), "time": time.time()}
        _cache_save(cache)

    header = [f"Library: {root}", "Mode:    lib --genre (moves whole show and movie folders into genre "
              "folders; nothing inside them changes)"]
    if genre_dirs:
        header.append("Genre folders here: " + ", ".join(f"{f}/" for f in sorted(genre_dirs.values(), key=natural_key)))
    plan = lib_plan(root, items, genre_dirs, wraps)
    plan.warnings = warnings
    print_preview(ui, header, plan)
    unsure = [i for i in todo if not i.sure and not i.conflict]
    if unsure and ui.interactive and ask_unsure(ui, unsure, config, genre_dirs, get):
        plan = lib_plan(root, items, genre_dirs, wraps)
        changed = [row for rows in plan.sections.values() for row in rows
                   if any(row.old.rstrip("/") == i.path.name for i in unsure if i.why.endswith("chosen"))]
        for row in changed:
            _print_row(ui, row)
        ui.say()
    if not any(op.kind == "genre" for op in plan.ops):
        ui.say("Nothing to move.")
        return 0
    if not confirm(ui, _summary(plan.ops)):
        return 0 if ui.interactive else 1
    return apply_ops(plan.ops, root, ui, "Moving")


# ------------------------------------------------- library: sorting shows

_RENAMER_SHOW_DIR = re.compile(r"^[^_\s]+(?:_\d{4}(?:-(?:\d{4}|present))?)?(?:_Seasons?_\d{2,3}(?:-\d{2,3})?)?(?:_Dub)?$")
_BUNDLE_NUMBERING = re.compile(r"^\s*\d+[a-z]?[.)]\s")   # "1a. Example Show - Part One"


def _episode_videos(folder: Path) -> list[Path]:
    """Episode videos anywhere in a folder, hidden folders and samples left out."""
    found = []
    for root, dirs, files in os.walk(folder):
        dirs[:] = [d for d in dirs if not d.startswith(".")]
        found += [Path(root, f) for f in files
                  if Path(f).suffix.lower() in VIDEO_EXTS and not f.startswith(".") and parse_episode(f)
                  and not _SAMPLE.search(Path(f).stem)]
    return found


def _is_bundle(folder: Path) -> bool:
    """Several shows (and maybe movies) in one folder: "EXAMPLE SHOW Cartoons … The FIVE Complete Animated
    Series" with "1a. Example Show - Part One (1992-99)/", "2a. Example Show Part Two …/"."""
    subs = [d for d in _entries(folder, dirs=True) if season_from_folder(d.name) is None
            and not _SHOW_EXTRAS.fullmatch(d.name)]
    if len(subs) < 2 or any(season_from_folder(d.name) is not None for d in _entries(folder, dirs=True)):
        return False
    # A release with its own seasons beside other things (Example 1⁄2/Example ½ OG Series/Example ½ Season 1) (1.2.0).
    if any(not _SEASONS_LAYER.fullmatch(d.name) and any(season_from_folder(x.name) is not None
                                                        for x in _entries(d, dirs=True)) for d in subs):
        return True
    # Only numbered parts ("1a. …", "2a. …") say for sure it's a bundle; "Book One - Air/" and
    # "Specials/" are one show's parts (Example Show).
    return sum(1 for d in subs if _BUNDLE_NUMBERING.match(d.name)) >= 2


def is_movie_collection(folder: Path) -> bool:
    """A folder of movies: at least two videos, most with a year in the name, none with an episode
    code and few with a plain number (Example Studio Collection/Example-Movie.2010.1080p.mkv) (1.2.0)."""
    videos = []
    for base, dirs, files in os.walk(folder):
        dirs[:] = [d for d in dirs if not d.startswith(".") and not _SAMPLE_FOLDER.fullmatch(d)]
        videos += [f for f in files if Path(f).suffix.lower() in VIDEO_EXTS and not f.startswith(".")
                   and not _SAMPLE.search(Path(f).stem)]
    if len(videos) < 2 or any(parse_episode(v) for v in videos):
        return False
    numbered = sum(1 for v in videos if plain_numbers(v))
    dated = sum(1 for v in videos if _HAS_YEAR.search(Path(v).stem))
    return dated * 2 > len(videos) and numbered * 5 <= len(videos)


def _release_tokens(name: str) -> set[str]:
    """The words of a filename that say which release it's from ("1080p", "web", "h264", "grace"),
    with its SxxEyy and anything before it left out."""
    stem = Path(name).stem.lower()
    m = _episode_match(stem)
    after = stem[m.end():] if m else stem
    return {t for t in re.split(r"[\s._\-\[\]()+,]+", after) if len(t) >= 2}


def prefer_release(copies: list, reference: list[str]) -> object | None:
    """Of several copies of one episode, the one whose name looks like the show's own files (the
    same release) when one clearly does (1.0.0); else None, and quality decides."""
    if not reference or len(copies) < 2:
        return None
    counts: Counter = Counter(t for name in reference for t in _release_tokens(name))
    common = {t for t, n in counts.items() if n >= max(2, len(reference) // 2)}
    if not common:
        return None
    scored = sorted(((len(_release_tokens(c.path.name) & common) / len(common), c) for c in copies),
                    key=lambda sc: sc[0], reverse=True)
    return scored[0][1] if scored[0][0] - scored[1][0] >= 0.25 else None


def find_movies_dir(root: Path) -> Path:
    """Where movies found in a TV library go: a Movies folder in ../, ../../ or ../../../ (for an
    animated library, Movies(Animated) first), else a hidden .movies/ in the library."""
    animated = "anim" in root.name.lower()
    wanted = (["moviesanimated", "animatedmovies"] if animated else []) + ["movies"]
    for key in wanted:
        for base in (root.parent, root.parent.parent, root.parent.parent.parent):
            try:
                found = next((Path(e.path) for e in os.scandir(base)
                              if e.is_dir() and normalize_title(e.name) == key), None)
            except OSError:
                found = None
            if found and found != root:
                return found
    return root / ".movies"


@dataclass
class SortGroup:
    """One show's pieces in a library, and the folder they end up in."""
    show: str                      # TVmaze's name
    tvmaze_id: str
    members: list[LibItem]
    target: Path | None = None     # an existing folder, or a new one to make
    new: bool = False


def _target_for(members: list[LibItem], root: Path, name: str, dub: bool = False) -> tuple[Path, bool]:
    """The folder a show's pieces gather in: one already in a genre folder, else one in renamer's
    own format, else the one with the most episodes; a new folder when all are lone seasons or
    loose episodes."""
    folders = [m for m in members if m.kind == "show" and not m.lone]
    if folders:
        best = max(folders, key=lambda m: (m.in_genre, bool(_RENAMER_SHOW_DIR.match(m.path.name)), m.videos))
        return best.path, False
    base = next((m.path.parent for m in members if m.in_genre), root)
    return base / ((clean_text(name) or "Show") + ("_Dub" if dub else "")), True


def lookup_loose(item: LibItem, get: Getter) -> None:
    """Loose episode files at the top of a library, by the show name in their filenames."""
    item.title = item.title or readable(show_from_folder(show_in_filename(item.files[0].name), True))
    shows = _search_tvmaze(get, item.title) if item.title else []
    if not shows:
        item.why = f'TVmaze has no show matching "{item.title}"'
        return
    years = [y for f in item.files for y in _HAS_YEAR.findall(f.stem)]
    show = pick_twin(shows, Evidence(years=years), get) or shows[0]
    if not _same_name(show.get("name", ""), item.title):
        item.match_note = f'TVmaze\'s best match for "{item.title}"'
    item.tvmaze_id = str(show["id"])
    item.found = f"{show.get('name')} ({(show.get('premiered') or '')[:4] or 'year unknown'})"


def match_by_titles(items: list[LibItem], get: Getter) -> None:
    """Season folders with no show name ("SEASON 02" holding "S02E01 - Episode Title…") are
    matched by their episode titles against the shows found in the library."""
    nameless = [i for i in items if i.kind == "show" and not i.tvmaze_id and i.why.startswith("can't tell")]
    known = {i.tvmaze_id: i.found for i in items if i.tvmaze_id}
    if not nameless or not known:
        return
    episodes: dict[str, dict[tuple[int, int], str]] = {}
    for show_id in known:
        data = get(f"{TVMAZE}/shows/{show_id}/episodes", what=f"getting the episodes of {known[show_id]}") or []
        episodes[show_id] = {(e.get("season"), e.get("number")): normalize_title(e.get("name") or "")
                             for e in data if e.get("number")}
    for item in nameless:
        titled = []
        for video in _episode_videos(item.path):
            code = parse_episode(video.name)
            title = normalize_title(title_from_filename(video.name)[0])
            if code and title:
                titled.append((code[0], code[1][0], title))
        def close(a: str, b: str | None) -> bool:
            return bool(a and b) and (a == b or a.startswith(b) or b.startswith(a)
                                      or difflib.SequenceMatcher(None, a, b).ratio() >= 0.8)
        scores = sorted(((sum(1 for s, e, t in titled if close(t, eps.get((s, e)))), show_id)
                         for show_id, eps in episodes.items()), reverse=True)
        score, best = scores[0] if scores else (0, None)
        runner_up = scores[1][0] if len(scores) > 1 else 0
        if best and score >= min(3, len(titled)) and score >= 2 * runner_up:
            item.tvmaze_id, item.found = best, known[best]
            item.why = f"{score} of {len(titled)} episode titles are {known[best]}'s"
            item.match_note = "" if score >= 3 else "matched by its episode titles"


def scan_for_sort(root: Path, config: GenreConfig) -> tuple[list[LibItem], list[str]]:
    """Everything at the top of a library that --sort looks at, plus the shows inside genre
    folders (as places to merge into)."""
    items: list[LibItem] = []
    warnings: list[str] = []
    loose: dict[str, list[Path]] = {}
    parts = []

    def add_folder(path: Path, in_genre: bool) -> None:
        marker = read_group_marker(path)
        if marker is not None:
            items.append(LibItem(path, "group", found=marker.get("show", path.name), in_genre=in_genre,
                                 tvmaze_id=marker.get("tvmaze_id", ""), why="copies of one show, kept apart; left as it is"))
            return
        videos = _episode_videos(path)
        all_videos = [f for _, _, fs in os.walk(path) for f in fs
                      if Path(f).suffix.lower() in VIDEO_EXTS and not f.startswith(".")]
        downloading = [f for _, _, fs in os.walk(path) for f in fs if f.lower().endswith(DOWNLOAD_EXTS)]
        has_seasons = any(season_from_folder(d.name) is not None for d in _entries(path, dirs=True))
        named_season = (season_from_folder(path.name) or 0) > 0   # "+Specials" isn't a season of its own
        seasons = {parse_episode(v.name)[0] for v in videos}
        dub = is_dub(path.name) or sum(1 for v in all_videos if is_dub(v)) * 2 > len(all_videos) > 0
        if _is_bundle(path):
            items.append(LibItem(path, "skip", why="holds several shows; left as it is", in_genre=in_genre))
        elif not has_seasons and is_movie_collection(path):
            items.append(LibItem(path, "movie", why="a collection of movies", in_genre=in_genre))
        elif videos or has_seasons or named_season or len(all_videos) >= 4 or downloading or seasons_layer(path):
            # A show, even when its files have no SxxEyy ("Episode 11 Episode Title.mkv")
            # or are all still downloading.
            lone = not has_seasons and named_season and len(seasons) <= 1
            items.append(LibItem(path, "show", lone=lone, videos=len(videos) or len(all_videos), in_genre=in_genre, dub=dub))
        elif all_videos:
            if len(all_videos) == 1 and not _HAS_YEAR.search(path.name + all_videos[0]) and not same_show_key(
                    normalize_title(Path(all_videos[0]).stem) or "-", normalize_title(path.name) or "-"):
                # SOME-FOLDER/SOME_AUTH_SCN.avi: nothing says what it is (1.2.0)
                items.append(LibItem(path, "skip", why="one video, with no year and a name unlike its folder's: "
                                                        "can't tell what it is", in_genre=in_genre))
            else:
                items.append(LibItem(path, "movie", in_genre=in_genre))

    for entry in sorted(os.scandir(root), key=lambda e: natural_key(e.name)):
        path = Path(entry.path)
        if entry.name.startswith("."):
            if entry.name.endswith(".parts") and entry.is_file():
                parts.append(entry.name)
            continue
        if entry.name == UNSORTED_DIR:
            continue
        if entry.is_dir():
            if config.genre_for(entry.name):
                for d in _entries(path, dirs=True):
                    add_folder(d, True)
                continue
            add_folder(path, False)
        elif path.suffix.lower() in VIDEO_EXTS:
            if parse_episode(path.name):
                key = normalize_title(readable(show_from_folder(show_in_filename(path.name), True)))
                loose.setdefault(key + ("|dub" if is_dub(path.name) else ""), []).append(path)
            else:
                items.append(LibItem(path, "movie"))
    for files in loose.values():
        subs = [p for p in _entries(root, dirs=False) if p.suffix.lower() in SUB_EXTS
                and any(p.name.startswith(f.stem + ".") for f in files)]
        items.append(LibItem(root, "loose", files=sorted(files + subs, key=lambda p: natural_key(p.name)),
                             videos=len(files), dub=any(is_dub(f.name) for f in files)))
    if parts:
        warnings.append(f"{_plural(len(parts), 'qBittorrent .parts file')} ({', '.join(parts[:3])}"
                        + (", …" if len(parts) > 3 else "") + ") left alone: they hold pieces of files a torrent "
                        "skipped, and qBittorrent may still use them.")
    return items, warnings


def group_shows(items: list[LibItem], root: Path) -> tuple[list[SortGroup], list[LibItem]]:
    """Items of the same TVmaze show, and what needs doing about each: merging, a new show folder
    for lone seasons or loose episodes. Returns the groups with work, and the items left alone."""
    by_id: dict[str, list[LibItem]] = {}
    left = []
    for item in items:
        if item.kind in ("show", "loose") and item.tvmaze_id and not item.leave:
            # A dub stays apart from the show's other copies; lib --group puts them in one folder (1.2.0).
            by_id.setdefault(item.tvmaze_id + ("|dub" if item.dub else ""), []).append(item)
        elif item.kind != "movie":
            left.append(item)
    groups = []
    for key, members in by_id.items():
        show_id, _, dub = key.partition("|")
        name = re.sub(r"\s*\((?:\d{4}|year unknown)\)$", "", members[0].found)
        needs = len(members) > 1 or any(m.lone or m.kind == "loose" for m in members)
        if not needs:
            continue
        target, new = _target_for(members, root, name, bool(dub))
        groups.append(SortGroup(name, show_id, members, target, new))
    return groups, left


@dataclass
class MixedFolder:
    """One folder holding shows that share a name (Example ½ of 1989 and of 2024), and what's whose (1.2.0)."""
    parts: list[tuple[dict, list[Path]]]   # (TVmaze's show, what's its in the folder)
    unknown: list[Path]


def _child_videos(child: Path) -> list[Path]:
    if child.is_file():
        return [child]
    return [Path(b, f) for b, _, fs in os.walk(child) for f in fs
            if Path(f).suffix.lower() in VIDEO_EXTS and not f.startswith(".")]


def whose_child(child: Path, twins: list[dict], lists: dict) -> dict | None:
    """Which of the shows a piece of a mixed folder belongs to: a year in its names, its episode or
    special titles, or a number only one of them reaches."""
    videos = _child_videos(child)
    names = [child.name] + [v.stem for v in videos]
    years = [y for n in names for y in _HAS_YEAR.findall(n)]
    for year in dict.fromkeys(years):
        fits = [s for s in twins if (s.get("premiered") or "9999")[:4] <= year <= ((s.get("ended") or "9999")[:4])]
        if len(fits) == 1:
            return fits[0]
    titles = []
    for v in videos:
        titled = title_from_filename(v.name)[0] or (p.title if (p := plain_numbers(v.name)) else "")
        if titled:
            titles.append(titled)
    scores = {s["id"]: _title_hits(titles, lists[s["id"]]) for s in twins}
    # A movie's name holds its title among other words: "Example Movie 2 - Movie Title".
    for s in twins:
        for v in videos:
            key = normalize_title(v.stem)
            for listed in lists[s["id"]]:
                tail = listed.removeprefix(normalize_title(s.get("name", "")))
                if len(tail) >= 8 and tail in key:
                    scores[s["id"]] += 1
                    break
    ranked = sorted(twins, key=lambda s: scores[s["id"]], reverse=True)
    if scores[ranked[0]["id"]] and scores[ranked[0]["id"]] >= 2 * scores[ranked[1]["id"]] + 1:
        return ranked[0]
    top = max((n for v in videos if (p := plain_numbers(v.name)) and not p.special for n in p.numbers), default=0)
    fits = [s for s in twins if len(lists[s["id"]]) >= top]
    return fits[0] if top and len(fits) == 1 else None


def find_mixed(items: list[LibItem], get: Getter) -> None:
    """Folders left as "several shows" that are really shows with one name: each piece is worked out."""
    for item in items:
        if item.kind != "skip" or item.in_genre or not item.path.is_dir() or not _is_bundle(item.path):
            continue
        name = readable(show_from_folder(item.path.name))
        try:
            shows = _search_tvmaze(get, name) if name else []
            twins = [s for s in shows if _same_name(s.get("name", ""), shows[0].get("name", ""))]
            if len(twins) < 2:
                continue
            lists = {s["id"]: _titles_of(get, s) for s in twins}
        except RenamerError as e:
            debug(f"mixed folder {item.path.name}: {e}")
            continue
        children = _entries(item.path, dirs=True) + [p for p in _entries(item.path, dirs=False)
                                                     if p.suffix.lower() in VIDEO_EXTS or p.name.lower().endswith(DOWNLOAD_EXTS)]
        parts: dict[int, tuple[dict, list[Path]]] = {}
        unknown = []
        for child in children:
            show = whose_child(child, twins, lists)
            if show:
                parts.setdefault(show["id"], (show, []))[1].append(child)
            else:
                unknown.append(child)
        if len(parts) >= 2:
            item.split = MixedFolder(sorted(parts.values(), key=lambda p: p[0].get("premiered") or ""), unknown)
            item.why = "several shows of one name; split below"


def _plan_split(plan: Plan, item: LibItem, root: Path) -> list[Path]:
    """Each show's pieces go in a folder named with its year. Two or more whole releases stay whole,
    as lib --group keeps them; other pieces get sorted into seasons in the next step. Returns those."""
    def rel(p: Path) -> str:
        return p.relative_to(root).as_posix()

    to_sort = []
    moved = 0
    for show, children in item.split.parts:
        name = show.get("name", "")
        year = (show.get("premiered") or "")[:4]
        target = root / "_".join(p for p in (clean_text(name) or "Show", year) if p)
        rows = plan.sections.setdefault(f"{rel(target)}/  ({name}, {year}, out of {item.path.name}/)", [])
        if target.exists():
            rows.append(Row("CONFLICT", target.name + "/", "", f"{rel(target)}/ already exists"))
            continue
        ready = [c for c in children if not (find_downloads(c) if c.is_dir() else c.name.lower().endswith(DOWNLOAD_EXTS))]
        for c in children:
            if c not in ready:
                rows.append(Row("CONFLICT", rel(c), "", "still downloading (.!qb)"))
        if not ready:
            continue
        releases = [c for c in ready if c.is_dir() and len(_child_videos(c)) >= 4]
        plan.ops.append(Op("mkdir", dst=rel(target)))
        if len(releases) >= 2:
            marker = json.dumps({"show": name, "tvmaze_id": str(show.get("id", ""))}) + "\n"
            plan.ops.append(Op("create", dst=f"{rel(target)}/{GROUP_MARKER}", content=marker.encode()))
        else:
            to_sort.append(target)
        for c in ready:
            slash = "/" if c.is_dir() else ""
            plan.ops.append(Op("lib", rel(c), f"{rel(target)}/{c.name}", is_dir=c.is_dir()))
            rows.append(Row("MOVE", rel(c) + slash, f"{rel(target)}/{c.name}{slash}", ""))
            moved += 1
    rows = plan.sections.setdefault(f"{item.path.name}/  (left in it)", [])
    for c in item.split.unknown:
        rows.append(Row("WARN", rel(c), "", "can't tell which show it belongs to; left where it is"))
    if moved == len(os.listdir(item.path)):
        plan.ops.append(Op("rmdir", dst=rel(item.path), is_dir=True))
        rows.append(Row("REMOVE", item.path.name + "/", "", "empty by then"))
    return to_sort


def lib_sort_plan(root: Path, groups: list[SortGroup], movies: list[LibItem], movies_dir: Path,
                  left: list[LibItem], layers: tuple = (), mixed: list[LibItem] | None = None,
                  split_targets: list[Path] | None = None) -> Plan:
    plan = Plan()
    made: set[Path] = set()
    for item in mixed or []:
        found = _plan_split(plan, item, root)
        if split_targets is not None:
            split_targets += found

    def rel(p: Path) -> str:
        return p.relative_to(root).as_posix()

    def label(p: Path) -> str:
        return p.name + ("/" if p.is_dir() else "")

    # First, while the paths are still as they are now: the gathering below may move these shows whole.
    for show_dir, layer in layers:
        rows = plan.sections.setdefault(f"{rel(show_dir)}/  (seasons up out of {layer.name}/)", [])
        if find_downloads(show_dir):
            rows.append(Row("CONFLICT", rel(layer) + "/", "", "still downloading (.!qb)"))
            continue
        ops, new_rows = unwrap_plan(show_dir, layer, root)
        plan.ops += ops
        rows += new_rows
    if movies:
        inside = movies_dir.parent == root
        dest = rel(movies_dir) if inside else str(movies_dir)
        rows = plan.sections.setdefault(f"{dest}/  (movies found in this TV library)", [])
        same_disk = movies_dir.exists() and os.stat(movies_dir).st_dev == os.stat(root).st_dev
        if inside and not movies_dir.exists():
            plan.ops.append(Op("mkdir", dst=rel(movies_dir)))
            same_disk = True
        taken = {n.casefold() for n in os.listdir(movies_dir)} if movies_dir.is_dir() else set()
        for m in movies:
            if not same_disk:
                rows.append(Row("CONFLICT", label(m.path), "", f"{movies_dir} is on another disk; move it yourself"))
            elif m.path.name.casefold() in taken:
                rows.append(Row("CONFLICT", label(m.path), "", f"{dest}/{m.path.name} already exists"))
            elif find_downloads(m.path) if m.path.is_dir() else m.path.name.lower().endswith(DOWNLOAD_EXTS):
                rows.append(Row("CONFLICT", label(m.path), "", "still downloading (.!qb)"))
            else:
                target = movies_dir / m.path.name
                plan.ops.append(Op("lib", rel(m.path), rel(target) if inside else os.path.relpath(target, root),
                                   is_dir=m.path.is_dir()))
                rows.append(Row("MOVE", rel(m.path) + ("/" if m.path.is_dir() else ""), f"{dest}/{m.path.name}",
                                m.why or "a movie"))
    for g in sorted(groups, key=lambda g: natural_key(g.show)):
        rows = plan.sections.setdefault(
            f"{rel(g.target)}/  ({g.show}" + (", a new show folder)" if g.new else ")"), [])
        busy = [m for m in g.members if
                (find_downloads(m.path) if m.kind != "loose" else [f for f in m.files if f.name.lower().endswith(DOWNLOAD_EXTS)])]
        if not g.new and find_downloads(g.target):
            busy.append(next(m for m in g.members if m.path == g.target))
        if busy:
            rows.append(Row("CONFLICT", label(g.target), "", "still downloading (.!qb) in "
                            + ", ".join(label(m.path) for m in busy) + "; the whole show is left alone"))
            continue
        if g.new and g.target not in made:
            if g.target.exists():
                rows.append(Row("CONFLICT", label(g.target), "", f"{rel(g.target)}/ already exists"))
                continue
            plan.ops.append(Op("mkdir", dst=rel(g.target)))
            made.add(g.target)
        taken = {n.casefold() for n in os.listdir(g.target)} if g.target.is_dir() else set()
        for m in g.members:
            if m.path == g.target:
                rows.append(Row("KEEP", label(m.path), "", "the folder the others gather in"))
                continue
            sources = m.files if m.kind == "loose" else [m.path]
            for src in sources:
                if src.name.casefold() in taken:
                    rows.append(Row("CONFLICT", label(src), "", f"{rel(g.target)}/{src.name} already exists"))
                    continue
                taken.add(src.name.casefold())
                note = (m.why if m.match_note else "") or ("a season on its own" if m.lone else
                                                            "loose in the library" if m.kind == "loose" else "")
                rows.append(Row("MOVE" if not m.match_note else "GUESS", rel(src) + ("/" if src.is_dir() else ""),
                                f"{rel(g.target)}/{src.name}" + ("/" if src.is_dir() else ""), note))
                plan.ops.append(Op("lib", rel(src), f"{rel(g.target)}/{src.name}", is_dir=src.is_dir()))
    rows = [Row("SKIP", label(i.path) if i.kind != "loose" else ", ".join(f.name for f in i.files[:2]), "",
                i.why or "nothing to do") for i in left if i.why and not i.in_genre and not i.split]
    if rows:
        plan.sections["Left where they are"] = rows
    return plan


def ask_unsure_matches(ui: UI, unsure: list[LibItem], get: Getter) -> bool:
    """After the preview: the pieces matched to a show only by a guess, and which to change."""
    ui.say(f"Not sure about {len(unsure)}:")
    width = min(45, max(len(i.path.name if i.kind != "loose" else i.files[0].name) for i in unsure))
    for n, item in enumerate(unsure, 1):
        name = item.path.name if item.kind != "loose" else item.files[0].name
        ui.say(f"  {n:>2}. {name[:width]:<{width}} → {item.found}")
        ui.say(f"      {'':<{width}}   {_short(item.why or item.match_note, 110)}")
    picked = _parse_numbers(ui.ask("Select which to change (numbers, all, Enter for none): "), len(unsure))
    for n in picked:
        item = unsure[n - 1]
        ui.say()
        ui.say(f"{item.path.name if item.kind != 'loose' else item.files[0].name}  (now: {item.found})")
        answer = ui.ask("0 to leave it where it is, or type the show's name to search TVmaze for: ", "0")
        if answer == "0" or not answer:
            item.leave = True
            continue
        shows = _search_tvmaze(get, answer)
        show = _choose_show(answer, shows, ui)[0] if len(shows) > 1 else (shows or [None])[0]
        if show:
            item.tvmaze_id, item.match_note = str(show["id"]), ""
            item.found = f"{show.get('name')} ({(show.get('premiered') or '')[:4] or 'year unknown'})"
            item.why = "chosen"
        else:
            ui.say("Nothing found; it's left where it is.")
            item.leave = True
    ui.say()
    return bool(picked)


def identify_shows(items: list[LibItem], ui: UI, fetch: Callable[[str], object]) -> Getter:
    """Which show each folder and set of loose episodes is, with the lookups kept in the cache."""
    get = Getter(_Paced(fetch), ui, quiet=True)
    cache = _cache_load()
    todo = [i for i in items if i.kind in ("show", "loose")]
    progress = Progress(ui, "Finding the shows", len(todo))
    try:
        for done, item in enumerate(todo):
            progress.update(done, item.path.name if item.kind != "loose" else item.files[0].name)
            key = f"sort2-{item.kind}:{item.path.name if item.kind != 'loose' else item.files[0].name}"
            if key in cache:
                for name in _CACHED:
                    setattr(item, name, cache[key].get(name, getattr(item, name)))
            else:
                try:
                    (lookup_loose if item.kind == "loose" else lookup_show)(item, get)
                    if item.tvmaze_id:
                        cache[key] = {name: getattr(item, name) for name in _CACHED} | {"time": time.time()}
                except RenamerError as e:
                    item.why = str(e)
            debug(f"lib sort item {item}")
        progress.update(len(todo))
        match_by_titles(items, get)
        find_mixed(items, get)
    finally:
        progress.finish()
        _cache_save(cache)
    return get


def run_lib_sort(args, ui: UI, fetch: Callable[[str], object] = http_get_json) -> int:
    """renamer lib --sort: gather each show's pieces in a library (lone seasons, loose
    episodes, several folders of one show) into one show folder, move movies to a movies library,
    then sort the episodes inside each gathered show into season folders."""
    global config_for_names
    root = _full_path(args.path)
    if not root.is_dir():
        raise RenamerError(f"Not a folder: {root}")
    subdirs = _entries(root, dirs=True)
    if subdirs and all(season_from_folder(d.name) is not None or _SHOW_EXTRAS.fullmatch(d.name) for d in subdirs):
        raise RenamerError(f"{root} is a show folder (it holds season folders). Give the library folder "
                           f"above it, for example: renamer lib --sort {shlex.quote(str(root.parent))}")
    read_only = not os.access(root, os.W_OK)   # still worth a preview
    ui.start_log(log_name_for(root) + "_lib_sort")
    config = config_for_names = load_genre_config(ui)
    items, warnings = scan_for_sort(root, config)
    get = identify_shows(items, ui, fetch)

    movies = [i for i in items if i.kind == "movie" and not i.in_genre]
    layers = []
    for item in items:
        if item.kind == "show" and not item.in_genre and item.path.is_dir():
            layer = seasons_layer(item.path)
            if layer:
                layers.append((item.path, layer))
            movies += [LibItem(p, "movie", why=f"a movie inside {item.path.name}/")
                       for p in movies_in_show(item.path, layer)]
    movies_dir = find_movies_dir(root)

    mixed = [i for i in items if i.split]
    split_targets: list[Path] = []

    def plan_now() -> tuple[Plan, list[SortGroup]]:
        groups, left = group_shows(items, root)
        split_targets.clear()
        p = lib_sort_plan(root, groups, movies, movies_dir, left, tuple(layers), mixed, split_targets)
        p.warnings = list(warnings)
        return p, groups

    plan, groups = plan_now()
    header = [f"Library: {root}", "Mode:    lib --sort (gathers each show's folders, lone seasons and loose "
              "episodes into one show folder; movies go to a movies library)"]
    print_preview(ui, header, plan)
    unsure = [m for g in groups for m in g.members if m.match_note and m.path != g.target]
    if unsure and ui.interactive and ask_unsure_matches(ui, unsure, get):
        plan, groups = plan_now()
        print_preview(ui, ["After your changes:"], plan)
    moves = [op for op in plan.ops if op.kind == "lib"]
    groups = groups + [SortGroup(t.name, "", [], t, True) for t in split_targets]
    if not moves:
        ui.say("Nothing to gather.")
        return 0
    if read_only:
        ui.say(f"No write permission in {root}, so that's only a preview. Nothing was changed.")
        return 1
    if not confirm(ui, _summary(plan.ops)):
        return 0 if ui.interactive else 1
    reference = {g.target: [p.name for p in _episode_videos(g.target)] if g.target.is_dir() else []
                 for g in groups}
    code = apply_ops(plan.ops, root, ui, "Gathering")
    if code:
        return code
    return sort_gathered(root, [g for g in groups if g.target.is_dir()], reference, ui, getattr(args, "clean", False))


def sort_gathered(root: Path, groups: list[SortGroup], reference: dict[Path, list[str]], ui: UI,
                  clean: bool) -> int:
    """The second step of lib --sort: inside each show that got new pieces, the episodes go into
    season folders and worse copies to .duplicates/, as --sort does, in one more preview."""
    combined = Plan()
    for g in groups:
        try:
            p, _ = build_sort_plan(g.target, UI(interactive=False, debug_dir=None), clean,
                                   prefer=reference.get(g.target, []))
        except RenamerError as e:
            combined.warnings.append(f"{g.target.name}/: {e}")
            continue
        base = g.target.relative_to(root).as_posix()
        for section, rows in p.sections.items():
            combined.sections[f"{base}/{section}"] = [
                dataclasses.replace(r, old=f"{base}/{r.old}" if r.old else "", new=f"{base}/{r.new}" if r.new else "")
                for r in rows]
        combined.warnings += [f"{g.target.name}/: {w}" for w in p.warnings]
        combined.ops += [dataclasses.replace(op, src=os.path.normpath(f"{base}/{op.src}") if op.src else "",
                                             dst=os.path.normpath(f"{base}/{op.dst}") if op.dst else "")
                         for op in p.ops]
    if not combined.ops:
        return 0
    ui.say()
    ui.say("Next, the episodes inside the gathered shows go into season folders:")
    print_preview(ui, [f"Library: {root}", "Mode:    lib --sort, step 2 (sorts the episodes inside each "
                       "gathered show; renames nothing)"], combined)
    if not confirm(ui, _summary(combined.ops)):
        ui.say("The shows stay gathered, unsorted inside; renamer --sort on each sorts them later.")
        return 0 if ui.interactive else 1
    code = apply_ops(combined.ops, root, ui, "Sorting")
    if code == 0:
        ui.say(f"To reverse both steps: renamer lib --undo {shlex.quote(str(root))}, twice (the sort, then "
               "the gathering).")
    return code


def group_copies(items: list[LibItem], root: Path) -> tuple[list[SortGroup], list[LibItem]]:
    """Shows with two or more copies, or with a new copy for a folder of copies made earlier.
    Returns those groups, and what couldn't be identified."""
    by_id: dict[str, list[LibItem]] = {}
    existing = {i.tvmaze_id: i for i in items if i.kind == "group" and i.tvmaze_id}
    left = []
    for item in items:
        if item.kind in ("show", "loose") and item.tvmaze_id and not item.leave:
            by_id.setdefault(item.tvmaze_id, []).append(item)
        elif item.kind not in ("movie", "group"):
            left.append(item)
    groups = []
    for show_id, members in by_id.items():
        have = existing.get(show_id)
        if len(members) < (1 if have else 2):
            continue
        name = re.sub(r"\s*\((?:\d{4}|year unknown)\)$", "", have.found if have else members[0].found)
        base = next((m.path.parent for m in members if m.in_genre), root)
        target = have.path if have else base / (clean_text(name) or "Show")
        groups.append(SortGroup(name, show_id, members, target, not have))
    return groups, left


def lib_group_plan(root: Path, groups: list[SortGroup], left: list[LibItem]) -> Plan:
    plan = Plan()

    def rel(p: Path) -> str:
        return p.relative_to(root).as_posix()

    def label(p: Path) -> str:
        return p.name + ("/" if p.is_dir() else "")

    for g in sorted(groups, key=lambda g: natural_key(g.show)):
        rows = plan.sections.setdefault(f"{rel(g.target)}/  ({g.show}" + (", a new folder)" if g.new else ")"), [])
        busy = [m for m in g.members if (find_downloads(m.path) if m.kind != "loose"
                                         else [f for f in m.files if f.name.lower().endswith(DOWNLOAD_EXTS)])]
        if busy or (not g.new and find_downloads(g.target)):
            rows.append(Row("CONFLICT", label(g.target) if g.target.exists() else g.target.name + "/", "",
                            "still downloading (.!qb) in " + (", ".join(label(m.path) for m in busy) or label(g.target))
                            + "; the whole show is left alone"))
            continue
        # A copy already called what the new folder will be: Example Show/ stays Example-Show/Example Show/.
        holder = next((m for m in g.members if m.kind != "loose" and g.new
                       and m.path.parent == g.target.parent and m.path.name.casefold() == g.target.name.casefold()), None)
        if g.new and g.target.exists() and not holder:
            rows.append(Row("CONFLICT", g.target.name + "/", "", f"{rel(g.target)} already exists"))
            continue
        moving = {}
        if holder:
            aside = holder.path.with_name(f"{GROUP_MARKER}-moving-{holder.path.name}")
            plan.ops.append(Op("group", rel(holder.path), rel(aside), is_dir=True))
            moving[holder.path] = aside
        if g.new:
            plan.ops.append(Op("mkdir", dst=rel(g.target)))
            marker = json.dumps({"show": g.show, "tvmaze_id": g.tvmaze_id}) + "\n"
            plan.ops.append(Op("create", dst=f"{rel(g.target)}/{GROUP_MARKER}", content=marker.encode()))
        taken = {n.casefold() for n in os.listdir(g.target)} if not g.new else set()
        loose_dir = g.target / LOOSE_EPISODES
        taken_loose = {n.casefold() for n in os.listdir(loose_dir)} if loose_dir.is_dir() else set()
        made_loose = loose_dir.is_dir()
        for m in sorted(g.members, key=lambda m: natural_key(m.path.name)):
            if m.kind == "loose":
                for src in m.files:
                    if src.name.casefold() in taken_loose:
                        rows.append(Row("CONFLICT", src.name, "", f"{rel(loose_dir)}/{src.name} already exists"))
                        continue
                    if not made_loose:
                        plan.ops.append(Op("mkdir", dst=rel(loose_dir)))
                        made_loose = True
                    taken_loose.add(src.name.casefold())
                    plan.ops.append(Op("group", rel(src), f"{rel(loose_dir)}/{src.name}"))
                    rows.append(Row("MOVE" if not m.match_note else "GUESS", rel(src), f"{rel(loose_dir)}/{src.name}",
                                    m.why if m.match_note else "loose in the library"))
                continue
            if m.path.name.casefold() in taken:
                rows.append(Row("CONFLICT", label(m.path), "", f"{rel(g.target)}/{m.path.name} already exists"))
                continue
            taken.add(m.path.name.casefold())
            plan.ops.append(Op("group", rel(moving.get(m.path, m.path)), f"{rel(g.target)}/{m.path.name}", is_dir=True))
            rows.append(Row("MOVE" if not m.match_note else "GUESS", rel(m.path) + "/",
                            f"{rel(g.target)}/{m.path.name}/", m.why if m.match_note else ""))
    rows = [Row("SKIP", label(i.path) if i.kind != "loose" else ", ".join(f.name for f in i.files[:2]), "",
                i.why or "nothing to do") for i in left if i.why and not i.in_genre]
    if rows:
        plan.sections["Left where they are"] = rows
    if any(op.kind == "group" for op in plan.ops):
        plan.warnings.append("A torrent still seeding from one of these folders loses track of its files unless you "
                             "move it in qBittorrent instead.")
    return plan


def run_lib_group(args, ui: UI, fetch: Callable[[str], object] = http_get_json) -> int:
    """renamer lib --group: each show with several copies gets one folder holding them, every
    release whole and under its own name; loose episodes go in a loose-episodes folder inside it."""
    global config_for_names
    root = _full_path(args.path)
    if not root.is_dir():
        raise RenamerError(f"Not a folder: {root}")
    refuse_group(root)
    subdirs = _entries(root, dirs=True)
    if subdirs and all(season_from_folder(d.name) is not None or _SHOW_EXTRAS.fullmatch(d.name) for d in subdirs):
        raise RenamerError(f"{root} is a show folder (it holds season folders). Give the library folder "
                           f"above it, for example: renamer lib --group {shlex.quote(str(root.parent))}")
    read_only = not os.access(root, os.W_OK)   # still worth a preview
    ui.start_log(log_name_for(root) + "_lib_group")
    config = config_for_names = load_genre_config(ui)
    items, warnings = scan_for_sort(root, config)
    get = identify_shows(items, ui, fetch)

    def plan_now() -> tuple[Plan, list[SortGroup]]:
        groups, left = group_copies(items, root)
        p = lib_group_plan(root, groups, left)
        p.warnings = list(warnings) + p.warnings
        return p, groups

    plan, groups = plan_now()
    header = [f"Library: {root}", "Mode:    lib --group (each show with several copies gets one folder holding them; "
              "every release stays whole, under its own name)"]
    print_preview(ui, header, plan)
    unsure = [m for g in groups for m in g.members if m.match_note]
    if unsure and ui.interactive and ask_unsure_matches(ui, unsure, get):
        plan, groups = plan_now()
        print_preview(ui, ["After your changes:"], plan)
    if not any(op.kind == "group" for op in plan.ops):
        ui.say("Nothing to group.")
        return 0
    if read_only:
        ui.say(f"No write permission in {root}, so that's only a preview. Nothing was changed.")
        return 1
    if not confirm(ui, _summary(plan.ops)):
        return 0 if ui.interactive else 1
    code = apply_ops(plan.ops, root, ui, "Grouping")
    if code == 0:
        ui.say(f"To reverse it: renamer lib --undo {shlex.quote(str(root))}")
    return code


LIB_SUMMARY = """renamer {version} lib: work on a whole library folder (TV/, TV (Animated)/, Movies/ …).

  renamer lib --sort PATH     gather each show's folders, lone seasons and loose episodes into one
  renamer lib --group PATH    put a show's copies in one folder, each release left whole
  renamer lib --genre PATH    move each show or movie into a genre folder (Comedy/, Sci-Fi/ …)
  renamer lib --undo PATH     reverse the last step

  --sort, -s        gather each show into one folder, sort its seasons, move movies out
  --clean, -c       with --sort: junk to .junk/, emptied folders removed
  --group, -G       a folder per show with several copies; nothing inside a release changes
  --genre, -g       sort into genre folders
  --verbose, -v     explain every decision and save a log
  --undo, --reset   reverse the last lib run
  --no-pager        print a long preview straight to the terminal

The genre folder names are in {config}.
The full help: renamer lib --help, or man renamer"""


class _HelpParser(argparse.ArgumentParser):
    """argparse with renamer's own --help: one section per kind of work."""

    def __init__(self, *args, sections: tuple[str, ...], **kwargs):
        super().__init__(*args, **kwargs)
        self.sections = sections

    def format_help(self) -> str:
        return help_text(self.sections)

    def error(self, message: str):
        debug(f"option error: {message}")
        if _debug_ui is not None:
            _debug_ui.early_name = "option-error"
        super().error(message)

    def print_help(self, file=None) -> None:
        debug("help shown")
        if _debug_ui is not None:
            _debug_ui.early_name = "help"
        text = self.format_help()
        if file is None and sys.stdout.isatty() and sys.stdin.isatty():
            ui = UI(interactive=True, debug_dir=None)
            with ui.paged("renamer help, q to quit"):
                for line in text.rstrip("\n").split("\n"):
                    ui.say(line)
        else:
            (file or sys.stdout).write(text)


def build_parser() -> argparse.ArgumentParser:
    p = _HelpParser(prog="renamer", sections=("rename", "meta", "sort", "clean", "names", "undo", "lib"))
    p.add_argument("path", metavar="PATH", nargs="?", default=".",
                   help="show folder (all seasons) or one season folder; without it, the current folder")
    p.add_argument("-s", "--show", metavar="NAME",
                   help="use this show name and skip the show-name question")
    p.add_argument("-n", "--names", metavar="FILE", type=Path,
                   help="take the titles from a nameInfo file instead of TVmaze; the run is then offline")
    p.add_argument("-g", "--make-names", metavar="FILE",
                   help="write TVmaze's titles to a nameInfo file, to edit and use with --names; renames nothing")
    p.add_argument("-f", "--fix-folders", action="store_true",
                   help="also rename the show folder and the season folders (Show-Name_Season_01)")
    p.add_argument("-y", "--years", action="store_true",
                   help="put the show's years in the show folder name; needs --fix-folders")
    p.add_argument("-m", "--nfo", action="store_true", help="also write Kodi .nfo files into .nfo/")
    p.add_argument("-t", "--meta", action="store_true",
                   help="rename as usual, and also check and fix the tags inside the videos (see META); "
                        "for tags only, use renamer meta")
    p.add_argument("-o", "--sort", action="store_true",
                   help="sort mode: move the videos into Season_NN folders; renames nothing (see SORT)")
    p.add_argument("-c", "--clean", action="store_true",
                   help="also move junk (samples, .txt, .url, screenshots) to .junk/; DELETE at the question "
                        "deletes it instead. On its own: clean only (see CLEAN ONLY)")
    p.add_argument("--renumber", action="store_true",
                   help="give a file TVmaze's episode number when its title belongs to a different number")
    p.add_argument("-a", dest="usual", action="store_true",
                   help="the usual full run without tags: --verbose --clean --years --fix-folders --nfo")
    p.add_argument("--all", action="store_true",
                   help="the usual full run with tags: everything -a does, plus --meta")
    p.add_argument("-v", "--verbose", action="store_true",
                   help="explain every decision and save the output to ~/.logs/")
    p.add_argument("-u", "--undo", action="store_true",
                   help="reverse the most recent run; old .nfo files stay in .nfo/.nfo-old")
    p.add_argument("-r", "--reset", action="store_true",
                   help="reverse the most recent run completely, old .nfo files included")
    p.add_argument("--no-pager", action="store_true",
                   help="print a long preview straight to the terminal instead of opening it in less")
    return p


def build_meta_parser() -> argparse.ArgumentParser:
    p = _HelpParser(prog="renamer meta", sections=("meta",))
    p.add_argument("path", metavar="PATH", nargs="?", default=".",
                   help="a video file, a season folder or a show folder; without it, the current folder")
    p.add_argument("-s", "--show", metavar="NAME",
                   help="use this show name and skip the show-name question")
    p.add_argument("-n", "--names", metavar="FILE", type=Path,
                   help="take the titles from a nameInfo file instead of TVmaze (offline); only the title, "
                        "show, season and episode tags are then set")
    p.add_argument("-v", "--verbose", action="store_true",
                   help="show every tag's old and new value and save the output to ~/.logs/")
    p.add_argument("-u", "--undo", action="store_true",
                   help="reverse the most recent run (the same as renamer --undo)")
    p.add_argument("-r", "--reset", action="store_true",
                   help="reverse the most recent run completely (the same as renamer --reset)")
    p.add_argument("--view", action="store_true",
                   help="list the tags already in the videos; changes nothing and needs no internet")
    p.add_argument("--compare", action="store_true",
                   help="list each tag beside what TVmaze has: same, different or missing; changes nothing "
                        "(implies --view)")
    p.add_argument("--no-pager", action="store_true",
                   help="print a long preview straight to the terminal instead of opening it in less")
    return p


def build_lib_parser() -> argparse.ArgumentParser:
    p = _HelpParser(prog="renamer lib", sections=("lib",))
    p.add_argument("path", metavar="PATH", nargs="?", default=".",
                   help="a library folder (TV/, TV (Animated)/, Movies/ …); without it, the current folder")
    p.add_argument("-g", "--genre", action="store_true",
                   help="move each show or movie into a genre folder (Comedy/, Sci-Fi/ …); nothing inside it changes")
    p.add_argument("-s", "--sort", action="store_true",
                   help="gather each show's lone seasons, loose episodes and extra folders into one show folder, "
                        "sort its episodes into season folders, and move movies to a movies library")
    p.add_argument("-G", "--group", action="store_true",
                   help="give each show with several copies one folder holding them; every release stays whole, "
                        "under its own name, and loose episodes go in a loose-episodes folder inside it")
    p.add_argument("-c", "--clean", action="store_true",
                   help="with --sort: also move junk to .junk/ and remove the folders left empty")
    p.add_argument("-v", "--verbose", action="store_true",
                   help="explain every decision and save the output to ~/.logs/")
    p.add_argument("-u", "--undo", action="store_true", help="reverse the most recent lib run")
    p.add_argument("-r", "--reset", action="store_true", help="reverse the most recent lib run completely")
    p.add_argument("--no-pager", action="store_true",
                   help="print a long preview straight to the terminal instead of opening it in less")
    return p


# The --help sections: (title, how to call it, what it does, what it changes on disk,
# [(parser, dest, text instead of the option's own help)], [(example, what it does)]).
HELP_SECTIONS = {
    "rename": ("RENAMING", ["renamer [options] [PATH]"],
               "Renames each video, and the subtitles that go with it, to Show-Name_S01E04_Episode-Title.mkv. "
               "The titles come from TVmaze. PATH is a show folder (every season in it) or one season folder; "
               "\".\" is the current folder, and so is no PATH when other options are given. Videos in release "
               "folders, or loose, are offered to SORT first.",
               "file names. Folders, .nfo files, junk and the tags inside the videos only with the options "
               "below. Nothing is ever deleted unless you answer DELETE.",
               [("main", "show", None), ("main", "names", None), ("main", "fix_folders", None),
                ("main", "years", None), ("main", "nfo", None), ("main", "meta", None),
                ("main", "clean", "also move junk (samples, .txt, .url, screenshots) to .junk/; DELETE at the "
                                  "question deletes it instead"),
                ("main", "renumber", None), ("main", "usual", None), ("main", "all", None),
                ("main", "verbose", None), ("main", "no_pager", None)],
               [("renamer .", "rename the show in the current folder"),
                ('renamer --fix-folders --years "/mnt/media/TV/Example Show"', "names and folders, with the years"),
                ("renamer --all", "the full run: names, folders, .nfo, junk and tags")]),
    "meta": ("META (tags only)", ["renamer meta [options] [PATH]"],
             "Checks the tags inside the videos (title, show, season, episode, air date, plot, genre, network, "
             "rating, IDs, audio and subtitle languages) against TVmaze and fixes them. PATH can also be one "
             "video file. MKV is changed in place; MP4 and AVI are rewritten by ffmpeg and checked before they "
             "replace the original.",
             "only the tags inside the videos. Never renames or moves anything. --view and --compare change "
             "nothing at all.",
             [("meta", "view", None), ("meta", "compare", None), ("meta", "show", None), ("meta", "names", None),
              ("meta", "verbose", None), ("meta", "undo", None), ("meta", "reset", None),
              ("meta", "no_pager", None)],
             [("renamer meta .", "fix the tags of the show in the current folder"),
              ("renamer meta --view Season_02", "look at the tags without changing them"),
              ("renamer meta --compare", "see which tags differ from TVmaze")]),
    "lib": ("LIBRARY", ["renamer lib --sort [PATH]", "renamer lib --group [PATH]", "renamer lib --genre [PATH]",
                        "renamer lib --undo [PATH]"],
            "Works on a whole library folder (TV/, TV (Animated)/, Movies/). --sort gathers each show's pieces "
            "into one show folder: several folders of one show, lone seasons, loose episodes, and season folders "
            "with no show name (matched by their episode titles); then sorts its episodes into season folders "
            "(the show's own release wins over a better copy from another), and moves movies to a Movies "
            "folder in ../, ../../ or ../../../ (Movies(Animated) for an animated library), else .movies/, "
            "including movies beside a show's seasons; a Series/ or Seasons/ folder around the seasons is removed. "
            "--group keeps copies apart instead: each show with two or more copies gets a folder (Example-Show/) "
            "holding every release whole, with loose episodes in loose-episodes/ inside it; a show with one copy "
            "stays where it is, spin-offs are separate shows, and later runs add new copies to that folder. "
            "--genre moves each show or movie at "
            "its top into a genre folder: Comedy/Example Show/, Sci-Fi/Another Show/. Shows get their genres from "
            "TVmaze, movies from Wikidata, and Wikipedia decides which is the main one. The ones renamer isn't "
            "sure about are listed after the preview, to change. The folder names are in "
            "~/.config/renamer/genres.conf; existing genre folders are found and used.",
            "--sort: where folders and files are (two steps, each with its own preview and question); renames "
            "nothing. --group: only where whole releases and loose episodes are. --genre: only where the show and movie folders are. Shows still downloading are left alone.",
            [("lib", "sort", None), ("lib", "clean", None), ("lib", "group", None), ("lib", "genre", None),
             ("lib", "verbose", None),
             ("lib", "undo", None), ("lib", "reset", None), ("lib", "no_pager", None)],
            [("renamer lib --sort /mnt/media/TV", "gather each show into one folder"),
             ("renamer lib --group /mnt/media/TV", "or keep the copies of each show apart, in one folder"),
             ("renamer lib --genre /mnt/media/TV", "then sort the shows into genre folders"),
             ("renamer lib --undo /mnt/media/TV", "reverse the last step")]),
    "sort": ("SORT", ["renamer --sort [--clean] [--verbose] [PATH]"],
             "Gathers a show's videos from loose files, release folders and wrongly named folders into "
             "Season_NN folders, with their subtitles. Worse copies of an episode go to .duplicates/, videos of "
             "other shows to ../unsorted/. Run renamer again afterwards to rename them.",
             "where the files are. Renames nothing.",
             [("main", "sort", "sort mode; can only be combined with --clean and --verbose"),
              ("main", "clean", "also move junk to .junk/ and remove the folders left empty"),
              ("main", "verbose", None)],
             [("renamer --sort --clean", "sort and tidy the show in the current folder")]),
    "clean": ("CLEAN ONLY", ["renamer --clean [PATH]"],
              "Only cleans: junk, samples and screenshots go to .junk/, and folders left empty are removed. "
              "Always with the full --verbose output and log.",
              "moves junk to .junk/ (DELETE at the question deletes it) and removes empty folders. "
              "Renames nothing.",
              [("main", "clean", "on its own, with no renaming options: clean only")],
              [("renamer --clean", "tidy the show in the current folder")]),
    "names": ("NAMES FILE", ["renamer --make-names FILE [PATH]", "renamer --names FILE [PATH]"],
              "For shows TVmaze gets wrong, or to work offline. --make-names writes TVmaze's titles to a "
              "nameInfo file you can edit; --names then renames from that file without going online.",
              "--make-names writes only FILE. --names renames like a normal run.",
              [("main", "make_names", None), ("main", "names", None), ("main", "show", None)],
              [("renamer --make-names names.txt", "write a starting file from TVmaze"),
               ("renamer --names names.txt", "rename from the edited file, offline")]),
    "undo": ("UNDO / RESET", ["renamer --undo [PATH]", "renamer --reset [PATH]"],
             "Reverses the most recent run in the show folder, from its undo log (.rename_undo.json): names, "
             "folders, .nfo files and tags.",
             "puts back what that run changed. --undo leaves old .nfo files archived in .nfo/.nfo-old; --reset "
             "puts those back too.",
             [("main", "undo", None), ("main", "reset", None), ("main", "verbose", None)],
             [("renamer --undo", "reverse the last run in the current folder")]),
}


def _option_label(action: argparse.Action) -> str:
    longs = [o for o in action.option_strings if o.startswith("--")]
    shorts = [o for o in action.option_strings if not o.startswith("--")]
    first = (longs or shorts)[0] + (f" {action.metavar}" if action.metavar else "")
    return ", ".join([first] + (shorts if longs else []))


def help_text(sections: tuple[str, ...]) -> str:
    """renamer's --help: a few lines on what renamer is, then one section per kind of work."""
    width = max(60, min(100, shutil.get_terminal_size((100, 24)).columns)) - 2
    parsers = {"main": build_parser(), "meta": build_meta_parser(), "lib": build_lib_parser()}
    actions = {name: {a.dest: a for a in p._actions} for name, p in parsers.items()}
    out = [f"renamer {VERSION}: rename TV episode files and fix the tags inside them.",
           "Every run shows a preview first and changes nothing until you answer y.",
           "renamer --undo reverses the last run. renamer on its own prints a short summary.",
           "The full manual: man renamer", ""]

    def para(text: str, indent: str = "  ") -> None:
        out.extend(textwrap.wrap(text, width, initial_indent=indent, subsequent_indent=indent,
                                 break_on_hyphens=False))

    for key in sections:
        title, calls, about, changes, options, examples = HELP_SECTIONS[key]
        out.append(f"{title:<28}{calls[0]}")
        out.extend(f"{'':28}{call}" for call in calls[1:])
        para(about)
        para("Changes: " + changes)
        for parser, dest, text in options:
            action = actions[parser][dest]
            label = _option_label(action)
            lines = textwrap.wrap(text or action.help, width - 28, break_on_hyphens=False)
            if len(label) > 24:
                out.append(f"    {label}")
                out.extend(f"{'':28}{line}" for line in lines)
            else:
                out.append(f"    {label:<24}{lines[0]}")
                out.extend(f"{'':28}{line}" for line in lines[1:])
        out.append("  Examples:")
        for example, what in examples:
            if len(example) > 34:
                out.append(f"    {example}")
                out.append(f"{'':40}{what}")
            else:
                out.append(f"    {example:<36}{what}")
        out.append("")
    if len(sections) > 1:
        out.append("    --help, -h              this help; renamer meta --help and renamer lib --help show "
                   "only their section")
    para("Logs: --verbose saves the output to ~/.logs/.", indent="")
    para("This product uses the TMDB API but is not endorsed or certified by TMDB.", indent="")
    return "\n".join(out) + "\n"


SUMMARY = """renamer {version}: rename TV episode files, fix the tags inside them, tidy whole libraries.
Every run shows a preview first and changes nothing until you answer y.

RENAMING   renamer [options] PATH     (PATH: a show folder or one season folder)
  Renames a show's videos and subtitles to Show-Name_S01E04_Episode-Title.mkv, titles from TVmaze.
  --show NAME        use this show name          --meta        also fix the tags (see META)
  --names FILE       titles from a file          --clean       move junk to .junk/
  --make-names FILE  write a titles file         --sort        sort into season folders
  --fix-folders      rename the folders too      --renumber    use TVmaze's numbers
  --years            years in the show folder    -a / --all    the usual full run (--all: with tags)
  --nfo              write Kodi .nfo files       --undo/--reset  reverse the last run

META       renamer meta [options] PATH     (PATH: a show or season folder, or one video)
  Checks the tags inside the videos (title, show, episode, plot, languages...) against TVmaze and
  fixes them. Renames nothing.
  --view             look at the tags            --compare     compare them with TVmaze
                     (neither changes anything)  --undo/--reset  reverse the last run

LIBRARY    renamer lib --sort | --group | --genre PATH     (PATH: a folder of shows or movies, like TV/)
  Works on a whole library: moves folders and files, renames no episodes.
  --sort             gather each show's folders, lone seasons and loose episodes into one show
                     folder, sort its seasons, and move movies out to a movies folder
  --group            put a show's copies in one folder, each release left whole
  --genre            move each show or movie into a genre folder (Comedy/, Sci-Fi/...)
  --clean            with --sort: move junk to .junk/    --undo/--reset  reverse the last step

Everywhere: --verbose explains every decision and saves a log; --no-pager skips less for previews.
To work on the current folder, give it as "." (renamer . or renamer meta .).
The full help: renamer --help, or man renamer"""


def _run_mode(ui: UI, fallback: str, work: Callable[[], int]) -> int:
    code = None
    try:
        code = work()
        return code
    except RenamerError as e:
        ui.debug(traceback.format_exc())
        ui.error(f"renamer: {e}")
        code = 1
        return 1
    except KeyboardInterrupt:
        ui.debug("Ctrl-C:\n" + traceback.format_exc())
        code = 130
        if ui.changing:
            ui.error("\nInterrupted. The changes made so far are in the undo log; --undo reverses them.")
        else:
            ui.error("\nStopped. Nothing was changed.")
        return 130
    except BaseException:
        ui.debug("CRASH:\n" + traceback.format_exc())
        raise
    finally:
        ui.debug(f"exit code {code}")
        ui.close_log(fallback)


def main_lib(argv: list[str], ui: UI) -> int:
    """renamer lib ...."""
    parser = build_lib_parser()
    args = parser.parse_args(argv)
    if args.undo and args.reset:
        parser.error("use either --undo or --reset, not both")
    if (args.undo or args.reset) and (args.genre or args.sort or args.group):
        parser.error("--undo and --reset can only be combined with --verbose")
    if args.genre and args.sort:
        parser.error("run --sort first, then --genre: one job at a time")
    if args.group and (args.sort or args.genre):
        parser.error("--group is a job of its own: --sort merges what --group keeps apart, and --genre comes after")
    if args.clean and not args.sort:
        parser.error("--clean goes with --sort")
    if not (args.genre or args.sort or args.group or args.undo or args.reset):
        parser.error("say what to do: --sort (gather each show into one folder), --group (keep each show's copies "
                     "together), --genre (genre folders), or --undo")
    ui.verbose, ui.pager = args.verbose, not args.no_pager
    path = _full_path(args.path)
    if path.is_dir():
        ui.debug(f"tree: {path} is a library; its top level only: "
                 + ", ".join(sorted(os.listdir(path), key=natural_key)[:500]))
    suffix = ("_lib_undo" if args.undo else "_lib_reset" if args.reset else "_lib_sort" if args.sort
              else "_lib_group" if args.group else "_lib")
    if args.undo or args.reset:
        return _run_mode(ui, log_name_for(path) + suffix, lambda: run_undo(path, ui, reset=args.reset))
    if args.sort:
        return _run_mode(ui, log_name_for(path) + suffix, lambda: run_lib_sort(args, ui))
    if args.group:
        return _run_mode(ui, log_name_for(path) + suffix, lambda: run_lib_group(args, ui))
    return _run_mode(ui, log_name_for(path) + suffix, lambda: run_lib_genre(args, ui))


def main_meta(argv: list[str], ui: UI) -> int:
    """renamer meta ...."""
    parser = build_meta_parser()
    args = parser.parse_args(argv)
    if args.undo and args.reset:
        parser.error("use either --undo or --reset, not both")
    if (args.undo or args.reset) and (args.show or args.names or args.view or args.compare):
        parser.error("--undo and --reset can only be combined with --verbose")
    if args.view and not args.compare and (args.show or args.names):
        parser.error("--show and --names say how to look the show up; use them with --compare")
    ui.verbose, ui.pager = args.verbose, not args.no_pager
    debug_tree(ui, _full_path(args.path))
    path = _full_path(args.path)
    folder = path.parent if path.is_file() else path
    suffix = ("_undo" if args.undo else "_reset" if args.reset else "_compare" if args.compare
              else "_view" if args.view else "_meta")
    if args.undo or args.reset:
        return _run_mode(ui, log_name_for(folder) + suffix, lambda: run_undo(folder, ui, reset=args.reset))
    return _run_mode(ui, log_name_for(folder) + suffix, lambda: run_meta(args, ui))


def main(argv: list[str] | None = None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    # The debug log starts before anything else, so every invocation leaves one.
    ui = UI(interactive=sys.stdin.isatty() and sys.stdout.isatty())
    debug_run_start(ui, argv)
    try:
        if argv == ["lib"]:
            ui.say(LIB_SUMMARY.format(version=VERSION, config=GENRE_CONFIG))
            ui.debug("exit code 0")
            ui.close_log("summary")
            return 0
        if argv and argv[0] == "lib":
            return main_lib(argv[1:], ui)
        if argv in ([], ["meta"]):
            # Nothing to work on: say what renamer does instead of running on the current folder.
            ui.say(SUMMARY.format(version=VERSION))
            ui.debug("exit code 0")
            ui.close_log("summary")
            return 0
        if argv[0] == "meta":   # a folder called "meta" is reached as ./meta
            return main_meta(argv[1:], ui)
        return _main_rename(argv, ui)
    except SystemExit as e:
        ui.debug(f"exit code {e.code} (from the option parser)")
        ui.close_log(ui.early_name or "run")
        raise


def _main_rename(argv: list[str], ui: UI) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    clean_only = is_clean_only(args)
    if clean_only:
        args.verbose = True   # a run that moves files for you always keeps the full record
    if args.all or args.usual:
        used = "--all" if args.all else "-a"
        if args.sort or args.undo or args.reset or args.make_names:
            parser.error(f"{used} is for renaming runs; it can't be combined with --sort, --undo, --reset or "
                         "--make-names")
        args.verbose = args.clean = args.years = args.fix_folders = args.nfo = True
        if args.all:
            args.meta = True   # -a leaves the tags alone, as it did before 0.7.0
    renaming = (args.show, args.names, args.fix_folders, args.years, args.nfo, args.clean, args.renumber, args.meta)
    if args.undo and args.reset:
        parser.error("use either --undo or --reset, not both")
    if (args.undo or args.reset) and (any(renaming) or args.make_names):
        parser.error("--undo and --reset can only be combined with --verbose")
    if args.make_names and any((args.names, args.fix_folders, args.years, args.nfo, args.clean, args.renumber,
                                args.meta)):
        parser.error("--make-names only writes a file; it can be combined with --show and --verbose")
    if args.years and not args.fix_folders:
        parser.error("--years only changes folder names, so it needs --fix-folders")
    if args.renumber and args.names:
        parser.error("--renumber compares against TVmaze, so it can't be used with --names")
    if args.sort and (any((args.show, args.names, args.make_names, args.fix_folders, args.years, args.nfo,
                           args.renumber, args.meta)) or args.undo or args.reset):
        parser.error("--sort is its own mode; it can only be combined with --clean and --verbose")
    ui.verbose, ui.pager = args.verbose, not args.no_pager
    debug_tree(ui, _full_path(args.path))
    suffix = ("_undo" if args.undo else "_reset" if args.reset else "_names" if args.make_names
              else "_sort" if args.sort else "_clean" if clean_only else "")
    fallback = log_name_for(_full_path(args.path)) + suffix

    def work() -> int:
        if args.undo or args.reset:
            return run_undo(args.path, ui, reset=args.reset)
        if args.make_names:
            return run_make_names(args, ui)
        if args.sort:
            return run_sort(args, ui)
        if clean_only:
            return run_clean(args, ui)
        return run_rename(args, ui)
    return _run_mode(ui, fallback, work)


if __name__ == "__main__":
    sys.exit(main())
