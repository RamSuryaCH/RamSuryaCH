#!/usr/bin/env python3
"""Generate the animated car-on-contribution-graph SVGs for the GitHub profile README.

Usage:
  python3 scripts/generate_car_animation.py --user RamSuryaCH --outdir dist

Writes two files into --outdir:
  car-animation-dark.svg
  car-animation-light.svg

A top-down sports car drives once, left to right, across the user's real public
contribution calendar (the last 53 weeks, Sunday on top), coloured with GitHub's own
contribution-level palette. Data comes from the GraphQL contributionCalendar API when a
token is available (GITHUB_TOKEN, GH_TOKEN, or `gh auth token`), otherwise from the public
contributions page. Empty days stay at level 0. The car may briefly brighten each cell as
it passes; once it has gone, every cell shows its true level, so the settled frame is the
real graph. The car throws one large, soft white tire-smoke cloud from its rear and sides,
plus a faint wide haze that trails behind it.

Standard library only. Output is deterministic for the same input data.
"""

import argparse
import datetime as dt
import html
import json
import math
import os
import random
import re
import subprocess
import sys
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path

USER_AGENT = "car-animation-generator (+https://github.com/RamSuryaCH/RamSuryaCH)"
GRAPHQL_URL = "https://api.github.com/graphql"
CONTRIBUTIONS_URL = "https://github.com/users/{user}/contributions"

# Grid geometry. Tight GitHub-like gaps. Extra vertical padding keeps smoke inside the canvas.
CELL = 10
GAP = 3
PITCH = CELL + GAP
ROWS = 7
PAD_X = 24
PAD_Y = 100
CELL_RX = 2.5

# Animation timing. Everything loops over LOOP_SECONDS.
LOOP_SECONDS = 12
PASS_START = 0.04   # loop fraction when the car starts moving on screen
PASS_END = 0.80     # loop fraction when the car has left the right edge
FILL_LEN = 0.025    # loop fraction over which one cell lights up (about 0.3 s)
ROW_STAGGER = 0.0012  # tiny per-row delay so the wave looks organic, not a hard column
TRAIL_HOLD = 0.90   # the finished trail stays lit until this fraction, then fades
TRAIL_FADE_END = 0.985
DRIFT_DEG = -24.0   # negative = nose up-right during the middle of the drift

# Car center travels from fully off the left edge to fully off the right edge.
CAR_X_MARGIN = 70
CAR_HALF_LEN = 40   # car spans local x in [-40, 40]

# Body extent along the car's x axis (nose to tail). Axles are placed by fraction of this
# length, measured from the nose: front at 22 percent, rear at 78 percent.
NOSE_X = 40.0
TAIL_X = -38.0
BODY_LEN = NOSE_X - TAIL_X
FRONT_AXLE_X = NOSE_X - 0.22 * BODY_LEN
REAR_AXLE_X = NOSE_X - 0.78 * BODY_LEN

# Tyres seen from above: dark rounded rectangles, longer along x (rolling direction) than y.
# Per axle: (axle x, half track |y|, tread length, tread width, steer degrees). Each axle
# yields a left and a right tyre at exactly +-|y|. The body is drawn over the tyres, so the
# fenders cover most of each one and only a thin sliver shows past the body edge.
FRONT_STEER_DEG = -10.0   # small negative steer into the drift; rear tyres stay parallel
AXLES = (
    (FRONT_AXLE_X, 13.4, 13.0, 6.0, FRONT_STEER_DEG),
    (REAR_AXLE_X, 14.8, 15.0, 7.4, 0.0),
)
WHEELS = tuple(
    (x, side * track, length, width, steer)
    for x, track, length, width, steer in AXLES
    for side in (-1, 1)
)

# Tire smoke has three parts, all anchored on the rear axle:
#  1. a big soft core cloud attached to the car, covering the rear and both flanks;
#  2. shed puffs that swell and fade where the car has just been, merged by blur;
#  3. a faint, wide haze that trails further back over the coloured cells.
CORE_FADE_IN_X = (-60, -15)     # car centre x over which the core cloud fades in
CORE_FADE_OUT_X = (-10, 55)     # offsets from the canvas width over which it fades out
PUFF_COUNT = 44
PUFF_LIFE = 0.10                # loop fraction (1.2 s)
PUFF_R0, PUFF_R1 = 16, 40
PUFF_SEED = 12
HAZE_COUNT = 18
HAZE_LIFE = 0.19
HAZE_R0, HAZE_R1 = 38, 62
HAZE_SEED = 7

# Official GitHub contribution-level colours, index 0..4.
LEVEL_DARK = ("#161b22", "#0e4429", "#006d32", "#26a641", "#39d353")
LEVEL_LIGHT = ("#ebedf0", "#9be9a8", "#40c463", "#30a14e", "#216e39")
# Brief pass glow: a lighter overlay on each real cell, then it returns to its true level.
GLOW_PEAK_EMPTY = 0.28
GLOW_PEAK_LIT = 0.62
GLOW_RISE = 0.012    # loop fraction to reach the glow peak (~0.14 s)
GLOW_FALL = 0.040    # loop fraction back to the true colour (~0.48 s)

THEMES = {
    "dark": {
        "bg": "url(#bgDark)",
        "levels": LEVEL_DARK,
        "smoke": "#ffffff",
        "smoke_peak": 0.8,
        "haze_peak": 0.17,
        "shadow": 0.6,
    },
    "light": {
        "bg": "#f6f7fb",
        "levels": LEVEL_LIGHT,
        "smoke": "#b0b8d0",       # a little darker and bluer than white, so it shows on a light page
        "smoke_peak": 0.85,
        "haze_peak": 0.22,
        "shadow": 0.42,
    },
}

LEVEL_FROM_GRAPHQL = {
    "NONE": 0,
    "FIRST_QUARTILE": 1,
    "SECOND_QUARTILE": 2,
    "THIRD_QUARTILE": 3,
    "FOURTH_QUARTILE": 4,
}

GRAPHQL_QUERY = """
query($login: String!) {
  user(login: $login) {
    contributionsCollection {
      contributionCalendar {
        weeks { contributionDays { date contributionCount contributionLevel } }
      }
    }
  }
}
"""


class Day:
    __slots__ = ("date", "count", "level")

    def __init__(self, date, count, level):
        self.date = date
        self.count = count  # None when only the level is known
        self.level = level  # 0..4

    def is_lit(self):
        if self.count is not None:
            return self.count > 0
        return self.level > 0


# ---------------------------------------------------------------- data fetching

def fetch_graphql(user, token):
    # Default contributionsCollection is the same 53-week window GitHub shows on the profile.
    variables = {"login": user}
    body = json.dumps({"query": GRAPHQL_QUERY, "variables": variables}).encode("utf-8")
    req = urllib.request.Request(
        GRAPHQL_URL,
        data=body,
        headers={
            "Authorization": f"bearer {token}",
            "Content-Type": "application/json",
            "User-Agent": USER_AGENT,
        },
    )
    with urllib.request.urlopen(req, timeout=30) as resp:
        payload = json.load(resp)
    if payload.get("errors"):
        raise RuntimeError(f"GraphQL errors: {payload['errors'][0].get('message')}")
    user_node = (payload.get("data") or {}).get("user")
    if not user_node:
        raise RuntimeError(f"GraphQL returned no user {user!r}")
    calendar = user_node["contributionsCollection"]["contributionCalendar"]
    days = []
    for week in calendar["weeks"]:
        for d in week["contributionDays"]:
            days.append(Day(
                date=dt.date.fromisoformat(d["date"]),
                count=int(d["contributionCount"]),
                level=LEVEL_FROM_GRAPHQL[d["contributionLevel"]],
            ))
    return days


TD_RE = re.compile(r"<td\b[^>]*>")
ATTR_RE = re.compile(r'([\w-]+)="([^"]*)"')
TIP_RE = re.compile(
    r'<tool-tip\b[^>]*\bfor="contribution-day-component-(\d+)-(\d+)"[^>]*>([^<]*)</tool-tip>'
)
COUNT_RE = re.compile(r"\s*(No|\d+)\s+contributions?\b")


def fetch_public_page(user):
    url = CONTRIBUTIONS_URL.format(user=user)
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT, "Accept": "text/html"})
    with urllib.request.urlopen(req, timeout=30) as resp:
        text = resp.read().decode("utf-8", "replace")

    # Exact counts come from the screen-reader tooltips, e.g. "8 contributions on November 23rd."
    counts = {}
    for m in TIP_RE.finditer(text):
        cm = COUNT_RE.match(html.unescape(m.group(3)))
        if cm:
            counts[(m.group(1), m.group(2))] = 0 if cm.group(1) == "No" else int(cm.group(1))

    days = []
    for tag in TD_RE.findall(text):
        attrs = dict(ATTR_RE.findall(tag))
        if "data-date" not in attrs:
            continue
        idm = re.search(r"contribution-day-component-(\d+)-(\d+)", attrs.get("id", ""))
        count = counts.get((idm.group(1), idm.group(2))) if idm else None
        days.append(Day(
            date=dt.date.fromisoformat(attrs["data-date"]),
            count=count,
            level=int(attrs.get("data-level", "0")),
        ))
    if not days:
        raise RuntimeError(f"no contribution days found at {url}")
    return days


def github_token():
    """Read-only token from the environment, or from the local `gh` login. Never printed."""
    for key in ("GITHUB_TOKEN", "GH_TOKEN"):
        token = os.environ.get(key)
        if token:
            return token
    try:
        proc = subprocess.run(["gh", "auth", "token"], capture_output=True, text=True, timeout=10)
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return None
    token = (proc.stdout or "").strip()
    return token or None


def fetch_days(user):
    token = github_token()
    graphql_days = None
    if token:
        try:
            graphql_days = fetch_graphql(user, token)
        except (urllib.error.URLError, RuntimeError, KeyError, ValueError) as exc:
            print(f"warning: GraphQL fetch failed ({exc}); trying the public contributions page",
                  file=sys.stderr)
    try:
        page_days = fetch_public_page(user)
    except (urllib.error.URLError, RuntimeError, KeyError, ValueError) as exc:
        if graphql_days is None:
            raise
        print(f"warning: public contributions page failed ({exc}); using GraphQL only",
              file=sys.stderr)
        return graphql_days
    if graphql_days is None:
        return page_days
    # Prefer the public calendar's level and count when both sources have a date, so the
    # settled frame matches the graph GitHub renders on the profile.
    by_date = {d.date: d for d in graphql_days}
    for d in page_days:
        by_date[d.date] = d
    return list(by_date.values())


def build_grid(days):
    """Map each day to (column, row). Rows are weekdays with Sunday at 0, like GitHub."""
    unique = {d.date: d for d in days}
    ordered = sorted(unique.values(), key=lambda d: d.date)
    first = ordered[0].date
    week_start = first - dt.timedelta(days=(first.weekday() + 1) % 7)
    cells = {}
    for d in ordered:
        col = (d.date - week_start).days // 7
        row = (d.date.weekday() + 1) % 7
        cells[(col, row)] = d
    ncols = max(c for c, _ in cells) + 1
    return cells, ncols


# ---------------------------------------------------------------- geometry and timing

def fmt(value):
    """Compact number text: integers as-is, floats trimmed to two decimals."""
    if isinstance(value, float):
        return f"{value:.2f}".rstrip("0").rstrip(".")
    return str(value)


def canvas_size(ncols):
    width = 2 * PAD_X + ncols * PITCH - GAP
    height = 2 * PAD_Y + ROWS * PITCH - GAP
    return width, height


def cell_x(col):
    return PAD_X + col * PITCH


def cell_y(row):
    return PAD_Y + row * PITCH


def cell_center_x(col):
    return cell_x(col) + CELL / 2


def car_center_y():
    return PAD_Y + (ROWS * PITCH - GAP) / 2


def car_span(width):
    """Car center x at the start and end of the pass, both fully off-canvas."""
    return -CAR_X_MARGIN, width + CAR_X_MARGIN


def car_center_at(frac, width):
    """Car center x at a loop fraction inside the pass (linear motion)."""
    x0, x1 = car_span(width)
    u = (frac - PASS_START) / (PASS_END - PASS_START)
    return x0 + (x1 - x0) * u


def fill_time(col, row, width):
    """Loop fraction when the car's front reaches the center of this cell's column."""
    x0, x1 = car_span(width)
    front_center_x = cell_center_x(col) - CAR_HALF_LEN  # car center when its nose is at the cell
    u = (front_center_x - x0) / (x1 - x0)
    u = min(max(u, 0.0), 1.0)
    return PASS_START + (PASS_END - PASS_START) * u + row * ROW_STAGGER


def keys(times):
    return ";".join(f"{t:.4f}" for t in times)


def animate(attr, values, times):
    vals = ";".join(fmt(float(v)) for v in values)
    return (f'<animate attributeName="{attr}" values="{vals}" keyTimes="{keys(times)}" '
            f'dur="{LOOP_SECONDS}s" repeatCount="indefinite" calcMode="linear"/>')


def animate_transform(kind, values, times, calc="linear", splines=None):
    extra = f' keySplines="{splines}"' if splines else ""
    return (f'<animateTransform attributeName="transform" type="{kind}" '
            f'values="{";".join(values)}" keyTimes="{keys(times)}" dur="{LOOP_SECONDS}s" '
            f'repeatCount="indefinite" calcMode="{calc}"{extra}/>')


def cell_rect(col, row, fill, extra=""):
    return (f'<rect x="{fmt(float(cell_x(col)))}" y="{fmt(float(cell_y(row)))}" '
            f'width="{CELL}" height="{CELL}" rx="{fmt(CELL_RX)}" fill="{fill}"{extra}/>')


def mix_white(hex_color, amount):
    """Move a hex colour toward white by `amount` (0..1), for the brief pass glow."""
    r, g, b = (int(hex_color[i:i + 2], 16) for i in (1, 3, 5))
    r = round(r + (255 - r) * amount)
    g = round(g + (255 - g) * amount)
    b = round(b + (255 - b) * amount)
    return "#{:02x}{:02x}{:02x}".format(r, g, b)


def cell_level(day):
    if day is None:
        return None
    if day.count is not None:
        if day.count <= 0:
            return 0
        return min(max(day.level, 1), 4)
    return min(max(day.level, 0), 4)


def real_grid(grid, theme):
    """One rect per real calendar day, filled with GitHub's colour for that day's level.

    Days that do not exist (for example future weekdays in the current week) are omitted,
    so the grid never invents a cell.
    """
    colors = THEMES[theme]["levels"]
    out = []
    for (col, row), day in sorted(grid.items()):
        level = cell_level(day)
        if level is None:
            continue
        out.append(cell_rect(col, row, colors[level]))
    return "".join(out)


def glow_cell(col, row, color, peak, width):
    """A short brightness pulse as the car passes, then back to fully transparent."""
    t0 = fill_time(col, row, width)
    t1 = min(t0 + GLOW_RISE, 0.98)
    t2 = min(t0 + GLOW_RISE + GLOW_FALL, 0.995)
    if t1 <= t0:
        t1 = min(t0 + 0.001, 0.99)
    if t2 <= t1:
        t2 = min(t1 + 0.001, 0.999)
    times = [0, t0, t1, t2, 1]
    anim = animate("opacity", [0, 0, peak, 0, 0], times)
    x = fmt(float(cell_x(col)))
    y = fmt(float(cell_y(row)))
    return (f'<rect x="{x}" y="{y}" width="{CELL}" height="{CELL}" rx="{fmt(CELL_RX)}" '
            f'fill="{color}" opacity="0">{anim}</rect>')


def glow_overlay(grid, theme, width):
    """Brief lighter overlay on each real cell as the car reaches it."""
    colors = THEMES[theme]["levels"]
    out = []
    for (col, row), day in sorted(grid.items()):
        level = cell_level(day)
        if level is None:
            continue
        peak = GLOW_PEAK_EMPTY if level == 0 else GLOW_PEAK_LIT
        out.append(glow_cell(col, row, mix_white(colors[level], 0.55), peak, width))
    return "".join(out)


# ---------------------------------------------------------------- car

def _mirror_path(nose, top_curves):
    """Closed, left-right symmetric body outline from the upper half.

    nose is the (x, y) tip on the centre line. top_curves are cubic segments
    (c1, c2, end) running from the nose back to the tail. The lower half is the same
    curves mirrored in y and walked in reverse.
    """
    def pt(p):
        return f"{fmt(p[0])},{fmt(p[1])}"
    d = [f"M{pt(nose)}"]
    for c1, c2, end in top_curves:
        d.append(f"C{pt(c1)} {pt(c2)} {pt(end)}")
    d.append(f"L{pt((top_curves[-1][2][0], -top_curves[-1][2][1]))}")
    ends = [nose] + [c[2] for c in top_curves]
    for i in range(len(top_curves) - 1, -1, -1):
        c1, c2, _ = top_curves[i]
        m = lambda p: (p[0], -p[1])
        d.append(f"C{pt(m(c2))} {pt(m(c1))} {pt(m(ends[i]))}")
    return " ".join(d) + " Z"


# Compact mid-engine supercar seen from directly above, nose to +x. Short blunt nose, rounded
# front fenders, a gentle waist at the doors, wider rear haunches and a short tail.
BODY_PATH = _mirror_path(
    (40, 0),
    [
        ((40.3, -5.0), (39.6, -9.4), (36.6, -11.8)),       # blunt nose into the front corner
        ((33.6, -14.0), (29.6, -15.4), (24, -15.6)),       # front fender
        ((18.5, -15.8), (14, -14.2), (8, -14.2)),          # fender eases into the doors
        ((2.5, -14.2), (-3.5, -14.4), (-9, -15.4)),        # door line
        ((-14, -16.4), (-18, -17.2), (-24, -17.2)),        # rear haunch, widest point
        ((-30, -17.2), (-34.4, -16.6), (-36.4, -14.6)),
        ((-37.6, -13.2), (-38, -11.8), (-38, -9.5)),       # short, broad tail
    ],
)

# Wraparound canopy glass and the lighter roof panel set into it.
GLASS_PATH = ("M14.5,-6.6 C11.5,-9.2 5.5,-10.8 -2,-10.8 C-9.5,-10.8 -15,-9.4 -18,-6.6 "
              "C-19.6,-3.4 -19.6,3.4 -18,6.6 C-15,9.4 -9.5,10.8 -2,10.8 C5.5,10.8 11.5,9.2 14.5,6.6 "
              "C16.2,3.4 16.2,-3.4 14.5,-6.6 Z")
ROOF_PATH = ("M8.4,-5.2 C5,-6.6 0,-6.8 -4,-6.8 C-8.2,-6.8 -11.2,-6.4 -12.4,-5 "
             "C-13.2,-2.6 -13.2,2.6 -12.4,5 C-11.2,6.4 -8.2,6.8 -4,6.8 C0,6.8 5,6.6 8.4,5.2 "
             "C9.6,2.6 9.6,-2.6 8.4,-5.2 Z")
ROOF_SEAM = "M-2.2,-6.6 C-2.8,-2 -2.8,2 -2.2,6.6"


def wheel_art(cx, cy, length, width, steer):
    """One tyre tread from above: a dark rounded rectangle with faint ribs and edge sheen."""
    hl, hw = length / 2, width / 2
    rx = min(hw, 2.6)
    ribs = " ".join(f"M{fmt(x)},{fmt(-hw + 0.7)} L{fmt(x)},{fmt(hw - 0.7)}"
                    for x in (-hl * 0.6, -hl * 0.2, hl * 0.2, hl * 0.6))
    rot = f" rotate({fmt(steer)})" if steer else ""
    return (
        f'<g transform="translate({fmt(cx)},{fmt(cy)}){rot}">'
        f'<rect x="{fmt(-hl - 0.8)}" y="{fmt(-hw - 0.8)}" width="{fmt(length + 1.6)}" '
        f'height="{fmt(width + 1.6)}" rx="{fmt(rx + 0.8)}" fill="#000" opacity="0.45" '
        'filter="url(#softEdge)"/>'
        f'<rect x="{fmt(-hl)}" y="{fmt(-hw)}" width="{fmt(length)}" height="{fmt(width)}" '
        f'rx="{fmt(rx)}" fill="url(#carTyre)"/>'
        f'<path d="{ribs}" stroke="#2a303d" stroke-width="0.7" stroke-linecap="round"/>'
        f'<rect x="{fmt(-hl + 0.4)}" y="{fmt(-hw + 0.4)}" width="{fmt(length - 0.8)}" '
        f'height="{fmt(width - 0.8)}" rx="{fmt(max(rx - 0.4, 0.5))}" fill="none" '
        'stroke="#4a5266" stroke-width="0.5" opacity="0.8"/>'
        '</g>'
    )


def deck_vents():
    """Short longitudinal vents on the rear deck: dark slits with a light lower lip."""
    out = []
    for y in (3.4, 6.4, 9.4):
        x_end = -22.5 - 11.0 + (y - 3.4) * 0.45
        for s in (-1, 1):
            out.append(f"M-22.5,{fmt(s * y)} L{fmt(x_end)},{fmt(s * y)}")
    lines = " ".join(out)
    return (f'<path d="{lines}" stroke="#1f3f80" stroke-width="1.1" stroke-linecap="round" opacity="0.85"/>'
            f'<path d="{lines}" transform="translate(0,0.9)" stroke="#b6d6ff" stroke-width="0.4" '
            'stroke-linecap="round" opacity="0.55"/>')


def car_shapes(theme):
    shadow = THEMES[theme]["shadow"]
    wheels = "".join(wheel_art(*w) for w in WHEELS)
    return (
        # Drop shadow under the chassis: the outline shifted down-right and blurred.
        f'<path d="{BODY_PATH}" transform="translate(2,3.8)" fill="#000" opacity="{shadow}" '
        'filter="url(#shadowBlur)"/>'
        # Tyres come first so the body and fenders drawn after them cover most of each one.
        f'{wheels}'
        # Light-blue metallic paint, a slightly darker lower flank and a gentle nose-to-tail wash.
        f'<path d="{BODY_PATH}" fill="url(#carBody)"/>'
        f'<path d="{BODY_PATH}" fill="url(#carUnder)"/>'
        f'<path d="{BODY_PATH}" fill="url(#carLong)"/>'
        '<g clip-path="url(#bodyClip)">'
        # Rear deck: a darker plate with the vents on it.
        '<path d="M-19.5,-12.6 C-25,-14 -31,-13.6 -34.6,-11.4 C-36.2,-10 -36.2,10 -34.6,11.4 '
        'C-31,13.6 -25,14 -19.5,12.6 Z" fill="#3d6fc2" opacity="0.5"/>'
        f'{deck_vents()}'
        # Soft sheen on the lower shoulder.
        '<path d="M30,12.4 C22,13.4 12,12.2 2,12.2 C-8,12.2 -16,14.6 -26,14.4" fill="none" '
        'stroke="#ffffff" stroke-width="2.6" stroke-linecap="round" opacity="0.18" filter="url(#glow)"/>'
        '</g>'
        # Outline in a deeper blue.
        f'<path d="{BODY_PATH}" fill="none" stroke="#2f5fae" stroke-width="0.7" opacity="0.9"/>'
        # Hood cut lines and door shut lines, kept faint.
        '<path d="M34,-8.4 C30,-9.4 26,-9.8 22.4,-9.6 M34,8.4 C30,9.4 26,9.8 22.4,9.6" fill="none" '
        'stroke="#2f5fae" stroke-width="0.5" opacity="0.5"/>'
        '<path d="M-9,-14.4 C-10,-10 -10.4,-8 -10.4,-6.4 M-9,14.4 C-10,10 -10.4,8 -10.4,6.4" fill="none" '
        'stroke="#2f5fae" stroke-width="0.5" opacity="0.45"/>'
        # Small dark intake low on the nose.
        '<path d="M39,-2.4 C37.6,-3 36.4,-3.4 35.2,-3.4 L35.2,3.4 C36.4,3.4 37.6,3 39,2.4 Z" '
        'fill="#0f1830" opacity="0.9"/>'
        # Headlamps: thin white slivers at the front corners.
        '<path d="M36.4,-9.4 L33.2,-11.8 L32.8,-10.8 L35.6,-8.4 Z M36.4,9.4 L33.2,11.8 L32.8,10.8 L35.6,8.4 Z" '
        'fill="#ffffff" opacity="0.95"/>'
        # Dark wraparound canopy with a lighter roof panel, a seam and a faint glare.
        '<g transform="translate(2,0)">'
        f'<path d="{GLASS_PATH}" fill="url(#carGlass)" stroke="#0c1220" stroke-width="0.5"/>'
        '<g clip-path="url(#glassClip)">'
        '<path d="M15,-9 L9,-9 L11.4,9 L16.6,9 Z" fill="#8ec2ff" opacity="0.2"/>'
        '</g>'
        f'<path d="{ROOF_PATH}" fill="url(#carRoof)" stroke="#5a8fe0" stroke-width="0.4"/>'
        f'<path d="{ROOF_SEAM}" fill="none" stroke="#4f86d8" stroke-width="0.6" opacity="0.8"/>'
        '</g>'
        # Clean white highlight along the upper shoulder, with a soft twin underneath.
        '<path d="M34.4,-9.6 C32,-11.8 28,-12.8 24,-13 C18,-13.2 14,-11.8 8,-11.8 C2,-11.8 -4,-12 -9,-13 '
        'C-14,-14 -18,-15 -24,-15" fill="none" stroke="#ffffff" stroke-width="2.4" stroke-linecap="round" '
        'opacity="0.45" filter="url(#softEdge)"/>'
        '<path d="M34.4,-9.6 C32,-11.8 28,-12.8 24,-13 C18,-13.2 14,-11.8 8,-11.8 C2,-11.8 -4,-12 -9,-13 '
        'C-14,-14 -18,-15 -24,-15" fill="none" stroke="url(#carSpec)" stroke-width="1.3" '
        'stroke-linecap="round"/>'
    )


def pass_frac_at_x(x, width):
    """Loop fraction at which the car centre is at x (linear motion)."""
    x0, x1 = car_span(width)
    return PASS_START + (PASS_END - PASS_START) * (x - x0) / (x1 - x0)


def smoke_core(width, theme):
    """A large, soft white cloud attached to the car, billowing from the rear and both flanks.

    Drawn in the car's local frame (under the body), so it follows the car; round lobes make
    the rotation invisible. It fades in as the car enters and out as it leaves.
    """
    peak = THEMES[theme]["smoke_peak"]
    ax = REAR_AXLE_X
    # Large merged lobes: a big rear/side bloom, bigger than the body, with a little wrap toward the nose.
    lobes = ((ax - 10, 0, 50), (ax - 32, 0, 42),
             (ax + 2, -28, 38), (ax + 2, 28, 38),
             (ax - 22, -20, 36), (ax - 22, 20, 36),
             (ax + 20, -26, 30), (ax + 20, 26, 30),
             (ax + 36, -20, 22), (ax + 36, 20, 22))
    circles = "".join(
        f'<circle cx="{fmt(float(x))}" cy="{fmt(float(y))}" r="{fmt(float(r))}" fill="url(#smoke{theme})"/>'
        for x, y, r in lobes
    )
    times = [0,
             pass_frac_at_x(CORE_FADE_IN_X[0], width), pass_frac_at_x(CORE_FADE_IN_X[1], width),
             pass_frac_at_x(width + CORE_FADE_OUT_X[0], width), pass_frac_at_x(width + CORE_FADE_OUT_X[1], width),
             1]
    anim = animate("opacity", [0, 0, peak, peak, 0, 0], times)
    return f'<g opacity="0">{anim}<g filter="url(#coreBlur)">{circles}</g></g>'


def car_layers(width, cy, theme):
    """One left-to-right drift pass. The car's center moves linearly; the body rotates."""
    x0, x1 = car_span(width)
    mid = PASS_START + (PASS_END - PASS_START) / 2
    move = animate_transform(
        "translate",
        [f"{fmt(x0)} {fmt(cy)}", f"{fmt(x0)} {fmt(cy)}", f"{fmt(x1)} {fmt(cy)}", f"{fmt(x1)} {fmt(cy)}"],
        [0, PASS_START, PASS_END, 1],
    )
    # Eased drift angle: flat on entry, swings nose-up in the middle, levels out on exit.
    ease = "0.42 0 0.58 1"
    rot = animate_transform(
        "rotate",
        ["0", "0", fmt(DRIFT_DEG), "0", "0"],
        [0, PASS_START, mid, PASS_END, 1],
        calc="spline",
        splines=";".join([ease] * 4),
    )
    return f"<g>{move}<g>{rot}{smoke_core(width, theme)}{car_shapes(theme)}</g></g>"


# ---------------------------------------------------------------- smoke

def drift_angle_at(frac):
    """Approximate drift angle (degrees) at a loop fraction; same easing shape as the SMIL spline."""
    mid = PASS_START + (PASS_END - PASS_START) / 2
    if frac <= PASS_START or frac >= PASS_END:
        return 0.0
    u = (frac - PASS_START) / (mid - PASS_START) if frac < mid else (PASS_END - frac) / (PASS_END - mid)
    eased = u * u * (3 - 2 * u)
    return DRIFT_DEG * eased


def local_to_world(born, lx, ly, width, cy):
    """World position of a car-local point at loop fraction `born`, following the car's yaw."""
    ang = math.radians(drift_angle_at(born))
    return (car_center_at(born, width) + lx * math.cos(ang) - ly * math.sin(ang),
            cy + lx * math.sin(ang) + ly * math.cos(ang))


def smoke_layers(width, cy, theme):
    """Shed smoke: puffs and a wide haze left behind where the car has been, merged by blur.

    The big cloud that rides on the car is drawn by smoke_core(). Both are anchored on the
    rear axle. Emission only runs while the car is on or near the canvas.
    """
    palette = THEMES[theme]
    t_in = pass_frac_at_x(-40, width)
    t_out = pass_frac_at_x(width + 20, width)

    rng = random.Random(PUFF_SEED)
    puffs = []
    for i in range(PUFF_COUNT):
        born = t_in + (t_out - t_in) * (i + rng.uniform(0.0, 1.0)) / PUFF_COUNT
        side = rng.choice((-1, 0, 1))                     # left flank, rear centre or right flank
        lx = REAR_AXLE_X + rng.uniform(-16, 4)
        ly = side * rng.uniform(6, 22) if side else rng.uniform(-8, 8)
        sx, sy = local_to_world(born, lx, ly, width, cy)
        scale = rng.uniform(0.85, 1.2)
        dx = -rng.uniform(16, 38)                        # left behind as the car moves on
        dy = side * rng.uniform(2, 10) + rng.uniform(-4, 4)
        r0, r1 = PUFF_R0 * scale, PUFF_R1 * scale
        times = [0, born, born + PUFF_LIFE, 1]
        anims = (
            animate("r", [r0, r0, r1, r1], times)
            + animate("cx", [sx, sx, sx + dx, sx + dx], times)
            + animate("cy", [sy, sy, sy + dy, sy + dy], times)
            + animate("opacity", [0, 0, palette["smoke_peak"], palette["smoke_peak"] * 0.5, 0, 0],
                      [0, born, born + PUFF_LIFE * 0.15, born + PUFF_LIFE * 0.55,
                       born + PUFF_LIFE, 1])
        )
        puffs.append(f'<circle cx="{fmt(sx)}" cy="{fmt(sy)}" r="{fmt(r0)}" '
                     f'fill="url(#smoke{theme})" opacity="0">{anims}</circle>')

    rng = random.Random(HAZE_SEED)
    haze = []
    for i in range(HAZE_COUNT):
        born = t_in + (t_out - t_in) * (i + rng.uniform(0.0, 1.0)) / HAZE_COUNT
        sx, sy = local_to_world(born, REAR_AXLE_X - 12, rng.uniform(-6, 6), width, cy)
        scale = rng.uniform(0.9, 1.15)
        dx = -rng.uniform(55, 100)
        rx0, rx1 = HAZE_R0 * 1.3 * scale, HAZE_R1 * 1.5 * scale
        ry0, ry1 = HAZE_R0 * 0.7 * scale, HAZE_R1 * 0.8 * scale
        times = [0, born, born + HAZE_LIFE, 1]
        anims = (
            animate("rx", [rx0, rx0, rx1, rx1], times)
            + animate("ry", [ry0, ry0, ry1, ry1], times)
            + animate("cx", [sx, sx, sx + dx, sx + dx], times)
            + animate("opacity", [0, 0, palette["haze_peak"], palette["haze_peak"] * 0.6, 0, 0],
                      [0, born, born + HAZE_LIFE * 0.2, born + HAZE_LIFE * 0.6, born + HAZE_LIFE, 1])
        )
        haze.append(f'<ellipse cx="{fmt(sx)}" cy="{fmt(sy)}" rx="{fmt(rx0)}" ry="{fmt(ry0)}" '
                    f'fill="url(#smoke{theme})" opacity="0">{anims}</ellipse>')

    return (f'<g filter="url(#hazeBlur)">{"".join(haze)}</g>'
            f'<g filter="url(#smokeWide)"><g filter="url(#smokeSoft)">{"".join(puffs)}</g></g>')


# ---------------------------------------------------------------- defs and document

def defs(theme, width, height):
    palette = THEMES[theme]
    smoke = palette["smoke"]
    return (
        "<defs>"
        '<radialGradient id="bgDark" cx="0.5" cy="0.45" r="0.75">'
        '<stop offset="0" stop-color="#1d1a3e"/><stop offset="0.6" stop-color="#0d0b1f"/>'
        '<stop offset="1" stop-color="#07060f"/></radialGradient>'
        # Light-blue metallic paint: a brighter crown on the lit shoulder rolling into a deeper flank.
        '<linearGradient id="carBody" x1="0" y1="0" x2="0" y2="1">'
        '<stop offset="0" stop-color="#9cc6fc"/><stop offset="0.22" stop-color="#78b0f8"/>'
        '<stop offset="0.6" stop-color="#6098e8"/><stop offset="1" stop-color="#4a82d6"/></linearGradient>'
        # Slightly darker lower flank.
        '<linearGradient id="carUnder" x1="0" y1="0" x2="0" y2="1">'
        '<stop offset="0.6" stop-color="#1c3f8a" stop-opacity="0"/>'
        '<stop offset="1" stop-color="#1c3f8a" stop-opacity="0.35"/></linearGradient>'
        # Tonal wash: a touch brighter toward the nose, a touch darker at the tail.
        '<linearGradient id="carLong" x1="0" y1="0" x2="1" y2="0">'
        '<stop offset="0" stop-color="#1c3f8a" stop-opacity="0.2"/>'
        '<stop offset="0.5" stop-color="#1c3f8a" stop-opacity="0"/>'
        '<stop offset="1" stop-color="#d4e6ff" stop-opacity="0.14"/></linearGradient>'
        '<linearGradient id="carSpec" x1="0" y1="0" x2="1" y2="0">'
        '<stop offset="0" stop-color="#ffffff" stop-opacity="0.5"/>'
        '<stop offset="0.5" stop-color="#ffffff" stop-opacity="1"/>'
        '<stop offset="1" stop-color="#ffffff" stop-opacity="0.45"/></linearGradient>'
        '<linearGradient id="carGlass" x1="0" y1="0" x2="1" y2="1">'
        '<stop offset="0" stop-color="#2a3346"/><stop offset="0.55" stop-color="#171d2b"/>'
        '<stop offset="1" stop-color="#0d111b"/></linearGradient>'
        '<linearGradient id="carRoof" x1="0" y1="0" x2="0" y2="1">'
        '<stop offset="0" stop-color="#a6cdfd"/><stop offset="1" stop-color="#7db3f6"/></linearGradient>'
        '<linearGradient id="carTyre" x1="0" y1="0" x2="0" y2="1">'
        '<stop offset="0" stop-color="#232733"/><stop offset="0.3" stop-color="#07080d"/>'
        '<stop offset="0.7" stop-color="#07080d"/><stop offset="1" stop-color="#232733"/></linearGradient>'
        f'<clipPath id="bodyClip"><path d="{BODY_PATH}"/></clipPath>'
        f'<clipPath id="glassClip"><path d="{GLASS_PATH}"/></clipPath>'
        # Smoke puff: dense milky core with a long soft falloff so neighbours merge.
        f'<radialGradient id="smoke{theme}" cx="0.5" cy="0.5" r="0.5">'
        f'<stop offset="0" stop-color="{smoke}" stop-opacity="1"/>'
        f'<stop offset="0.5" stop-color="{smoke}" stop-opacity="0.9"/>'
        f'<stop offset="0.75" stop-color="{smoke}" stop-opacity="0.35"/>'
        f'<stop offset="1" stop-color="{smoke}" stop-opacity="0"/></radialGradient>'
        '<filter id="softEdge" x="-20%" y="-50%" width="140%" height="200%">'
        '<feGaussianBlur stdDeviation="0.8"/></filter>'
        '<filter id="glow" x="-30%" y="-80%" width="160%" height="260%">'
        '<feGaussianBlur stdDeviation="1.8"/></filter>'
        '<filter id="shadowBlur" x="-30%" y="-50%" width="160%" height="200%">'
        '<feGaussianBlur stdDeviation="2.4"/></filter>'
        # Smoke filters cover the whole canvas, so animated puffs never clip.
        f'<filter id="smokeSoft" filterUnits="userSpaceOnUse" x="-120" y="0" width="{width + 240}" height="{height}">'
        '<feGaussianBlur stdDeviation="5"/></filter>'
        f'<filter id="smokeWide" filterUnits="userSpaceOnUse" x="-120" y="0" width="{width + 240}" height="{height}">'
        '<feGaussianBlur stdDeviation="6"/></filter>'
        f'<filter id="hazeBlur" filterUnits="userSpaceOnUse" x="-120" y="0" width="{width + 240}" height="{height}">'
        '<feGaussianBlur stdDeviation="11"/></filter>'
        # The core cloud lives in the car's local frame.
        # objectBoundingBox so the region follows the car; generous padding so the blur never clips.
        '<filter id="coreBlur" x="-80%" y="-80%" width="260%" height="260%">'
        '<feGaussianBlur stdDeviation="9"/></filter>'
        "</defs>"
    )


def svg_document(width, height, theme, title, desc, layers):
    bg = THEMES[theme]["bg"]
    return (
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
        f'viewBox="0 0 {width} {height}" role="img" aria-labelledby="t d">'
        f'<title id="t">{title}</title><desc id="d">{desc}</desc>'
        f'{defs(theme, width, height)}'
        f'<rect width="{width}" height="{height}" rx="8" fill="{bg}"/>'
        f"{layers}</svg>\n"
    )


# ---------------------------------------------------------------- render

def render(days, theme):
    palette = THEMES[theme]
    grid, ncols = build_grid(days)
    width, height = canvas_size(ncols)
    cy = car_center_y()

    cells = real_grid(grid, theme)
    glow = glow_overlay(grid, theme, width)

    layers = (
        cells
        + glow
        + smoke_layers(width, cy, theme)
        + car_layers(width, cy, theme)
    )
    desc = ("A light-blue sports car drifts across the real GitHub contribution graph. Each day "
            "keeps its true contribution level, briefly brightening as the car passes, and the "
            "rear tires throw a large cloud of white smoke.")
    return svg_document(width, height, theme, "Car contribution animation", desc, layers)


# ---------------------------------------------------------------- car preview

def car_preview_svg(theme, zoom=4):
    """Standalone, static SVG of just the car at 0 degrees and at the mid-drift angle."""
    w, h = 300, 150
    cars = "".join(
        f'<g transform="translate({fmt(cx)},{fmt(h / 2)}) rotate({fmt(ang)})">{car_shapes(theme)}</g>'
        for cx, ang in ((75, 0.0), (205, DRIFT_DEG))
    )
    bg = THEMES[theme]["bg"]
    return (
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{w * zoom}" height="{h * zoom}" '
        f'viewBox="0 0 {w} {h}">'
        f'{defs(theme, w, h)}<rect width="{w}" height="{h}" fill="{bg}"/>{cars}</svg>\n'
    )


# ---------------------------------------------------------------- CLI

def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--user", default="RamSuryaCH")
    parser.add_argument("--outdir", default="dist")
    parser.add_argument("--dump-car", metavar="PATH",
                        help="write a standalone 4x SVG of just the car (0 deg and mid-drift) "
                             "to PATH and exit; no network access")
    parser.add_argument("--theme", choices=("dark", "light"), default="dark",
                        help="theme used by --dump-car")
    args = parser.parse_args(argv)

    if args.dump_car:
        svg = car_preview_svg(args.theme)
        ET.fromstring(svg)
        Path(args.dump_car).write_text(svg, encoding="utf-8")
        print(f"wrote {args.dump_car}")
        return 0

    days = fetch_days(args.user)
    outputs = {}
    for theme in ("dark", "light"):
        svg = render(days, theme)
        ET.fromstring(svg)  # fail early if the markup is not well formed
        outputs[theme] = svg

    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    for theme, svg in outputs.items():
        (outdir / f"car-animation-{theme}.svg").write_text(svg, encoding="utf-8")
    print(f"wrote {outdir}/car-animation-dark.svg and {outdir}/car-animation-light.svg")
    return 0


if __name__ == "__main__":
    sys.exit(main())
