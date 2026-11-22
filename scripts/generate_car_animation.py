#!/usr/bin/env python3
"""Generate the animated car-on-contribution-graph SVGs for the GitHub profile README.

Usage:
  python3 scripts/generate_car_animation.py --user RamSuryaCH --outdir dist

Writes two files into --outdir:
  car-animation-dark.svg
  car-animation-light.svg

A top-down sports car drives once, left to right, across the user's public contribution
calendar. Data comes from the GraphQL API when GITHUB_TOKEN is set, otherwise from the
public contributions page. Only days with real contributions light up in bright neon as
the car passes. Empty days get a dim glow behind the car so the trail is not sparse, and
cells ahead of the car stay dark. The car leaves a milky tire-smoke bloom at the rear.

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
PAD_Y = 92
CELL_RX = 2.5

# Animation timing. Everything loops over LOOP_SECONDS.
LOOP_SECONDS = 12
PASS_START = 0.04   # loop fraction when the car starts moving on screen
PASS_END = 0.80     # loop fraction when the car has left the right edge
FILL_LEN = 0.025    # loop fraction over which one cell lights up (about 0.3 s)
ROW_STAGGER = 0.0012  # tiny per-row delay so the wave looks organic, not a hard column
TRAIL_HOLD = 0.90   # the finished trail stays lit until this fraction, then fades
TRAIL_FADE_END = 0.985
DRIFT_DEG = -32.0   # negative = nose up-right during the middle of the drift

# Car center travels from fully off the left edge to fully off the right edge.
CAR_X_MARGIN = 70
CAR_HALF_LEN = 50   # car spans local x in [-50, 50]

# Wheels in car-local coordinates: (x, y, tyre radius). Rear tyres are slightly larger.
WHEELS = (
    (30.0, -12.6, 6.4), (30.0, 12.6, 6.4),
    (-29.0, -14.0, 7.0), (-29.0, 14.0, 7.0),
)

# Tire smoke: overlapping blurred puffs are emitted right behind the rear wheels and
# between them, so they merge into one bloom hugging the rear. Each puff grows and fades
# in about 1.25 s (0.104 of the 12 s loop).
PUFF_PER_WHEEL = 80
PUFF_CENTER = 56
PUFF_LIFE = 0.104
PUFF_R0, PUFF_R1 = 12, 32
PUFF_SEED = 12
SMOKE_BEHIND = 34   # local x of the emission points, just behind the rear tyres

# Zero-contribution days glow dim as the car passes, so the trail looks packed. Real
# contribution days keep the bright neon.
EMPTY_GLOW_COLOR = "#7b3ff2"

# Neon palette for the trail, keyed by GitHub contribution level 1..4.
NEON_BY_LEVEL = {1: "#7b3ff2", 2: "#c83bdc", 3: "#ff3d9a", 4: "#ff8a1f"}

THEMES = {
    "dark": {
        "bg": "url(#bgDark)",
        "base": "#1b1a2c",        # unlit cells: dark charcoal, a bit lighter than the background
        "smoke": "#ffffff",
        "smoke_peak": 0.5,
        "empty_color": EMPTY_GLOW_COLOR,
        "empty_peak": 0.28,
        "shadow": 0.6,
        "cone": "#f4fbff",
        "cone_peak": 0.62,
    },
    "light": {
        "bg": "#f6f7fb",
        "base": "#e1e4ed",
        "smoke": "#98a0ba",       # a little darker and bluer than white, so it shows on a light page
        "smoke_peak": 0.62,
        "empty_color": "#8a5cf5",
        "empty_peak": 0.34,
        "shadow": 0.42,
        "cone": "#ffd45c",
        "cone_peak": 0.55,
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
query($login: String!, $from: DateTime!, $to: DateTime!) {
  user(login: $login) {
    contributionsCollection(from: $from, to: $to) {
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
    now = dt.datetime.now(dt.timezone.utc)
    start = now - dt.timedelta(days=365)
    variables = {
        "login": user,
        "from": start.strftime("%Y-%m-%dT00:00:00Z"),
        "to": now.strftime("%Y-%m-%dT%H:%M:%SZ"),
    }
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


def fetch_days(user):
    token = os.environ.get("GITHUB_TOKEN")
    if token:
        try:
            return fetch_graphql(user, token)
        except (urllib.error.URLError, RuntimeError, KeyError, ValueError) as exc:
            print(f"warning: GraphQL fetch failed ({exc}); using the public contributions page",
                  file=sys.stderr)
    return fetch_public_page(user)


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


def trail_cell(col, row, color, peak, width):
    """A cell that fades to `peak` opacity as the car arrives and holds until the loop ends."""
    t0 = fill_time(col, row, width)
    times = [0, t0, t0 + FILL_LEN, TRAIL_HOLD, TRAIL_FADE_END, 1]
    values = [0, 0, peak, peak, 0, 0]
    anim = animate("opacity", values, times)
    x = fmt(float(cell_x(col)))
    y = fmt(float(cell_y(row)))
    return (f'<rect x="{x}" y="{y}" width="{CELL}" height="{CELL}" rx="{fmt(CELL_RX)}" '
            f'fill="{color}" opacity="0">{anim}</rect>')


def base_grid(ncols, color):
    out = []
    for col in range(ncols):
        for row in range(ROWS):
            out.append(cell_rect(col, row, color))
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


# Mid-engine two-door coupe seen from above, nose to +x. A short sharp nose, front fenders,
# a tight waist at the doors, wide rear haunches and a short ducktail. Drawn from scratch.
BODY_PATH = _mirror_path(
    (49, 0),
    [
        ((49.2, -3.0), (47.6, -6.0), (44, -8.4)),          # sharp nose and front corner
        ((41, -10.2), (36, -14.3), (30, -14.5)),           # front fender flare
        ((24, -14.6), (19, -11.8), (12, -11.6)),           # fender tapers into the waist
        ((6, -11.4), (-2, -11.3), (-9, -12.6)),            # doors and the tight waist
        ((-14, -13.8), (-19, -17.4), (-28, -17.4)),        # rear haunch swells wider than the front
        ((-33, -17.4), (-37, -17.2), (-40, -16.4)),
        ((-44.5, -15.6), (-47.6, -14.6), (-48.3, -11.5)),  # short ducktail corner
    ],
)

# Glass: a compact cabin set well ahead of the engine bay.
GLASS_PATH = ("M21,-7.6 C17,-9 10,-9.6 3,-9.4 C-4,-9.2 -9,-8.4 -12,-6.8 L-12,6.8 "
              "C-9,8.4 -4,9.2 3,9.4 C10,9.6 17,9 21,7.6 C23,3.5 23,-3.5 21,-7.6 Z")
ROOF_PATH = ("M13,-6 C9,-6.8 4,-7 0,-6.8 C-3,-6.6 -5,-6 -6,-5 L-6,5 C-5,6 -3,6.6 0,6.8 "
             "C4,7 9,6.8 13,6 C14,3 14,-3 13,-6 Z")


def wheel_art(cx, cy, r):
    """A tyre with a dished multi-spoke rim and a red brake caliper, drawn at radius 10 and scaled."""
    spokes = []
    for k in range(5):
        a = k * 72
        spokes.append(
            f'<g transform="rotate({a})">'
            '<path d="M0,-1.8 L0,-3.7" stroke="#d9e2f3" stroke-width="2" stroke-linecap="round"/>'
            '<path d="M0,-3.7 L-2,-5.9 M0,-3.7 L2,-5.9" stroke="#d9e2f3" stroke-width="1.35" '
            'stroke-linecap="round"/></g>'
        )
    return (
        f'<g transform="translate({fmt(cx)},{fmt(cy)}) scale({fmt(r / 10)})">'
        '<circle r="11.9" fill="#02040c" opacity="0.8"/>'                       # shadowed wheel arch
        '<circle r="10" fill="url(#carTyre)"/>'
        '<circle r="9.2" fill="none" stroke="#3a4152" stroke-width="0.5"/>'     # sidewall edge
        '<circle r="7.1" fill="url(#rimGrad)"/>'                                # rim ring
        '<circle r="6.1" fill="#0a0e19"/>'                                      # dish between spokes
        '<path d="M-2.6,4.7 A5.4,5.4 0 0 0 3.6,4.1" fill="none" stroke="#ff2e4d" '
        'stroke-width="1.3" stroke-linecap="round"/>'                           # caliper
        f'{"".join(spokes)}'
        '<circle r="2" fill="#eef2fb"/><circle r="0.8" fill="#3b4256"/>'
        '<path d="M-5.6,-3.6 A6.6,6.6 0 0 1 2.4,-6.2" fill="none" stroke="#ffffff" '
        'stroke-width="0.8" stroke-linecap="round" opacity="0.7"/>'             # glint on the rim
        '</g>'
    )


def deck_slats():
    """Engine-bay louvres: short light and dark lines across the rear deck."""
    out = []
    for x in (-20, -23.4, -26.8, -30.2, -33.6, -37):
        h = 7.4 + (-14 - x) / 27 * 2.2 - 1.3
        out.append(f'M{fmt(x)},{fmt(-h)} L{fmt(x)},{fmt(h)}')
    lines = " ".join(out)
    return (f'<path d="{lines}" stroke="#02092a" stroke-width="1.1" opacity="0.85"/>'
            f'<path d="{lines}" transform="translate(-1,0)" stroke="#5b92f0" stroke-width="0.45" '
            'opacity="0.7"/>')


def car_shapes(theme):
    shadow = THEMES[theme]["shadow"]
    wheels = "".join(wheel_art(x, y, r) for x, y, r in WHEELS)
    return (
        # Drop shadow under the chassis: the outline shifted down-right and blurred.
        f'<path d="{BODY_PATH}" transform="translate(2.5,4.5)" fill="#000" opacity="{shadow}" '
        'filter="url(#shadowBlur)"/>'
        # Paint: sculpted base gradient, a darker underside, and a front-to-rear tonal wash.
        f'<path d="{BODY_PATH}" fill="url(#carBody)"/>'
        f'<path d="{BODY_PATH}" fill="url(#carUnder)"/>'
        f'<path d="{BODY_PATH}" fill="url(#carLong)"/>'
        # Reflections live inside the body outline: a soft sky highlight on each shoulder, a
        # dark horizon band low on the flank, and a faint neon bounce from the trail below.
        '<g clip-path="url(#bodyClip)">'
        '<path d="M42,-7.6 C34,-11.6 20,-10.2 6,-10.2" fill="none" stroke="#ffffff" stroke-width="5" '
        'stroke-linecap="round" opacity="0.26" filter="url(#glow)"/>'
        '<path d="M-14,-12.6 C-22,-15.4 -34,-15.4 -42,-12" fill="none" stroke="#ffffff" stroke-width="4.4" '
        'stroke-linecap="round" opacity="0.22" filter="url(#glow)"/>'
        '<path d="M40,9 C30,12 16,10.4 4,10.4 C-8,10.4 -18,15 -30,15 C-40,14.6 -44,12.6 -46,10.6" '
        'fill="none" stroke="#020c3a" stroke-width="4" opacity="0.4" filter="url(#glow)"/>'
        '<path d="M45,6 C39,10.6 35,13.2 30,13.4 C23,13.4 18,10.6 12,10.6 M-12,12 C-18,15.4 -24,16.4 '
        '-31,16.4 C-37,16.4 -41,15.4 -44,13.4" fill="none" stroke="#ff5db0" stroke-width="1" '
        'stroke-linecap="round" opacity="0.4" filter="url(#softEdge)"/>'
        # Lighter centre ridge along the hood and the rear deck.
        '<path d="M47,-3.2 C38,-4 30,-4.6 21,-4.6 L21,4.6 C30,4.6 38,4 47,3.2 Z" fill="url(#carRidge)"/>'
        '</g>'
        # Outline.
        f'<path d="{BODY_PATH}" fill="none" stroke="#04113d" stroke-width="0.7"/>'
        # Panel seams: hood cut lines, cowl, door shut lines.
        '<path d="M43,-6.4 C36,-8.4 28,-10.2 21.6,-9.6 M43,6.4 C36,8.4 28,10.2 21.6,9.6" fill="none" '
        'stroke="#041044" stroke-width="0.6" opacity="0.7"/>'
        '<path d="M12,-11.6 C10.6,-9 10.4,-6 11,-1 M12,11.6 C10.6,9 10.4,6 11,1" fill="none" '
        'stroke="#041044" stroke-width="0.6" opacity="0.55"/>'
        # Front splitter slot and nose.
        '<path d="M48.4,-1.6 L45,-2.8 L45,2.8 L48.4,1.6 Z" fill="#03092a" opacity="0.85"/>'
        # Side intakes ahead of the rear haunches and the engine-bay deck with louvres.
        '<path d="M-3,-10.6 C-8,-11 -14,-12.6 -19,-14.6 L-19,-12.4 C-14,-11 -8,-9.4 -3,-9.2 Z '
        'M-3,10.6 C-8,11 -14,12.6 -19,14.6 L-19,12.4 C-14,11 -8,9.4 -3,9.2 Z" fill="#030b30" opacity="0.85"/>'
        '<path d="M-14,-7.4 L-41,-9.6 Q-43,-9.6 -43,-7.6 L-43,7.6 Q-43,9.6 -41,9.6 L-14,7.4 Z" '
        'fill="#06154a" opacity="0.78" stroke="#02092a" stroke-width="0.5"/>'
        f'{deck_slats()}'
        # Ducktail lip and its highlight.
        '<path d="M-43.8,-13.4 C-45,-6 -45,6 -43.8,13.4" fill="none" stroke="#02082a" stroke-width="0.9" opacity="0.8"/>'
        '<path d="M-45,-13 C-46.2,-6 -46.2,6 -45,13" fill="none" stroke="#9cc4ff" stroke-width="0.5" opacity="0.5"/>'
        # Wheels sit in shadowed arches at the four corners.
        f'{wheels}'
        # Dark windshield and cabin, with a slightly lighter roof panel.
        f'<path d="{GLASS_PATH}" fill="url(#carGlass)" stroke="#020717" stroke-width="0.6"/>'
        f'<path d="{ROOF_PATH}" fill="url(#carRoof)"/>'
        '<g clip-path="url(#glassClip)">'
        '<path d="M22,-9 L13,-9 L16.5,9 L23,9 Z" fill="#8ec2ff" opacity="0.22"/>'
        '<path d="M-6,-9 L-12,-9 L-12,9 L-8,9 Z" fill="#8ec2ff" opacity="0.14"/>'
        '</g>'
        '<path d="M20.6,-6.6 C22.4,-3 22.4,3 20.6,6.6" fill="none" stroke="#a9d6ff" stroke-width="0.7" opacity="0.7"/>'
        # Mirrors.
        '<path d="M18,-9.4 L15.2,-12.8 L13.6,-12.3 L15.4,-9 Z M18,9.4 L15.2,12.8 L13.6,12.3 L15.4,9 Z" '
        'fill="#1d4fc8" stroke="#04113d" stroke-width="0.4"/>'
        # Crisp specular streaks, a long one along the shoulder and a short one on the haunch,
        # each with a blurred twin for the softer reflected highlight.
        '<path d="M44,-8.4 C39,-11.2 35,-13.2 30,-13.2 C23,-13.2 18,-10.4 12,-10.2" fill="none" '
        'stroke="url(#carSpec)" stroke-width="1.1" stroke-linecap="round"/>'
        '<path d="M-10,-12.2 C-15,-14.6 -21,-16 -28,-16 C-34,-16 -38,-15.4 -41,-14.2" fill="none" '
        'stroke="url(#carSpec)" stroke-width="1" stroke-linecap="round" opacity="0.85"/>'
        '<path d="M40,-9.4 C34,-12.2 28,-11.8 20,-9.2" fill="none" stroke="#ffffff" stroke-width="2.6" '
        'stroke-linecap="round" opacity="0.3" filter="url(#softEdge)"/>'
        # Taillights: slim red bars at the rear corners, with a soft glow.
        '<path d="M-47.4,-5.6 L-47.4,-10.6 L-45.6,-12.8 L-45.2,-11.6 L-46.3,-9.8 L-46.3,-5.6 Z '
        'M-47.4,5.6 L-47.4,10.6 L-45.6,12.8 L-45.2,11.6 L-46.3,9.8 L-46.3,5.6 Z" fill="#ff2442" '
        'filter="url(#softEdge)"/>'
        '<path d="M-47.4,-5.6 L-47.4,-10.6 L-45.6,-12.8 L-45.2,-11.6 L-46.3,-9.8 L-46.3,-5.6 Z '
        'M-47.4,5.6 L-47.4,10.6 L-45.6,12.8 L-45.2,11.6 L-46.3,9.8 L-46.3,5.6 Z" fill="#ff6a7c"/>'
        # Headlights: bright slanted lamps with a soft halo.
        '<path d="M40.4,-9 L45.8,-5.8 L45.4,-4.2 L39.8,-7 Z M40.4,9 L45.8,5.8 L45.4,4.2 L39.8,7 Z" '
        'fill="#ffffff" opacity="0.9" filter="url(#glow)"/>'
        '<path d="M40.4,-9 L45.8,-5.8 L45.4,-4.2 L39.8,-7 Z M40.4,9 L45.8,5.8 L45.4,4.2 L39.8,7 Z" '
        'fill="#ffffff"/>'
    )


def light_cone(theme):
    """Two overlapping tapered beams ahead of the nose, soft at the edges."""
    return (
        '<g filter="url(#haze)">'
        '<path d="M45,-6.4 L142,-30 Q154,-12 148,-2 L45,-3.2 Z" fill="url(#lightCone)"/>'
        '<path d="M45,6.4 L142,30 Q154,12 148,2 L45,3.2 Z" fill="url(#lightCone)"/>'
        '<path d="M45,-5 L150,-22 Q164,0 150,22 L45,5 Z" fill="url(#lightCone)" opacity="0.7"/>'
        '</g>'
    )


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
    return f"<g>{move}<g>{rot}{light_cone(theme)}{car_shapes(theme)}</g></g>"


# ---------------------------------------------------------------- smoke

def drift_angle_at(frac):
    """Approximate drift angle (degrees) at a loop fraction; same easing shape as the SMIL spline."""
    mid = PASS_START + (PASS_END - PASS_START) / 2
    if frac <= PASS_START or frac >= PASS_END:
        return 0.0
    u = (frac - PASS_START) / (mid - PASS_START) if frac < mid else (PASS_END - frac) / (PASS_END - mid)
    eased = u * u * (3 - 2 * u)
    return DRIFT_DEG * eased


def smoke_layers(width, cy, theme):
    """Tire smoke: overlapping blurred puffs born just behind the rear wheels, merged into one bloom."""
    palette = THEMES[theme]
    rng = random.Random(PUFF_SEED)
    # Emit only while the car is on or near the canvas.
    x0, x1 = car_span(width)
    t_in = PASS_START + (PASS_END - PASS_START) * ((-30 - x0) / (x1 - x0))
    t_out = PASS_START + (PASS_END - PASS_START) * ((width + 10 - x0) / (x1 - x0))
    sources = [(-SMOKE_BEHIND, WHEELS[2][1], PUFF_PER_WHEEL),
               (-SMOKE_BEHIND, WHEELS[3][1], PUFF_PER_WHEEL),
               (-SMOKE_BEHIND - 3, 0.0, PUFF_CENTER)]
    out = []
    for lx, ly, count in sources:
        for i in range(count):
            born = t_in + (t_out - t_in) * (i + rng.uniform(0.0, 1.0)) / count
            ang = math.radians(drift_angle_at(born))
            px = lx + rng.uniform(-2.5, 2.5)
            py = ly + rng.uniform(-5, 5)
            # Rotate the emission point into the world, following the car's yaw.
            sx = car_center_at(born, width) + px * math.cos(ang) - py * math.sin(ang)
            sy = cy + px * math.sin(ang) + py * math.cos(ang)
            scale = rng.uniform(0.85, 1.2)
            dx = rng.uniform(-16, -7)       # the cloud is left behind as the car moves on
            dy = rng.uniform(-6, 6)
            r0, r1 = PUFF_R0 * scale, PUFF_R1 * scale
            times = [0, born, born + PUFF_LIFE, 1]
            anims = (
                animate("r", [r0, r0, r1, r1], times)
                + animate("cx", [sx, sx, sx + dx, sx + dx], times)
                + animate("cy", [sy, sy, sy + dy, sy + dy], times)
                + animate("opacity", [0, 0, palette["smoke_peak"], palette["smoke_peak"] * 0.55, 0, 0],
                          [0, born, born + PUFF_LIFE * 0.12, born + PUFF_LIFE * 0.5,
                           born + PUFF_LIFE, 1])
            )
            out.append(
                f'<circle cx="{fmt(sx)}" cy="{fmt(sy)}" r="{fmt(r0)}" '
                f'fill="url(#smoke{theme})" opacity="0">{anims}</circle>'
            )
    # A light blur on each puff plus a wider blur on the group fuses them into a milky volume.
    return f'<g filter="url(#smokeWide)"><g filter="url(#smokeSoft)">{"".join(out)}</g></g>'


# ---------------------------------------------------------------- defs and document

def defs(theme, width, height):
    palette = THEMES[theme]
    smoke = palette["smoke"]
    return (
        "<defs>"
        '<radialGradient id="bgDark" cx="0.5" cy="0.45" r="0.75">'
        '<stop offset="0" stop-color="#1d1a3e"/><stop offset="0.6" stop-color="#0d0b1f"/>'
        '<stop offset="1" stop-color="#07060f"/></radialGradient>'
        # Paint: bright crown on the lit shoulder, rolling into deep shade on the far flank.
        '<linearGradient id="carBody" x1="0" y1="0" x2="0" y2="1">'
        '<stop offset="0" stop-color="#1c4bb8"/><stop offset="0.14" stop-color="#63a6ff"/>'
        '<stop offset="0.34" stop-color="#4a90fa"/><stop offset="0.5" stop-color="#3373ec"/>'
        '<stop offset="0.7" stop-color="#2255c8"/><stop offset="0.9" stop-color="#112f86"/>'
        '<stop offset="1" stop-color="#0a1f66"/></linearGradient>'
        # Darker underside along the lower flank.
        '<linearGradient id="carUnder" x1="0" y1="0" x2="0" y2="1">'
        '<stop offset="0.55" stop-color="#010622" stop-opacity="0"/>'
        '<stop offset="0.9" stop-color="#010622" stop-opacity="0.5"/>'
        '<stop offset="1" stop-color="#010622" stop-opacity="0.75"/></linearGradient>'
        # Tonal wash: a little brighter toward the nose, darker at the tail.
        '<linearGradient id="carLong" x1="0" y1="0" x2="1" y2="0">'
        '<stop offset="0" stop-color="#000a30" stop-opacity="0.28"/>'
        '<stop offset="0.45" stop-color="#000a30" stop-opacity="0"/>'
        '<stop offset="1" stop-color="#bcd8ff" stop-opacity="0.16"/></linearGradient>'
        '<linearGradient id="carRidge" x1="0" y1="0" x2="0" y2="1">'
        '<stop offset="0" stop-color="#a8cfff" stop-opacity="0"/>'
        '<stop offset="0.35" stop-color="#a8cfff" stop-opacity="0.4"/>'
        '<stop offset="1" stop-color="#a8cfff" stop-opacity="0"/></linearGradient>'
        '<linearGradient id="carSpec" x1="0" y1="0" x2="1" y2="0">'
        '<stop offset="0" stop-color="#ffffff" stop-opacity="0.15"/>'
        '<stop offset="0.5" stop-color="#ffffff" stop-opacity="1"/>'
        '<stop offset="1" stop-color="#ffffff" stop-opacity="0.2"/></linearGradient>'
        '<linearGradient id="carGlass" x1="0" y1="0" x2="1" y2="1">'
        '<stop offset="0" stop-color="#16316c"/><stop offset="0.5" stop-color="#050f28"/>'
        '<stop offset="1" stop-color="#010309"/></linearGradient>'
        '<linearGradient id="carRoof" x1="0" y1="0" x2="0" y2="1">'
        '<stop offset="0" stop-color="#2a5cc4"/><stop offset="1" stop-color="#0b2060"/></linearGradient>'
        '<radialGradient id="carTyre" cx="0.5" cy="0.5" r="0.5">'
        '<stop offset="0.6" stop-color="#05060a"/><stop offset="1" stop-color="#1c202b"/></radialGradient>'
        '<linearGradient id="rimGrad" x1="0" y1="0" x2="1" y2="1">'
        '<stop offset="0" stop-color="#f4f7ff"/><stop offset="0.5" stop-color="#8f9bb5"/>'
        '<stop offset="1" stop-color="#4a5368"/></linearGradient>'
        f'<clipPath id="bodyClip"><path d="{BODY_PATH}"/></clipPath>'
        f'<clipPath id="glassClip"><path d="{GLASS_PATH}"/></clipPath>'
        '<linearGradient id="lightCone" x1="0" y1="0" x2="1" y2="0">'
        f'<stop offset="0" stop-color="{palette["cone"]}" stop-opacity="{palette["cone_peak"]}"/>'
        f'<stop offset="0.5" stop-color="{palette["cone"]}" stop-opacity="{fmt(palette["cone_peak"] * 0.4)}"/>'
        f'<stop offset="1" stop-color="{palette["cone"]}" stop-opacity="0"/></linearGradient>'
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
        '<filter id="haze" x="-10%" y="-60%" width="150%" height="220%">'
        '<feGaussianBlur stdDeviation="5"/></filter>'
        # Smoke filters cover the whole canvas, so animated puffs never clip.
        f'<filter id="smokeSoft" filterUnits="userSpaceOnUse" x="-120" y="0" width="{width + 240}" height="{height}">'
        '<feGaussianBlur stdDeviation="3.5"/></filter>'
        f'<filter id="smokeWide" filterUnits="userSpaceOnUse" x="-120" y="0" width="{width + 240}" height="{height}">'
        '<feGaussianBlur stdDeviation="5"/></filter>'
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

    base = base_grid(ncols, palette["base"])
    trail = []
    for col in range(ncols):
        for row in range(ROWS):
            day = grid.get((col, row))
            if day is not None and day.is_lit():
                color = NEON_BY_LEVEL[min(max(day.level, 1), 4)]
                trail.append(trail_cell(col, row, color, 1.0, width))
            else:
                # Days without contributions never get bright neon. They glow dim behind the car.
                trail.append(trail_cell(col, row, palette["empty_color"], palette["empty_peak"], width))

    layers = (
        base
        + "".join(trail)
        + smoke_layers(width, cy, theme)
        + car_layers(width, cy, theme)
    )
    desc = ("A blue sports car drives across a contribution graph. Each day with contributions "
            "lights up in neon as the car passes, empty days glow faintly, and the rear tires "
            "throw a cloud of smoke.")
    return svg_document(width, height, theme, "Car contribution animation", desc, layers)


# ---------------------------------------------------------------- CLI

def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--user", default="RamSuryaCH")
    parser.add_argument("--outdir", default="dist")
    args = parser.parse_args(argv)

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
