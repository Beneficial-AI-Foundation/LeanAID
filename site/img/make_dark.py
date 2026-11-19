"""Make dark-slide versions of the diagrams: site/img/dark/<name>.png.

The light SVGs in site/img are the source. This swaps the palette for one that reads on
a black slide (light text, dark boxes, green accent), drops the background and the
diagram's own heading (the slide has a title), adds a soft glow to the accent boxes,
and renders a transparent PNG at 2x with rsvg-convert.

Run: python3 site/img/make_dark.py
"""
import os
import re
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "dark")
NAMES = ["loop", "loop-vertical", "did", "tested", "found"]
# space freed at the top once the heading is gone: crop it (viewBox top, in SVG units)
CROP_TOP = {"loop": 84, "loop-vertical": 96, "did": 88, "tested": 68, "found": 60}

GREEN = "#3ee08f"
GREEN_FILL = "#0c2a1d"
ORANGE = "#ff9f43"
ORANGE_FILL = "#2e1a08"
TEXT = "#eef2f6"
MUTED = "#a7b0bd"
BOX = "#10151c"
STROKE = "#3a4350"
LINE = "#7d8794"

SWAPS = [
    # order matters: specific before generic
    ("fill: #e0f2ef; stroke: #0f766e", f"fill: {GREEN_FILL}; stroke: {GREEN}; filter: url(#glow)"),
    ("fill: #fdf3e7; stroke: #b45309", f"fill: {ORANGE_FILL}; stroke: {ORANGE}"),
    ("fill: #ffffff; stroke: #c9ccd1", f"fill: {BOX}; stroke: {STROKE}"),
    ("fill: #1b1d21", f"fill: {TEXT}"),
    ("fill: #5e636e", f"fill: {MUTED}"),
    ("fill:#5e636e", f"fill:{MUTED}"),
    ("fill: #0f766e", f"fill: {GREEN}"),
    ("fill: #b45309", f"fill: {ORANGE}"),
    ("fill:#b45309", f"fill:{ORANGE}"),
    ('fill="#fdf3e7"', f'fill="{ORANGE_FILL}"'),
    ('fill="#eceef0"', 'fill="#222a33"'),
    ("stroke: #5e636e", f"stroke: {LINE}"),
    ('fill="#5e636e"', f'fill="{LINE}"'),
    ('stroke="#0f766e"', f'stroke="{GREEN}"'),
    ('stroke="#c9ccd1"', f'stroke="{STROKE}"'),
]

GLOW = f"""<filter id="glow" x="-20%" y="-20%" width="140%" height="140%">
      <feGaussianBlur in="SourceAlpha" stdDeviation="7" result="b"/>
      <feFlood flood-color="{GREEN}" flood-opacity="0.45"/>
      <feComposite in2="b" operator="in" result="g"/>
      <feMerge><feMergeNode in="g"/><feMergeNode in="SourceGraphic"/></feMerge>
    </filter>"""


def convert(svg: str, top: int = 0) -> str:
    for a, b in SWAPS:
        svg = svg.replace(a, b)
    # remove the background rect (either form) and the diagram's heading lines
    svg = re.sub(r'\s*<rect (id="bg" )?width="\d+" height="\d+" fill="#fbfbfa"/>', "", svg)
    svg = re.sub(r'\s*<text class="heading"[^>]*>.*?</text>', "", svg)
    # crop the top
    if top:
        m = re.search(r'viewBox="0 0 (\d+) (\d+)" width="\d+" height="\d+"', svg)
        w, h = int(m.group(1)), int(m.group(2))
        svg = svg.replace(m.group(0), f'viewBox="0 {top} {w} {h - top}" width="{w}" height="{h - top}"', 1)
    # glow filter
    if "<defs>" in svg:
        svg = svg.replace("<defs>", "<defs>\n    " + GLOW, 1)
    else:
        svg = svg.replace("  <style>", "  <defs>\n    " + GLOW + "\n  </defs>\n  <style>", 1)
    return svg


def main():
    os.makedirs(OUT, exist_ok=True)
    for name in NAMES:
        with open(os.path.join(HERE, name + ".svg")) as f:
            svg = convert(f.read(), CROP_TOP.get(name, 0))
        path = os.path.join(OUT, name + ".svg")
        with open(path, "w") as f:
            f.write(svg)
        subprocess.run(["rsvg-convert", "-z", "2", path, "-o", os.path.join(OUT, name + ".png")], check=True)
        print("wrote", os.path.relpath(path, HERE))


if __name__ == "__main__":
    main()
