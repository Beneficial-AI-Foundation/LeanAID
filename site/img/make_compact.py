"""Compact dark diagrams for one slide: site/img/compact/.

Four panels, each 940 x 420, made to sit in a 2 x 2 grid on a 1920-wide dark slide
(1920 x 880 below the title). Also writes all.png, the four panels already arranged.
Transparent backgrounds; rendered at 2x with rsvg-convert.

Run: python3 site/img/make_compact.py
"""
import os
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "compact")
W, H = 940, 420

GREEN, GREEN_FILL = "#3ee08f", "#0c2a1d"
ORANGE, ORANGE_FILL = "#ff9f43", "#2e1a08"
TEXT, MUTED = "#eef2f6", "#a7b0bd"
BOX, STROKE, LINE = "#10151c", "#3a4350", "#7d8794"

STYLE = f"""
  <defs>
    <marker id="head" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="8" markerHeight="8" orient="auto-start-reverse">
      <path d="M0 0 L10 5 L0 10 z" fill="{LINE}"/>
    </marker>
    <filter id="glow" x="-20%" y="-20%" width="140%" height="140%">
      <feGaussianBlur in="SourceAlpha" stdDeviation="6" result="b"/>
      <feFlood flood-color="{GREEN}" flood-opacity="0.45"/>
      <feComposite in2="b" operator="in" result="g"/>
      <feMerge><feMergeNode in="g"/><feMergeNode in="SourceGraphic"/></feMerge>
    </filter>
  </defs>
  <style>
    text {{ font-family: Inter, "Helvetica Neue", Arial, sans-serif; fill: {TEXT}; }}
    .box {{ fill: {BOX}; stroke: {STROKE}; stroke-width: 2; }}
    .main {{ fill: {GREEN_FILL}; stroke: {GREEN}; stroke-width: 2.5; filter: url(#glow); }}
    .hot {{ fill: {BOX}; stroke: {ORANGE}; stroke-width: 2; }}
    .h {{ font-size: 28px; font-weight: 700; fill: {GREEN}; letter-spacing: 0.5px; }}
    .t {{ font-size: 26px; font-weight: 700; }}
    .tg {{ font-size: 26px; font-weight: 700; fill: {GREEN}; }}
    .s {{ font-size: 20px; fill: {MUTED}; }}
    .i {{ font-size: 22px; }}
    .n {{ font-size: 28px; font-weight: 700; fill: {GREEN}; }}
    .nm {{ font-size: 28px; font-weight: 700; fill: {MUTED}; }}
    .no {{ font-size: 28px; font-weight: 700; fill: {ORANGE}; }}
    .big {{ font-size: 40px; font-weight: 700; fill: {GREEN}; }}
    .bigo {{ font-size: 34px; font-weight: 700; fill: {ORANGE}; }}
    .pill {{ font-size: 18px; font-weight: 700; }}
    .line {{ stroke: {LINE}; stroke-width: 2.5; fill: none; }}
  </style>"""


def svg(body, label, w=W, h=H):
    return (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="-10 -4 {w + 20} {h + 14}" width="{w + 20}" height="{h + 14}" '
            f'role="img" aria-label="{label}">{STYLE}\n{body}\n</svg>\n')


def box(x, y, w, h, title, sub=None, main=False):
    cx = x + w / 2
    cls, tcls = ("main", "tg") if main else ("box", "t")
    if sub:
        return (f'  <rect class="{cls}" x="{x}" y="{y}" width="{w}" height="{h}" rx="12"/>\n'
                f'  <text class="{tcls}" x="{cx}" y="{y + h/2 - 4}" text-anchor="middle">{title}</text>\n'
                f'  <text class="s" x="{cx}" y="{y + h/2 + 24}" text-anchor="middle">{sub}</text>\n')
    return (f'  <rect class="{cls}" x="{x}" y="{y}" width="{w}" height="{h}" rx="12"/>\n'
            f'  <text class="{tcls}" x="{cx}" y="{y + h/2 + 9}" text-anchor="middle">{title}</text>\n')


def arrow(d):
    return f'  <path class="line" d="{d}" marker-end="url(#head)"/>\n'


def text(x, y, cls, s, anchor="start"):
    return f'  <text class="{cls}" x="{x}" y="{y}" text-anchor="{anchor}">{s}</text>\n'


# 1. Automated insulin delivery -------------------------------------------------
def aid():
    b = text(0, 30, "h", "Automated insulin delivery (AID)")
    b += text(940, 30, "s", "every 5 minutes", "end")
    b += box(0, 60, 220, 90, "Sensor", "reads glucose")
    b += box(350, 60, 240, 90, "Controller", "decides the dose", main=True)
    b += box(720, 60, 220, 90, "Pump", "delivers insulin")
    b += arrow("M220 105 H342") + text(285, 95, "s", "glucose", "middle")
    b += arrow("M590 105 H712") + text(655, 95, "s", "insulin", "middle")
    b += arrow("M470 212 V158") + text(482, 190, "s", "runs")
    b += '  <rect class="main" x="190" y="214" width="560" height="150" rx="12"/>\n'
    b += text(470, 252, "tg", "oref0", "middle")
    b += f'  <line x1="214" y1="270" x2="726" y2="270" stroke="{GREEN}" stroke-opacity="0.35" stroke-width="2"/>\n'
    b += text(220, 308, "i", "•  open source") + text(490, 308, "i", "•  JavaScript")
    b += text(220, 344, "i", "•  do-it-yourself systems") + text(490, 344, "i", "•  not checked by the FDA")
    return svg(b, "Automated insulin delivery: every 5 minutes a sensor sends glucose to the controller, "
                  "which sends an insulin dose to the pump. The controller runs oref0: open source, JavaScript, "
                  "used in do-it-yourself systems, not checked by the FDA.", h=370)


# 2. What we did ----------------------------------------------------------------
def did():
    b = text(0, 30, "h", "What we did")
    b += box(0, 52, 230, 84, "oref0", "JavaScript, original")
    b += box(355, 52, 230, 84, "lean-oref0", "same logic, in Lean", main=True)
    b += box(710, 52, 230, 84, "Binary", "compiled via C")
    b += arrow("M230 94 H347") + text(292, 84, "s", "AI agent", "middle")
    b += arrow("M585 94 H702") + text(646, 84, "s", "compile", "middle")
    b += '  <path class="line" d="M470 136 V164 M230 164 H710"/>\n'
    b += arrow("M230 164 V178") + arrow("M710 164 V178")
    b += text(458, 156, "s", "AI agent proves", "end")
    # left card
    b += '  <rect class="main" x="0" y="186" width="460" height="232" rx="12"/>\n'
    b += text(230, 222, "tg", "Safety rules", "middle")
    b += text(230, 250, "s", "from FDA research on insulin pumps", "middle")
    rows = [("n", "10", "proved for every valid input"), ("n", "4", "proved in part"),
            ("no", "1", "does not hold: a finding"), ("nm", "6", "still to prove")]
    for k, (c, num, lab) in enumerate(rows):
        y = 290 + k * 34
        b += text(70, y, c, num, "end") + text(86, y - 2, "i", lab)
    # right card
    b += '  <rect class="main" x="480" y="186" width="460" height="232" rx="12"/>\n'
    b += text(710, 222, "tg", "oref0’s tests, generalized", "middle")
    b += text(710, 250, "s", "116 tests; 59 state a general rule", "middle")
    for k, (c, num, lab) in enumerate([("n", "52", "proved for every valid input"), ("nm", "7", "still to prove")]):
        y = 290 + k * 34
        b += text(550, y, c, num, "end") + text(566, y - 2, "i", lab)
    return svg(b, "What we did: an AI agent rewrote oref0 from JavaScript into lean-oref0, compiled to a binary via C, "
                  "and proved theorems. Safety rules from FDA research on insulin pumps: 10 proved for every valid input, "
                  "4 in part, 1 does not hold, 6 still to prove. oref0's tests generalized: of 116 tests, 59 state a "
                  "general rule; 52 proved for every valid input, 7 still to prove.")


# 3. Tested against oref0 --------------------------------------------------------
def tested():
    b = text(0, 30, "h", "Tested against oref0")
    b += box(0, 76, 190, 60, "same input")
    b += box(300, 52, 220, 52, "oref0")
    b += box(300, 112, 220, 52, "lean-oref0", main=True)
    b += arrow("M190 98 L292 80") + arrow("M190 114 L292 136")
    b += text(560, 122, "t", "same output?")
    b += text(560, 152, "s", "every number, word for word")
    tiles = [("oref0’s own test cases", "148", "of 148 identical"),
             ("random inputs", "100,000", "of 100,000 identical"),
             ("30 virtual patients, 12 h", "220,608", "of 220,608 decisions identical")]
    for k, (lab, big, sub) in enumerate(tiles):
        x = k * 320
        w = 300
        b += f'  <rect class="box" x="{x}" y="196" width="{w}" height="170" rx="12"/>\n'
        b += text(x + 20, 234, "s", lab)
        b += text(x + 20, 292, "big", big)
        b += text(x + 20, 330, "s", sub)
    return svg(b, "Tested against oref0: the same input goes to oref0 and lean-oref0. oref0's own test cases: 148 of 148 "
                  "identical. Random inputs: 100,000 of 100,000 identical. 30 virtual patients over 12 hours of computing: "
                  "220,608 of 220,608 decisions identical.", h=370)


# 4. What we found ---------------------------------------------------------------
def found():
    b = text(0, 30, "h", "What we found in oref0")
    b += text(940, 30, "s", "proved in Lean, reproduced in JavaScript", "end")
    cards = [
        ("medium", ["Old reading", "treated as new"], ["No timestamp: its age", "is NaN, never too old"],
         "NaN > 12", "is false in JavaScript"),
        ("medium", ["Missing setting", "turns the limit off"], ["No max basal: the limit", "uses a missing value"],
         "min(…, NaN)", "is NaN: no cap at all"),
        ("low", ["Rounding goes", "over the limit"], ["Capped first, then", "rounded up to a step"],
         "0.83 → 0.85", "U/h, above the limit"),
    ]
    for k, (sev, title, body, big, cap) in enumerate(cards):
        x = k * 320
        b += f'  <rect class="{"hot" if sev == "medium" else "box"}" x="{x}" y="52" width="300" height="316" rx="12"/>\n'
        fg, bg, pw = (ORANGE, ORANGE_FILL, 104) if sev == "medium" else (MUTED, "#222a33", 70)
        b += f'  <rect x="{x + 20}" y="70" width="{pw}" height="28" rx="14" fill="{bg}"/>\n'
        b += f'  <text class="pill" x="{x + 34}" y="90" style="fill:{fg}">{sev}</text>\n'
        b += text(x + 20, 136, "t", title[0]) + text(x + 20, 166, "t", title[1])
        b += text(x + 20, 204, "s", body[0]) + text(x + 20, 230, "s", body[1])
        b += text(x + 20, 290, "bigo", big)
        b += text(x + 20, 326, "s", cap)
    b += text(470, 400, "s", "Severity is our estimate: medium = large overdose possible, but apps normally supply the data.", "middle")
    return svg(b, "What we found in oref0, proved in Lean and reproduced in JavaScript. Medium: an old reading with no "
                  "timestamp is treated as new, because its age is NaN and NaN > 12 is false. Medium: a missing max basal "
                  "setting turns the limit off, because min with NaN is NaN. Low: rounding goes over the limit, "
                  "0.83 becomes 0.85 U/h. Severity is our estimate.")


def render(name, content):
    path = os.path.join(OUT, name + ".svg")
    with open(path, "w") as f:
        f.write(content)
    subprocess.run(["rsvg-convert", "-z", "2", path, "-o", os.path.join(OUT, name + ".png")], check=True)
    return content


def main():
    os.makedirs(OUT, exist_ok=True)
    parts = {"1-aid": aid(), "2-did": did(), "3-tested": tested(), "4-found": found()}
    for name, content in parts.items():
        render(name, content)
    # composite: 2 x 2 grid, 1920 x 880
    import re
    cells = [(0, 0), (1040, 0), (0, 460), (1040, 460)]
    inner = ""
    defs_done = False
    for (x, y), content in zip(cells, parts.values()):
        m = re.search(r'viewBox="0 0 (\d+) (\d+)"', content)
        body = content[content.index("</style>") + len("</style>"):content.rindex("</svg>")]
        inner += f'<g transform="translate({x} {y})">{body}</g>\n'
    allsvg = (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="-12 -4 2004 898" width="2004" height="898" '
              f'role="img" aria-label="LeanAID in four diagrams">{STYLE}\n{inner}</svg>\n')
    render("all", allsvg)
    print("wrote", ", ".join(list(parts) + ["all"]))


if __name__ == "__main__":
    main()
