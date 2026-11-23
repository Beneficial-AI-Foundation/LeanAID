"""Write the UPPAAL models of the abstraction to uppaal/model/generated/.

The checks in `uppaal/queries/check.py` build each model in memory and write it to the
ignored folder `uppaal/out/`. This script writes the same models, without witness flags
and without mutations, so that they can be opened in the UPPAAL GUI. It adds only layout
coordinates to the locations, in a grid. Next to each model, a `.q` file holds the
queries of `check.py` that run on that model without witness flags or mutations.

Usage: python3 -I uppaal/model/export.py
"""
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "queries"))
import check as C  # noqa: E402
import model as M  # noqa: E402

OUT = HERE / "generated"
BASE = ("free", "relaxed", "contract", "nopump", "nobolus")
EXT = tuple(f"{e}-{p}" for e in M.U5_EXTS for p in ("pump", "bolus"))
COLS, DX, DY = 4, 220, 160


def with_layout(xml):
    """Give the locations of each template grid coordinates, in the order of the file."""
    out, i = [], 0
    for line in xml.splitlines():
        if line.startswith("<template>"):
            i = 0
        m = re.match(r'<location id="([^"]+)">', line)
        if m:
            x, y = (i % COLS) * DX, (i // COLS) * DY
            line = line.replace(m.group(0), f'<location id="{m.group(1)}" x="{x}" y="{y}">', 1)
            i += 1
        out.append(line)
    return "\n".join(out) + "\n"


def main():
    for name in BASE + EXT:
        path = OUT / ("extensions" if name in EXT else "") / f"{name}.xml"
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = HERE.parent / "out" / f"export-{name}.xml"
        tmp.parent.mkdir(exist_ok=True)
        M.write_uppaal(C.build(name, (), False), tmp)
        path.write_text(with_layout(tmp.read_text()))
        queries = [q for (qid, _i, kind, model, muts, q, *_r) in C.RUN
                   if model == name and not muts and kind != "witness"]
        text = "".join(q + "\n" for q in queries) or (
            "// check.py runs no query on this model without witness flags or mutations\n")
        path.with_suffix(".q").write_text(text)
        print(path.relative_to(HERE.parent), len(queries), "queries")


if __name__ == "__main__":
    main()
