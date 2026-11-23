"""Shrink a Munta network while Munta still reaches a formula (U4 diagnosis): remove
edges of every automaton one by one; drop locations without edges."""
import copy, json, subprocess, sys
src, dst = sys.argv[1], sys.argv[2]
d = json.load(open(src))
CAP = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=16G", "-p", "MemorySwapMax=0"]
def reaches(dd):
    json.dump(dd, open("/tmp/smbtest/shrink_try.muntax", "w"))
    try:
        out = subprocess.run(CAP + ["vendor/munta-build/munta.sh", "-m", "/tmp/smbtest/shrink_try.muntax"],
                             capture_output=True, text=True, timeout=900).stdout
    except subprocess.TimeoutExpired:
        return False
    return "Property is satisfied!" in out
assert reaches(d)
for ai in range(len(d["automata"])):
    i = 0
    while i < len(d["automata"][ai]["edges"]):
        d2 = copy.deepcopy(d)
        del d2["automata"][ai]["edges"][i]
        if reaches(d2):
            d = d2
        else:
            i += 1
    print(d["automata"][ai]["name"], "edges left:", len(d["automata"][ai]["edges"]), flush=True)
json.dump(d, open(dst, "w"), indent=1)
for a in d["automata"]:
    names = {n["id"]: n["name"] for n in a["nodes"]}
    print(a["name"], "committed", [names[c] for c in a["committed"]])
    for e in a["edges"]:
        print(" ", names[e["source"]], "->", names[e["target"]], "|", e["guard"][:150], "|", e["label"], "|", e["update"])
