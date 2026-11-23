"""Shrink the lowered nopump network while Munta still reaches err1 == 1 (U4 diagnosis).
Removes Controller edges in halves, then one by one."""
import copy, json, subprocess, sys
src = sys.argv[1]
d = json.load(open(src))
d["formula"] = "E<> (err1 == 1)"
CAP = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=16G", "-p", "MemorySwapMax=0"]
def reaches(dd):
    json.dump(dd, open("/tmp/smbtest/shrink_try.muntax", "w"))
    try:
        out = subprocess.run(CAP + ["vendor/munta-build/munta.sh", "-m", "/tmp/smbtest/shrink_try.muntax"],
                             capture_output=True, text=True, timeout=900).stdout
    except subprocess.TimeoutExpired:
        return False
    return "Property is satisfied!" in out
ci = next(i for i, a in enumerate(d["automata"]) if a["name"] == "Controller")
assert reaches(d), "Munta does not reach err1 on the start network"
n = 2
while len(d["automata"][ci]["edges"]) > 1:
    edges = d["automata"][ci]["edges"]
    k = max(1, len(edges) // n)
    removed = False
    for s in range(0, len(edges), k):
        d2 = copy.deepcopy(d)
        d2["automata"][ci]["edges"] = edges[:s] + edges[s + k:]
        if d2["automata"][ci]["edges"] and reaches(d2):
            d = d2; removed = True; print("kept removal, edges left:", len(d2["automata"][ci]["edges"]), flush=True)
            break
    if not removed:
        if k == 1:
            break
        n *= 2
json.dump(d, open("uppaal/u4/p1_munta_minimal.muntax", "w"), indent=1)
print("Controller edges left:")
for e in d["automata"][ci]["edges"]:
    print(" ", e["guard"], "|", e["label"], "|", e["update"])
