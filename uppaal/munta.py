"""Translate the UPPAAL model for Munta and run Munta (work item U4).

`lower(model)` turns a model of `model.py` into one that uses only the features that
Munta accepts (uppaal/u0b/README.md, "Input limits" and "Effect on the plan"):

  - each `select` becomes one edge for each value,
  - a copy `x = y` of a variable becomes one edge for each value k of y, with the
    guard `y == k` and the update `x = k`,
  - the pump location `Temp` becomes one location `Temp_d` for each duration d, so
    that every clock bound (`y <= d * 60`, `y < d * 60`) is a constant,
  - a guard that is a disjunction with a clock atom becomes one edge for each
    disjunct,
  - a variable with a non-zero initial value gets it on a first committed edge,
    because Munta starts every integer at 0. The `Step` template starts in a new
    committed location `Init`,
  - the local clock `y` of `Pump` becomes a global clock,
  - every location with an edge gets a self-loop that never fires: its guard has a contradictory
    data atom and every clock at its largest constant. Munta computes the clock
    ceilings of each location (`local_ceiling`), and on some graphs it gives 0 where
    a larger constant is reachable. Its own precondition "Ceiling resets" then
    rejects the network (uppaal/u4/ceiling_minimal.muntax). With the self-loops, every
    location has the largest constants, so the precondition holds. The self-loops
    change no behavior, and UPPAAL checks the same lowered network.

The lowered model is written both as UPPAAL XML (`model.write_uppaal`) and as Munta
JSON (`write_munta`), so the two tools check the same network. Munta needs the
variables in the order of its own numbering; `munta_order` gets it from the
diagnostic checker of `munta_order.sh`.
"""

import ast
import keyword
import itertools
import json
import re
import subprocess
from dataclasses import replace

import model as M

IDENT = r"[A-Za-z_]\w*"


# ---------------------------------------------------------------- declarations

def parse_decls(lines):
    """(ints, clocks, chans): ints maps a name to (lo, hi, init)."""
    ints, clocks, chans = {}, [], []
    for line in (x for block in lines for x in block.splitlines()):
        code = line.split("//")[0]
        for stmt in [s.strip() for s in code.split(";") if s.strip()]:
            m = re.fullmatch(r"int\[(-?\d+),(-?\d+)\] (\w+)(?: = (-?\d+))?", stmt)
            if m:
                ints[m[3]] = (int(m[1]), int(m[2]), int(m[4] or 0))
            elif stmt.startswith("clock "):
                clocks += [c.strip() for c in stmt[6:].split(",")]
            elif stmt.startswith("chan "):
                chans += [c.strip() for c in stmt[5:].split(",")]
            else:
                raise ValueError(f"declaration not understood: {stmt!r}")
    return ints, clocks, chans


def write_decls(ints, clocks, chans):
    out = [f"int[{lo},{hi}] {n}{f' = {i}' if i else ''};" for n, (lo, hi, i) in ints.items()]
    if clocks:
        out.append("clock " + ", ".join(clocks) + ";")
    if chans:
        out.append("chan " + ", ".join(chans) + ";")
    return out


# ---------------------------------------------------------------- text helpers

def subst(text, values):
    """Replace whole identifiers in `text` by values."""
    if not text:
        return text
    return re.sub(rf"\b({IDENT})\b", lambda m: str(values.get(m[1], m[1])), text)


def split_top(text, op):
    """Split `text` at `op` outside parentheses."""
    parts, depth, cur, i = [], 0, "", 0
    while i < len(text):
        c = text[i]
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        if depth == 0 and text.startswith(op, i):
            parts.append(cur)
            cur, i = "", i + len(op)
            continue
        cur += c
        i += 1
    return parts + [cur]


def strip_parens(text):
    t = text.strip()
    while t.startswith("(") and t.endswith(")"):
        depth = 0
        for i, c in enumerate(t):
            depth += c == "("
            depth -= c == ")"
            if depth == 0 and i < len(t) - 1:
                return t
        t = t[1:-1].strip()
    return t


def fold_constants(text):
    """Evaluate `(a * b)` of two integer constants."""
    prev = None
    while prev != text:
        prev = text
        text = re.sub(r"\((-?\d+) \* (-?\d+)\)", lambda m: str(int(m[1]) * int(m[2])), text)
    return text


def updates(text):
    return [u.strip() for u in text.split(",") if u.strip()] if text else []


# ---------------------------------------------------------------- lowering

def expand_selects(t, reps=None):
    """One edge for each value of the select variables. `reps` maps a variable x to
    a function that gives the representative of a value (see `value_classes`); a
    select variable whose only use is `x = v` takes only the representatives."""
    out = []
    for e in t.edges:
        if not e.select:
            out.append(e)
            continue
        names, ranges = [], []
        decls = re.findall(r"(\w+) : int\[(-?\d+),(-?\d+)\]", e.select)
        if not decls:
            raise ValueError(f"select not understood: {e.select!r}")
        for n, lo, hi in decls:
            names.append(n)
            vals = range(int(lo), int(hi) + 1)
            target = [u.split(" = ")[0] for u in updates(e.update) if re.fullmatch(rf"\w+ = {n}", u)]
            g_atoms = atoms_on(n, e.guard or "")
            uses = len(re.findall(rf"\b{n}\b", e.guard or "")) + len(re.findall(rf"\b{n}\b", e.update))
            if reps and len(target) == 1 and target[0] in reps and uses == 1 + len(g_atoms):
                # one value per class of the target, refined by the atoms on n in
                # this guard
                atoms = reps[target[0]] + g_atoms
                firsts = {}
                for k in vals:
                    firsts.setdefault(tuple(OPS[op](k, c) for op, c in atoms), k)
                vals = sorted(firsts.values())
            ranges.append(vals)
        for vals in itertools.product(*ranges):
            env = dict(zip(names, vals))
            g = subst(e.guard, env)
            if g:
                c = simplify(to_ast(g))     # constant atoms evaluated
                if c is False:
                    continue
                g = "" if c is True else render(c)
            out.append(replace(e, select="", guard=g, update=subst(e.update, env)))
    t.edges = out


def expand_copies(t, ints):
    """`x = y` with y an integer variable: one edge for each value of y."""
    changed = True
    while changed:
        changed = False
        out = []
        for e in t.edges:
            copy = next((u for u in updates(e.update)
                         if re.fullmatch(rf"\w+ = ({IDENT})", u) and u.split(" = ")[1] in ints), None)
            if not copy:
                out.append(e)
                continue
            changed = True
            src = copy.split(" = ")[1]
            lo, hi, _ = ints[src]
            for k in range(lo, hi + 1):
                g = f"({src} == {k})"
                ups = [u if u != copy else f"{copy.split(' = ')[0]} = {k}" for u in updates(e.update)]
                out.append(replace(e, guard=f"({paren(e.guard)} && {g})" if e.guard else g,
                                   update=", ".join(ups)))
        t.edges = out


def split_clock_disjunctions(t, clocks):
    out = []
    for e in t.edges:
        parts = split_top(strip_parens(e.guard), "||") if e.guard else [""]
        has_clock = any(re.search(rf"\b{c}\b", p) for p in parts for c in clocks)
        if len(parts) > 1 and has_clock:
            out += [replace(e, guard=f"({p.strip()})") for p in parts]
        else:
            out.append(e)
    t.edges = out


def pump_per_duration(t, ints):
    """`Temp` with `y <= (dur * 60)` becomes `Temp_d` for each duration d."""
    temp = next((l for l in t.locs if l.name == "Temp"), None)
    if temp is None:
        raise ValueError("the Pump template has no location Temp")
    if "dur" not in ints:
        raise ValueError("the Pump needs an integer dur")
    if any(re.fullmatch(r"Temp_\d+", l.name) for l in t.locs):
        raise ValueError("the pump already has a location Temp_d")
    lo, hi, _ = ints["dur"]
    durs = range(max(lo, 1), hi + 1)
    t.locs = [l for l in t.locs if l.name != "Temp"] + \
        [M.Loc(f"Temp_{d}", inv=fold_constants(subst(temp.inv, {"dur": d})), kind=temp.kind)
         for d in durs]
    out = []
    for e in t.edges:
        src_d = durs if e.src == "Temp" else [None]
        for d in src_d:
            g = fold_constants(subst(e.guard, {"dur": d})) if d is not None else e.guard
            if e.dst == "Temp":
                m = re.search(r"\bdur = (\d+)", e.update)
                dd = int(m[1]) if m else d
                if dd not in durs:      # refused before by check_pump_duration
                    raise ValueError(f"Pump edge into Temp with dur = {dd}")
                dst = f"Temp_{dd}"
            else:
                dst = e.dst
            out.append(replace(e, src=f"Temp_{d}" if d is not None else e.src, dst=dst, guard=g))
    t.edges = out


# ---------------------------------------------------------------- expressions

def bind_not(text):
    """`!x` becomes `(not x)` with x the next identifier, number or parenthesized
    group. In UPPAAL `!` binds tighter than a comparison; in Python `not` binds
    looser, so `!(v) == 1` must become `(not (v)) == 1`, not `not ((v) == 1)`."""
    i = text.find("!")
    while i >= 0:
        if text[i + 1:i + 2] == "=":
            i = text.find("!", i + 2)
            continue
        j = i + 1
        while j < len(text) and text[j] == " ":
            j += 1
        if text[j:j + 1] == "(":
            depth, k = 0, j
            while True:
                depth += text[k] == "("
                depth -= text[k] == ")"
                k += 1
                if depth == 0:
                    break
        elif text[j:j + 1] == "!":
            raise ValueError(f"double negation not handled: {text!r}")
        else:
            mm = re.match(r"[\w.]+", text[j:])
            if not mm:
                raise ValueError(f"negation not understood: {text!r}")
            k = j + mm.end()
        inner = bind_not(text[j:k])
        text = f"{text[:i]}(not {inner}){text[k:]}"
        i = text.find("!", i + 5 + len(inner))
    return text


def to_ast(text):
    py = bind_not(" ".join(text.split())).replace("&&", " and ").replace("||", " or ")
    py = re.sub(r"\btrue\b", "True", re.sub(r"\bfalse\b", "False", py))
    return Neg().visit(ast.parse(py, mode="eval").body)


class Neg(ast.NodeTransformer):
    """`-1` as one constant."""
    def visit_UnaryOp(self, node):
        self.generic_visit(node)
        if isinstance(node.op, ast.USub) and isinstance(node.operand, ast.Constant):
            return ast.Constant(-node.operand.value)
        return node


INV = {ast.Eq: None, ast.Lt: ast.GtE, ast.LtE: ast.Gt, ast.Gt: ast.LtE, ast.GtE: ast.Lt}
SYM = {ast.Eq: "==", ast.Lt: "<", ast.LtE: "<=", ast.Gt: ">", ast.GtE: ">="}


def fold_not(x):
    """`!k` on an integer constant k is 1 if k is 0, else 0, as in UPPAAL."""
    if isinstance(x, ast.UnaryOp) and isinstance(x.op, ast.Not):
        inner = fold_not(x.operand)
        if isinstance(inner, ast.Constant):
            return ast.Constant(int(not inner.value))
    return x


def simplify(node, neg=False):
    """`node` (negated with `neg`) with constant atoms evaluated and negations pushed
    to the atoms: True, False, or a node without `not`. `!(x == c)` becomes
    `(x < c) || (x > c)`, as Munta guards need (uppaal/u0b/README.md, limit 15)."""
    if isinstance(node, ast.Constant):
        return bool(node.value) != neg
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return simplify(node.operand, not neg)
    if isinstance(node, ast.BoolOp):
        is_and = isinstance(node.op, ast.And) != neg
        parts = []
        for v in node.values:
            r = simplify(v, neg)
            if r is (not is_and):
                return not is_and
            if r is not is_and:
                parts.append(r)
        if not parts:
            return is_and
        return parts[0] if len(parts) == 1 else ast.BoolOp(ast.And() if is_and else ast.Or(), parts)
    if isinstance(node, ast.Compare) and len(node.ops) == 1:
        a, b, op = fold_not(node.left), fold_not(node.comparators[0]), type(node.ops[0])
        node = ast.Compare(a, node.ops, [b])
        if isinstance(a, ast.Constant) and isinstance(b, ast.Constant):
            return OPS[SYM[op]](a.value, b.value) != neg
        if not neg:
            return node
        if op is ast.Eq:
            return ast.BoolOp(ast.Or(), [ast.Compare(a, [ast.Lt()], [b]), ast.Compare(a, [ast.Gt()], [b])])
        return ast.Compare(a, [INV[op]()], [b])
    raise ValueError(f"expression not understood: {ast.dump(node)}")


def render(node):
    if isinstance(node, ast.BoolOp):
        op = " && " if isinstance(node.op, ast.And) else " || "
        return "(" + op.join(render(v) for v in node.values) + ")"
    if isinstance(node, ast.Compare):
        def side(x):
            if isinstance(x, ast.Name):
                return x.id
            if isinstance(x, ast.Constant):
                return str(x.value)
            raise ValueError(f"expression not supported for Munta: {ast.dump(x)}")
        return f"({side(node.left)} {SYM[type(node.ops[0])]} {side(node.comparators[0])})"
    raise ValueError(ast.dump(node))


def paren(x):
    """`x` in parentheses if it has a top-level `||`, so that `&&` with it keeps
    its meaning."""
    t = x.strip()
    return f"({t})" if strip_parens(t) == t and len(split_top(t, "||")) > 1 else t


def conj(*parts):
    """Conjunction of guard texts; None if one part is False."""
    out = []
    for p in parts:
        if p is False:
            return None
        if p in (True, "", None):
            continue
        out.append(paren(p) if len(parts) > 1 else p)
    return "(" + " && ".join(out) + ")" if len(out) > 1 else (out[0] if out else "")


def expand_conditionals(t):
    """`x = (c) ? x : k` becomes two edges: guard c without the update, and the
    negation of c with `x = k`. Constant atoms are evaluated first, and a branch
    whose condition is false is dropped. Repeated until no conditional is left."""
    cond = re.compile(r"\w+ = \(.*\) \? \w+ : -?\d+")
    while any(cond.fullmatch(u) for e in t.edges for u in updates(e.update)):
        t.edges = expand_conditionals_once(t.edges)


def expand_conditionals_once(edges):
    out = []
    for e in edges:
        cond = next(((u, m) for u in updates(e.update)
                     for m in [re.fullmatch(r"(\w+) = \((.*)\) \? \1 : (-?\d+)", u)] if m), None)
        if not cond:
            out.append(e)
            continue
        u, mm = cond
        rest = [x for x in updates(e.update) if x != u]
        for neg, extra in ((False, []), (True, [f"{mm[1]} = {mm[3]}"])):
            c = simplify(to_ast(mm[2]), neg)
            g = conj(e.guard, c if isinstance(c, bool) else render(c))
            if g is not None:
                out.append(replace(e, guard=g, update=", ".join(rest + extra)))
    return out


ATOM = r"\b({n})\s*(==|<=|>=|<|>)\s*(-?\d+)"


def atoms_on(n, text):
    """The atoms `n op c` with a constant c in `text` that stand alone: the text
    before is empty or ends in `(`, `&` or `|`, and the text after is empty or
    starts with `)`, `&` or `|`. So `n == 1 + 1`, `1 + n == 2` and `!n == 1` give no
    atom; a variable with such an occurrence gets no value classes."""
    out = []
    for mm in re.finditer(ATOM.format(n=n), text or ""):
        before, after = text[:mm.start()].rstrip(), text[mm.end():].lstrip()
        if (not before or before[-1] in "(&|") and (not after or after[0] in ")&|"):
            out.append((mm[2], int(mm[3])))
    return out
OPS = {"==": lambda a, b: a == b, "<=": lambda a, b: a <= b, ">=": lambda a, b: a >= b,
       "<": lambda a, b: a < b, ">": lambda a, b: a > b}


def value_classes(m, ints, formula):
    """Exact quotient of the value of an integer variable (U4, step 1).

    A variable x qualifies if it occurs in guards, invariants and the formula only in
    atoms `x op c` with a constant c, and in updates only as `x = c` or `x = v` with a
    select variable v. Two values of x are then equivalent when every atom gives the
    same truth on both. Two states that differ only in equivalent values of x satisfy
    the same guards, invariants and formula atoms, and every update either keeps x
    or overwrites it. So the relation is a bisimulation (clocks and delays are not
    touched), and a select `v` with the update `x = v` can take one value per class
    without a change to any answer, the deadlock answers included. If the guard of
    that edge has atoms on v, they refine the classes (`expand_selects`). Returns
    {x: the atoms on x}."""
    texts = [e.guard for t in m.templates for e in t.edges] + \
            [l.inv for t in m.templates for l in t.locs] + [formula]
    ups = [(u, set(re.findall(r"(\w+) : int", e.select or "")))
           for t in m.templates for e in t.edges for u in updates(e.update)]
    out = {}
    for x, (lo, hi, _) in ints.items():
        atoms, occ = [], 0
        for tx in texts:
            atoms += atoms_on(x, tx or "")
            occ += len(re.findall(rf"\b{x}\b", tx or ""))
        if occ != len(atoms) or not atoms:
            continue
        ok = True
        for u, sel in ups:
            lhs, _, rhs = u.partition(" = ")
            if re.search(rf"\b{x}\b", rhs) or (lhs.strip() == x and not (
                    re.fullmatch(r"-?\d+", rhs.strip()) or rhs.strip() in sel)):
                ok = False
        if not ok:
            continue
        # the bounds of x keep an out-of-range value in a class of its own, so that
        # the reduced select keeps the UPPAAL range error (U4 review round 8)
        out[x] = sorted(set(atoms)) + [(">=", lo), ("<=", hi)]
    return out


def conjuncts(g):
    """The conjuncts of a guard, with nested conjunctions flattened."""
    t = strip_parens(g or "")
    if not t:
        return []
    parts = split_top(t, "&&")
    if len(parts) == 1:
        return [t]
    return [c for p in parts for c in conjuncts(p)]


def names_in(text):
    return set(re.findall(rf"\b({IDENT})\b", text or "")) - {"true", "false"}


def holds(expr, env):
    return simplify(to_ast(subst(expr, env))) is True


def stays_in_range(u, e, ints):
    """The update `u` of edge `e` keeps its variable inside its declared range: a
    constant inside it, a copy of a variable or select value whose range lies
    inside it, a conditional whose constant lies inside it, or `x = x + k` under a
    guard conjunct `x < c` or `x <= c` that keeps the sum inside it. The range of a
    copied name is narrowed by the guard conjuncts `y op c` of the edge."""
    x, _, rhs = (s.strip() for s in u.partition(" = "))
    lo, hi, _ = ints[x]
    sel = {n: (int(a), int(b)) for n, a, b in re.findall(r"(\w+) : int\[(-?\d+),(-?\d+)\]", e.select or "")}
    inside = lambda a, b: lo <= a and b <= hi
    if re.fullmatch(r"-?\d+", rhs):
        return inside(int(rhs), int(rhs))
    if rhs in sel or rhs in ints:
        a, b = sel[rhs] if rhs in sel else ints[rhs][:2]
        for c in conjuncts(e.guard):
            mm = re.fullmatch(rf"{rhs} (==|<=|>=|<|>) (-?\d+)", strip_parens(c))
            if mm:
                op, k = mm[1], int(mm[2])
                if op in ("==", ">="):
                    a = max(a, k)
                if op in ("==", "<="):
                    b = min(b, k)
                if op == ">":
                    a = max(a, k + 1)
                if op == "<":
                    b = min(b, k - 1)
        return inside(a, b)
    cm = re.fullmatch(rf"\(.*\) \? {x} : (-?\d+)", rhs)
    if cm:
        return inside(int(cm[1]), int(cm[1]))
    inc = re.fullmatch(rf"{x} \+ (\d+)", rhs)
    if inc:
        k = int(inc[1])
        for c in conjuncts(e.guard):
            mm = re.fullmatch(rf"{x} (<|<=) (-?\d+)", strip_parens(c))
            if mm and int(mm[2]) - (mm[1] == "<") + k <= hi:
                return True
    return False


def drop_names(m, drop, ints, clocks, formula):
    """Remove the observer variables and clocks `drop` (U4, step 1), with a check
    that the removal is exact.

    Conditions, each checked here:
      1. no name of `drop` occurs in the formula, in an invariant, or on the right
         side of an update of a variable that stays,
      2. every guard is a conjunction whose conjuncts each mention only dropped names
         or only names that stay,
      3. group the edges by template, source, target, synchronization, the conjuncts
         that stay and the updates that stay. In each group, the disjunction of the
         dropped parts of the guards holds for every value of the dropped names
         (integers over their ranges; clocks at every integer and half-integer up to
         one above their largest constant). A conjunct on a dropped clock must be an
         atom `c op k` or `k op c` with an integer k. Then these test points meet
         every region of each clock, and testing every combination of clock values
         covers more than the reachable ones.
    Under these conditions an edge of the reduced network is enabled exactly when
    one edge of its group is enabled, with the same effect on the names that stay,
    and the delays do not change. So the projection on the names that stay is a
    bisimulation: every answer on the reduced network, the deadlock answers
    included, is the answer on the network before the removal. Raises ValueError if
    a condition fails."""
    drop = set(drop)
    if drop - set(ints) - set(clocks):
        raise ValueError(f"cannot drop {sorted(drop - set(ints) - set(clocks))}: not a declared "
                         "integer or clock")
    bad = names_in(formula) & drop
    for t in m.templates:
        for l in t.locs:
            bad |= names_in(l.inv) & drop
        for e in t.edges:
            for u in updates(e.update):
                lhs, _, rhs = u.partition(" = ")
                if lhs.strip() not in drop:
                    bad |= names_in(rhs) & drop
    if bad:
        raise ValueError(f"cannot drop {sorted(bad)}: read outside an observer guard")
    for t in m.templates:
        for e in t.edges:
            for u in updates(e.update):
                if u.split(" = ")[0].strip() in drop and u.split(" = ")[0].strip() in ints \
                        and not stays_in_range(u, e, ints):
                    raise ValueError(f"cannot drop: {u!r} in {t.name} may leave the range, and the "
                                     "removal would hide the UPPAAL range error")
    for t in m.templates:
        groups = {}
        for e in t.edges:
            keep_c, drop_c = [], []
            for c in conjuncts(e.guard):
                ns = names_in(c)
                if ns & drop and ns - drop:
                    raise ValueError(f"cannot drop: mixed conjunct {c!r} in {t.name}")
                (drop_c if ns & drop else keep_c).append(c)
            keep_u = [u for u in updates(e.update) if u.split(" = ")[0].strip() not in drop]
            key = (e.src, e.dst, e.sync, e.select, tuple(sorted(set(keep_c))), tuple(keep_u))
            groups.setdefault(key, []).append(drop_c)
        new_edges = []
        for (src, dst, sync, select, keep_c, keep_u), parts in groups.items():
            used = sorted({n for p in parts for c in p for n in names_in(c)})
            if used:
                doms = []
                for n in used:
                    if n in ints:
                        doms.append(range(ints[n][0], ints[n][1] + 1))
                    else:
                        ks = []
                        for c in (c for p in parts for c in p if n in names_in(c)):
                            a = re.fullmatch(rf"\s*(?:{n}\s*(?:==|<=|>=|<|>)\s*(\d+)"
                                             rf"|(\d+)\s*(?:==|<=|>=|<|>)\s*{n})\s*", strip_parens(c))
                            if not a:
                                raise ValueError(f"cannot drop clock {n}: {c!r} in {t.name} is not "
                                                 f"an atom '{n} op k' or 'k op {n}'")
                            ks.append(int(a.group(1) or a.group(2)))
                        top = max(ks + [0]) + 1
                        doms.append([i / 2 for i in range(0, 2 * top + 1)])
                for vals in itertools.product(*doms):
                    env = dict(zip(used, vals))
                    if not any(all(holds(c, env) for c in p) for p in parts):
                        raise ValueError(f"cannot drop: in {t.name} {src}->{dst} the dropped "
                                         f"guards do not cover {env}")
            g = " && ".join(f"({c})" for c in keep_c)
            new_edges.append(M.Edge(src, dst, guard=f"({g})" if len(keep_c) > 1 else g,
                                    sync=sync, update=", ".join(keep_u), select=select))
        t.edges = new_edges
    for n in drop:
        ints.pop(n, None)
        if n in clocks:
            clocks.remove(n)
    if not clocks:
        raise ValueError("the removal leaves no clock, and Munta needs one (U0b limit)")


def split_channels(m, ints):
    """A channel whose receivers copy integer variables (`x = v`) becomes one
    channel for each value of these variables (U4, step 4). A sender gets one edge
    for each value with its guard plus `v == k`; a value whose guard is false after
    substitution gets no edge. A receiver gets one edge for each value, with k in
    place of v. The sender must not write v, so the receiver reads the same value in
    UPPAAL (sender updates first) and in Munta (updates on the state before the
    edge). Then the synchronization with value k happens exactly when the original
    one happens with v == k, with the same effect."""
    chans = {e.sync[:-1] for t in m.templates for e in t.edges if e.sync.endswith("?")}
    new_chans = {}
    taken = set()       # names made for earlier channels
    used = {e.sync[:-1] for t in m.templates for e in t.edges if e.sync} | \
        {n for part in parse_decls(m.decl) for n in part} | \
        {n for t in m.templates if t.decl for part in parse_decls([t.decl]) for n in part} | \
        {t.name for t in m.templates}
    for ch in sorted(chans):
        recv = [e for t in m.templates for e in t.edges if e.sync == ch + "?"]
        vs = sorted({u.partition(" = ")[2].strip() for e in recv for u in updates(e.update)
                     if re.fullmatch(rf"\w+ = ({IDENT})", u) and u.partition(" = ")[2].strip() in ints})
        if not vs:
            continue
        if any(u.partition(" = ")[0].strip() in vs for e in recv for u in updates(e.update)):
            raise ValueError(f"cannot split {ch}: a receiver writes one of {vs}")
        values = {}
        for t in m.templates:
            out = []
            for e in t.edges:
                if e.sync != ch + "!":
                    out.append(e)
                    continue
                written = {u.split(" = ")[0].strip() for u in updates(e.update)}
                if written & set(vs) or e.select:
                    raise ValueError(f"cannot split {ch}: a sender writes or selects {vs}")
                for ks in itertools.product(*[range(ints[v][0], ints[v][1] + 1) for v in vs]):
                    env = dict(zip(vs, ks))
                    c = simplify(to_ast(subst(e.guard, env))) if e.guard else True
                    if c is False:
                        continue
                    name = ch + "_" + "_".join(str(k).replace("-", "m") for k in ks)
                    if name in used or name in taken:
                        raise ValueError(f"split channel name {name} is not fresh")
                    values[name] = env
                    atoms = " && ".join(f"({v} == {k})" for v, k in env.items())
                    out.append(replace(e, guard=conj(e.guard, f"({atoms})"), sync=name + "!"))
            t.edges = out
        for t in m.templates:
            out = []
            for e in t.edges:
                if e.sync != ch + "?":
                    out.append(e)
                    continue
                for name, env in values.items():
                    out.append(replace(e, guard=subst(e.guard, env), sync=name + "?",
                                       update=subst(e.update, env)))
            t.edges = out
        new_chans[ch] = sorted(values)
        taken |= set(values)
    return new_chans


def merge_complementary(t):
    """Two edges that are equal except for one conjunct, `(c < k)` in one and
    `(c >= k)` in the other, become one edge without that conjunct. One of the two is
    enabled exactly when the merged edge is, with the same effect."""
    def key(e, skip):
        cs = conjuncts(e.guard)
        return (e.src, e.dst, e.sync, e.update, e.select,
                tuple(sorted(c for i, c in enumerate(cs) if i != skip)))
    changed = True
    while changed:
        changed = False
        index = {}
        for i, e in enumerate(t.edges):
            for j, c in enumerate(conjuncts(e.guard)):
                mm = re.fullmatch(r"(\w+) (<|>=) (\d+)", c)
                if mm:
                    index.setdefault((key(e, j), mm[1], mm[3], mm[2]), i)
        used, merged = set(), []
        for (k, c, n, op), i in index.items():
            j = index.get((k, c, n, ">="))
            if op == "<" and j is not None and not {i, j} & used:
                used |= {i, j}
                rest = list(k[5])
                g = " && ".join(f"({x})" for x in rest)
                merged.append(replace(t.edges[i], guard=f"({g})" if len(rest) > 1 else g))
        if used:
            t.edges = [e for x, e in enumerate(t.edges) if x not in used] + merged
            changed = True


def ceiling_loops(m, ints, clocks):
    """A self-loop at every location with an edge that never fires and carries the largest
    constant of every clock (see the module docstring)."""
    const = {}
    for t in m.templates:
        for x in [e.guard for e in t.edges] + [l.inv for l in t.locs]:
            pairs = re.findall(rf"\b({IDENT})\s*(?:==|[<>]=?)\s*(\d+)", x or "") + \
                [(c, k) for k, c in re.findall(rf"\b(\d+)\s*(?:==|[<>]=?)\s*({IDENT})\b", x or "")]
            for c, k in pairs:
                if c in clocks:
                    const[c] = max(const.get(c, 0), int(k))
    if not const:
        return
    flag = next((n for n, (lo, hi, _) in ints.items() if lo <= 0 <= 1 <= hi), None)
    if flag is None:
        raise ValueError("no integer with 0 and 1 in its range for the ceiling loops")
    atoms = " && ".join(f"({c} <= {k})" for c, k in sorted(const.items()))
    guard = f"(({flag} == 0) && ({flag} == 1) && {atoms})"
    for t in m.templates:
        for l in t.locs:
            if any(e.src == l.name or e.dst == l.name for e in t.edges):
                t.edges.append(M.Edge(l.name, l.name, guard=guard))


def init_values(m, ints):
    """Munta starts every integer at 0: a first committed edge sets the others.
    Only Step.Init is committed at the start (checked), so in UPPAAL and in Munta
    (where committed locations are also urgent) no other process moves and no time
    passes before this edge. A query must then skip the state at Step.Init
    (`run_u4.lowered_formula`)."""
    nonzero = {n: i for n, (lo, hi, i) in ints.items() if i}
    if not nonzero:
        if any(l.name == "Init" for t in m.templates if t.name == "Step" for l in t.locs):
            raise ValueError("Step has a location Init, which the formula rewrite would skip")
        return
    step = next((t for t in m.templates if t.name == "Step"), None)
    if step is None:
        raise ValueError("no Step template for the start values")
    if any(l.name == "Init" for l in step.locs):
        raise ValueError("Step already has a location Init")
    for t in m.templates:
        if t is not step and any(l.name == t.init and l.kind == "committed" for l in t.locs):
            raise ValueError(f"cannot add Step.Init: {t.name} starts in a committed location, "
                             "so it could move before the start values are set")
    for t in m.templates:
        for l in t.locs:
            if l.name == t.init and names_in(l.inv) & set(nonzero):
                raise ValueError(f"cannot add Step.Init: the initial invariant of {t.name} reads "
                                 f"{sorted(names_in(l.inv) & set(nonzero))}")
    step.locs.insert(0, M.Loc("Init", kind="committed"))
    step.edges.insert(0, M.Edge("Init", step.init,
                                update=", ".join(f"{n} = {i}" for n, i in nonzero.items())))
    step.init = "Init"
    for n in nonzero:
        lo, hi, _ = ints[n]
        ints[n] = (lo, hi, 0)


# ---------------------------------------------------------------- input language

TOKEN = re.compile(r"\s*(\d+|[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)?|==|<=|>=|&&|\|\||[<>()!*+?:\-\[\]])")
RELOPS = ("==", "<", "<=", ">", ">=")


def tokens(text):
    out, i = [], 0
    text = text.rstrip()
    while i < len(text):
        mm = TOKEN.match(text, i)
        if not mm:
            raise ValueError(f"outside the input language: {text!r} at {text[i:]!r}")
        out.append(mm[1])
        i = mm.end()
    return out


class Lang:
    """Recursive descent over the input language of `lower` (U4 review round 5).
    Boolean expressions: `||` and `&&` of parenthesized expressions, `true`,
    `false` and atoms `term op term` with op in == < <= > >=. A term is an integer
    (with an optional `-`), a name, or `(name * integer)`. In a formula, also
    `!( expression )`, `Template.Location` and one `imply` per parenthesized level,
    whose operands are each one parenthesized expression, atom or location (UPPAAL
    and Munta group `a || b imply c` differently, U0b difference 4). `&&` and `||`
    are not mixed on one level without parentheses. Names must be declared."""

    def __init__(self, text, names, clocks, formula=False, ints=None, munta=False):
        self.t, self.i, self.names, self.clocks, self.formula = tokens(text), 0, names, clocks, formula
        self.ints, self.munta = ints, munta
        self.text = text

    def fail(self, what):
        raise ValueError(f"outside the input language ({what}): {self.text!r}")

    def peek(self, k=0):
        return self.t[self.i + k] if self.i + k < len(self.t) else None

    def take(self, tok=None):
        x = self.peek()
        if x is None or (tok is not None and x != tok):
            self.fail(f"expected {tok or 'a token'}")
        self.i += 1
        return x

    def done(self):
        if self.peek() is not None:
            self.fail(f"unexpected {self.peek()!r}")

    def bexpr(self):
        n = self.disj()
        if self.formula and self.peek() == "imply":
            self.take()
            if n > 1 or self.disj() > 1:
                self.fail("an operand of imply must be one parenthesized expression or atom")

    def disj(self):
        """The number of operands at this level. `&&` and `||` must not be mixed
        on one level without parentheses."""
        sizes = [self.conj()]
        while self.peek() == "||":
            self.take()
            sizes.append(self.conj())
        if len(sizes) > 1 and max(sizes) > 1:
            self.fail("&& and || mixed without parentheses")
        return sum(sizes)

    def conj(self):
        n = 1
        self.unary()
        while self.peek() == "&&":
            self.take()
            self.unary()
            n += 1
        return n

    def is_product(self):
        return (self.peek() == "(" and self.peek(2) == "*" and self.peek(4) == ")"
                and (self.peek(3) or "").isdigit())

    def unary(self):
        x = self.peek()
        if x in ("true", "false"):
            if self.formula or self.munta:
                self.fail("true or false in a formula (U0b limit)")
            self.take()
        elif x == "!" and self.formula and self.peek(1) == "(":
            self.take()
            self.take("(")
            self.bexpr()
            self.take(")")
        elif x == "(" and not self.is_product():
            self.take()
            self.bexpr()
            self.take(")")
        elif x and "." in x and self.formula:
            self.take()
        else:
            self.atom()

    def atom(self):
        a = self.term()
        op = self.take()
        if op not in RELOPS:
            self.fail(f"comparison operator expected, got {op!r}")
        b = self.term()
        if a in self.clocks and b in self.clocks:
            self.fail("a clock on both sides")
        lits = [x for x in (a, b) if x.lstrip("-").isdigit()]
        if (self.munta or self.formula) and not (b in lits and a not in lits):
            self.fail("Munta takes only 'name op integer' (U0b limit 7)")
        if (self.formula or self.munta) and not lits:
            self.fail("a comparison of two names (U0b limits 2 and 7)")
        if self.munta and len(lits) == 1 and (a in self.clocks or b in self.clocks) and int(lits[0]) < 0:
            self.fail("a clock compared with a negative constant (U0b limit 4)")

    def term(self):
        x = self.peek()
        if x == "-":
            self.take()
            if not (self.peek() or "").isdigit():
                self.fail("integer after -")
            return "-" + self.take()
        if x is not None and x.isdigit():
            return self.take()
        if self.is_product():
            if self.formula or self.munta:
                self.fail("arithmetic in a formula (U0b limit)")
            self.take("(")
            n = self.name(clock=False)
            self.take("*")
            k = int(self.take())
            self.take(")")
            if self.ints is None or n not in self.ints or \
                    k * max(abs(self.ints[n][0]), abs(self.ints[n][1])) > 32767:
                self.fail("a product that may leave -32768..32767 (U0b difference 6)")
            return n
        return self.name()

    def name(self, clock=True):
        x = self.take()
        if x not in self.names or "." in x or (not clock and x in self.clocks):
            self.fail(f"undeclared or misplaced name {x!r}")
        return x


def check_language(m, formula=""):
    """Refuse any input outside the language of the U4 networks, with ValueError.
    Besides the expressions of `Lang`: declarations `int[lo,hi] x (= k)`,
    `clock ...` and `chan ...`; selects `n : int[lo,hi]`; synchronizations `c!` and
    `c?` on a declared channel; ranges inside -32768..32767, so that with k below
    1000 no update overflows and a range error stays an UPPAAL error (U0b
    differences 3 and 6); updates `x = k`, `x = y`, `x = x + k`, `y = 0` for a
    clock y, and `x = (expression) ? x : k`; location kinds "", committed, urgent;
    formulas `A[] e`, `E<> e` and `A[] (!deadlock)`."""
    ints, clocks, chans = parse_decls(m.decl)
    declared = set(ints) | set(clocks) | set(chans) | {t.name for t in m.templates} | \
        {l.name for t in m.templates for l in t.locs} | \
        {n for t in m.templates if t.decl for part in parse_decls([t.decl]) for n in part} | \
        {t.name for t in m.templates} | \
        {n for t in m.templates for e in t.edges for n in re.findall(r"(\w+) : int", e.select or "")}
    texts = list(m.decl) + [formula] + [t.decl or "" for t in m.templates] + \
        [x or "" for t in m.templates for l in t.locs for x in (l.inv,)] + \
        [x or "" for t in m.templates for e in t.edges for x in (e.guard, e.update, e.select)]
    if any(re.search(r"(?<![\w.])0\d", x) for x in texts):
        raise ValueError("an integer literal with a leading zero")
    reserved = declared & (set(keyword.kwlist) | {"true", "false", "imply", "deadlock", "int", "clock",
                                                  "chan"})
    if reserved:
        raise ValueError(f"reserved names declared: {sorted(reserved)} (Python reads them as keywords "
                         "or constants)")
    for n, (lo, hi, i) in ints.items():
        if not -32768 <= lo <= i <= hi <= 32767:
            raise ValueError(f"range of {n} outside -32768..32767 or start value outside it "
                             "(U0b difference 6, overflow)")
        if not lo <= 0 <= hi:
            raise ValueError(f"range of {n} does not contain 0, where Munta starts it")
    locs = {f"{t.name}.{l.name}" for t in m.templates for l in t.locs}
    for t in m.templates:
        li, lc, lch = parse_decls([t.decl] if t.decl else [])
        tclocks = set(clocks) | set(lc)
        for l in t.locs:
            if l.kind not in ("", "committed", "urgent"):
                raise ValueError(f"location kind {l.kind!r} in {t.name}")
            if l.inv:
                p = Lang(l.inv, set(ints) | tclocks, tclocks, ints=ints)
                p.bexpr()
                p.done()
        for e in t.edges:
            sel = {}
            if e.select:
                one = r"(\w+) : int\[-?\d+,-?\d+\]"
                if not re.fullmatch(rf"{one}(?:, {one})*", e.select.strip()):
                    raise ValueError(f"select outside the input language: {e.select!r}")
                sel = dict.fromkeys(re.findall(r"(\w+) : int", e.select), True)
            names = set(ints) | tclocks | set(sel) | set(li)
            if e.sync and not (re.fullmatch(r"\w+[!?]", e.sync) and e.sync[:-1] in set(chans) | set(lch)):
                raise ValueError(f"synchronization outside the input language: {e.sync!r}")
            if e.guard:
                p = Lang(e.guard, names, tclocks, ints=ints)
                p.bexpr()
                p.done()
            for u in updates(e.update):
                mm = re.fullmatch(r"(\w+) = (.*)", u)
                if not mm or mm[1] not in set(ints) | tclocks | set(li):
                    raise ValueError(f"update outside the input language: {u!r}")
                x, rhs = mm[1], mm[2].strip()
                if x in tclocks:
                    if rhs != "0":
                        raise ValueError(f"clock update other than reset: {u!r}")
                    continue
                inc = re.fullmatch(rf"{x} \+ (\d+)", rhs)
                if re.fullmatch(r"-?\d+", rhs) or (rhs in names and rhs not in tclocks) \
                        or (inc and int(inc[1]) < 1000):
                    continue
                cm = re.fullmatch(rf"\((.*)\) \? {x} : (-?\d+)", rhs)
                if not cm:
                    raise ValueError(f"update outside the input language: {u!r}")
                p = Lang(cm[1], names - tclocks, set())
                p.bexpr()
                p.done()
    if formula and formula != "A[] (!deadlock)":
        mm = re.fullmatch(r"(A\[\]|E<>) (.*)", formula)
        if not mm:
            raise ValueError(f"formula outside the input language: {formula!r}")
        allc = set(clocks) | {c for t in m.templates for c in parse_decls([t.decl] if t.decl else [])[1]}
        p = Lang(mm[2], set(ints) | locs | allc, allc, formula=True)
        p.bexpr()
        p.done()


def check_scopes(m):
    """A select variable must not have the name of a declared variable or clock of
    any template (local clocks become global in `lower`):
    `split_channels` and `value_classes` run before the selects are expanded and
    read names as the declared ones. Raises ValueError."""
    ints, clocks, _ = parse_decls(m.decl)
    names = set(ints) | set(clocks)
    for t in m.templates:       # local names of every template: lower makes them global
        if t.decl:
            li, lc, _ = parse_decls([t.decl])
            names |= set(li) | set(lc)
    for t in m.templates:
        for e in t.edges:
            for n in re.findall(r"(\w+) : int", e.select or ""):
                if n in names:
                    raise ValueError(f"select variable {n} in {t.name} shadows a declaration")


def check_updates(m):
    """The updates of an edge must be independent: no assignment reads or writes a
    variable that an earlier assignment of the same edge writes. UPPAAL runs the
    assignments in order, while the expansion steps move the read values into the
    guard, which is evaluated before any assignment. Raises ValueError."""
    for t in m.templates:
        for e in t.edges:
            written = set()
            for u in updates(e.update):
                lhs, _, rhs = u.partition(" = ")
                if (names_in(rhs) | {lhs.strip()}) & written:
                    raise ValueError(f"dependent updates {e.update!r} in {t.name}")
                written.add(lhs.strip())


def check_sync_writes(m):
    """On a synchronization, the sender and the receiver must not write the same
    variable, and neither may read in its updates a variable that the other writes.
    UPPAAL runs the sender updates first, and Munta does not keep that order, so
    otherwise the result can differ (U4 review). Raises ValueError."""
    def rw(e):
        ups = [u.partition(" = ") for u in updates(e.update)]
        return {l.strip() for l, _, _ in ups}, {n for _, _, r in ups for n in names_in(r)}
    edges = [(t.name, e) for t in m.templates for e in t.edges if e.sync]
    for tn, s in edges:
        if not s.sync.endswith("!"):
            continue
        ws, rs = rw(s)
        for tr, r in edges:
            if r.sync != s.sync[:-1] + "?":
                continue
            wr, rr = rw(r)
            if ws & wr or ws & rr or wr & rs:
                raise ValueError(f"synchronization {s.sync[:-1]} between {tn} and {tr}: "
                                 f"conflicting writes {sorted(ws & wr | ws & rr | wr & rs)}")


def check_pump_duration(m):
    """`pump_per_duration` keeps the answers only if `dur` matches the location
    `Temp_d` while the pump is in `Temp`: `dur` is written only by Pump edges into
    `Temp`, each edge into `Temp` from another location writes `dur` with a
    constant of at least 1 (after `split_channels` and the expansions), and the pump
    does not start in `Temp`. Raises ValueError."""
    for t in m.templates:
        for e in t.edges:
            for u in updates(e.update):
                lhs, _, rhs = u.partition(" = ")
                if lhs.strip() != "dur":
                    continue
                if t.name != "Pump" or e.dst != "Temp" or not re.fullmatch(r"-?\d+", rhs.strip()):
                    raise ValueError(f"dur written outside a Pump edge into Temp: {t.name} "
                                     f"{e.src}->{e.dst} {u!r}")
                if int(rhs) < 1:
                    raise ValueError(f"Pump edge {e.src}->Temp sets dur = {rhs}: a temp of "
                                     "duration 0 is not handled")
            if t.name == "Pump" and e.dst == "Temp" and e.src != "Temp" and \
                    not re.search(r"\bdur = -?\d+", e.update or ""):
                raise ValueError(f"Pump edge {e.src}->Temp does not set dur")
        if t.name == "Pump" and t.init == "Temp":
            raise ValueError("the pump starts in Temp")


def canonical(m, formula):
    """The network and formula with one spelling of whitespace: runs of whitespace
    become one space, and an update is `x = rhs` with one space on each side of
    `=`, and a minus sign touches its integer. The regular expressions of the later
    steps and Munta's parser expect this spelling (U4 review rounds 13 and 15)."""
    sp = lambda x: re.sub(r"-\s+(?=\d)", "-", " ".join((x or "").split()))   # `- 1` is `-1`

    def upd(u):
        mm = re.fullmatch(r"(\w+)\s*=\s*(?!=)(.*)", sp(u))
        return f"{mm[1]} = {mm[2]}" if mm else sp(u)
    for t in m.templates:
        t.locs = [replace(l, inv=sp(l.inv)) for l in t.locs]
        t.edges = [replace(e, guard=sp(e.guard), select=sp(e.select), sync=sp(e.sync),
                           update=", ".join(upd(u) for u in updates(e.update)))
                   for e in t.edges]
    return sp(formula)


def lower(model, formula="", drop=()):
    """The model with only the features that Munta accepts. With `formula`, a select
    over a variable with a value quotient (`value_classes`) takes one value per class.
    `drop` names observer variables and clocks to remove (`drop_names`)."""
    m = M.Model(decl=list(model.decl), templates=[replace(t, locs=list(t.locs), edges=list(t.edges))
                                                  for t in model.templates])
    formula = canonical(m, formula)
    check_language(m, formula)
    if any(t.name == "Pump" for t in m.templates) and re.search(r"\bPump\.Temp\b", formula):
        raise ValueError("the formula names Pump.Temp, which pump_per_duration replaces")
    check_scopes(m)
    check_updates(m)
    check_sync_writes(m)        # before the expansions move update reads into guards
    ints, clocks, chans = parse_decls(m.decl)
    for t in m.templates:
        if t.decl:
            li, lc, lch = parse_decls([t.decl])
            if li or lch:
                raise ValueError(f"local integers or channels in {t.name} are not handled")
            if set(lc) & (set(clocks) | set(ints) | set(chans) | {x.name for x in m.templates}):
                raise ValueError(f"a local clock of {t.name} shadows a global name")
            clocks += lc
            t.decl = ""
    # names inside clock arithmetic (`y <= (dur * 60)`) are dropped after the pump
    # has one location per duration; the others before any expansion
    arith = {n for t in m.templates for x in [e.guard for e in t.edges] + [l.inv for l in t.locs]
             for c in conjuncts(x) if "*" in c for n in names_in(c)}
    early, late = [n for n in drop if n not in arith], [n for n in drop if n in arith]
    if early:
        drop_names(m, early, ints, clocks, formula)
    split = split_channels(m, ints)
    chans = [c for ch in chans for c in split.get(ch, [ch])]
    reps = value_classes(m, ints, formula) if formula else {}
    for t in m.templates:
        expand_selects(t, reps)
        expand_conditionals(t)
        expand_copies(t, ints)
        split_clock_disjunctions(t, clocks)
    if any(t.name == "Pump" for t in m.templates):
        check_pump_duration(m)
    for t in m.templates:
        if t.name == "Pump":
            pump_per_duration(t, ints)
        for e in t.edges:
            e.guard = fold_constants(e.guard)
        merge_complementary(t)
    if late:
        drop_names(m, late, ints, clocks, formula)
    check_sync_writes(m)
    for t in m.templates:
        for e in t.edges:
            for c in conjuncts(e.guard):
                if len(split_top(strip_parens(c), "||")) > 1 and names_in(c) & set(clocks):
                    raise ValueError(f"a clock inside a nested disjunction, which Munta does not "
                                     f"take: {e.guard!r} in {t.name}")
        out = []
        for e in t.edges:
            if e.guard and re.search(r"(?<![\w.])-?\d+\s*(==|<=|>=|<|>)\s*-?\d+\b|\b(true|false)\b",
                                     e.guard):
                c = simplify(to_ast(e.guard))   # constant atoms evaluated
                if c is False:
                    continue
                e = replace(e, guard="" if c is True else render(c))
            out.append(e)
        t.edges = out
        for e in t.edges:
            if e.guard:
                p = Lang(e.guard, set(ints) | set(clocks), set(clocks), munta=True)
                p.bexpr()
                p.done()
        for l in t.locs:
            if names_in(l.inv) - set(clocks):
                raise ValueError(f"an invariant with data in {t.name}.{l.name}: {l.inv!r} "
                                 "(Munta takes only clock invariants)")
            if l.inv:
                p = Lang(l.inv, set(clocks), set(clocks), munta=True)
                p.bexpr()
                p.done()
    if not clocks:
        raise ValueError("the network has no clock, and Munta needs one (U0b limit)")
    for t in m.templates:
        if not any(e.src == t.init or e.dst == t.init for e in t.edges):
            raise ValueError(f"the initial location {t.name}.{t.init} has no edge, and the Munta "
                             "writer drops locations without edges")
    for tn, ln in re.findall(r"\b(\w+)\.(\w+)\b", formula):
        t = next((x for x in m.templates if x.name == tn), None)
        if t is None or not any(e.src == ln or e.dst == ln for e in t.edges):
            raise ValueError(f"the formula names {tn}.{ln}, a location without edges, which the "
                             "Munta writer drops")
    init_values(m, ints)
    in_net = {n for t in m.templates for x in [e.guard for e in t.edges] + [e.update for e in t.edges]
              + [l.inv for l in t.locs] for n in names_in(x)}
    if (names_in(formula) & set(ints)) - in_net:
        raise ValueError(f"the formula reads {sorted((names_in(formula) & set(ints)) - in_net)}, which "
                         "no edge or invariant uses; Munta refuses such variables (U0b limit 10)")
    ceiling_loops(m, ints, clocks)
    m.decl = write_decls(ints, clocks, chans)
    return m


# ---------------------------------------------------------------- Munta JSON

def used_vars(m, formula, ints):
    texts = [e.guard for t in m.templates for e in t.edges] + \
            [e.update for t in m.templates for e in t.edges] + \
            [l.inv for t in m.templates for l in t.locs] + [formula]
    found = set()
    for x in texts:
        found |= set(re.findall(rf"\b({IDENT})\b", x or ""))
    return [n for n in ints if n in found]


def munta_text(text):
    """UPPAAL expression or update text in Munta's spelling."""
    text = re.sub(r"(?<![=!<>]) = (?!=)", " := ", text)
    return text


def munta_formula(q):
    q = re.sub(r"-\s+(?=\d)", "-", q)
    return re.sub(r"\s*(?<![\w.])imply(?![\w.])\s*", " -> ", q)


def write_munta(m, formula, path, order=None):
    ints, clocks, chans = parse_decls(m.decl)
    vars_ = used_vars(m, formula, ints)
    if order:
        assert sorted(order) == sorted(vars_), (order, vars_)
        vars_ = order
    autos = []
    for t in m.templates:
        locs = [l for l in t.locs if any(e.src == l.name or e.dst == l.name for e in t.edges)]
        ids = {l.name: i for i, l in enumerate(locs)}
        autos.append({
            "name": t.name, "initial": ids[t.init],
            "committed": [ids[l.name] for l in locs if l.kind == "committed"],
            # In UPPAAL a committed location is also urgent. In Munta "committed" only
            # restricts which process moves and lets time pass
            # (uppaal/u4/committed_delay.muntax), so committed locations are also urgent.
            "urgent": [ids[l.name] for l in locs if l.kind in ("urgent", "committed")],
            "nodes": [{"id": ids[l.name], "name": l.name, "invariant": l.inv} for l in locs],
            "edges": [{"source": ids[e.src], "target": ids[e.dst], "guard": e.guard,
                       "label": e.sync, "update": munta_text(e.update)} for e in t.edges],
        })
    path.write_text(json.dumps({
        "automata": autos, "clocks": ", ".join(clocks),
        "vars": ", ".join(f"{v}[{ints[v][0]}:{ints[v][1]}]" for v in vars_),
        "broadcast": [], "formula": munta_formula(formula)}, indent=1) + "\n")
    return vars_


CAP = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=16G", "-p", "MemorySwapMax=0"]


def munta_order(order_checker, m, formula, path):
    """The variable order that Munta's numbering gives, from the diagnostic checker.
    The checker prints the order before it checks the model, so it is stopped as soon
    as the order is printed."""
    write_munta(m, formula, path)
    p = subprocess.Popen(CAP + [order_checker, "-m", str(path)], stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True)
    seen, line = [], None
    for out in p.stdout:
        seen.append(out)
        if out.startswith("Var order:"):
            line = out
            break
    p.kill()
    p.wait()
    if line is None:
        raise RuntimeError("no variable order from Munta:\n" + "".join(seen)[-2000:])
    return line.split(":", 1)[1].split()
