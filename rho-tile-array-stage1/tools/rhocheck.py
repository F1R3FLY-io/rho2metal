#!/usr/bin/env python3
"""rhocheck: step checker for logs of the tile array.

The checker rebuilds the soup of every tile from the log alone and tests
each record against a reference written from the specification, not from
the hardware:

  C  a commit names a send slot and a receive slot. They must hold a send
     and a receive on the same channel; the chosen row and values must be
     a solution of the pattern, and the clause must hold. The continuation
     is exploded by the reference, and its components become expected.
  S, R  an insert must be an expected component, and must arrive at the
     tile that owns its channel.
  V  a residue must be an expected component.
  Q  at quiescence nothing may still be expected, and the reference must
     find no redex in any tile.
  ES, ER  the tables the machine reports at the end must be exactly the
     tables the checker reconstructed.

It reports the final soup, so a test can also state what a program should
leave behind.
"""
import json
import sys
from collections import Counter

IW = 29
IMASK = (1 << IW) - 1
E = 6
T_ZERO, T_BOOL, T_INT, T_SYM = 0, 1, 2, 3


class CheckError(Exception):
    pass


def tag(w):
    return w >> 29


def val(w):
    return w & IMASK


def signed(v):
    return v - (1 << IW) if v >> (IW - 1) else v


def mk(tagv, v=0):
    return (tagv << 29) | (v & IMASK)


class SortFault(Exception):
    pass


class Reference:
    def __init__(self, img, ntiles):
        self.img, self.nt = img, ntiles

    def owner(self, w):
        return 0 if tag(w) == T_ZERO else val(w) % self.nt

    @staticmethod
    def opnd(o, env, tmps=()):
        if o["k"] == 0:
            return env[o["w"]]
        if o["k"] == 1:
            return o["w"]
        return tmps[o["w"]]

    def eval_x(self, addr, env):
        n = self.img["xnodes"][addr]
        if n["kind"] == 0:
            return self.opnd(n["a"], env)
        if n["kind"] == 1:
            row = 0
            for i, s in enumerate(n["sup"]):
                w = env[s]
                if tag(w) != T_BOOL:
                    raise SortFault()
                row |= (w & 1) << i
            return mk(T_BOOL, (n["table"] >> row) & 1)
        tmps = []
        while True:
            n = self.img["xnodes"][addr]
            a, b = self.opnd(n["a"], env, tmps), self.opnd(n["b"], env, tmps)
            if tag(a) != T_INT or (n["op"] != 3 and tag(b) != T_INT):
                raise SortFault()
            r = [val(a) + val(b), val(a) - val(b), val(a) * val(b), -val(a)][n["op"]] & IMASK
            tmps.append(mk(T_INT, r))
            if n["last"]:
                return tmps[-1]
            addr += 1

    def solutions(self, r, env, pl):
        """Return (set of rows, checker for unknown values), or None when
        the pair is not a redex. Raises SortFault as the machine must."""
        pk = r["pkind"]
        rows = {0}
        pre = list(env)
        if pk == 0:
            pre = [pl] + pre
        elif pk == 1:
            if pl != 0:
                return None
        elif pk == 2:
            if tag(pl) != T_BOOL:
                raise SortFault()
            b = pl & 1
            rows = {x for x in range(1 << r["nmask"]) if ((r["btable"] >> x) & 1) == b}
            pre = [0] * r["nmask"] + pre
        else:
            if tag(pl) != T_INT:
                raise SortFault()
            m = val(pl)
            if r["k"] == 0:
                if m != r["c0"]:
                    return None
            else:
                # solvable exactly when some assignment satisfies the leaf;
                # for an affine leaf that is divisibility by 2^t
                if (m - r["c0"]) & ((1 << r["t"]) - 1):
                    return None
                if r["k"] == 1 and r["t"] == 0:
                    v = ((m - r["c0"]) * r["oinv"]) & IMASK
                    pre = [mk(T_INT, v)] + pre
                else:
                    pre = [0] * r["k"] + pre
        pre = pre[:E] + [0] * (E - len(pre))
        g = r["guard"]
        if g:
            ab = 0
            for i, a in enumerate(g["atoms"]):
                x, y = self.opnd(a["a"], pre), self.opnd(a["b"], pre)
                if a["op"] == 2:
                    if tag(x) != T_BOOL:
                        raise SortFault()
                    bit = x & 1
                else:
                    if tag(x) != T_INT or tag(y) != T_INT:
                        raise SortFault()
                    bit = int(signed(val(x)) < signed(val(y))) if a["op"] == 0 else int(val(x) == val(y))
                ab |= bit << i
            rows = {x for x in rows if (g["table"] >> ((ab << r["nmask"]) | x)) & 1}
        return rows or None

    def commit_env(self, r, env, pl, row, v0, v1):
        pk = r["pkind"]
        if pk == 0:
            new = [pl]
        elif pk == 1:
            new = []
        elif pk == 2:
            new = [mk(T_BOOL, (row >> i) & 1) for i in range(r["nmask"])][::-1]
        else:
            m = val(pl)
            vs = [v0, v1][:r["k"]]
            cs = [r["c1"], r["c2"]][:r["k"]]
            if (r["c0"] + sum(c * v for c, v in zip(cs, vs))) & IMASK != m:
                raise CheckError("values %s do not solve the arithmetic leaf against %d" % (vs, m))
            new = [mk(T_INT, v) for v in vs][::-1]
        e = new + list(env)
        return e[:E] + [0] * (E - len(e))

    def explode(self, addr, env):
        """Components of the process at addr under env."""
        out, stack = [], [addr]
        while stack:
            n = self.img["cnodes"][stack.pop()]
            k = n["kind"]
            if k == 1:
                stack += [n["y"], n["x"]]
            elif k == 2:
                out.append(("S", self.opnd(n["chan"], env), self.eval_x(n["x"], env)))
            elif k == 3:
                out.append(("R", self.opnd(n["chan"], env), n["x"], tuple(env)))
            elif k == 4:
                out.append(("V", self.eval_x(n["x"], env)))
        return out


def check(img, ntiles, lines):
    ref = Reference(img, ntiles)
    events, end = [], None
    dump_s, dump_r = set(), set()
    for ln in lines:
        f = ln.split()
        if f and f[0] == "ES":
            dump_s.add((int(f[1]), int(f[2]), int(f[3], 16), int(f[4], 16)))
            continue
        if f and f[0] == "ER":
            dump_r.add((int(f[1]), int(f[2]), int(f[3], 16), int(f[4]), tuple(int(x, 16) for x in f[5:5 + E])))
            continue
        if not f or f[0] not in "CSRVFQXT" or len(f[0]) != 1:
            continue
        if f[0] in "QXT":
            end = (f[0], int(f[1]))
        elif f[0] == "F":
            raise CheckError("tile %s raised fault %s at cycle %s" % (f[2], f[3], f[1]))
        else:
            events.append((int(f[1]), 0 if f[0] == "C" else 1, f))
    if end is None:
        raise CheckError("the log has no end record")
    if end[0] != "Q":
        raise CheckError("the run ended with %s at cycle %d, not with quiescence" % end)
    events.sort(key=lambda e: (e[0], e[1]))

    S = [dict() for _ in range(ntiles)]
    R = [dict() for _ in range(ntiles)]
    expected = Counter(ref.explode(0, [0] * E))
    residues, commits = [], 0
    per_cycle = Counter()
    seen = set()
    for cyc, _, f in events:
        t = int(f[2])
        if f[0] == "C":
            si, ri, row = int(f[3]), int(f[4]), int(f[5])
            v0, v1 = int(f[6], 16), int(f[7], 16)
            if (cyc, t) in seen:
                raise CheckError("tile %d commits twice in cycle %d" % (t, cyc))
            seen.add((cyc, t))
            if si not in S[t] or ri not in R[t]:
                raise CheckError("cycle %d tile %d: commit on an empty slot" % (cyc, t))
            sch, pl = S[t][si]
            rch, rinfo, env = R[t][ri]
            if sch != rch:
                raise CheckError("cycle %d tile %d: commit across different channels" % (cyc, t))
            r = img["rinfos"][rinfo]
            try:
                rows = ref.solutions(r, env, pl)
            except SortFault:
                raise CheckError("cycle %d tile %d: commit on a pair that is a sort fault" % (cyc, t))
            if rows is None or row not in rows:
                raise CheckError("cycle %d tile %d: row %d is not a solution" % (cyc, t, row))
            env1 = ref.commit_env(r, env, pl, row, v0, v1)
            expected.update(ref.explode(r["body"], env1))
            del S[t][si]
            if not r["persist"]:
                del R[t][ri]
            commits += 1
            per_cycle[cyc] += 1
        elif f[0] == "S":
            slot, ch, pl = int(f[3]), int(f[4], 16), int(f[5], 16)
            comp = ("S", ch, pl)
            if expected[comp] == 0:
                raise CheckError("cycle %d tile %d: unexpected send %s" % (cyc, t, comp))
            expected[comp] -= 1
            if ref.owner(ch) != t:
                raise CheckError("cycle %d: send on %x reached tile %d, not its owner" % (cyc, ch, t))
            if slot in S[t]:
                raise CheckError("cycle %d tile %d: send slot %d overwritten" % (cyc, t, slot))
            S[t][slot] = (ch, pl)
        elif f[0] == "R":
            slot, ch, rinfo = int(f[3]), int(f[4], 16), int(f[5])
            env = tuple(int(x, 16) for x in f[6:6 + E])
            comp = ("R", ch, rinfo, env)
            if expected[comp] == 0:
                raise CheckError("cycle %d tile %d: unexpected receive %s" % (cyc, t, comp))
            expected[comp] -= 1
            if ref.owner(ch) != t:
                raise CheckError("cycle %d: receive on %x reached tile %d, not its owner" % (cyc, ch, t))
            if slot in R[t]:
                raise CheckError("cycle %d tile %d: receive slot %d overwritten" % (cyc, t, slot))
            R[t][slot] = (ch, rinfo, env)
        else:
            comp = ("V", int(f[3], 16))
            if expected[comp] == 0:
                raise CheckError("cycle %d tile %d: unexpected residue" % (cyc, t))
            expected[comp] -= 1
            residues.append(comp[1])

    left = +expected
    if left:
        raise CheckError("quiescence reported with components undelivered: %s" % dict(left))
    for t in range(ntiles):
        for sch, pl in S[t].values():
            for rch, rinfo, env in R[t].values():
                if sch == rch:
                    try:
                        if ref.solutions(img["rinfos"][rinfo], env, pl):
                            raise CheckError("quiescence reported but tile %d has a redex" % t)
                    except SortFault:
                        raise CheckError("quiescence reported but tile %d has a sort fault pending" % t)
    # the machine's own report of its tables must equal the reconstruction
    model_s = {(t, slot, ch, pl) for t in range(ntiles) for slot, (ch, pl) in S[t].items()}
    model_r = {(t, slot, ch, ri, env) for t in range(ntiles) for slot, (ch, ri, env) in R[t].items()}
    if model_s != dump_s:
        raise CheckError("final send tables differ from the log's reconstruction: %s" % sorted(model_s ^ dump_s))
    if model_r != dump_r:
        raise CheckError("final receive tables differ from the log's reconstruction")
    names = {v: k for k, v in img["syms"].items()}

    def show(w):
        tg = tag(w)
        if tg == T_ZERO:
            return "Nil"
        if tg == T_BOOL:
            return "true" if w & 1 else "false"
        if tg == T_INT:
            return str(signed(val(w)))
        return names.get(val(w), "sym%d" % val(w))

    sends = sorted((show(c), show(p)) for t in range(ntiles) for c, p in S[t].values())
    return {"cycles": end[1], "commits": commits,
            "max_commits_in_a_cycle": max(per_cycle.values(), default=0),
            "concurrent_cycles": sum(1 for v in per_cycle.values() if v > 1),
            "sends": sends,
            "receives": sum(len(r) for r in R),
            "residues": sorted(show(v) for v in residues)}


if __name__ == "__main__":
    if len(sys.argv) != 4:
        sys.exit("usage: rhocheck.py image.json NTILES LOG")
    try:
        res = check(json.load(open(sys.argv[1])), int(sys.argv[2]), open(sys.argv[3]).read().splitlines())
    except CheckError as err:
        sys.exit("FAIL: " + str(err))
    print(json.dumps(res))
