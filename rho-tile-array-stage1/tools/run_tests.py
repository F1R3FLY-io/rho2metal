#!/usr/bin/env python3
"""Build the array at several sizes, run the directed programs under
Icarus Verilog with several seeds each, and pass every log through the
step checker. Usage: run_tests.py [WxH ...]   (default 1x1 2x2 10x10)
"""
import os
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rhoc
import rhocheck

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BSV = os.environ.get("RHO_BSV", ROOT + "/bsv")       # source override, for mutation runs
BSC = os.environ.get("BSC_HOME", "/opt/bsc/bsc-2026.07.1-ubuntu-24.04")
TWO28 = 1 << 28


def sends(*pairs):
    want = sorted(pairs)
    return lambda r: r["sends"] == want


def each(pred):
    return lambda rs: all(pred(r) for r in rs)


def outcomes(*alts):
    """Every run gives one of the alternatives, and every alternative is seen."""
    alts = [sorted(a) for a in alts]

    def f(rs):
        seen = {tuple(r["sends"]) for r in rs}
        return seen == {tuple(a) for a in alts}
    f.weak = lambda rs: {tuple(r["sends"]) for r in rs} <= {tuple(a) for a in alts}
    return f


def inverse_adder(rs):
    vals = set()
    for r in rs:
        d = dict(r["sends"])
        if set(d) != {"l", "r"} or (int(d["l"]) + int(d["r"]) - 7) % (1 << 29):
            return False
        vals.add(d["r"])
    return len(vals) > len(rs) // 2          # the free value really varies


# name, source, predicate over the list of runs, nondeterministic?
TESTS = [
    ("forwarder", "for(a <- x) y!(*a) | x!(true)", each(sends(("y", "true"))), False),
    ("and_gate", "for(a <- x) for(b <- y) z!(*a && *b) | x!(true) | y!(false)",
     each(sends(("z", "false"))), False),
    ("xor_gate", "for(a <- x) for(b <- y) z!(*a xor *b) | x!(true) | y!(true)",
     each(sends(("z", "false"))), False),
    ("half_adder", "for(a <- x) for(b <- y) { s!(*a xor *b) | c!(*a && *b) } | x!(true) | y!(true)",
     each(sends(("c", "true"), ("s", "false"))), False),
    ("full_adder",
     "for(a <- x) for(b <- y) for(c <- ci) { s!(*a xor *b xor *c) | co!(*a && *b || *c && (*a xor *b)) }"
     " | x!(true) | y!(true) | ci!(true)",
     each(sends(("co", "true"), ("s", "true"))), False),
    ("adders_composed",
     "for(a <- x) for(b <- y) { s1!(*a xor *b) | c1!(*a && *b) }"
     " | for(a <- s1) for(b <- ci) { s!(*a xor *b) | c2!(*a && *b) }"
     " | for(a <- c1) for(b <- c2) co!(*a || *b)"
     " | x!(true) | y!(false) | ci!(true)",
     each(sends(("co", "true"), ("s", "false"))), False),
    ("inverse_xor", "for(@(p xor q) <- x) { l!(*p) | r!(*q) } | x!(true)",
     outcomes([("l", "true"), ("r", "false")], [("l", "false"), ("r", "true")]), True),
    ("inverse_and_false", "for(@(p && q) <- x) { l!(*p) | r!(*q) } | x!(false)",
     outcomes([("l", "false"), ("r", "false")], [("l", "true"), ("r", "false")],
              [("l", "false"), ("r", "true")]), True),
    ("unsatisfiable", "for(@(v && ~v) <- x) y!(*v) | x!(true)",
     each(lambda r: r["sends"] == [("x", "true")] and r["commits"] == 0 and r["receives"] == 1), False),
    ("comm_race", "for(a <- x) l!(*a) | for(a <- x) r!(*a) | x!(true)",
     outcomes([("l", "true")], [("r", "true")]), True),
    ("persistent", "for(a <= x) y!(*a) | x!(true) | x!(false)",
     each(lambda r: r["sends"] == [("y", "false"), ("y", "true")] and r["receives"] == 1), False),
    ("equal_names", "for(a <- @(true && false)) z!(*a) | @false!(true)", each(sends(("z", "true"))), False),
    ("name_passing", "for(k <- x) k!(true) | x!(*y)", each(sends(("y", "true"))), False),
    ("nil_pattern", "for(@Nil <- x) z!(true) | x!(Nil)", each(sends(("z", "true"))), False),
    ("residue", "for(a <- x) for(b <- y) (*a || *b) | x!(false) | y!(true)",
     each(lambda r: r["sends"] == [] and r["residues"] == ["true"]), False),
    ("int_adder", "for(@a <- x) for(@b <- y) z!(*a + *b) | x!(3) | y!(4)", each(sends(("z", "7"))), False),
    ("int_expression", "for(@a <- x) z!((*a + 1) * (*a - 2) - *a) | x!(5)", each(sends(("z", "13"))), False),
    ("int_wraps", "for(@a <- x) z!(*a + 1) | x!(268435455)", each(sends(("z", str(-TWO28)))), False),
    ("literal_pattern", "for(@7 <- x) z!(true) | x!(7) | x!(8)",
     each(sends(("x", "8"), ("z", "true"))), False),
    ("comparator_low",
     "for(@v <- x where *v < 5) r!(true) | for(@v <- x where *v >= 5) r!(false) | x!(3)",
     each(lambda r: r["sends"] == [("r", "true")] and r["receives"] == 1), False),
    ("comparator_high",
     "for(@v <- x where *v < 5) r!(true) | for(@v <- x where *v >= 5) r!(false) | x!(7)",
     each(lambda r: r["sends"] == [("r", "false")] and r["receives"] == 1), False),
    ("comparator_signed",
     "for(@v <- x where *v < 0) r!(true) | for(@v <- x where 0 <= *v) r!(false) | x!(0 - 3)",
     each(lambda r: r["sends"] == [("r", "true")]), False),
    ("countdown", "for(@(v + 1) <= c where 0 <= *v) c!(*v) | c!(2)",
     each(lambda r: r["sends"] == [("c", "0")] and r["receives"] == 1 and r["commits"] == 2), False),
    ("counter", "for(@n <= c where *n < 5) c!(*n + 1) | c!(0)",
     each(lambda r: r["sends"] == [("c", "5")] and r["commits"] == 5), False),
    ("ping_pong",
     "for(@n <= p where *n < 6) q!(*n + 1) | for(@n <= q) p!(*n + 1) | p!(0)",
     each(lambda r: r["sends"] == [("p", "6")] and r["commits"] == 6), False),
    ("clause_on_mask", "for(@(p xor q) <- x where *p) l!(*q) | x!(true)", each(sends(("l", "false"))), False),
    ("clause_boolean_atom",
     "for(a <- x) for(@n <- y where *a && *n < 3) z!(*n) | x!(true) | y!(1)", each(sends(("z", "1"))), False),
    ("clause_two_atoms",
     "for(@n <= x where 2 < *n && *n != 5) y!(*n) | x!(1) | x!(4) | x!(5)",
     each(lambda r: r["sends"] == [("x", "1"), ("x", "5"), ("y", "4")]), False),
    ("inverse_adder", "for(@(a + b) <- x) { l!(*a) | r!(*b) } | x!(7)", inverse_adder, True),
    ("even_coefficient", "for(@(v + v) <= x) y!(*v) | x!(6) | x!(7)",
     outcomes([("x", "7"), ("y", "3")], [("x", "7"), ("y", str(3 - TWO28))]), True),
    ("leaf_with_constants", "for(@(3 * v - 4) <- x) y!(*v) | x!(11)", each(sends(("y", "5"))), False),
    ("independent_gates",
     " | ".join("for(a <- c%d) d%d!(*a) | c%d!(true)" % (i, i, i) for i in range(4)),
     each(lambda r: r["sends"] == [("d%d" % i, "true") for i in range(4)]), False),
    ("parallel_counters",
     " | ".join("for(@n <= k%d where *n < 20) k%d!(*n + 1) | k%d!(0)" % (i, i, i) for i in range(4)),
     each(lambda r: r["sends"] == [("k%d" % i, "20") for i in range(4)] and r["commits"] == 80), False),
]

# programs the machine must stop on, with the fault code
FAULTS = [
    ("ill_sorted_boolean", "for(a <- x) for(b <- y) z!(*a && *b) | x!(5) | y!(true)", "fault 1"),
    ("ill_sorted_arithmetic", "for(@a <- x) z!(*a + 1) | x!(true)", "fault 1"),
    ("ill_sorted_leaf", "for(@(p && q) <- x) z!(*p) | x!(3)", "fault 1"),
    ("ill_sorted_clause", "for(a <- x where *a < 3) z!(*a) | x!(true)", "fault 1"),
]

# programs the compiler must reject
REJECTS = [
    ("clause_free_unknown", "for(@(a + b) <- x where *a < *b) y!(*a) | x!(7)"),
    ("comparison_in_term", "for(@a <- x) y!(*a < 3) | x!(1)"),
    ("non_affine_leaf", "for(@(a * b) <- x) y!(*a) | x!(6)"),
    ("mixed_languages", "for(a <- x) y!(*a && 1) | x!(true)"),
    ("quoted_send_payload", "x!(y!(true))"),
]


def sh(cmd, **kw):
    return subprocess.run(cmd, shell=True, capture_output=True, text=True, **kw)


def build(w, h):
    bdir = "%s/%dx%d" % (os.environ.get("RHO_BUILD", ROOT + "/build"), w, h)
    os.makedirs(bdir, exist_ok=True)
    with open(bdir + "/Config.bs", "w") as fh:
        fh.write("package Config where\n\ntype NT = %d\n\ntilesW :: Integer\ntilesW = %d\n\n"
                 "tilesH :: Integer\ntilesH = %d\n\nnumTiles :: Integer\nnumTiles = %d\n" % (w * h, w, h, w * h))
    r = sh("%s/bin/bsc -u -p %s:%s:+ -bdir %s -vdir %s -verilog %s/Top.bs"
           % (BSC, bdir, BSV, bdir, bdir, BSV))
    if r.returncode or "Error" in r.stdout + r.stderr:
        sys.exit("bsc failed:\n" + r.stdout + r.stderr)
    lib = BSC + "/lib/Verilog"
    r = sh("iverilog -o %s/sim -DTOP=mkTop -y %s -y %s %s/main.v %s/mkTop.v" % (bdir, lib, bdir, lib, bdir))
    if r.returncode:
        sys.exit("iverilog failed:\n" + r.stderr)
    return bdir + "/sim"


def run(sim, img, seed, ntiles, limit=6000):
    with tempfile.TemporaryDirectory() as d:
        rhoc.write_image(img, d)
        with open(d + "/ctl.hex", "w") as fh:
            fh.write("%08x\n%08x\n" % (seed, limit))
        out = sh("vvp " + sim, cwd=d).stdout
    return rhocheck.check(img, ntiles, out.splitlines())


def main():
    sizes = sys.argv[1:] or ["1x1", "2x2", "10x10"]
    failures = 0
    for name, src in REJECTS:
        try:
            rhoc.compile_source(src)
            print("FAIL  compiler accepted %s" % name)
            failures += 1
        except rhoc.CompileError as err:
            print("ok    compiler rejects %-22s (%s)" % (name, err))
    for size in sizes:
        w, h = (int(x) for x in size.split("x"))
        nt = w * h
        sim = build(w, h)
        big = nt > 16
        conc = 0
        with ThreadPoolExecutor(max_workers=os.cpu_count() or 2) as pool:
            for name, src, pred, nondet in TESTS:
                img = rhoc.compile_source(src)
                nseeds = (24 if nondet else 4) if not big else (4 if nondet else 1)
                seeds = [0x1234567 + 7919 * i * (nt + 1) for i in range(nseeds)]
                try:
                    rs = list(pool.map(lambda s: run(sim, img, s, nt), seeds))
                    ok = pred.weak(rs) if big and hasattr(pred, "weak") else pred(rs)
                    if name == "parallel_counters" and nt > 1:
                        ok = ok and all(r["concurrent_cycles"] > 0 for r in rs)
                    conc += sum(r["concurrent_cycles"] for r in rs)
                    note = "cycles %d-%d" % (min(r["cycles"] for r in rs), max(r["cycles"] for r in rs))
                except rhocheck.CheckError as err:
                    ok, note = False, str(err)
                print("%s  %-5s %-22s %2d seeds  %s" % ("ok  " if ok else "FAIL", size, name, nseeds, note))
                failures += not ok
            for name, src, want in FAULTS:
                img = rhoc.compile_source(src)
                try:
                    run(sim, img, 99, nt)
                    ok, note = False, "no fault was raised"
                except rhocheck.CheckError as err:
                    ok, note = want in str(err), str(err)
                print("%s  %-5s %-22s           %s" % ("ok  " if ok else "FAIL", size, name, note))
                failures += not ok
        print("      %s: cycles in which more than one tile committed: %d" % (size, conc))
    print("\n%s" % ("ALL PASS" if not failures else "%d FAILURES" % failures))
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
