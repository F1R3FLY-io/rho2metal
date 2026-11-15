#!/usr/bin/env python3
"""Mutation run: inject one bug at a time into a copy of the Bluespec
source and confirm that the directed suite on a 2x2 array fails. A mutant
that survives marks a hole in the tests.
"""
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

MUTANTS = [
    ("priority encoder for the row", "Tile.bs",
     "row = nthSet res.mmask (choose l3 cnt)", "row = nthSet res.mmask 0"),
    ("priority encoder for the receive", "Tile.bs",
     "ri = truncate (nthSet (zeroExtend rMatch) (choose l2 nR))", "ri = truncate (nthSet (zeroExtend rMatch) 0)"),
    ("clause ignored", "RhoTypes.bs",
     "mask = if hasg then mask0 & gmask else mask0", "mask = mask0"),
    ("solver without the inverse", "RhoTypes.bs",
     "pv = (((rr >> r.rt) * r.roinv) & lm)", "pv = ((rr >> r.rt) & lm)"),
    ("free values constant", "Tile.bs",
     "(v0, v1) = solveLeaf info res.md l4", "(v0, v1) = solveLeaf info res.md 0"),
    ("send not consumed", "Tile.bs",
     "rmS.wset si", "noAction"),
    ("persistent receive consumed", "Tile.bs",
     "if info.rpersist == 0 then rmR.wset ri else noAction", "rmR.wset ri"),
    ("everything owned by tile 0", "Tile.bs",
     "let o = ownerOf ch", "let o = 0"),
    ("unsigned comparison", "RhoTypes.bs",
     "signedLT (intOf av) (intOf bv)", "(intOf av) < (intOf bv)"),
    ("quiescence without the scan", "Tile.bs",
     "idle = started && clean && qEmpty", "idle = started && qEmpty"),
    ("mask rows not limited", "RhoTypes.bs",
     "mask0 = if isB then rowsMask & bm else 1", "mask0 = if isB then bm else 1"),
    ("sort of a Boolean leaf unchecked", "RhoTypes.bs",
     "psort = (isB && tg /= tBOOL) || (isA && tg /= tINT)", "psort = (isA && tg /= tINT)"),
]


def main():
    survived = 0
    for name, fname, old, new in MUTANTS:
        with tempfile.TemporaryDirectory() as d:
            shutil.copytree(ROOT + "/bsv", d + "/bsv")
            path = d + "/bsv/" + fname
            src = open(path).read()
            if src.count(old) != 1:
                sys.exit("mutant %r does not apply" % name)
            open(path, "w").write(src.replace(old, new))
            env = dict(os.environ, RHO_BSV=d + "/bsv", RHO_BUILD=d + "/build")
            r = subprocess.run([sys.executable, ROOT + "/tools/run_tests.py", "2x2"],
                               capture_output=True, text=True, env=env)
            fails = [l.split()[2] for l in r.stdout.splitlines() if l.startswith("FAIL")]
            if r.returncode == 0:
                survived += 1
                print("SURVIVED  %s" % name)
            else:
                print("killed    %-36s by %s" % (name, ", ".join(fails[:4]) or r.stdout[-200:] + r.stderr[-200:]))
            sys.stdout.flush()
    print("\n%d of %d mutants killed" % (len(MUTANTS) - survived, len(MUTANTS)))
    sys.exit(1 if survived else 0)


if __name__ == "__main__":
    main()
