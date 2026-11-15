# rho tile array, stage 1, in Bluespec

This is the Bluespec implementation of **stage 1** of the design
specification "A hardware rendering of the rho calculus with Boolean
arithmetic and builtin data" (draft 0.6, Section 10): the concurrent tile
array with Boolean and integer immediates. It is written in Bluespec
Classic (BH) syntax throughout, as decision D9 requires, and is tested in
simulation against a step checker.

It is not the whole specification. Stages 2 to 6 are not written; the list
is under "Not implemented" below.

## Layout

    bsv/RhoTypes.bs    words, image formats, and the pure functions:
                       operands, expressions, matcher and mask solver,
                       affine solver, guard, arbiter, entropy, ownership
    bsv/Tile.bs        one tile: tables, COMMIT, ARRIVE, EXPLODE, router, SCAN
    bsv/Top.bs         the array and its mesh links; simulation harness
    bsv/Config.bs      array dimensions (rewritten per build by the tests)
    tools/rhoc.py      compiler from source text to ROM images
    tools/rhocheck.py  step checker over a simulation log
    tools/run_tests.py directed programs at several array sizes
    tools/mutate.py    mutation run over the Bluespec source
    tests/             example source

## What is implemented

| Specification | Here |
|---|---|
| Source language of Section 3: Boolean and arithmetic expressions as separate languages; crisp `where` clause; Boolean and arithmetic patterns | `rhoc.py`, with the stage 1 limits below |
| Canonical forms: truth table over a minimal ordered support; constant folding; clause as a truth table over mask variables and atoms | `rhoc.py` |
| Tile as concurrent rules, at most one COMM per cycle (D19, D20) | `Tile.bs`: rules `commit`, `arrive`, `explode`, `route`, `tick` fire in the same cycle |
| Three-stage choice with no pruning; three 32-bit Galois registers, taps 32, 22, 2, 1, advancing 32 positions per clock | `choose`, `nthSet`, `lfsr32` |
| Pattern operations NBIND, QZERO, BLEAF, ALEAF; mask solver | `matchPair` |
| Affine solver with pivot, precomputed inverse and free values | `solveLeaf`; free values from a 64-bit register, taps 64, 63, 61, 60 |
| Guard programs: less-than, equal, Boolean atom, table restricted to the mask | `matchPair`, in the same cycle as the match |
| Evaluator for inline operations | `evalX`: add, subtract, multiply, negate; one step per cycle |
| Mesh, dimension-ordered routing, rotating grant, inbound never waits on outbound | rule `route`, `Top.bs` |
| Default namespace map: content of the name modulo the number of tiles (D31) | `ownerOf` |
| Persistent receive as a primitive (D3) | `rpersist` |
| Faults halt every tile on the following cycle | `FAULT_SORT`, `FAULT_STORE`, `FAULT_STACK` |
| Quiescence | per-tile scan of every pair of slots, plus empty queues, in every tile in one cycle |
| Per-tile, cycle-stamped decision log; inserts and residues reported | `$display` records `C`, `S`, `R`, `V`, `F` |

## Stage 1 limits and departures from the specification

1. **Integers are 29 bits wide**, not 64. Stage 1 has no heap, so every
   value is an immediate. The integer width is a parameter of the design
   (the specification already asks for an 8-bit instantiation in layer
   V20); arithmetic wraps and the solver works modulo 2^29.
2. **Payloads are values**: Nil, a Boolean, an integer, or the process
   named by a symbol. A quoted send or receive as a payload needs the heap.
3. **Patterns are shallow**: one operation against the payload.
4. **Clauses** compare operands (a variable or a numeral), not compound
   terms, and have at most two atoms. `/` and `%` are not provided.
5. **Packets are one flit**, as stage 1 allows; wormhole routing of term
   streams belongs to stage 2.
6. **The program starts as one job in tile 0**, which explodes it over the
   mesh. The specification has the compiler place the initial components.
   The reachable processes are the same.
7. **A tile delivers to itself through its router**, so every insert into
   the tables comes from the inbox. This costs two cycles on a local
   delivery and removes a second writer of the tables.
8. **The quiescence scan is sequential**, one pair of slots per cycle, so
   quiescence is reported 64 to 128 cycles after the last activity.
9. **The log is simulation output.** There is no log port, no stall on a
   full log buffer, and no board wrapper; those are proposed in the
   development specification and not ruled on.
10. **No replay mode** in the arbiter.
11. **A sort fault is raised when a pair is tried**, not only when it is
    committed, as Section 3.4 says of leaves.

## Not implemented

Stage 2: heap, interner, reference counts, instantiation of quoted code,
general drop, replication by encoding, term-stream packets, namespace
formulae and the class automaton, 64-bit and boxed integers, fixed-point,
bytes, strings, tuples, lists. Stage 3: deep patterns, the multi-cycle
matcher, sets and maps. Stage 4: service units. Stage 5: grades and
weighted choice. Stage 6: the typed fast path.

Nothing has been synthesised for an FPGA. There are no area or timing
figures, and `commit` is one long combinational path that will need
pipelining. The ROM words are wide and are read combinationally.

## Verification

`tools/rhocheck.py` rebuilds every tile's tables from the log alone and
checks, against a reference written from the specification:

- every commit names a send and a receive on one channel, and the chosen
  row and values are a solution of the pattern and satisfy the clause
  (arithmetic solutions are checked by substituting them into the leaf,
  not by repeating the solver);
- every insert is a component that some earlier continuation was owed, and
  reaches the tile that owns its channel;
- at quiescence nothing is still owed and no tile holds a redex;
- no tile commits twice in a cycle.
- the tables each tile reports at the end are exactly the tables the
  checker reconstructed from the log.

The checker and the hardware read the same compiled image, so the checker
does not test the compiler. Each directed program therefore also states
what it must leave behind.

Results are in `RESULTS.txt`.

## Running

    export PATH=$BSC_HOME/bin:$PATH        # bsc 2026.07.1, Icarus Verilog
    python3 tools/run_tests.py 1x1 2x2 10x10
    python3 tools/mutate.py

One program by hand:

    python3 tools/rhoc.py tests/and_gate.rho run/     # writes rom*.hex, image.json
    printf '%08x\n%08x\n' 12345 6000 > run/ctl.hex    # seed, cycle bound
    (cd run && vvp ../build/2x2/sim > log.txt)
    python3 tools/rhocheck.py run/image.json 4 run/log.txt

## Source syntax

    for(a <- x) for(b <- y) z!(*a && *b) | x!(true) | y!(false)
    for(@(v + 1) <= c where 0 <= *v) c!(*v) | c!(2)
    for(@(a + b) <- x) { l!(*a) | r!(*b) } | x!(7)

The null process is written `Nil`. In the specification's grammar `0` is
both the null process and the numeral zero; see finding 1.

## Findings for the specification

1. **`0` is ambiguous in draft 0.6.** With numerals in the grammar,
   `x!(0)` reads as a send of the null process or of the integer zero. The
   implementation writes `Nil` for the process, as rholang does. The
   specification needs the same repair.
2. **The width of the free-value register depends on the integer width.**
   Section 6.9 gives 64U bits and taps for U = 2 at 64-bit integers. The
   rule that matters is that the register is wider than the free bits of
   one leaf; the specification should state it that way.
3. **A clause over a determined unknown needs a multiplication in the
   match path**, to compute the unknown before the guard runs. Section 6.8
   says a guard of additions and comparisons is combinational; that is
   true only when the unknown's coefficient is 1 or -1.
4. **Quiescence needs every queue of every tile sampled in one cycle.**
   Section 6.10 describes the per-tile scan and leaves the array-level
   condition implicit.
