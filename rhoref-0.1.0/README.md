# rhoref

Reference implementation of the rho calculus with Boolean arithmetic and of the
tuple-space machine that renders it in hardware. It conforms to the design
specification, draft 0.2 (`rho-bool-hardware-spec`), and is the "reference
library" of that document's Section 6.1: the executable semantics that the
compiler, the checker and the hardware are measured against.

It is plain Haskell. It needs GHC and the libraries that ship with it
(`base`, `containers`, `mtl`); nothing from Hackage.

## Build and run

    make            # builds build/rhoref and build/rhoref-test
    make test       # runs the verification suite (about two seconds)

    build/rhoref run examples/and.rho
    build/rhoref run examples/inverse-xor.rho --seed 2
    build/rhoref run examples/half-adder.rho --egress s,c
    build/rhoref norm examples/and.rho

`rhoref run` loads a program into the machine model and steps it to quiescence
with every step checked against the reference semantics. `--egress` names the
channels that are output ports; `--seed` seeds the entropy source.

Built and tested with GHC 9.14.1. A `rhoref.cabal` file is included but has
not been exercised: the build machine had no access to the Hackage index, which
cabal insists on even for a package with no external dependencies.

## Source syntax

    P ::= 0 | true | false | ~P | P && P | P || P | P xor P
        | for(ptrn <- x){ P } | for(ptrn <= x){ P }      // <= is the persistent receive
        | x!(P) | P | P | *x | (P) | { P }
    x ::= @P | identifier
    ptrn ::= identifier | @dp
    dp ::= 0 | true | false | identifier | ptrn!(dp) | ~dp | dp && dp | dp || dp | dp xor dp

Precedence, loosest first: `|`, `||`, `xor`, `&&`, `~`. A `for` body is a
single term at the `~` level, so use braces for anything larger. `//` starts
a comment.

An identifier that no enclosing `for` binds is a *symbol*: a distinct closed
name chosen by the compiler (the k-th symbol is the numeral `@0`,
`@(@0!(0))`, ...). This is a convenience for writing closed programs and is
not part of the calculus.

## What is here

| Module | Spec | Content |
|---|---|---|
| `Rho.Syntax` | 3.1 | Surface syntax and parser |
| `Rho.Core` | 3, 4 | Scoping to de Bruijn indices; normal forms; truth-table algebra; pattern compilation; pattern programs; the matching oracle; instantiation; the reduction relation with all redexes |
| `Rho.Machine` | 5 | Word-level model: hash-consed heap with reference counts and deferred free, normalising constructors, send and receive tables, matcher and mask solver, LFSR arbiter, the step (pick, match, commit, explode), instantiation with the closed shortcut, ingress and egress, decision/insert/residue streams, faults, replay, the abstraction function, the invariant audit |
| `Rho.Checker` | 8.3 | The step-refinement checker |
| `app/Main.hs` | | Command-line driver |
| `test/Test.hs` | 8.2, 8.5 | The verification suite |

The machine model abstracts from clock cycles and from the packing of nodes
into memory words. It keeps everything else: its states are the machine's
boundary states and its steps are the machine's steps, so an RTL
implementation can be compared with it record for record through the decision
log.

## Verification suite

`make test` runs these, and all pass.

| Layer | What is checked |
|---|---|
| V1 | Normal forms decide structural congruence: 4000 random terms and congruence-preserving rewrites of them, against a brute-force decision procedure that shares no code with the normaliser. Boolean normal forms exhaustively for all 256 functions of three variables. |
| V3 | The machine's interner: equal words exactly for congruent terms, both for reference normal forms and for raw terms normalised by the machine's own constructors; readback equals the reference normal form. |
| | Instantiation commutes with normalisation, in the reference and in the machine, against textbook substitution on raw terms. |
| | Pattern programs, and the machine's matcher on heap words, against the oracle that computes match sets from the source pattern by enumeration. |
| V5 | The arbiter: an entropy witness for every `n <= 64` and every `u < n`. (The LFSR's period, 2^32 - 1, was confirmed separately by running it through its full cycle.) |
| V4 | 1200 runs of random programs under the step-refinement checker, with the invariant audit and the abstraction function checked at every boundary; and 200 more on a deliberately tiny machine, where every resource fault must be detected. |
| V6 | Redex coverage: on nine small programs, the set of transitions the machine takes over 400 seeds equals the reference transition graph exactly. |
| V7 | Replay: a run reproduced from its decision log on a machine with a different seed passes through identical boundary states and emits identical egress. |
| V9 | Persistent receive against the reflective encoding, at the level of egress traces. |
| 8.5 | The directed programs of the spec, plus adders, the general drop, deep send patterns, partial instantiation, ingress, and negative tests. |

The suite was itself tested by mutation: eighteen deliberate bugs were
injected, fourteen in the machine model and four in the reference, and every
one is caught. Two were not caught at first (parallel components left
unsorted, and `@(*x)` not collapsed to `x`); they exposed that the interner
had only been tested on terms the reference had already normalised, which is
why the raw-term and instantiation tests exist.

## Not included

- **The hardware.** Bluespec and Clash sources and generated Verilog are the
  next deliverable. Neither toolchain was available where this was built.
- **Node packing and memory images.** `NodeCodec` and the block-RAM
  initialisation files are deferred to the RTL, since the packing must be
  fixed together with it.
- **The sort checker.** The spec treats the spatial-behavioural type system
  as a black box. The reference raises sort faults dynamically.
- **Proofs.** Obligation 1 (persistent receive weakly bisimilar to its
  encoding) is tested on egress traces only. Everything here is evidence by
  testing, not proof.
- **V2 and V8 as stated**, which concern generated Verilog and RTL assertions.

## Findings against the spec

Writing and testing the reference turned up six points where draft 0.2 is
wrong, incomplete or ambiguous. The reference implements the corrected
reading in each case.

1. **A closed bit is not enough (5.2).** Whether a receive node is closed
   depends on whether its body's free variables are all bound by its own
   pattern, which a one-bit flag on the body cannot tell. The node header
   needs a free-variable depth (the least `k` such that every free index is
   below `k`); a node is closed when it is zero, and instantiation skips a
   subterm when its depth is at most the number of binders passed.
2. **Sort faults are not complete (5.10, D10).** A Boolean law can erase an
   ill-sorted operand before anything inspects it: `*v xor *v` normalises to
   `false` and `*v && true` to `*v`, whatever `v` is later bound to. So
   `FAULT_SORT` fires only for operands that survive normalisation, and its
   never firing does not show a program is well sorted. The flag is a
   debugging aid; the sort checker carries the whole obligation.
3. **Bare variables (5.5 against Appendix A).** Section 5.5 says a bare
   Boolean-sorted variable is a projection leaf; the appendix compiles the
   AND gate's `a` to `NBIND`. The reference follows the appendix: a variable
   is a Boolean (mask) variable exactly when it occurs under a Boolean
   operator in the pattern, and then all its occurrences are leaves.
   Otherwise it is bound structurally, and its sort is checked where it is
   used.
4. **A Boolean leaf on a non-Boolean (3.4, 5.10).** The reference treats
   this as a sort fault, not as a failed match, in line with the fault table.
   This means a pattern such as `@true` cannot be used to test whether a
   message is a Boolean.
5. **Replication by encoding (8.5).** The spec says the run is unbounded
   "until heap fault". Hash-consing shares every copy, so the heap does not
   grow; the run ends on the receive-table bound if the replicated process
   leaves receives behind, and otherwise never.
6. **Entropy sampling (5.6).** "Sampled once per choice" leaves the relation
   between samples open. The model advances the LFSR 32 positions per choice,
   so successive choices use disjoint bits. Hardware need not match this,
   since runs are compared through the decision log and not through seeds.

Two modelling choices that are refinements, not corrections: parallel
composition is built by merging sorted component lists where the spec says
sorted insertion (the result is the same canonical list), and a receive's
environment is held in the table entry where the spec says a heap vector (the
length bound `E` and the reference counts are enforced all the same).
