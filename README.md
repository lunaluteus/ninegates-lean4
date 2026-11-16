<div align="center">

# 🀇🀇🀇🀈🀉🀊🀋🀌🀍🀎🀏🀏🀏
# Beyond Nine Gates

Classification of Full-Sided Mahjong Waits with 3n Ranks  
Structural formalization in Lean 4

[![arXiv](https://img.shields.io/badge/arXiv-2611.06944-b31b1b?style=flat-square&logo=arxiv&logoColor=white)](https://arxiv.org/abs/2611.06944)

</div>

This is the experimental **v3** rewrite, aligned with the rewritten paper.
The previous implementation is archived on [`v2`](https://github.com/lunaluteus/ninegates-lean4/tree/v2).
The new library replaces its API completely and proves the classification
structurally, without enumerating candidate hands or using `native_decide`.
Work is on Luna's fork; no upstream pull request is currently planned.

## The model

Nine Gates is the one-suit Mahjong wait `1112345678999`: drawing any of the nine
ranks makes a winning hand. We study the same question on `3*n` ranks, allowing
the order `n`, number of melds `m`, and copy bound `cap` to vary independently.
A full-sided wait has `3*m+1` tiles; every possible draw completes `m` melds
and a pair. Liveness additionally requires every draw to respect the copy bound.

`Mahjong.VirtualHand n` is an integer multiplicity vector on `Fin (3*n)`.
`Nonnegative` specifies actual hands. Integer subtraction lets us express
removing a pair or meld directly. A placement has one coefficient for each
legal sequence start and each triplet rank; nonnegative coefficients describe
actual meld decompositions, while integer coefficients describe virtual ones.

Lean indices are zero-based. The rank used in the paper's weighted sum and
congruences is `i.val+1`. The last two ranks are excluded from the sequence-start
type, and both final scan states are checked in the meldability criterion.

## Results proved

The main declarations are in the `Mahjong.VirtualHand` namespace:

- [`Classification`](Ninegates/Classification.lean): for `n>=2`, full-sided
  waits with `m=n+1` are exactly the eight families `A`, `B`, `B'`, `C`, `C'`,
  `D`, `D'`, and `E`. With live draws under copy bound four, only `A` remains.
- [`Standard/One`](Ninegates/Standard/One.lean): at order one and meld count
  two, the six full-sided waits are `(3,1,3)`, `(2,3,2)`, `(3,3,1)`,
  `(1,3,3)`, `(3,2,2)`, and `(2,2,3)`. All are live.
- [`Wait/Bounds`](Ninegates/Wait/Bounds.lean): every full-sided wait satisfies
  `m>n`, without a copy bound.
- [`Wait/Abundance`](Ninegates/Wait/Abundance.lean): sufficiently abundant hands
  of the required size are full-sided; adding any meldable hand preserves
  full-sidedness. At order one the sufficient threshold improves to `(2,2,2)`.
- [`Minimal`](Ninegates/Minimal/Defs.lean): minimality excludes removal of any
  nonzero meldable hand leaving a full-sided wait. Every full wait at `m=n+1`
  is minimal, and all order-one minimal waits are among the six above.
- [`Minimal/Maximum`](Ninegates/Minimal/Maximum.lean) and
  [`Minimal/Double/Minimal`](Ninegates/Minimal/Double/Minimal.lean): the largest
  minimal meld count `M(n)` exists for every positive order, `M(1)=2`, and
  `2*n <= M(n) < 8*n`. The minimal family `(3,2,...,2)` gives the first lower bound;
  the alternating families strengthen it to `9*n/2-3 <= M(n)` (integer division).
- [`Minimal/Alternating/Minimal`](Ninegates/Minimal/Alternating/Minimal.lean): both
  stronger even/odd alternating constructions are minimal full-sided waits, with
  meld counts `9*a+6` and `9*a+10`. Their canonical sequence coefficients have
  an exact formula for arbitrary order, draw, and pair. Critical draws rule out
  each elementary removal and hence every nonzero meldable removal.

[`Cardinality`](Ninegates/Cardinality.lean) proves the exact counts: eight
full-sided and minimal waits at `m=n+1` for `n>=2`, exactly one of them live;
six full-sided, minimal, and live waits at order one and meld count two.
There are no full-sided waits for `m<=n`, and no other minimal waits at order one.
The eight named families are proved distinct at every `n>=2`.

The Taiwanese counts `149/11/27` remain to be formalized. The paper's exact
general formula for `M(n)` is a conjecture;
it is neither assumed nor presented as proved. See [DEVELOPMENT.md](DEVELOPMENT.md)
for the detailed correspondence with the paper.

## Proof structure

Virtual meldability is characterized by size and rank sum modulo three.
Each virtual meldable hand has a unique canonical placement, with sequence
coefficients in `{0,1,2}`. Its triplet coefficients decide actual meldability.
This gives the scan criterion, local tile-moving rules, and interval properties.

The draw-pair relation records which pair can accompany each winning draw.
Missing-rank splits and class bounds force exact class sizes when `m=n+1`.
Two distinguished ranks then supply the only possible pairs. Counting the
sequence starts required by their moves determines the eight families.
Their explicit constructions prove sufficiency, and their coordinate patterns
exclude every live family except Nine Gates.

Minimality is defined for arbitrary meldable removals. A separate theorem
reduces it to single triplet and sequence removals; the latter may either use
a canonical sequence or borrow three covered triplets. No bound on the number
of ranks or candidate hands is used in these arguments.

## Build and validate

Use the pinned **Lean 4.35.0** toolchain and Mathlib revision in
[`lake-manifest.json`](lake-manifest.json):

```sh
lake exe cache get
lake build --wfail
lake env lean -j2 -M4096 -DwarningAsError=true Audit.lean > axioms.log
python3 scripts/check_axioms.py Audit.lean axioms.log
```

The default library target is `Ninegates`. [`Ninegates.lean`](Ninegates.lean)
imports the complete library. The axiom audit covers the foundational results,
classification, bounds, constructions, and explicit examples; it checks the
expected declarations and rejects extra diagnostics or forbidden axioms.

The library has no placeholder proofs and uses only `propext`,
`Classical.choice`, and `Quot.sound`. Small explicit examples and fixed prefix
states use `decide +kernel`; no proof uses native evaluation.

### Comparator

The new challenge checks the actual classification, including live uniqueness,
order one, minimal classification, attained coarse and improved bounds, and
both full-sidedness and minimality of the alternating constructions, and the
exact standard-family cardinalities:

```sh
lake comparator --config=ComparatorChallenges/config.json
```

This uses the Comparator bundled with the pinned Lean toolchain and requires
`bubblewrap` with working user namespaces on Linux. The normal command keeps
the sandbox enabled. No external checker is enabled by this configuration.

[`Challenge.lean`](ComparatorChallenges/Challenge.lean) fixes the theorem
statements and imports the definitions they refer to, without importing the
classification or its solution. Its intentional theorem holes are confined to
the challenge and excluded from the default library build.
[`Solution.lean`](ComparatorChallenges/Solution.lean) supplies the library's
proofs of those same statements. Comparator exports and checks the proofs,
compares their statements against the challenge, and permits only the three
standard axioms above. This complements the larger axiom audit; it does not
claim to certify unfinished results or replace review of the definitions.

See the [Lean proof-validation documentation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
for the meaning and trust assumptions of these checks.

## Library map and conventions

| Path | Contents |
| --- | --- |
| `Hand/` | Vectors, elementary patterns, sums, classes, intervals, reversal |
| `Meldable/` | Placements, canonicalization, scan, movement, splitting, removal |
| `Wait/` | Draw-pair graph, positivity, class bounds, pillars, constructions |
| `Standard/` | Eight named families and the six order-one hands |
| `Classification.lean` | Classification and live uniqueness |
| `Minimal/` | Arbitrary removals, maximal meld counts, lower-bound families |
| `*Examples.lean` | Explicit examples checking boundaries and hypotheses |

We aim for readable structural arguments and reusable local lemmas. Follow the
[Lean `grind` annotation guidance](https://lean-lang.org/doc/reference/latest/The--grind--tactic/Annotating-Libraries-for--grind/):
apply lemmas without conditionals use `@[simp]`; conditional apply lemmas use
`@[grind]`. Avoid redundant annotations. Keep finite sums inside their owning
modules and provide lemmas for downstream use. Definitions and theorem
statements deserve the same care as their proofs.

## Citation

```bibtex
@misc{xue_beyond_2026,
  title = {Beyond Nine Gates: Classification of Full-Sided Mahjong Waits with $3n$ Ranks},
  doi = {10.48550/arXiv.2611.06944},
  number = {{arXiv}:2611.06944},
  publisher = {{arXiv}},
  author = {Xue, Shubin and Zhong, Xingyu},
  eprinttype = {arxiv},
  eprint = {2611.06944},
}
```
