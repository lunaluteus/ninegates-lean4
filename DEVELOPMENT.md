# Development status

Experimental work on Luna's `v3` branch. No pull request is planned at present.
`README.md` has been rewritten for v3 with sun123zxy's explicit authorization.
`AGENTS.md` remains unchanged.

The target is the rewritten paper: independent order `n`, meld count `m`, and
copy bound, with a structural, non-enumerative proof of the classification.
The default library target is `Ninegates`. The previous API, finite
enumeration and old Comparator reduction challenge have been removed from this
branch; the complete previous implementation is archived on `v2` at
`e45fd512ebb2cd0bac7d69690f3163647bdc3bc8`.

## Model

`Mahjong.VirtualHand n` is an integer vector on `Fin (3*n)`; `Nonnegative`
specifies actual hands. Subtraction is integer subtraction. The paper rank of
index `i` is `i.val+1`, including in the rank sum and congruence classes.
`Winning m`, `IsFullWait m`, and `IsLiveFullWait cap m` keep all three parameters
independent. Explicit size conditions exclude vacuous zero-rank full waits.

`Hand/Defs` and `Hand/Basic` contain the elementary patterns and linear
statistics. `Meldable/Defs` and `Meldable/Basic` introduce integer placements,
nonnegative placements, and the necessary congruence conditions. `Wait` starts
the draw-pair relation and its connection to full-sidedness and liveness.

`Meldable/Coordinates` hides the finite sums behind the coordinate equation,
using zero extension to integer indices. Its injectivity argument works over
any cancellative additive monoid, so it proves uniqueness both over the
integers and over residues. `Sequence` proves uniqueness of sequence placements;
`Canonical` constructs and proves uniqueness of canonical virtual placements,
preserves nonnegativity when present, and reduces meldability of a known
canonical placement to nonnegativity of its triplet coefficients.

`Hand/Classes` groups the ranks into blocks of three. `Meldable/Recovery`
proves the sequence recurrence, its closed form, and the two endpoint formulas.
It constructs a sequence placement exactly when all three integer class sizes
are equal; nonnegative recovered coefficients characterize actual sequential
meldability. `Meldable/Virtual` balances congruent class sizes using integer
triplets, proving that virtual meldability is equivalent to both size and rank
sum vanishing modulo three, and hence to a unique canonical virtual placement.

`Meldable/Scan` computes the canonical sequence coefficients and integer triplet
quotients. It proves the triplet-greedy recurrence, identifies the computed
placement with the unique canonical placement, and establishes the full scan
criterion: both right-end sequence values vanish and every triplet quotient is
nonnegative. Prefix congruence is equivalent to equality of the canonical
sequence prefixes. `ClosedForm` proves the weighted-prefix formula modulo three.

`Meldable/Reverse` transports placements, canonicalization, and both sequence
and general meldability under reversal. `Moving` gives the local sequence
replacement and the exact canonical borrow/carry update. It proves all four
rows of the rightward tile-moving table and that any successful long rightward
move permits the first step. The proof uses equality of the first three
triplet quotients, obtained from exact prefix agreement. `Interval` iterates
these steps and reverses them for leftward moves, proving the interval property
inside each congruence class. Its endpoint version also works when the original
hand is not meldable.

`SequentialMoving` writes the telescoping long-range sequence update explicitly
on integer indices. Uniqueness then gives the required-sequence criteria in
both directions: starts `i,i+3,...,j-3` for a rightward move, and
`j+1,j+4,...,i-2` for a leftward move. These are structural proofs for arbitrary
order, with no enumeration of hands.

`Meldable/Triplets` proves that adding integer triplets preserves the canonical
sequence part and translates the canonical triplet coefficients. A triplet can
be removed exactly when its canonical coefficient is positive. `Preserve`
proves that a successful step from a rank with no canonical triplet preserves
all existing triplets.

`Wait/Graph` introduces the fixed class, the class involution, incoming
intervals, and two-pair decompositions. It proves the equivalence between a
bidirectional edge on distinct ranks and a two-pair decomposition. `Classes`
proves that, for size one modulo three, each nonfixed class size plus one is
congruent to the fixed class size. `Consecutive` proves that two consecutive
edges yield a mutual edge at an intermediate rank in the same class as the
outer vertices. It follows the moving tile by well-founded induction while
preserving the middle vertex's triplet; a self-loop is allowed as the witness.
`TwoPair` derives the full-wait two-pair theorem for independent `n,m`: every
used pair in a nonfixed class participates in a two-pair decomposition, and
such a decomposition always exists. The pairs lie in different nonfixed
classes and the actual remainder has `m-1` melds.

`Hand/Cut` gives linear restrictions to the ranks strictly before and after a
cut, keeping the original rank space. `Meldable/Split` proves that a zero tile
count in an actual placement forces all crossing sequence coefficients and the
triplet at the cut to vanish. Restricting the placement then proves that a
hand missing that rank is meldable exactly when both sides are meldable. No
canonical-placement assumption is needed.

`Wait/Missing` proves the side-size residues and the opposite-side rule when
there are waiting tiles on both sides of a missing rank. Every draw on a given
side has the same congruence class. It also proves that a pair receiving draws
from both sides requires at least three copies in the original hand.
`Positive` derives positivity at every interior rank of a full-sided wait,
including order one: the only exceptional cut would be the middle of three
ranks, but the middle draw then has no available pair.

`Hand/Interior` gives the indicator hand with one copy of every interior rank
and zero at both boundaries. Its class sizes are `n` in class two and `n-1` in
each boundary class. The excess above this hand is nonnegative in a full wait.
Class-size monotonicity and bounds on one or two terms turn small class totals
into constraints on individual multiplicities. `Neighbours` constructs a rank
of either other congruence class within two steps on each side when there is
room.

`Wait/Bounds` proves that the fixed class contains at least `n` tiles and each
nonfixed class at least `n+1`. If a class of size at most `n` supplies a pair,
it must be a boundary class with a unique interior rank of multiplicity two.
For a nonfixed class, full-sidedness forces draws from both sides to use that
rank, contradicting the three-copy requirement. Summing the three class bounds
proves `IsFullWait.meldCount_gt_order`: every full-sided wait satisfies `m>n`.
The proof uses no bound on tile multiplicities.

`Meldable/Statistics` proves that each sequence contributes one tile to every
class, and that a placement's class size equals its sequence count plus three
times its triplet count in that class. In an actual meldable hand, a class
larger than another class must supply a removable triplet. This conclusion
retains an actual meldable remainder, not just a large original multiplicity.

`Wait/ClassSizes` proves the exact sizes at `m=n+1` and `n>=2`: the fixed class
has `n` tiles and every other class has `n+2`. Congruence and the lower bounds
first reduce the sizes to two possibilities, including the order-one exception.
In the unwanted case, every nonfixed draw requires triplets in both its own
class and the fixed class. If the fixed class is not class two, a draw of
multiplicity one in class two cannot supply the required triplet. If it is
class two, all fixed-class triplets are forced to a single original rank.
Removing that triplet leaves a missing rank while preserving waiting on both
other classes, contradicting the cut constraints. The assumption `n>=2` is
used explicitly and the proof does not enumerate hands.

`Wait/Pillars` proves that the fixed class has at most one original rank of
multiplicity two, while each nonfixed class has a unique rank of multiplicity
at least two; that rank has three or four copies. Removing the two forced
triplets from fixed-class winning remainders and splitting at a hypothetical
extra pair excludes any second candidate. `PillarPlacements` strengthens this
to every actual winning placement of a fixed-class draw: its sequence count is
`n-1` and its entire triplet vector consists of one triplet at each pillar.

`PillarPair` packages the two pillars and determines all edges from either
nonfixed class. The only two-pair decompositions are the pillar pair and its
exchange. `PillarRemainder` proves that removing the two pairs leaves a sequential
hand of size `3n`. Moving a tile from either pillar to any rank in its own class
preserves sequential meldability. These are the structural inputs for the
eight-family argument below.

`Meldable/Required` indexes each pillar's required starts by `Fin (n-1)` and
proves that the row is injective and has exactly `n-1` entries. Moving to both
ends of the class forces every entry to occur. Generic nonnegative-weight
bounds control row unions and their overlap; equality forces the entire
sequence vector to be the indicator of the required set.

`RequiredTwo` and `Wait/Required` settle the fixed-class-two counting step:
the two rows exhaust all possible common middle starts, so the paper pillar
ranks are `p in {1,4}`, `q in {3n-3,3n}`, and every sequence coefficient is
fixed by their union. `RequiredOne` and `Wait/RequiredOne` settle the
fixed-class-one step: a sequence outside both rows forces them to coincide,
so `p=3`, `q=3n-1`, and the remainder is the periodic row plus a sequence
starting at paper rank one or two. The proof explicitly handles the hypothetical
pillar at rank two using the missing-rank split.

`Hand/Reverse` proves size and rank-sum reversal identities, and `Wait/Reverse`
transports full and live waits with fixed class sent to `1-s`.

`Hand/Segment` describes intervals of single tiles and their sizes.
`Meldable/Segment` partitions any interval of length divisible by three into
sequences, including the two pieces obtained by removing an appropriate tile.
`RequiredCoordinates` gives arithmetic row membership and proves its converse:
containing the row suffices for all moves in that class. `RequiredPatterns`
identifies the two forced coefficient templates with their hand vectors.

`Standard/Defs` defines the paper's eight named families with interval vectors;
`Standard/Basic` proves their coordinate patterns and reflection identities.
The description of `E` includes the overlapping end patterns at order two.
`Standard/Necessity` proves every full-sided `(n,n+1)` wait for `n>=2` belongs
to these families, using the row argument and reflection for fixed class zero.

`Wait/Construction` turns the two rows and fixed-class winning decompositions
into full-sidedness. `Standard/WaitTwo` and `Standard/WaitOne` verify all the
family constructions with sequences and triplets. For `D`, the bottom
fixed-class draw pairs at paper rank four; all its other fixed-class draws
self-pair. The interval lemma verifies the remaining tiles in each case.

`Classification.isFullWait_iff_eightFamily` is the resulting non-enumerative
eight-family equivalence. `liveFullWait_unique` and `isLiveFullWait_iff_eq_A`
derive live uniqueness under copy bound four: every other family has a
coordinate of multiplicity four, while every coordinate of `A` is at most three.
These declarations are in the `Mahjong.VirtualHand` namespace.

`Standard/One` handles order one separately. Each class contains one rank, so
the two class-size alternatives give precisely the six displayed hands.
Their eighteen explicit draw-pair decompositions are verified by kernel
evaluation of the proved meldability criterion; no hands are searched to
establish necessity. All six are live. `Standard/Valid` also proves that every
full-sided `(n,n+1)` wait, including order one, respects the four-copy bound.

`Meldable/Coverage` bounds the tile contribution of canonical sequences by the
paper's threshold `(2,4,6,...,6,4,2)`, with `(2,4,2)` at order one.
`Wait/Abundance` proves every congruence-permitted draw-pair edge above this
threshold, and hence full-sidedness whenever the hand has the required size.
The proof uses the canonical virtual placement: each triplet coefficient has
three times its value at least `-2`, so integrality forces nonnegativity.
At order one this threshold can be improved to `(2,2,2)`:
`drawPair_orderOne_of_two` and `isFullWait_orderOne_of_two` prove the stronger
statement using nonnegative virtual meldability. The paper's stated threshold
remains sufficient.

`Wait/Add` preserves all draw-pair edges and full-sidedness under adding an
arbitrary actual meldable hand. `Minimal/Defs` defines minimal full waits by
excluding every nonzero meldable removal leaving a full wait of any meld count.
`Minimal/Basic` proves that every full wait with `m=n+1` is automatically minimal.
The eight-family classification therefore also classifies minimal waits at
that meld count.

`Meldable/OrderOne` proves that nonnegativity and the congruence conditions
suffice for meldability at order one. `Minimal/One` uses the class bounds to
place one of the six smallest full waits below any order-one full wait, with
the same fixed class. Their difference is nonnegative and virtually meldable,
hence actually meldable. Thus every minimal order-one full wait has `m=2` and
is one of the six classified hands.

`Meldable/Large` proves that seven tiles at one rank of a meldable hand force
a removable triplet. `Minimal/Upper` applies this uniformly to all winning
remainders when an original rank has at least nine copies. Removing that
triplet preserves full-sidedness, so every minimal full wait has multiplicities
at most eight and satisfies `m<8n`.
`Minimal/Maximum` defines `maxMinimalMeldCount n` and proves the maximum is
attained at every positive order, with `M(1)=2`.

`Minimal/Double/Full` constructs the paper's `(3,2,...,2)` family at meld count
`2n`, including live full-sidedness. Fixed-class draws move a tile within the
sequential hand of all twos; the other two classes use two doubled intervals
and two triplets. `Double/Rigidity` proves that the first draw must self-pair
and that a draw at the middle of a three-rank block forbids that block's
sequence in every actual winning placement.

`Double/Minimal` applies these constraints to an arbitrary meldable removal.
The first draw forces the removed hand to contain only block sequences, with
no triplets; the corresponding middle draws force every such coefficient to
vanish. Thus the family is minimal. `maxMinimalMeldCount_bounds` and
`exists_maximal_minimal_meldCount` now give the full paper bound `2n<=M(n)<8n`,
including attainment and maximality. The alternating constructions below
strengthen the lower bound.

`Meldable/RemoveSequence` gives an exact removal criterion: either the canonical
sequence coefficient is positive, or all three covered ranks supply a canonical
triplet. In the second case, replacing those three triplets by two sequences
provides the remaining hand. `Meldable/Elementary` proves that every nonzero
meldable hand has an elementary meld that can be removed. `Minimal/Criterion`
therefore reduces minimality to excluding individual triplet and sequence
removals, while retaining the paper's definition for arbitrary meldable removals.

`Minimal/Alternating` starts the two stronger even/odd families. Their common
coordinate definition, sizes, and the forced location of later draws' pairs
are formalized: any draw at zero-based index at least four must pair among the
first three ranks. `Alternating/Class` proves their fixed classes are two and
zero. `Alternating/Full` proves full-sidedness for all parameters, with meld
counts `9a+6` and `9a+10`. The boundary-sensitive abundance estimate covers all
but the short exceptional prefix, whose fixed states are checked in the kernel
and transferred across orders using `Meldable/Prefix`.

`Alternating/Scan` proves a closed formula for every legal canonical sequence
coefficient after any draw and pair removal. It combines the base sequence
recurrence with two single-tile impulses. The formula is valid for arbitrary
orders and indices; it does not rely on checking finitely many family members.
`Alternating/Critical` now proves the critical-draw obstructions in the
alternating middle: the selected draw forces a zero triplet coefficient, or a
zero sequence coefficient together with a zero covered triplet coefficient.
These identities hold at arbitrary order. `Alternating/Boundary` transports
fixed prefix certificates through the common `PrefixModel`; `Exceptional`
handles the two early draws whose pairs need not lie among the first three
ranks. `Alternating/Minimal` excludes every elementary removal and therefore
every nonzero meldable removal. It proves minimality of both families and
`9*n/2-3 <= M(n)`. Together with the double family the bound is
`max(2*n,9*n/2-3) <= M(n) < 8*n` at every positive order.

The example `(0,2,2,4,2,3)` is verified by six explicit meld placements as a
full-sided `(2,4)`-wait. It is live for copy bound five and not live for four.
This checks parameters beyond the old fixed relation `m=n+1`.
The negative-sequence example checks that `-1 = 2 + 3*(-1)` is used in virtual
canonicalization; it is not converted to a natural-number coefficient.
Two right-boundary examples have zero recovered coefficients at every legal
sequence start, but endpoint states `(1,0)` and `(0,1)`. Both are rejected;
checking only the admissible start coefficients would miss these failures.
Their computed triplet quotients are all zero. Conversely, the nonnegative hand
with tiles at paper ranks `1,3,5` satisfies the size/rank-sum congruences but has
a negative triplet quotient, so it is virtually meldable and not actually
meldable. These examples check each part of the scan criterion separately.

`MovingExamples` checks the overlapping borrow/carry case, where only the
source triplet is needed, and a failed borrow despite source-tile availability.
It also separates success of the first sequential step from failure of a longer
move with a later required sequence absent.

`GraphExamples` verifies two different two-pair decompositions of the larger
example. It also checks the paper's full-sided `(3,7)`-wait
`(2,2,2,3,3,2,4,1,3)`: its fixed class is zero and the incoming neighbours of
paper rank nine are exactly ranks three and six. Thus a used pair in the fixed
class need not have a self-loop.

`SplitExamples` checks that splitting cannot be extended to virtual placements:
`e_1-e_4` has a virtual sequence placement and is zero at rank two, but its left
piece has size one and is not even virtually meldable. The order-one hand
`(2,0,2)` has outgoing edges for the two boundary draws and none for the middle
draw, checking the special case in the interior-positivity argument.

`BoundsExamples` verifies the order-one full wait `(2,3,2)` with fixed class two
and class sizes `(2,2,3)`. It attains the two nonfixed-class lower bounds and
checks the order-one exception that the later `m=n+1` classification must retain.

## Paper alignment

| Part of the rewritten paper | Current status |
| --- | --- |
| Virtual hands, independent parameters, elementary tile patterns | Implemented |
| Class-size partition and rank-sum congruence | Proved as sums over `ZMod 3` |
| Equal-class residue criterion from the two linear congruences | Proved |
| Virtual and nonnegative meld placements | Implemented |
| Virtual meldability iff class residues agree iff size and rank sum vanish modulo three | Proved |
| Draw-pair congruence and pair availability | Proved |
| Virtual sequence placement uniqueness | Proved |
| Sequence recurrence, closed form, boundary formulas, and existence criterion | Proved |
| Nonnegative sequence-placement criterion | Proved |
| Virtual canonicalization and unique canonical placements | Proved |
| Meldability of a known canonical placement iff triplet coefficients are nonnegative | Proved |
| Canonical sequence part under coordinatewise congruence | Global and prefix versions proved |
| Canonical scan, weighted closed form, boundary formulas, and full criterion | Proved |
| Sequential tile moving, four-case general moving, interval property | Proved |
| Fixed/interchanging classes and class-size congruence | Proved |
| Incoming intervals, bidirectional edges, consecutive edges, two-pair theorem | Proved |
| Missing-rank split, waits across a missing rank, interior positivity | Proved |
| Incoming edges from both sides force three copies | Proved |
| Class-size lower bounds and `m>n` | Proved |
| Classwise sequence/triplet statistics and removable triplets | Proved |
| Exact class sizes at `m=n+1` for `n>=2` | Proved |
| Two pillars and all fixed-draw winning placements at `m=n+1` | Proved |
| Unique two-pair decomposition and sequential remainder/moves | Proved |
| Required sequence rows and exact fixed-class-two/one templates | Proved |
| Full-wait reversal and fixed-class transformation | Proved |
| Named eight-family classification and six order-one hands | Proved |
| Live uniqueness as a corollary of the new classification | Proved |
| Four-copy validity of every full-sided `(n,n+1)` wait | Proved |
| Abundance and preservation under adding melds | Proved |
| Minimality at `m=n+1` and all order-one minimal waits | Proved |
| Eight-copy bound for minimal waits and `m<8n` | Proved |
| Existence of the maximum `M(n)` and `M(1)=2` | Proved |
| Minimal `(3,2,...,2)` family and lower bound `2n<=M(n)` | Proved |
| Full-sidedness of the stronger even/odd constructions | Proved |
| Minimality of the stronger constructions and improved lower bound | Proved |
| Distinct families and exact standard cardinalities 0/8/6, live 1/6 | Proved |
| Nonminimal `(n,n+2)` characterization, Taiwanese nonminimal count 122 | Proved |
| Taiwanese total/live/minimal counts 149/11/27 | Pending |

`Standard/Distinct` proves the eight named families are pairwise distinct at
every order at least two. Their two endpoints and second coordinate distinguish
all but `D` and `E`; the fourth coordinate separates that last pair. The six
explicit order-one vectors are distinct as well. `Cardinality` constructs
bijections from `Fin 8` and `Fin 6` to the full-wait subtypes, giving the exact
counts for full and minimal waits. It also proves live cardinalities one and
six, zero cardinalities for `m<=n`, and six minimal order-one waits across all
meld counts. These are consequences of the structural classification, not an
enumeration of candidate hands.

`Minimal/Next` characterizes all nonminimal full-sided `(n,n+2)` waits at
`n>=2`: each is one of the eight standard hands plus one triplet or sequence.
This follows from elementary removal and the structural classification at
`m=n+1`. `Numerical/Taiwanese` proves there are exactly 122 such hands at
`n=3`, by kernel evaluation of the finite set of 128 standard-hand/meld
combinations with duplicates removed. The paper's total/live/minimal Taiwanese
counts 149/11/27 remain unformalized; independent discovery computations are
not used as Lean proofs.

The exact general `M(n)` formula remains a conjecture in the paper. It is not
assumed as an axiom or used to prove any part of this development. Existing
computer-assisted upper-bound experiments are separate from this structural
formalization.

## Verification

Use the pinned Lean 4.35.0 and dependencies:

```sh
lake build --wfail Ninegates
lake env lean -j2 -M4096 -DwarningAsError=true Audit.lean > axioms.log
python3 scripts/check_axioms.py Audit.lean axioms.log
```

The audit covers the foundational results and the complete explicit example.
Allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`. There are no
placeholder proofs or uses of `native_decide` in the library. `Audit.lean`
and `scripts/check_axioms.py` enforce the standard axiom set in CI. The new
`ComparatorChallenges` target checks sixteen key statements against a
definition-only challenge boundary, including the classification itself,
alternating minimality, the improved bound, standard cardinalities, and the
Taiwanese nonminimal count. Run
`lake comparator --config=ComparatorChallenges/config.json` with its sandbox
enabled. Its intentional challenge holes are outside the default library.
`README.md` introduces the current API; this file records its detailed status.
