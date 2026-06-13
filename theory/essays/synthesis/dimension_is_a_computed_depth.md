# Dimension is a computed depth

A structure's dimension is not a cardinal it "has" but a **finite depth you
compute** from its graded count: the number of times the forward difference must
be iterated before the count is constant.  No `∞` is ever written; an infinite-
dimensional object is one whose difference ladder simply does not floor.

## 213-native answer

The ladder is the corpus's **divergence-depth** ladder
(`Lib/Math/Analysis/Cauchy/DivergenceLadder`): the forward difference `Δs(n) =
s(n+1) − s(n)` (`diff`), its iterate `liftK`, and the predicate `reachesFloor s =
∃ k, isConst (liftK k s)` — the least such `k` is the *depth*.  A constant floors
at depth `0` (`const_reaches_floor`); a super-polynomially growing sequence
**never floors**, depth `∞` (`infinite_depth`, the Liouville case).  *Dimension is
this depth read on a graded count.*

Take a structure that grows by a generating step and count it by degree —
`monoCount k d` = the number of degree-`d` elements over `k` generators
(`theory/math/numbersystems/slot_arithmetic.md` §1.5; `MultSystem.monoCount`).
Each difference drops the rung by one (`MultSystem.diff_drops_rung`:
`Δ(monoCount (k+1)) = monoCount k` shifted), so `Δ^k` leaves the constant `1`
(`diffIter_dim_const`) and `Δ^{k+1}` annihilates it (`diffIter_dim_zero`) — the
graded count of the rung-`(k+1)` structure floors at depth `k+1`.  Its dimension
`k+1` *is* that depth, computable (`monoCount 3 = [1,3,6,10,…] → Δ²=[1,1,…] →
Δ³=[0,…] ⇒ dim 3`).

## Derivation

The depth is well-posed because the generating step is the same at every rung:
`+`-elements become `×`-axes become `^`-axes, and the **degree-1 count is exactly
the generator count** (`MultSystem.monoCount_vertices`: `monoCount k 1 = k`).  So
"dimension" = generator count = the lattice axes of the demotion view
(`theory/.../number_tower_theory` R4: `+` is the 1-axis line, `×` the `∞`-axis
prime lattice) = the simplex vertices of the generative view.  One quantity, read
three ways, and `Δ` computes it.

The inverse direction is the partial sum.  `Σ` (`MultSystem.sumf`) raises the rung
by one (`totalCount_eq`), and iterating it builds the count from the constant:
`Σ^k 1 = monoCount(k+1)` (`sumfIter_const_one`) — the generating function
`(1−x)^{−(k+1)}` realized as iterated summation, with no formal power series.
`Δ` and `Σ` are therefore the dimension `∓1` operators, inverse up to a shift:
`Δ(Σf) = shift` (`diff_sumf`, the discrete fundamental theorem).  Dimension is a
quantity you move up by summing and down by differencing.

## Dual function

This *is* the classical notion of dimension — the degree of the Hilbert
polynomial, the order of the pole of the Hilbert series at `x = 1`, the Krull
dimension — with the cardinal packaging stripped.  Classical dimension theory
wraps exactly this finite computation: a graded module's dimension is where its
Hilbert function becomes polynomial, i.e. where the differences stabilize.  213
keeps the computation and drops the wrapper: there is no separate "dimension
number" hovering above the count; there is the count, and the depth at which `Δ`
kills it.  The reading is sharper at the top — an `∞`-dimensional object
(`×`, all primes as axes) is not a thing with cardinality `ℵ₀` but precisely a
count whose difference ladder never floors (`DivergenceLadder.infinite_depth`,
the same depth-`∞` the corpus reads on super-polynomial growth), equivalently
whose Hilbert series has an essential singularity (the Euler product, `ζ`).

## Cross-frame connections

The same depth ladder runs through neighbouring arcs.  The finite-difference depth
is the **additive** annihilation depth of a polynomial / C-finite count
(`Lib/Math/Analysis/Cauchy/CFiniteRing`, where `applyOp` commutes with `Δ`); its
multiplicative twin is the **Casoratian / Wronskian** depth of a holonomic
sequence (`DetSpectrumPoles`, `DepthPRecursive`) — the additive `Δ`/`Σ` and the
multiplicative Casoratian are the one depth operator at two resolutions.  In cohomology
the dimension-raising `Σ` is the **cup-ladder graduation** `+1` per degree
(`Lib/Physics/AlphaEM/CupLadderResidueUnit.cup_ladder_graduation_is_residue_unit`),
*proven* to be the residue unit `NS − NT = 1`.  And the symplectic frame puts the
same unit at the **floor of the cross-determinant tower**: `|det| = 1` is the
dimension-`0` point, the bottom rung whose tower-grade the completability boundary
climbs (`CrossDet/CrossDetOvertake.crossdet_floor_eq_point`).  Summation
graduation, cohomology graduation, and the symplectic det-one floor are one
`+1`-step — the unit that raises dimension by one, read in three frames.

## Open frontier

The `∞` case is named, not closed: the `×`-rung's non-terminating difference
tower *points at* `ζ` (the essential singularity), but the analytic object — and
whether the `^`-rung's shape is a `ζ`-of-`ζ` iterate — is open
(`research-notes/frontiers/`).  The reconciliation of the abstract degree-count
with the arithmetic value-count, where the two agree only in the limit, is prime
counting, pinned as a finite two-sided band
(`Lens/Number/Nat213/ChebyshevLower.chebyshev_defect`) whose width is the
PNT-constant gap — the irreducible content sitting on the certifiability boundary.
The conceptual reading of `∞`/the continuous as construction-produced *shapes*
characterized by finite signatures is tracked as an active frontier.
