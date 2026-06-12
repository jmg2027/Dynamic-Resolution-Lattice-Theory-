# What is holonomy (in 213)?

The net transition a closed loop of state-transitions composes to — and, because
a state-transition *is* a state, that net transition is itself a state of the same
kind. Holonomy is the single object a loop returns; it is non-trivial exactly when
the negation fold has been admitted.

## 213-native answer

A path is a list of state-transitions `w : List Mat2`; its **holonomy** is the
ordered fold-product `holonomy w = g₀ · g₁ · … · gₙ · I`
(`lean/E213/Lib/Math/NumberSystems/Real213/HolonomyLattice.lean`, `holonomy`). The
fold is well-posed because a `2×2` integer matrix is the object in which the
*frozen* reading (a configuration, four counts) and the *dynamic* reading (the map
`x ↦ M·x`) coincide: without an external time axis a transition is not separable
from the state it transitions to
(`seed/AXIOM/06_lens_readings.md` §6.6, §5.7). So a loop of *transitions*
composes to a single *state* — that composite is the holonomy.

## Derivation

Three facts make `holonomy` a holonomy in the genuine sense, all ∅-axiom.

**It is a functor.** `holonomy (p ++ q) = holonomy p · holonomy q`
(`HolonomyLattice.holonomy_append`): concatenating paths composes their
holonomies, so `holonomy` is a monoid homomorphism from the free monoid of paths
`(List Mat2, ++, [])` into the matrix monoid `(Mat2, ·, I)`. The codomain is
*states*: transport around a path lands on an object of the same kind it
transported — the §6.6 collapse made computational, riding only matrix
associativity (`Mat2Assoc.mul_assoc`).

**It is flat.** If every step has `det = 1`, then `det (holonomy w) = 1` around
the whole loop (`HolonomyLattice.det_holonomy_eq_one`, via the Cauchy–Binet
`det_mul`). The conserved quantity `det = 1 = NS − NT` is the founding shared unit
(`lean/E213/Lens/Number/FoundingDynamicBridge.lean`), the discrete flat
connection. It is the same invariant the convergent pair reads as the constant
`−1` (`Lib/Math/Algebra/Mobius213.lean`,
`mobius_213_pell_unit_invariant_forall`) — the symplectic area form transport
preserves.

**It is born from the fold.** The Stern–Brocot generators `L = [[1,0],[1,1]]`,
`R = [[1,1],[0,1]]` have entries in ℕ — the ℕ⁺ sector — and every non-empty
positive word strictly grows its entry-sum, so it never returns to `I`
(`HolonomyLattice.positive_loop_trivial`): the positive monoid `⟨L,R⟩` is a tree,
loop-free. The first non-trivial loop appears exactly when the negation-fold
composite `S = N·R = z ↦ −1/z` is admitted: `holonomy [S,S] = −I ≠ I`, of order 4
(`HolonomyLattice.first_loop_is_the_fold`). `S` carries the entry `S.b = −1` that
the ℕ⁺ sector excludes. Holonomy is the residue-internal signature of the same
fold the number tower's ℕ→ℤ rung is (`seed/AXIOM/06_lens_readings.md` §6.7;
`theory/essays/analysis/integers_as_difference_lens.md`).

## Dual function

Classically holonomy is parallel transport around a closed loop, trivial for a
flat connection on a simply-connected base. Strip the packaging: the connection is
`det = 1`, the simply-connected base is the ℕ⁺ Stern–Brocot tree, and "parallel
transport" is the fold-product. 213's reading is sharper on *where* holonomy comes
from — not a feature of a pre-given fibre bundle, but the obstruction a Lens
choice creates: the count-Lens (ℕ⁺) sees only trivial holonomy; the
difference-Lens (ℤ) creates the first loop. The holonomy group is therefore not
imported — it is generated at the exact step the founding sign fold enters, and
its first order, 4, is the elliptic Gaussian period the finite-order spectrum
`{1,2,3,4,6}` already pins (`theory/essays/analysis/the_modular_group_from_two_folds.md`).

## Cross-frame connections

The negation fold appears at three resolutions as one event. As **number tower**
it is the swap `(a,b) ↦ (b,a)` read as negation, building ℤ
(`FoundingDynamicBridge.founding_swap_is_elliptic_floor`, §6.7). As **discriminant
dial** it is the elliptic floor `S`, `disc < 0`, `S² = −I`. As **holonomy** it is
the first closed loop `[S,S] = −I`. ℤ's birth, the elliptic floor, and holonomy's
birth are one fold admitted — the static pair-completion, the dynamic discriminant
floor, and the loop obstruction, three faces of the period-2 swap fixed only at
the residue's `0` (§6.6, §5.7, §6.9).

## Open frontier

The ℕ⁺ loop-freeness is proven here only as *no-return*
(`positive_loop_trivial`); the stronger faithful-monoid statement (every positive
matrix is a unique `L,R` word) needs the continued-fraction / odometer digit
extraction. The general order law (a loop's holonomy has finite order ∈ `{1,2,3,4,6}`
by its trace) and the holonomy group as π₁ of the modular orbifold
`PSL(2,ℤ) = ℤ₂ * ℤ₃` are short bridges to `FiniteOrderSpectrum` and
`the_modular_geodesic_lens`, not yet written
(`research-notes/frontiers/holonomy_lattice.md`).
