# Cup-ladder ↔ cork H¹ bridge

The four cochains ω_00, ω_10, ω_01, ω_11 in H¹(K_{3,2}^{(c=2)})
carry two simultaneous structural readings — cup-ladder α²/d²
Gram coefficient operates on their span; cork-twist Z/2 grading
sums to `+4` over them as singleton orbits.  Same basis, two
precision frames.

## 213-native answer

`Sym3IrrepDecomp.fixedSize = 4` is the cardinality of the
Sym(3)-trivial-isotypic subspace of `H¹(K_{3,2}^{(c=2)})` over
F_2 (dim 2 → 2² = 4 cochains).  The cup-ladder formula
`Δ_H^k(c) = ‖c‖² · α^(k+1) / d^(k+1)` at k = 1 operates on H¹
classes; the four fixed cochains form the Sym(3)-invariant basis
the Gram coefficient consumes.  The cork-twist signed count
`+4 = #twistEven − #twistOdd = 32 − 28` is the same 4 cochains
read as singleton Sym(3)-orbits with `M_S01² = id`.

## Derivation

The Sym(3)-fixed dim 2 is established at
`lean/E213/Lib/Physics/Symmetry/Sym3IrrepDecomp.lean` via
`fixedSize_eq_4` (explicit Burnside enumeration of M_S01-fixed
cochains on H¹).  The four fixed cochains have explicit names
`ω_00`, `ω_10`, `ω_01`, `ω_11`.  They satisfy `M_S01 · ω = ω`
and `M_S12 · ω = ω` for each — Sym(3)-invariant under all three
transpositions.

On the cup-ladder side
(`theory/math/cohomology/cup_ladder_graduation.md`), the formula
`Δ_H^k(c) = ‖c‖² · α^(k+1) / d^(k+1)` at k = 1 specialises to the
Gram self-energy α²/d² (with d = chartBase = 5, d² = 25 per
`lean/E213/Lib/Physics/AlphaEM/CupLadderFormula.lean`).  The
L¹-norm-squared ‖c‖² operates on H¹ cochains; for c in the
Sym(3)-fixed subspace, this is the "trivial-isotypic" component
of the precision contribution.

On the cork side (`theory/math/exotic_4mfd_cork.md`), the same
four cochains appear as the singleton orbits in the Burnside
count `sym3OrbitCount = 60`: 4 singletons + 28 size-3 + 28 size-6.
The signed cork-twist count = 4 + 28 − 28 = +4
(`lean/E213/Lib/Math/AkbulutCork/SignedOrbits.lean`).

The bridge is proved at
`lean/E213/Lib/Math/AkbulutCork/CrossFrame.lean`:

- `cork_count_eq_sym3_fixed_cardinality`: `signedCorkTwistCount
  = (Sym3IrrepDecomp.fixedSize : Int)`
- `cork_count_eq_two_squared`: `= 2²` (dim²)
- `cork_cup_ladder_H1_correspondence` capstone
- `alpha_em_cork_precision_citation`: extends to the
  precision-stack constants `d_squared = 25 = chartBase 3 2
  squared`, joint `d² · cork = 100`

## Dual function

The cup-ladder / cork bridge IS Donaldson-style gauge-invariant
precision-counting with the smooth-structure-equivalence packaging
stripped (just count Sym(3)-orbits with M_S01 grading on a fixed
bipartite H¹), and IS the α_em Gram coefficient with the
trivial-isotypic component pre-identified (the 4 fixed cochains
are the structural carriers, not arbitrary basis vectors).

## Cross-frame connections

Five-way Sym(3) convergence at
`five_way_sym3_cross_frame_capstone`: same Sym(3) algebraic spine
surfaces in (1) Geometrization 8 = 3 isotropic + 5 anisotropic;
(2) gluon octet H¹ rank 8 = 2·trivial ⊕ 3·standard; (3) HC_K32
256 = 2⁸ Hodge cup-subring; (4) Möbius P mod-5 pentagonal cycle
(`half_period = 5`, `full_period = 10`); (5) cork signed count
+4 = trivial-isotypic cardinality.  The cup-ladder
`α^(k+1)/d^(k+1)` graduation at k = 1, 2 reads the (k+1)-th
cohomology layer's contribution — at k = 1, the 4 Sym(3)-fixed
cochains; at k = 2, the ω class extending +6 = 4 + 2 in
`signedCorkTwistCount_H1_H2`.

## Constructive accessibility

`Sym3IrrepDecomp.ω_10 : Fin 8 → Bool` is a pointable function.
`M_S01 : Fin 8 → Fin 8 → Bool` is pointable.  The fix-property
`M_mul_vec M_S01 ω_10 j = ω_10 j` is a pointable Bool equality.
The cup-ladder coefficient `cup_ladder_trace_e9 1
= gram_correction_e9` is a pointable Nat equality
(`CupLadderFormula.cup_ladder_at_k1`).  The bridge is the
structural sentence: the same 4 cochains generate both readings.
