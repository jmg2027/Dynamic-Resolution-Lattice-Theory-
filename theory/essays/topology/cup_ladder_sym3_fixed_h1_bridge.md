# Cup-ladder ↔ Sym(3)-fixed H¹ bridge

The four cochains ω_00, ω_10, ω_01, ω_11 in H¹(K_{3,2}^{(c=2)})
are the Sym(3)-trivial-isotypic basis: the cup-ladder α²/d²
Gram coefficient operates on their span, and their cardinality
`+4` is exactly the Sym(3)-fixed dimension `2² = 4`.

## 213-native answer

`OctetModule.fixedSize = 4` is the cardinality of the
Sym(3)-trivial-isotypic subspace of `H¹(K_{3,2}^{(c=2)})` over
F_2 (dim 2 → 2² = 4 cochains).  The cup-ladder formula
`Δ_H^k(c) = ‖c‖² · α^(k+1) / d^(k+1)` at k = 1 operates on H¹
classes; the four fixed cochains form the Sym(3)-invariant basis
the Gram coefficient consumes.

## Derivation

The Sym(3)-fixed dim 2 is established at
`lean/E213/Lib/Physics/Symmetry/OctetModule.lean` via
`fixedSize_eq_4` (`decide` enumeration of the M_S01/M_S12-fixed
cochains on H¹).  The 2-dim fixed subspace has basis `ω_10`,
`ω_01` (4 cochains: `0`, `ω_10`, `ω_01`, `ω_10 ⊕ ω_01`).  Each
basis vector satisfies `M_mul_vec M_S01 ω = ω` and
`M_mul_vec M_S12 ω = ω` — Sym(3)-invariant under the transpositions
(`ω_10_fixed_S01`, `ω_10_fixed_S12`, `ω_01_fixed_S01`, …).

On the cup-ladder side
(`theory/math/cohomology/cup_ladder_graduation.md`), the formula
`Δ_H^k(c) = ‖c‖² · α^(k+1) / d^(k+1)` at k = 1 specialises to the
Gram self-energy α²/d² (with d = chartBase = 5, d² = 25 per
`lean/E213/Lib/Physics/AlphaEM/CupLadderFormula.lean`).  The
L¹-norm-squared ‖c‖² operates on H¹ cochains; for c in the
Sym(3)-fixed subspace, this is the "trivial-isotypic" component
of the precision contribution.

The Sym(3)-fixed cardinality `fixedSize = 2² = 4` is established at
`lean/E213/Lib/Physics/Symmetry/OctetModule.lean`
(`fixedSize_eq_4`).  The four fixed cochains are the structural
carriers the Gram coefficient consumes.

## Dual function

The bridge IS the α_em Gram coefficient with the
trivial-isotypic component pre-identified (the 4 fixed cochains
are the structural carriers, not arbitrary basis vectors).

## Cross-frame connections

The same Sym(3) algebraic spine surfaces in the gluon octet
H¹ rank `8 = 2·trivial ⊕ 3·standard` and the octet full cohomology
`|H¹| = 256 = 2⁸` (`theory/math/cohomology/sym3_spine.md`).  The
cup-ladder `α^(k+1)/d^(k+1)` graduation at k = 1, 2 reads the
(k+1)-th cohomology layer's contribution — at k = 1, the 4
Sym(3)-fixed cochains; at k = 2, the ω class extending the
trivial-isotypic count to `3·trivial ⊕ 3·standard`.

## Constructive accessibility

`OctetModule.ω_10 : Fin 8 → Bool` is a pointable function.
`M_S01 : Fin 8 → Fin 8 → Bool` is pointable.  The fix-property
`M_mul_vec M_S01 ω_10 j = ω_10 j` is a pointable Bool equality.
The cup-ladder coefficient `cup_ladder_trace_e9 1
= gram_correction_e9` is a pointable Nat equality
(`CupLadderFormula.cup_ladder_at_k1`).  The bridge is the
structural sentence: the same 4 cochains generate both readings.
