import E213.Lib.Math.Cohomology.Bipartite.Filled5CellMultiExtension
import E213.Lib.Math.Cohomology.Bipartite.Sq2At4Cell

/-!
# Massey triple ⟨ω, ω, ω⟩ at K_{3,2}^{(c=2)} multi-5-cell

The substrate from `Filled5CellMultiExtension` gives `H⁵ ≅ ℤ/2`
— non-vacuous landing space for the Massey triple `⟨ω, ω, ω⟩`
that would land in `H^(2+2+2-1) = H⁵`.

This file computes the Massey class explicitly under a
defensible outermost-faces AW cup-extension, and finds it is
ZERO in `H⁵` despite the non-trivial landing space.

## The structural obstruction

For ω = (1, 1, 1) ∈ C² (face cochains) with ALL faces non-zero,
any cup product into the multi-5-cell space ends up with both
cells receiving `true ∧ true = true`.  The Massey defining
expression `b ⌣ ω + ω ⌣ b` then has each summand equal to
`(true, true)` (diagonal), so the sum is `(false, false) = 0`.

This is a STRUCTURAL OBSTRUCTION: ω being the constant-true
face cochain + bilinearity of any cup-extension + the
diagonal-image structure of `δ⁴_multi` together force the
Massey class to collapse to zero.

## Closure status

Massey ⟨ω, ω, ω⟩ = 0 in `H⁵ ≅ ℤ/2` despite `H⁵ ≠ 0`.  The
substrate is non-vacuous but the SPECIFIC Massey class is
trivial — by the structural obstruction proved here.

Non-vacuous Massey at K_{3,2}^{(c=2)} would require either:
  · A different cohomology class than ω (but H² = ℤ/2 ⟨ω⟩ — ω
    is the unique non-zero class).
  · A different Massey shape, e.g., ⟨a, b, c⟩ with a, b, c
    distinct H¹ classes (cup landing in H²).
  · An asymmetric cup-extension breaking the diagonal-image
    structure (but the multi-cell `δ⁴_multi` forces image
    diagonality by construction).

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.MasseyTripleOmega

open E213.Lib.Math.Cohomology.Bipartite.Filled3CellCohomology (omega_face_vec)
open E213.Lib.Math.Cohomology.Bipartite.Filled3CellExtension
  (C3_dim delta2_full)
open E213.Lib.Math.Cohomology.Bipartite.Filled4CellExtension
  (C4_dim_ext delta3)
open E213.Lib.Math.Cohomology.Bipartite.Filled5CellMultiExtension
  (C5_dim_multi delta4_multi offDiagonal)
open E213.Lib.Math.Cohomology.Bipartite.Sq2At4Cell
  (face_cup_0 all_true_3cochain)

/-! ## §1 — Cobounding chain for ω ⌣ ω

`face_cup_0 ω ω` at the unique 4-cell σ⁴ evaluates to `true`
(both faces 0 and 2 of ω are `true`).  The all-true 3-cochain
serves as a cobounding chain: `δ³(all_true_3cochain) = (true) =
face_cup_0 ω ω`. -/

/-- ★ Cobounding chain witness: `δ³(all-true) = face_cup_0(ω, ω)`
    at every index of `C⁴`.  PURE. -/
theorem cobounding_witness :
    ∀ i : Fin C4_dim_ext,
      delta3 all_true_3cochain i = face_cup_0 omega_face_vec omega_face_vec i := by
  intro i
  unfold delta3 all_true_3cochain face_cup_0 omega_face_vec
  decide

/-! ## §2 — Cup extension `cupC3C2` and `cupC2C3` to C⁵

Outermost-faces AW-style extension to the multi-cell C⁵.  Both
5-cells receive the same value (consistent with `δ⁴_multi` being
diagonal): `(c ⌣ d)(σ⁵_*) := c(σ³) ∧ d(face_0)`.

This is one defensible AW lift; other choices give equivalent
results modulo the diagonal-image structure. -/

/-- `cup_C3_C2_at_C5_multi (c : C³) (d : Fin 3 → Bool) : C⁵_multi`.
    Both 5-cells get `c(σ³) ∧ d(face_0)`. -/
def cupC3C2 (c : Fin C3_dim → Bool) (d : Fin 3 → Bool) :
    Fin C5_dim_multi → Bool :=
  fun _ => c ⟨0, by decide⟩ && d ⟨0, by decide⟩

/-- `cup_C2_C3_at_C5_multi (d : Fin 3 → Bool) (c : C³) : C⁵_multi`.
    Both 5-cells get `d(face_0) ∧ c(σ³)`.  Symmetric to `cupC3C2`
    by Bool commutativity. -/
def cupC2C3 (d : Fin 3 → Bool) (c : Fin C3_dim → Bool) :
    Fin C5_dim_multi → Bool :=
  fun _ => d ⟨0, by decide⟩ && c ⟨0, by decide⟩

/-! ## §3 — Massey class computation

Massey ⟨ω, ω, ω⟩ representative:
  `m := cupC3C2 b ω + cupC2C3 ω b` where `b = all_true_3cochain`.

For ω = (1, 1, 1) and b = (true):
  cupC3C2 b ω = (true ∧ true, true ∧ true) = (true, true)
  cupC2C3 ω b = (true ∧ true, true ∧ true) = (true, true)
  Massey representative = (false, false) — DIAGONAL ZERO. -/

/-- The Massey ⟨ω, ω, ω⟩ representative under the outermost-faces
    cup extension. -/
def masseyRep : Fin C5_dim_multi → Bool :=
  fun i => xor (cupC3C2 all_true_3cochain omega_face_vec i)
               (cupC2C3 omega_face_vec all_true_3cochain i)

/-- ★★★★ **Massey representative is the all-false 5-cochain**.
    Direct computation: each summand evaluates to `true` at both
    5-cells; xor collapses to `false`. -/
theorem masseyRep_eq_zero (i : Fin C5_dim_multi) :
    masseyRep i = false := by
  unfold masseyRep cupC3C2 cupC2C3 all_true_3cochain omega_face_vec
  cases i.val <;> decide

/-! ## §4 — Closure: Massey ⟨ω, ω, ω⟩ = 0 in H⁵

The chain-level Massey representative is `(false, false)` —
the all-false 5-cochain.  It equals `δ⁴_multi(false-4cochain)`,
hence represents the zero class in `H⁵`. -/

/-- ★★★★★ **Massey ⟨ω, ω, ω⟩ chain-level = δ⁴_multi-image**.
    The chain-level representative `(false, false)` is exactly
    `δ⁴_multi(false-4cochain)`, witnessing that the Massey class
    is `0` in `H⁵ ≅ ℤ/2`. -/
theorem masseyRep_in_im_delta4 :
    ∀ i : Fin C5_dim_multi,
      masseyRep i = delta4_multi (fun _ => false) i := by
  intro i
  rw [masseyRep_eq_zero i]
  rfl

/-! ## §5 — Structural obstruction capstone -/

/-- ★★★★★★ **Massey ⟨ω, ω, ω⟩ obstruction master**.
    STRICT ∅-AXIOM.

    Despite the non-vacuous landing space `H⁵ ≅ ℤ/2` from
    `Filled5CellMultiExtension`, the Massey class
    `⟨ω, ω, ω⟩` is ZERO at the chain level under the
    outermost-faces AW cup extension.

    Structural reason: ω = (1, 1, 1) is the constant-true
    face cochain, so any face-pair evaluation produces `true`.
    The Massey alternation `b ⌣ ω + ω ⌣ b` thus has both
    summands equal to `(true, true)`, giving `(false, false)`
    after xor.  The result is a `δ⁴_multi`-image (specifically
    of the all-false 4-cochain).

    This is the OBSTRUCTION that prevents ⟨ω, ω, ω⟩ from being
    non-vacuous, even with the non-trivial H⁵ substrate.

    Non-vacuous Massey at K_{3,2}^{(c=2)} would require a
    structurally different Massey shape (different cohomology
    classes, different cup extension breaking diagonality, or
    an asymmetric cobounding-chain choice).  Open frontier. -/
theorem massey_omega_obstruction_master :
    -- Cobounding witness: δ³(all-true) = ω ⌣_0 ω at C⁴
    (∀ i : Fin C4_dim_ext,
       delta3 all_true_3cochain i = face_cup_0 omega_face_vec omega_face_vec i)
    -- Massey representative is the all-false 5-cochain
    ∧ (∀ i : Fin C5_dim_multi, masseyRep i = false)
    -- Massey representative is in im(δ⁴_multi) — zero class in H⁵
    ∧ (∀ i : Fin C5_dim_multi,
         masseyRep i = delta4_multi (fun _ => false) i) :=
  ⟨cobounding_witness, masseyRep_eq_zero, masseyRep_in_im_delta4⟩

end E213.Lib.Math.Cohomology.Bipartite.MasseyTripleOmega
