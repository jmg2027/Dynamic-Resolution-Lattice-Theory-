import E213.Lib.Math.Cohomology.Hodge.Star
import E213.Lib.Math.Cohomology.Hodge.InvolutionTemplate
import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Physics.Simplex.Counts

/-!
# Hodge ⋆⋆ = id Prop-lifts — all five Δ⁴ strata

The Hodge star `⋆` is an involution on K_{3,2}^{(c=2)} cochain
strata of the 5-simplex Δ⁴ at every dimension `k ∈ {0,1,2,3,4}`.
This file packages all five strata together using the COH-2
`hodge_involution_pointwise_5` template.

Each non-trivial stratum `(5, k)` (for `k = 1, 2, 3, 4`) follows
the identical template:

  · 3 private `decide`-lemmas on `complementIdx`
    (parametrised by `(k, k') = (1,4), (2,3), (3,2), (4,1)`)
  · 5-line capstone via `hodge_involution_pointwise_5 k k' σ i`

The `k = 0` stratum is the trivial case (one cochain index,
two functions) handled by direct `Fin` elimination.

Stratum sizes:
  (5, 0): 1 cochain index × 2 patterns =     2 evaluations
  (5, 1): 5 × 32                       =   160
  (5, 2): 10 × 1024                    = 10240
  (5, 3): 10 × 1024                    = 10240
  (5, 4): 5 × 32                       =   160

The all-strata capstone `hodge_involution_5strata_capstone`
concludes by bundling the five Prop-level statements.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Cohomology.Hodge.InvolutionLifts

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Hodge.Star (hodgeStar complementIdx)
open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Hodge.InvolutionTemplate
  (hodge_involution_pointwise_5)

/-! ### §1 — Stratum (5, 0): trivial case via Fin elimination -/

/-- `⋆⋆ = id` at `(5, 0)` — only one valid index, two functions. -/
theorem hodge_involution_capstone_5_0 :
    ∀ σ : Cochain 5 0, ∀ i : Fin (binom 5 0),
      hodgeStar 5 5 0 (hodgeStar 5 0 5 σ) i = σ i := by
  intro σ i
  rcases i with ⟨val, hval⟩
  cases val with
  | zero => rfl
  | succ n =>
    have h : n + 1 < 1 := hval
    exact absurd (Nat.le_of_succ_le_succ h) (Nat.not_succ_le_zero n)

/-! ### §2 — Stratum (5, 1) -/

private theorem c1_lt_binom4_5_1 :
    ∀ i : Fin (binom 5 1), complementIdx 5 1 i.val < binom 5 4 := by decide

private theorem c2_lt_binom1_5_1 :
    ∀ i : Fin (binom 5 1),
      complementIdx 5 4 (complementIdx 5 1 i.val) < binom 5 1 := by decide

private theorem c2_eq_i_5_1 :
    ∀ i : Fin (binom 5 1),
      complementIdx 5 4 (complementIdx 5 1 i.val) = i.val := by decide

/-- Pointwise `⋆⋆ = id` at `(5, 1)` (downstream-named form). -/
theorem hodge_sq_prop_5_1 (σ : Cochain 5 1) (i : Fin (binom 5 1)) :
    hodgeStar 5 4 1 (hodgeStar 5 1 4 σ) i = σ i :=
  hodge_involution_pointwise_5 1 4 σ i
    (c1_lt_binom4_5_1 i) (c2_lt_binom1_5_1 i) (c2_eq_i_5_1 i)

/-- ∀-form capstone at `(5, 1)`. -/
theorem hodge_involution_capstone_5_1 :
    ∀ σ : Cochain 5 1, ∀ i : Fin (binom 5 1),
      hodgeStar 5 4 1 (hodgeStar 5 1 4 σ) i = σ i :=
  hodge_sq_prop_5_1

/-! ### §3 — Stratum (5, 2) -/

private theorem c1_lt_binom3_5_2 :
    ∀ i : Fin (binom 5 2), complementIdx 5 2 i.val < binom 5 3 := by decide

private theorem c2_lt_binom2_5_2 :
    ∀ i : Fin (binom 5 2),
      complementIdx 5 3 (complementIdx 5 2 i.val) < binom 5 2 := by decide

private theorem c2_eq_i_5_2 :
    ∀ i : Fin (binom 5 2),
      complementIdx 5 3 (complementIdx 5 2 i.val) = i.val := by decide

/-- Pointwise `⋆⋆ = id` at `(5, 2)` (downstream-named form). -/
theorem hodge_sq_prop_5_2 (σ : Cochain 5 2) (i : Fin (binom 5 2)) :
    hodgeStar 5 3 2 (hodgeStar 5 2 3 σ) i = σ i :=
  hodge_involution_pointwise_5 2 3 σ i
    (c1_lt_binom3_5_2 i) (c2_lt_binom2_5_2 i) (c2_eq_i_5_2 i)

/-- ∀-form capstone at `(5, 2)`. -/
theorem hodge_involution_capstone_5_2 :
    ∀ σ : Cochain 5 2, ∀ i : Fin (binom 5 2),
      hodgeStar 5 3 2 (hodgeStar 5 2 3 σ) i = σ i :=
  hodge_sq_prop_5_2

/-! ### §4 — Stratum (5, 3) -/

private theorem c1_lt_binom2_5_3 :
    ∀ i : Fin (binom 5 3), complementIdx 5 3 i.val < binom 5 2 := by decide

private theorem c2_lt_binom3_5_3 :
    ∀ i : Fin (binom 5 3),
      complementIdx 5 2 (complementIdx 5 3 i.val) < binom 5 3 := by decide

private theorem c2_eq_i_5_3 :
    ∀ i : Fin (binom 5 3),
      complementIdx 5 2 (complementIdx 5 3 i.val) = i.val := by decide

/-- ∀-form capstone at `(5, 3)`. -/
theorem hodge_involution_capstone_5_3 :
    ∀ σ : Cochain 5 3, ∀ i : Fin (binom 5 3),
      hodgeStar 5 2 3 (hodgeStar 5 3 2 σ) i = σ i :=
  fun σ i => hodge_involution_pointwise_5 3 2 σ i
    (c1_lt_binom2_5_3 i) (c2_lt_binom3_5_3 i) (c2_eq_i_5_3 i)

/-! ### §5 — Stratum (5, 4) -/

private theorem c1_lt_binom1_5_4 :
    ∀ i : Fin (binom 5 4), complementIdx 5 4 i.val < binom 5 1 := by decide

private theorem c2_lt_binom4_5_4 :
    ∀ i : Fin (binom 5 4),
      complementIdx 5 1 (complementIdx 5 4 i.val) < binom 5 4 := by decide

private theorem c2_eq_i_5_4 :
    ∀ i : Fin (binom 5 4),
      complementIdx 5 1 (complementIdx 5 4 i.val) = i.val := by decide

/-- ∀-form capstone at `(5, 4)`. -/
theorem hodge_involution_capstone_5_4 :
    ∀ σ : Cochain 5 4, ∀ i : Fin (binom 5 4),
      hodgeStar 5 1 4 (hodgeStar 5 4 1 σ) i = σ i :=
  fun σ i => hodge_involution_pointwise_5 4 1 σ i
    (c1_lt_binom1_5_4 i) (c2_lt_binom4_5_4 i) (c2_eq_i_5_4 i)

/-! ### §6 — All-strata capstone -/

/-- **Hodge ⋆⋆ = id on Δ⁴ (all five strata)** — bundle.

  The Hodge star `⋆` is an involution on K_{3,2}^{(c=2)} cochain
  strata of the 5-simplex Δ⁴, at every dimensional level
  `k ∈ {0, 1, 2, 3, 4}`. -/
theorem hodge_involution_5strata_capstone :
    (∀ σ : Cochain 5 0, ∀ i : Fin (binom 5 0),
      hodgeStar 5 5 0 (hodgeStar 5 0 5 σ) i = σ i)
    ∧ (∀ σ : Cochain 5 1, ∀ i : Fin (binom 5 1),
        hodgeStar 5 4 1 (hodgeStar 5 1 4 σ) i = σ i)
    ∧ (∀ σ : Cochain 5 2, ∀ i : Fin (binom 5 2),
        hodgeStar 5 3 2 (hodgeStar 5 2 3 σ) i = σ i)
    ∧ (∀ σ : Cochain 5 3, ∀ i : Fin (binom 5 3),
        hodgeStar 5 2 3 (hodgeStar 5 3 2 σ) i = σ i)
    ∧ (∀ σ : Cochain 5 4, ∀ i : Fin (binom 5 4),
        hodgeStar 5 1 4 (hodgeStar 5 4 1 σ) i = σ i) :=
  ⟨hodge_involution_capstone_5_0,
   hodge_involution_capstone_5_1,
   hodge_involution_capstone_5_2,
   hodge_involution_capstone_5_3,
   hodge_involution_capstone_5_4⟩

end E213.Lib.Math.Cohomology.Hodge.InvolutionLifts
