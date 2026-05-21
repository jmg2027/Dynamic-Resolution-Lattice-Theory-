import E213.Lib.Math.Cohomology.Hodge.Star
import E213.Lib.Math.Cohomology.Cup.Core
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz

/-!
# Cup-Ring Trace functionals on H*(Δ⁴) — bottom-up α_em derivation test

**Purpose**: Test whether `1/α_em(IR) ≈ 137.036` arises from a single
parameter-free functional on the cup-ring `H*(K_{3,2}^{(c=2)})`
(or `H*(Δ⁴)`), per the user's conjecture.

This is a **bottom-up** test: define candidate functionals
intrinsically from the ring structure, compute their values via
`decide`, then compare to 137.  No fitting — the functional is
defined first, the result observed second.

## Two candidates tested

  · **Cand-1** (unit-class self-energy):
    F₁ := Σ_{k=1..5} cup(1_k, *1_k)(top)
    where `1_k` is the all-true cochain at grade k.

  · **Cand-2** (basis self-Hodge sum at top):
    F₂ := Σ_{k=1..5} Σ_{α ∈ basis(C^k)} cup(α, *α)(top)
    summed over the colex-indexed basis.

Both are SINGLE functionals on the cup-ring, depending only on
the ring structure (cup, Hodge ⋆, top-cell evaluation) — zero
physical parameters.

STRICT ∅-AXIOM (all by `decide` on basis enumeration).
-/

namespace E213.Lib.Physics.AlphaEM.CupRingTrace

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Cup.Core (cup)
open E213.Lib.Math.Cohomology.Hodge.Star (hodgeStar)
open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis)
open E213.Lib.Physics.Simplex.Counts (binom)



/-! ## §1 — Unit cochain at each grade -/

/-- All-true cochain at grade k: `1_k(τ) = true` for every τ. -/
def unit_cochain (n k : Nat) : Cochain n k := fun _ => true

/-- Helper: top cell of Δ⁴ as Fin 1 (Cochain 5 5 has 1 entry). -/
def top_5 : Fin (binom 5 5) := ⟨0, by decide⟩

/-! ## §2 — Cand-1: unit-class self-energy at top -/

/-- F₁ contribution at grade k: `cup(1_k, *1_k)(top)` as Nat (0/1). -/
def F1_at_grade (k : Nat) : Nat :=
  if k = 1 then
    if cup 5 1 4 (unit_cochain 5 1) (hodgeStar 5 1 4 (unit_cochain 5 1)) top_5
    then 1 else 0
  else if k = 2 then
    if cup 5 2 3 (unit_cochain 5 2) (hodgeStar 5 2 3 (unit_cochain 5 2)) top_5
    then 1 else 0
  else if k = 3 then
    if cup 5 3 2 (unit_cochain 5 3) (hodgeStar 5 3 2 (unit_cochain 5 3)) top_5
    then 1 else 0
  else if k = 4 then
    if cup 5 4 1 (unit_cochain 5 4) (hodgeStar 5 4 1 (unit_cochain 5 4)) top_5
    then 1 else 0
  else 0

/-- F₁ := Σ_{k=1..4} F1_at_grade k. -/
def F1 : Nat := F1_at_grade 1 + F1_at_grade 2 + F1_at_grade 3 + F1_at_grade 4

-- F1_value (F1 = 4) and F1_grade_breakdown (F1_at_grade k = 1 for
-- k=1..4) folded into `cup_ring_trace_master` below.



/-! ## §3 — Cand-2: basis self-Hodge cup at top (all colex basis)

  For each grade k ∈ {1, 2, 3, 4} and each basis element α at
  grade k, compute `cup(α, *α)(top)`.  Sum over all α.

  Per AW analysis: at top τ = [0,1,2,3,4], `cup(basis_i, *basis_i)(top)`
  = 1 iff `kSubset 5 k i = [0..k-1]` (the colex-first k-subset).
  For each k, exactly ONE basis element (i=0) satisfies this. -/

/-- Cand-2 contribution at grade k: count of basis α with cup(α, *α)(top) = 1. -/
def F2_at_grade_1 : Nat :=
  ((List.finRange (binom 5 1)).filter (fun i =>
    cup 5 1 4 (basis 5 1 i) (hodgeStar 5 1 4 (basis 5 1 i)) top_5)).length
def F2_at_grade_2 : Nat :=
  ((List.finRange (binom 5 2)).filter (fun i =>
    cup 5 2 3 (basis 5 2 i) (hodgeStar 5 2 3 (basis 5 2 i)) top_5)).length
def F2_at_grade_3 : Nat :=
  ((List.finRange (binom 5 3)).filter (fun i =>
    cup 5 3 2 (basis 5 3 i) (hodgeStar 5 3 2 (basis 5 3 i)) top_5)).length
def F2_at_grade_4 : Nat :=
  ((List.finRange (binom 5 4)).filter (fun i =>
    cup 5 4 1 (basis 5 4 i) (hodgeStar 5 4 1 (basis 5 4 i)) top_5)).length

/-- F₂ := Σ_{k=1..4} F2_at_grade_k. -/
def F2 : Nat := F2_at_grade_1 + F2_at_grade_2 + F2_at_grade_3 + F2_at_grade_4

-- F2_value (F2 = 4), F2_grade_breakdown, F1_eq_F2 folded into
-- cup_ring_trace_master.



/-! ## §4 — Total cup-channels (F₃, from Step A)

  F₃ = total nonzero cup-channels on Δ⁴ across all (a, b) with
       a, b ≥ 1 and a + b ≤ 5.
     = Σ_{k=1..5} k · binom(5, k)
     = 5 + 20 + 30 + 20 + 5
     = 80. -/

/-- F₃ closed form: total cup-channels = Σ k · binom 5 k. -/
def F3 : Nat := 1 * binom 5 1 + 2 * binom 5 2 + 3 * binom 5 3
              + 4 * binom 5 4 + 5 * binom 5 5

-- F3_value (F3 = 80) folded into master.

/-! ## §5 — Cand-4: output-grade-weighted channel sum

  F₄ := Σ_k k · (channels_at_grade k)
      = Σ_k k · k · binom(5, k)
      = Σ_k k² · binom(5, k). -/

/-- Output-grade-weighted cup-channel total. -/
def F4 : Nat := 1*1 * binom 5 1 + 2*2 * binom 5 2 + 3*3 * binom 5 3
              + 4*4 * binom 5 4 + 5*5 * binom 5 5

-- F4_value (F4 = 240) folded into master.

/-! ## §6 — Cand-5: input-grade-product weighted (a · b summed)

  For each (a, b) with a + b ≤ 5 (cup output ≤ 5), weight by
  the product a · b times the number of cup channels.  -/

/-- F₅ := Σ_{(a, b): a + b ≤ 5} a · b · (channels at output a+b for that
    decomposition).  For `cup`, channels per (a, b) = binom 5 (a+b). -/
def F5 : Nat :=
    1*1 * binom 5 2 + 1*2 * binom 5 3 + 2*1 * binom 5 3
  + 1*3 * binom 5 4 + 2*2 * binom 5 4 + 3*1 * binom 5 4
  + 1*4 * binom 5 5 + 2*3 * binom 5 5 + 3*2 * binom 5 5 + 4*1 * binom 5 5

-- F5_value (F5 = 120) folded into master.

/-! ## §7 — Master cup-ring trace results + gap analysis

  Bottom-up test of "1/α_em = single cup-ring functional" conjecture.

  Five candidate functionals, all parameter-free, computed via decide:

    F₁ (unit self-energy at top):           4
    F₂ (basis self-Hodge sum at top):        4
    F₃ (total cup-channels on Δ⁴):          80
    F₄ (output-grade²-weighted total):     240
    F₅ (input-grade-product weighted):     120

  Target:  1/α_em(IR) ≈ 137.036.

  **Gap**: NONE of the simple cup-ring functionals on Δ⁴ alone
  yield 137.  This is a meaningful negative result:

  · The conjecture **does not** trivially close at the level of
    elementary cup-ring counts on H*(Δ⁴; ℤ).
  · A "single canonical functional = 1/α_em" must use either:
      (a) Laplacian spectrum (Σ 1/λ_k² style), bringing back ζ(2)
          but as a finite eigenvalue sum at resolution N_U;
      (b) K_{3,2}^{(c=2)} multi-edge structure beyond Δ⁴ alone
          (the c=2 multiplicity doubles certain channel counts);
      (c) ℤ-coefficient signed cup pairings (Hodge–Riemann
          signature integrals), not Bool/ℤ_2;
      (d) Cup-ring convolved with the resolution N_resolution =
          5²⁵ (so that "ζ(2) ≈ S(5²⁵) ≈ π²/6" reads as a finite
          rational at lattice scale).

  This bottom-up data argues (a) or (d) is the right direction —
  the integer 137 isn't a small Δ⁴ count; it requires the
  resolution-scale spectral structure or its surrogate. -/

/-- ★★★★★ Cup-ring trace bottom-up test results.  STRICT ∅-AXIOM. -/
theorem cup_ring_trace_master :
    F1 = 4
    ∧ F2 = 4
    ∧ F1 = F2
    ∧ F3 = 80
    ∧ F4 = 240
    ∧ F5 = 120
    -- Gap: none equal 137
    ∧ F1 ≠ 137
    ∧ F2 ≠ 137
    ∧ F3 ≠ 137
    ∧ F4 ≠ 137
    ∧ F5 ≠ 137 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Physics.AlphaEM.CupRingTrace
