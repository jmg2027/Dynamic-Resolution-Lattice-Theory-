import E213.Lib.Physics.Simplex.Counts
import E213.Lib.Physics.Simplex.Generations

/-!
# Generation structure — Λᵏ(ℂ⁵) → 1 generation = 15 fermions (0 axioms)

DRLT derivation (SU(5)):

  ∧¹(ℂ⁵) = 5̄ representation (dim 5)  → 5 fermions
  ∧²(ℂ⁵) = 10 representation (dim 10) → 10 fermions
  Total per generation: 5 + 10 = 15 fermions ★ = SU(5) multiplet count

  3 generations × 15 fermions = 45 fermion states.
  
  CPT pair:
    ∧¹ ↔ ∧⁴ (5 = C(5,4))
    ∧² ↔ ∧³ (10 = C(5,3))
    ∧⁰ = 1 (singlet)
    ∧⁵ = 1 (CPT of singlet)

## ★ Standard Model fermion content ★

  1 generation = 15 = C(d,1) + C(d,2) = d + d(d-1)/2
                  = 5 + 10
                  = 15 (per generation)
  
  3 generations forced by C(NS, NT) = C(3, 2) = 3.
  3 × 15 = 45 fermion states.

  No 4th generation: Λ⁶ doesn't exist (d=5 < 6).

## Λᵏ matter assignment

  ∧¹ = 5̄: d_R^c (3) + L (2) [3 quarks + lepton doublet]
  ∧² = 10: u_R^c (3) + Q_L (6) + e_R^c (1) [10 = 3+6+1]

  Numbers 5, 10, 5, 10, etc. are all *binomial coefficients of d=5*.
  Pure combinatorial.
-/

namespace E213.Lib.Physics.Simplex.GenerationStructure

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Physics.Simplex.Generations

/-- 1 generation fermion count: ∧¹ + ∧² = 5 + 10 = 15. -/
def gen_fermion_count : Nat := lambda_dim 1 + lambda_dim 2

/-- 3 generations × 15 fermions = 45 SM fermion states. -/
def total_fermion_states : Nat := N_gen * gen_fermion_count

/-- ★ Capstone — SM matter content from atomicity ★

    1 generation = Λ¹ ⊕ Λ² = 5 + 10 = 15 fermions (SU(5) GUT
    multiplet count, no tuning).  3 generations forced by
    C(NS, NT) = 3.  Total SM fermion states = 45.  No 4th
    generation (Λ⁶ doesn't exist).

    Bundles: gen_fermion_count = 15 with atomic form C(d,1)+C(d,2),
    total_fermion_states = 45 = 3·15, Λᵏ dimension table C(5,k)
    for k=0..5, exterior-algebra total 2^d = 32, Hodge pairings
    Λᵏ ↔ Λᵈ⁻ᵏ, falsifier (no 4th gen, no Λ⁶), atomic primitives. -/
theorem matter_content_capstone :
    -- 1 gen = 15
    gen_fermion_count = 15
    -- Atomic form: C(d,1) + C(d,2)
    ∧ gen_fermion_count = d + d * (d - 1) / 2
    ∧ d * (d - 1) / 2 = 10
    -- 3 gens × 15 = 45
    ∧ N_gen = 3
    ∧ total_fermion_states = 45
    -- Λᵏ(ℂ⁵) dimension table
    ∧ lambda_dim 0 = 1
    ∧ lambda_dim 1 = 5
    ∧ lambda_dim 2 = 10
    ∧ lambda_dim 3 = 10
    ∧ lambda_dim 4 = 5
    ∧ lambda_dim 5 = 1
    -- Total = 2^d = 32
    ∧ lambda_dim 0 + lambda_dim 1 + lambda_dim 2
        + lambda_dim 3 + lambda_dim 4 + lambda_dim 5 = 32
    -- Hodge: Λᵏ ↔ Λᵈ⁻ᵏ
    ∧ lambda_dim 1 = lambda_dim 4
    ∧ lambda_dim 2 = lambda_dim 3
    -- Per-gen breakdown N_gen · (Λ¹+Λ²) = 45
    ∧ N_gen * (lambda_dim 1 + lambda_dim 2) = 45
    -- Falsifier: no 4th gen slot, no Λ⁶
    ∧ binom NS 4 = 0
    ∧ binom d 6 = 0
    -- Atomic primitives
    ∧ NS = 3 ∧ NT = 2 ∧ d = 5 := by decide

end E213.Lib.Physics.Simplex.GenerationStructure
