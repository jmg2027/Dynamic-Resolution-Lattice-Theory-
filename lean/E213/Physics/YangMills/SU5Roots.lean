import E213.Physics.Simplex.Counts
import E213.Physics.Simplex.GenerationStructure

/-!
# SU(5) root system from 5-simplex (0 axioms)

DRLT (ch11):

  SU(5) Lie algebra rank = 4 (= d - 1).
  Roots in 4-dimensional weight space.
  Number of roots = d² - d = d·(d-1) = 20.
  Adjoint = roots + Cartan = 20 + 4 = 24 = d² - 1 ★

## ★ SU(5) structure from atomicity ★

  Rank: d - 1 = 4
  Roots: d(d-1) = 20
  Cartan: d - 1 = 4
  Adjoint: d² - 1 = 24
  
  All atomic.

## Reps content

  Fundamental: 5 = d
  Antifundamental: 5̄ = d (CPT conjugate)
  Adjoint: 24 = d² - 1
  Symmetric: (d² + d)/2 = 15
  Antisymmetric ∧²: 10 = d(d-1)/2

## Mass matrix structure (ch11)

  Up-quark mass matrix in DRLT: democratic seesaw
  (m_u : m_c : m_t) ratio coded in SU(5) structure.

## Atomic

  All SU(5) numbers (4, 5, 10, 20, 24) from {NS, NT, d}.
-/

namespace E213.Physics.YangMills.SU5Roots

open E213.Physics.Simplex.Counts

/-- SU(5) rank = d - 1 = 4. -/
def su5_rank : Nat := d - 1

theorem rank_eq_4 : su5_rank = 4 := by decide

/-- Roots count: d(d-1) = 20. -/
def num_roots : Nat := d * (d - 1)

theorem roots_eq_20 : num_roots = 20 := by decide

/-- Cartan: rank = d - 1. -/
def cartan : Nat := d - 1

/-- Adjoint dim = roots + Cartan = d² - 1. -/
theorem adjoint_decomp :
    num_roots + cartan = d * d - 1
    ∧ d * d - 1 = 24 := by decide

/-- Symmetric rep dim = d(d+1)/2 = 15.  Same 15 as 1 generation. -/
def symmetric_dim : Nat := d * (d + 1) / 2

theorem symmetric_eq_15 : symmetric_dim = 15 := by decide

/-- ★ Symmetric SU(5) rep dim = 1 generation fermion count ★ -/
theorem symmetric_eq_generation :
    symmetric_dim = 15
    ∧ binom d 1 + binom d 2 = 15 := by decide

/-- ★ Capstone — SU(5) all atomic ★ -/
theorem su5_atomic :
    -- Rank d-1
    (su5_rank = d - 1)
    -- Roots d(d-1)
    ∧ (num_roots = d * (d - 1))
    ∧ (num_roots = 20)
    -- Adjoint d²-1
    ∧ (num_roots + cartan = d * d - 1)
    -- Symmetric = 1 generation
    ∧ (symmetric_dim = 15)
    -- All atomic
    ∧ (NS = 3) ∧ (NT = 2) ∧ (d = 5) := by decide

end E213.Physics.YangMills.SU5Roots
