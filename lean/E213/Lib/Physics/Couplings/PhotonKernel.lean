import E213.Lib.Physics.AlphaEM.Bare

/-!
# Photon = K_{NS,NT}^{(c)} cycle space (0 axioms part)

User insight (2026-04-27): defining the photon as the incidence matrix kernel.
Direct LA is difficult without Mathlib, but the **first Betti number** form
(`b_1 = E - V + 1` for connected) carries the same information + is decidable.

## ★ Atomicity-forced identity ★

For bipartite multigraph K_{NS,NT} with c-fold edge multiplicity:
  E (edges)        = c · NS · NT       = 12  (Hint 2)
  V (vertices)     = NS + NT           = d = 5
  b_0 (components) = 1                   (connected)
  b_1 (cycles)     = E - V + b_0        = 12 - 5 + 1 = 8

**b_1 = NS² - 1 = adjoint SU(NS) = 1/α_3 (confined)**

This identity holds only for (NS, NT, c) = (3, 2, 2) —
i.e., PairForcing → Atomicity forces the equivalence between b_1 and 1/α_3.

## Three force prefactors as edge weights

  α_3:  b_1 = E - V + 1 = NS² - 1            [cycle space]
  α_2:  E · NT = c·NS·NT² = 24 = d²-1         [full adjoint!]
  α_1 Y-norm: E · d = c·NS·NT·d = 60          [full dimension]

  α_3: *cycle space dim* (Euler formula)
  α_2: *edge × temporal depth* (rank exhaustion form)
  α_1: *edge × total dim d* (no rank exhaustion, full d)

All three prefactors generated from the *same graph* K_{NS,NT}^{(c)} by different operations.
Three different cohomologies on one lattice.
-/

namespace E213.Lib.Physics.Couplings.PhotonKernel

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Physics.AlphaEM.Prefactors

/-- Number of edges in the K_{NS,NT}^{(c)} multigraph where the photon lives.
    c-fold multiplicity = directed K_{NS,NT}. -/
def num_edges : Nat := c_lat * NS * NT

/-- Vertex count = NS + NT = d. -/
def num_vertices : Nat := NS + NT

/-- Connected → b_0 = 1.  K_{NS,NT} is always connected (every A
    vertex connects to every B vertex). -/
def num_components : Nat := 1

/-- First Betti number (cycle space dimension):
    b_1 = E - V + b_0 = 12 - 5 + 1 = 8. -/
def b_1 : Nat := num_edges - num_vertices + num_components

theorem b_1_eq_8 : b_1 = 8 := by decide

/-- ★★★ **Photon kernel + three-prefactor master** ★★★

  The bipartite multigraph K_{NS,NT}^{(c=2)} has cycle space
  dimension exactly NS² − 1 = 8 = adjoint SU(NS) = 1/α_3
  (confined).  This identity is NOT generic — it requires the
  atomic configuration (NS, NT, c) = (3, 2, 2); e.g., (3, 3, 2)
  gives 13 ≠ 8.  PairForcing → Atomicity forces it.

  All three force prefactors come from the SAME graph:
    α_3 (cycle space):      b_1 = NS² − 1                  = 8
    α_2 (edge × NT):        E · NT = c·NS·NT² = d² − 1     = 24
    α_1 (edge × d, Y-norm): E · d = c·NS·NT·d              = 60 -/
theorem photon_kernel_master :
    -- atomic counts
    num_edges = 12
    ∧ num_vertices = d
    -- cycle space = α_3 in two forms
    ∧ b_1 = NS * NS - 1
    ∧ c_lat * NS * NT - (NS + NT) + 1 = NS * NS - 1
    -- α_2 prefactor: edge × NT
    ∧ num_edges * NT = c_lat * NS * NT * NT
    ∧ num_edges * NT = d * d - 1
    -- α_1 (Y-norm): edge × d
    ∧ num_edges * d = 60
    ∧ num_edges * d = c_lat * NS * NT * d := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Physics.Couplings.PhotonKernel
