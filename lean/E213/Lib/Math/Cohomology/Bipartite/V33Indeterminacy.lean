import E213.Lib.Math.Cohomology.Bipartite.V33Massey4Fold

/-!
# 4-fold Massey indeterminacy at K_{3,3}^{(c=2)} — ⟨g1, g4, g2, g5⟩

★★★★★★★★★★★★★★★ **rep₄ is a non-trivial H² cohomology class**
★★★★★★★★★★★★★★★

Promotes the chain-level `rep₄ = (0, 0, 1, 0, 0, 0, 0, 0, 0)`
breakthrough (`V33Massey4Fold`) to a genuine non-trivial H² class:

  [rep₄] ∉ Indeterminacy(⟨g1, g4, g2, g5⟩) in H²

via a discriminating linear functional ψ : H² → F₂ that

  · `ψ(rep₄) = 1`
  · vanishes on the principal indeterminacy `g1 ∪ C¹ + C¹ ∪ g5`
    — *for all cochains* (not just cocycles), so sub-Massey shift
    contributions (which land in the same principal terms after
    lift) are absorbed automatically
  · vanishes on `imδ¹` (well-defined functional on H²)

## Definition of ψ

  `ψ(v) = ⊕_{f=0}^{8} v(f)`
        = `R_{S₀₁}(v) + R_{S₀₂}(v) + R_{S₁₂}(v)`

where `R_{S_{ij}} = face_{i,j,0} + face_{i,j,1} + face_{i,j,2}` is
the S-row sum at S-pair (i,j).  Equivalently, the "S-block total"
functional that is dual to the 5th H² direction not reached by
any 3-fold Massey product (whose violation vectors all have
S-block-sum = 0).

## Why ψ kills cup image *for all cochains*

Symbolic expansion of `cupOpp g1 ξ`: g1 = e_0 + e_2 + e_4, so each
diagonal-pair contribution involves a single ξ-edge from
{e_6, e_8, e_10, e_12, e_14, e_16}.  Summing the 18 diagonal-pair
terms across the 9 faces, each of these 6 ξ-edges appears
*exactly twice*, hence XORs to 0.  No cocycle hypothesis needed.

Symmetrically for `cupOpp ξ g5` with g5 = e_2 + e_8 + e_14: each
of the 6 ξ-edges {0, 4, 6, 10, 12, 16} appears twice.

## Why ψ kills imδ¹

Each mult-0 edge e_{2k} appears in *exactly* 4 of the 9 simple
4-cycle faces (4 = `C(2,1)·C(2,1)`: 2 S-pairs containing src ×
2 T-pairs containing tgt).  Hence `XOR_{faces} δ¹σ(face)` =
`XOR_e (4·σ(e))` = 0 in F₂.  Mult-1 edges never appear in faces.

## Categorical content

`ψ` exhibits the 5th H² direction as the *exact* "Massey-witnessed
beyond cup-image" cohomology — an honest secondary operation.
This upgrades the Phase 18-B / post-merge result from a
*chain-level* breakthrough to a true *cohomology* one.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.V33Indeterminacy

open E213.Lib.Math.Cohomology.Bipartite.V33 (CochE delta1)
open E213.Lib.Math.Cohomology.Bipartite.V33OppositeCup (cupOpp g1 g5)
open E213.Lib.Math.Cohomology.Bipartite.V33Massey4Fold (eta_ab eta_cd)

/-- The 5th-dimension discriminating functional
    `ψ : (Fin 9 → Bool) → Bool` = XOR of all 9 face values. -/
def psi (v : Fin 9 → Bool) : Bool :=
  xor (xor (xor (xor (xor (xor (xor (xor
    (v ⟨0, by decide⟩) (v ⟨1, by decide⟩))
    (v ⟨2, by decide⟩))
    (v ⟨3, by decide⟩))
    (v ⟨4, by decide⟩))
    (v ⟨5, by decide⟩))
    (v ⟨6, by decide⟩))
    (v ⟨7, by decide⟩))
    (v ⟨8, by decide⟩)

/-! ## §1 — `ψ(rep₄) = 1`

The 4-fold Massey representative `rep₄ = cupOpp η_{ab} η_{cd}` =
`(0, 0, 1, 0, 0, 0, 0, 0, 0)` evaluates ψ to true (single face
support at face 2, XOR of 9 face values = 1). -/

theorem psi_rep4_eq_true : psi (cupOpp eta_ab eta_cd) = true := by
  unfold psi
  decide

/-! ## §2 — `ψ` kills the left principal indeterminacy `g1 ∪ C¹`

For any (not necessarily cocycle) edge cochain ξ, the face values
of `cupOpp g1 ξ` only involve `ξ` at six edges {6, 8, 10, 12, 14, 16}
(the "S₁-row" and "S₂-row" edges away from S₀'s star), and each
of these six values appears in *exactly two* of faces 0-8 in
the ψ-sum.  Hence the XOR cancels identically.

Faces 6, 7, 8 contribute 0 (no `g1`-edge in their diagonal sets). -/

set_option maxHeartbeats 800000 in
theorem psi_kills_cupOpp_g1_left :
    ∀ ξ : E213.Lib.Math.Cohomology.Bipartite.V33.CochE,
      psi (cupOpp g1 ξ) = false := by
  intro ξ
  unfold psi cupOpp
    E213.Lib.Math.Cohomology.Bipartite.V33OppositeCup.diagPair g1
  cases ξ ⟨6, by decide⟩ <;> cases ξ ⟨8, by decide⟩ <;>
    cases ξ ⟨10, by decide⟩ <;> cases ξ ⟨12, by decide⟩ <;>
    cases ξ ⟨14, by decide⟩ <;> cases ξ ⟨16, by decide⟩ <;> rfl

/-! ## §3 — `ψ` kills the right principal indeterminacy `C¹ ∪ g5`

Symmetric to §2: g5 = e_2 + e_8 + e_14 (T₁-incidence), so the
relevant ξ-edges are {0, 4, 6, 10, 12, 16}, each appearing twice
in the ψ-sum. -/

set_option maxHeartbeats 1600000 in
theorem psi_kills_cupOpp_g5_right :
    ∀ ξ : E213.Lib.Math.Cohomology.Bipartite.V33.CochE,
      psi (cupOpp ξ g5) = false := by
  intro ξ
  unfold psi cupOpp
    E213.Lib.Math.Cohomology.Bipartite.V33OppositeCup.diagPair g5
  cases ξ ⟨0, by decide⟩ <;> cases ξ ⟨2, by decide⟩ <;>
    cases ξ ⟨4, by decide⟩ <;> cases ξ ⟨6, by decide⟩ <;>
    cases ξ ⟨8, by decide⟩ <;> cases ξ ⟨10, by decide⟩ <;>
    cases ξ ⟨12, by decide⟩ <;> cases ξ ⟨14, by decide⟩ <;>
    cases ξ ⟨16, by decide⟩ <;> rfl

/-! ## §4 — `ψ` kills `imδ¹` (well-defined functional on H²)

Each mult-0 edge `e_{2k}` appears in *exactly* 4 of the 9 simple
4-cycle faces (`C(2,1) · C(2,1) = 4`: 2 S-pairs containing src ×
2 T-pairs containing tgt).  Mult-1 edges `e_{2k+1}` never appear
in any face (faces use only mult-0 edges).

Hence `ψ(δ¹σ) = XOR_f δ¹σ(f) = XOR_{e mult-0} 4·σ(e) = 0` in F₂. -/

theorem psi_kills_imd1 :
    ∀ σ : E213.Lib.Math.Cohomology.Bipartite.V33.CochE,
      psi (delta1 σ) = false := by
  intro σ
  unfold psi delta1
    E213.Lib.Math.Cohomology.Bipartite.V33.face0
    E213.Lib.Math.Cohomology.Bipartite.V33.face1
    E213.Lib.Math.Cohomology.Bipartite.V33.face2
    E213.Lib.Math.Cohomology.Bipartite.V33.face3
    E213.Lib.Math.Cohomology.Bipartite.V33.face4
    E213.Lib.Math.Cohomology.Bipartite.V33.face5
    E213.Lib.Math.Cohomology.Bipartite.V33.face6
    E213.Lib.Math.Cohomology.Bipartite.V33.face7
    E213.Lib.Math.Cohomology.Bipartite.V33.face8
    E213.Lib.Math.Cohomology.Bipartite.V33.faceBoundary
  cases σ ⟨0, by decide⟩ <;> cases σ ⟨2, by decide⟩ <;>
    cases σ ⟨4, by decide⟩ <;> cases σ ⟨6, by decide⟩ <;>
    cases σ ⟨8, by decide⟩ <;> cases σ ⟨10, by decide⟩ <;>
    cases σ ⟨12, by decide⟩ <;> cases σ ⟨14, by decide⟩ <;>
    cases σ ⟨16, by decide⟩ <;> rfl

/-! ## §5 — ψ-linearity over pointwise XOR

The XOR-of-9 functional ψ distributes over pointwise XOR.  Proved
via the abstract 18-variable Bool identity (`xor_18_distribute`)
which is decidable. -/

/-- Bool-XOR AC pair swap: `(a⊕b) ⊕ (c⊕d) = (a⊕c) ⊕ (b⊕d)`. -/
theorem xor_pair_swap (a b c d : Bool) :
    xor (xor a b) (xor c d) = xor (xor a c) (xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- Recursive XOR over a `Nat → Bool`.  Size `n+1`, base case
    `v 0` (no leading `false` — keeps definitional match with `psi`
    for `n+1 = 9`). -/
def psiNatPos : (n : Nat) → (Nat → Bool) → Bool
  | 0, v => v 0
  | k+1, v => xor (psiNatPos k v) (v (k+1))

theorem psiNatPos_linear (n : Nat) (v w : Nat → Bool) :
    psiNatPos n (fun i => xor (v i) (w i))
      = xor (psiNatPos n v) (psiNatPos n w) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show xor (psiNatPos k _) (xor (v (k+1)) (w (k+1)))
        = xor (xor (psiNatPos k v) (v (k+1)))
              (xor (psiNatPos k w) (w (k+1)))
    rw [ih]
    exact xor_pair_swap _ _ _ _

theorem psiNatPos_congr_all (n : Nat) (v w : Nat → Bool)
    (h : ∀ i, v i = w i) : psiNatPos n v = psiNatPos n w := by
  induction n with
  | zero => exact h 0
  | succ k ih =>
    show xor (psiNatPos k v) (v (k+1)) = xor (psiNatPos k w) (w (k+1))
    rw [ih, h (k+1)]

/-- Pattern-match lift of `Fin 9 → Bool` to `Nat → Bool` —
    avoids `dite` (and the `propext` it would bring through
    `dite_true`).  Out-of-range values default to false. -/
def vToNat (v : Fin 9 → Bool) : Nat → Bool
  | 0 => v ⟨0, by decide⟩
  | 1 => v ⟨1, by decide⟩
  | 2 => v ⟨2, by decide⟩
  | 3 => v ⟨3, by decide⟩
  | 4 => v ⟨4, by decide⟩
  | 5 => v ⟨5, by decide⟩
  | 6 => v ⟨6, by decide⟩
  | 7 => v ⟨7, by decide⟩
  | 8 => v ⟨8, by decide⟩
  | _ => false

/-- `psi v = psiNatPos 8 (vToNat v)` definitionally. -/
theorem psi_eq_psiNatPos (v : Fin 9 → Bool) :
    psi v = psiNatPos 8 (vToNat v) := rfl

/-- `vToNat` distributes over pointwise XOR at every Nat index. -/
theorem vToNat_xor (v w : Fin 9 → Bool) (i : Nat) :
    vToNat (fun f => xor (v f) (w f)) i = xor (vToNat v i) (vToNat w i) := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | _+9 => rfl

/-- ψ-linearity, lifted from `psiNatPos`.  No `funext` needed —
    pointwise agreement is handled by `psiNatPos_congr_all`. -/
theorem psi_linear (v w : Fin 9 → Bool) :
    psi (fun f => xor (v f) (w f)) = xor (psi v) (psi w) := by
  rw [psi_eq_psiNatPos, psi_eq_psiNatPos, psi_eq_psiNatPos]
  rw [psiNatPos_congr_all 8 (vToNat (fun f => xor (v f) (w f)))
       (fun i => xor (vToNat v i) (vToNat w i)) (vToNat_xor v w)]
  exact psiNatPos_linear 8 (vToNat v) (vToNat w)

/-! ## §6 — Capstone: `[rep₄] ∉ Indeterminacy` in H²

★★★★★★★★★★★★★★★ **rep₄ is a non-trivial H² class outside the
4-fold Massey indeterminacy** ★★★★★★★★★★★★★★★

Combining §1-§5: for ANY choice of left-shift `ξ₁`, right-shift
`ξ₂`, and chain-level shift `σ`, the cochain

  `rep₄ + cupOpp g1 ξ₁ + cupOpp ξ₂ g5 + δ¹σ`

is NEVER zero — by ψ-linearity its ψ-value is
`true ⊕ false ⊕ false ⊕ false = true`.

Hence `[rep₄] ≠ 0 + [indeterminacy]` in H², i.e., the chain-level
rep₄ breakthrough lifts to a genuine non-trivial cohomology class. -/

/-- The chain-level capstone: `rep₄` is never equal to a sum of
    principal-indeterminacy + coboundary contributions, so its
    H² class is outside the 4-fold Massey indeterminacy of
    `⟨g1, g4, g2, g5⟩`. -/
theorem rep4_outside_indeterminacy :
    ∀ (ξ1 ξ2 σ : E213.Lib.Math.Cohomology.Bipartite.V33.CochE),
      cupOpp eta_ab eta_cd ≠
        (fun f => xor (xor (cupOpp g1 ξ1 f) (cupOpp ξ2 g5 f)) (delta1 σ f)) := by
  intro ξ1 ξ2 σ heq
  have h := congrArg psi heq
  rw [psi_rep4_eq_true] at h
  have rhs_zero :
      psi (fun f => xor (xor (cupOpp g1 ξ1 f) (cupOpp ξ2 g5 f)) (delta1 σ f))
        = false := by
    rw [psi_linear, psi_linear]
    rw [psi_kills_cupOpp_g1_left, psi_kills_cupOpp_g5_right, psi_kills_imd1]
    rfl
  rw [rhs_zero] at h
  exact Bool.noConfusion h

end E213.Lib.Math.Cohomology.Bipartite.V33Indeterminacy
