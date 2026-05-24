import E213.Lib.Math.Cohomology.Bipartite.V33c3
import E213.Lib.Math.Cohomology.Bipartite.V33Indeterminacy

/-!
# 4-fold Massey indeterminacy at K_{3,3}^{(c=3)}

★★★★★★★★★★★★★★★ **The c-counter is NOT in principal indeterminacy:
ψ discriminates rep₄ at BOTH c=2 and c=3** ★★★★★★★★★★★★★★★

c=3 mirror of `V33Indeterminacy`, using the same simple-cycle
face structure (9 mult-0 faces).

## Setup at c=3

  · 27 edges (mult-0, mult-1, mult-2 for each of 9 (S,T) pairs)
  · Same 9 simple 4-cycle faces using mult-0 edges only
  · Same H² = F₂⁵
  · g1, g2, g4, g5 — star/incidence at mult-0 (`V33c3`)
  · η_{ab} = e_3 + e_6, η_{cd} = e_12

## Key ψ identity at c=3

The discriminating functional ψ (XOR of 9 face values) carries
over verbatim — the same R_{S₀₁} + R_{S₀₂} + R_{S₁₂} construction.
By symbolic analysis:

  · `ψ(cupOpp g1 ξ) = 0 ∀ ξ : CochE` — six g1-edge supports
    {9, 12, 15, 18, 21, 24} each appear twice in the ψ-sum
  · `ψ(cupOpp ξ g5) = 0 ∀ ξ : CochE` — six g5-edge supports
    {0, 6, 9, 15, 18, 24} each appear twice
  · `ψ(δ¹σ) = 0` — each mult-0 edge appears in 4 (=even) faces

Hence rep₄ class at c=3 is ALSO outside principal indeterminacy.

## Cross-frame conclusion

The 4-fold Massey indeterminacy at K_{3,3}^{(c=2)} does NOT grow
into K_{3,3}^{(c=3)} to absorb rep₄.  The principal-cup indeterminacy
factor `g1 ∪ H¹ + H¹ ∪ g5` is killed by ψ at BOTH c=2 and c=3.

The literal `(c−1)`-codim extrapolation fails, and the c-counter
must live in a different structural invariant — richer face
complex (mult-1/mult-2 cycles included), higher cohomology `H³`,
or Steenrod `Sq¹` (Bockstein on `ℤ/4` lifts), NOT in the
principal indeterminacy of the 4-fold Massey.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.V33c3Indeterminacy

open E213.Lib.Math.Cohomology.Bipartite.V33c3
  (CochE delta1 cupOpp g1 g5 eta_ab eta_cd)

/-- The c=3 discriminating functional `ψ : (Fin 9 → Bool) → Bool`
    = XOR of all 9 face values.  Identical definition to c=2 — face
    space is `Fin 9` in both regimes (same simple-cycle face complex). -/
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

/-! ## §1 — `ψ(rep₄) = 1` at c=3

`rep₄ = cupOpp η_{ab} η_{cd}` at c=3 has the same chain
`(0, 0, 1, 0, 0, 0, 0, 0, 0)` as at c=2 (per
`V33c3.c3_rep4_face_values`), so ψ-XOR = 1. -/

theorem psi_rep4_eq_true : psi (cupOpp eta_ab eta_cd) = true := by
  unfold psi
  decide

/-! ## §2 — `ψ` kills `cupOpp g1 ξ` for any ξ at c=3

The six relevant ξ-edges {9, 12, 15, 18, 21, 24} each appear in
exactly two face contributions, canceling in F₂. -/

set_option maxHeartbeats 800000 in
theorem psi_kills_cupOpp_g1_left :
    ∀ ξ : CochE, psi (cupOpp g1 ξ) = false := by
  intro ξ
  unfold psi cupOpp
    E213.Lib.Math.Cohomology.Bipartite.V33c3.diagPair g1
  cases ξ ⟨9, by decide⟩ <;> cases ξ ⟨12, by decide⟩ <;>
    cases ξ ⟨15, by decide⟩ <;> cases ξ ⟨18, by decide⟩ <;>
    cases ξ ⟨21, by decide⟩ <;> cases ξ ⟨24, by decide⟩ <;> rfl

/-! ## §3 — `ψ` kills `cupOpp ξ g5` for any ξ at c=3

Six relevant ξ-edges {0, 6, 9, 15, 18, 24} each appear twice. -/

set_option maxHeartbeats 1600000 in
theorem psi_kills_cupOpp_g5_right :
    ∀ ξ : CochE, psi (cupOpp ξ g5) = false := by
  intro ξ
  unfold psi cupOpp
    E213.Lib.Math.Cohomology.Bipartite.V33c3.diagPair g5
  cases ξ ⟨0, by decide⟩ <;> cases ξ ⟨3, by decide⟩ <;>
    cases ξ ⟨6, by decide⟩ <;> cases ξ ⟨9, by decide⟩ <;>
    cases ξ ⟨12, by decide⟩ <;> cases ξ ⟨15, by decide⟩ <;>
    cases ξ ⟨18, by decide⟩ <;> cases ξ ⟨21, by decide⟩ <;>
    cases ξ ⟨24, by decide⟩ <;> rfl

/-! ## §4 — `ψ` kills `imδ¹` at c=3

Each mult-0 edge (indices ≡ 0 mod 3 in {0..26}) appears in
exactly 4 (= even) faces.  Mult-1 / mult-2 edges never appear in
the simple-cycle faces. -/

set_option maxHeartbeats 800000 in
theorem psi_kills_imd1 : ∀ σ : CochE, psi (delta1 σ) = false := by
  intro σ
  unfold psi delta1
    E213.Lib.Math.Cohomology.Bipartite.V33c3.face0
    E213.Lib.Math.Cohomology.Bipartite.V33c3.face1
    E213.Lib.Math.Cohomology.Bipartite.V33c3.face2
    E213.Lib.Math.Cohomology.Bipartite.V33c3.face3
    E213.Lib.Math.Cohomology.Bipartite.V33c3.face4
    E213.Lib.Math.Cohomology.Bipartite.V33c3.face5
    E213.Lib.Math.Cohomology.Bipartite.V33c3.face6
    E213.Lib.Math.Cohomology.Bipartite.V33c3.face7
    E213.Lib.Math.Cohomology.Bipartite.V33c3.face8
    E213.Lib.Math.Cohomology.Bipartite.V33c3.faceBoundary
  cases σ ⟨0, by decide⟩ <;> cases σ ⟨3, by decide⟩ <;>
    cases σ ⟨6, by decide⟩ <;> cases σ ⟨9, by decide⟩ <;>
    cases σ ⟨12, by decide⟩ <;> cases σ ⟨15, by decide⟩ <;>
    cases σ ⟨18, by decide⟩ <;> cases σ ⟨21, by decide⟩ <;>
    cases σ ⟨24, by decide⟩ <;> rfl

/-! ## §5 — ψ-linearity at c=3 (reuse infrastructure)

The c=3 ψ is the same XOR-of-9-faces functional, so the
`psiNatPos` machinery from `V33Indeterminacy` applies verbatim.
We define `vToNat` here for c=3 face cochains (same `Fin 9` codomain). -/

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

theorem psi_eq_psiNatPos (v : Fin 9 → Bool) :
    psi v = E213.Lib.Math.Cohomology.Bipartite.V33Indeterminacy.psiNatPos
              8 (vToNat v) := rfl

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

theorem psi_linear (v w : Fin 9 → Bool) :
    psi (fun f => xor (v f) (w f)) = xor (psi v) (psi w) := by
  rw [psi_eq_psiNatPos, psi_eq_psiNatPos, psi_eq_psiNatPos]
  rw [E213.Lib.Math.Cohomology.Bipartite.V33Indeterminacy.psiNatPos_congr_all
       8 (vToNat (fun f => xor (v f) (w f)))
       (fun i => xor (vToNat v i) (vToNat w i)) (vToNat_xor v w)]
  exact E213.Lib.Math.Cohomology.Bipartite.V33Indeterminacy.psiNatPos_linear
          8 (vToNat v) (vToNat w)

/-! ## §6 — Capstone: `[rep₄] ∉ Indeterminacy` in H² at c=3

The 4-fold Massey class `⟨g1, g4, g2, g5⟩` at K_{3,3}^{(c=3)}
is non-trivial modulo principal indeterminacy + coboundary,
exactly as at c=2.  The c-multiplicity `c=3` does NOT enlarge
the principal-cup indeterminacy enough to absorb rep₄. -/

theorem rep4_outside_indeterminacy :
    ∀ (ξ1 ξ2 σ : CochE),
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

/-! ## §7 — Cross-frame: ψ-discriminator agrees at c=2 and c=3

The same XOR-of-9-faces functional discriminates rep₄ from
principal indeterminacy at BOTH multiplicities.  Hence the
indeterminacy does NOT enlarge with `c` under the simple-cycle
face structure, and the cohomological obstruction stays in the
same "5th H²-direction" location independent of `c`.

The c-multiplicity counter must therefore live in a different
structural invariant (richer face complex, H³, or Steenrod). -/

theorem cross_frame_psi_discriminator :
    -- ψ(rep₄) = 1 at c=2
    E213.Lib.Math.Cohomology.Bipartite.V33Indeterminacy.psi
      (E213.Lib.Math.Cohomology.Bipartite.V33OppositeCup.cupOpp
        E213.Lib.Math.Cohomology.Bipartite.V33Massey4Fold.eta_ab
        E213.Lib.Math.Cohomology.Bipartite.V33Massey4Fold.eta_cd) = true
    -- ψ(rep₄) = 1 at c=3
    ∧ psi (cupOpp eta_ab eta_cd) = true :=
  ⟨E213.Lib.Math.Cohomology.Bipartite.V33Indeterminacy.psi_rep4_eq_true,
   psi_rep4_eq_true⟩

end E213.Lib.Math.Cohomology.Bipartite.V33c3Indeterminacy
