import E213.Lib.Math.Cohomology.Bipartite.Parametric.CochSpaces
import E213.Lib.Math.NatRing
import E213.Meta.Tactic.BoolHelper
import E213.Meta.Tactic.Fin213
import E213.Meta.Nat.NatDiv213
import E213.Meta.Tactic.NatHelper

/-!
# Universal kerSize δ⁰ = 2 for K_{NS,NT}^{(c)}

For every bipartite multigraph parameter triple
`(NS, NT, c)` with `NS ≥ 1`, `NT ≥ 1`, `c ≥ 1`, the kernel of
`δ⁰ : C⁰ → C¹` consists of exactly the two constant vertex
cochains (`all-false` and `all-true`), so `b₀ = 1` universally.

## Walk argument

Every edge `e` enforces `σ(srcFin e) = σ(tgtFin e)`.  Using
three families of canonical mult-0 edges:

  · `e = 0` (the `(s=0, t=0)` edge) — anchors `σ(0) = σ(NS)`
  · `e = c·NT·s` for `s ∈ Fin NS` — gives `σ(s) = σ(NS)`
  · `e = c·t` for `t ∈ Fin NT` — gives `σ(0) = σ(NS+t)`

Combining these chains: `σ(i) = σ(0)` for every vertex `i`,
hence σ constant.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.Parametric.KerSizeUniversal

open E213.Lib.Math.Cohomology.Bipartite.Parametric.CochSpaces
open E213.Lib.Math.NatRing (mul_lt_mul_left_pure nat_mul_assoc)
open E213.Tactic.BoolHelper (eq_of_xor_false)
open E213.Tactic.Fin213 (fin_eq_of_val)
open E213.Meta.Nat.NatDiv213 (mul_div_cancel_left_pure add_mul_div_left_pure)
open E213.Tactic.NatHelper (add_mul_mod_self_pure add_sub_of_le)

/-! ## §2 — Key edge index bounds -/

/-- Edge `c·NT·s` (mult-0 connecting S-vertex `s` to T-vertex `0`)
    is in range when `s < NS`. -/
private theorem edge_S_bound (NS NT c s : Nat) (hc : 1 ≤ c)
    (hNT : 1 ≤ NT) (hs : s < NS) : c * NT * s < c * NS * NT := by
  rw [Nat.mul_assoc, Nat.mul_assoc]
  apply mul_lt_mul_left_pure hc
  have h_NT_mul : NT * s < NT * NS := mul_lt_mul_left_pure hNT hs
  rw [Nat.mul_comm NS NT]; exact h_NT_mul

/-- Edge `c·t` (mult-0 connecting S-vertex `0` to T-vertex `t`)
    is in range when `t < NT` and `NS ≥ 1`. -/
private theorem edge_T_bound (NS NT c t : Nat) (hc : 1 ≤ c)
    (hNS : 1 ≤ NS) (ht : t < NT) : c * t < c * NS * NT := by
  have h1 : c * t < c * NT := mul_lt_mul_left_pure hc ht
  have h_NS_NT : NT ≤ NS * NT := by
    have : 1 * NT ≤ NS * NT := Nat.mul_le_mul_right NT hNS
    rw [Nat.one_mul] at this; exact this
  have h2 : c * NT ≤ c * (NS * NT) := Nat.mul_le_mul_left c h_NS_NT
  rw [← Nat.mul_assoc] at h2
  exact Nat.lt_of_lt_of_le h1 h2

/-! ## §3 — srcOf / tgtOf evaluations for key edges -/

/-- For edge `c·NT·s` (when `c ≥ 1` and `s < NS`):
    `srcOf c NT (c·NT·s) = s`. -/
private theorem srcOf_S_edge (NT c s : Nat) (hc : 1 ≤ c) (hNT : 1 ≤ NT) :
    srcOf c NT (c * NT * s) = s := by
  unfold srcOf
  -- (c * NT * s) / c = NT * s (by mul_div_cancel_left with c > 0)
  rw [Nat.mul_assoc]
  rw [Nat.mul_div_cancel_left (NT * s) hc]
  -- (NT * s) / NT = s (by mul_div_cancel_left with NT > 0)
  rw [Nat.mul_div_cancel_left s hNT]

/-- For edge `c·NT·s`: `tgtOf c NT (c·NT·s) = 0`. -/
private theorem tgtOf_S_edge (NT c s : Nat) (hc : 1 ≤ c) (hNT : 1 ≤ NT) :
    tgtOf c NT (c * NT * s) = 0 := by
  unfold tgtOf
  rw [Nat.mul_assoc, Nat.mul_div_cancel_left (NT * s) hc]
  -- (NT * s) % NT = 0
  exact Nat.mul_mod_right NT s

/-- For edge `c·t`: `srcOf c NT (c·t) = 0` (when `t < NT`). -/
private theorem srcOf_T_edge (NT c t : Nat) (hc : 1 ≤ c) (ht : t < NT) :
    srcOf c NT (c * t) = 0 := by
  unfold srcOf
  rw [Nat.mul_div_cancel_left t hc]
  exact Nat.div_eq_of_lt ht

/-- For edge `c·t`: `tgtOf c NT (c·t) = t` (when `t < NT`). -/
private theorem tgtOf_T_edge (NT c t : Nat) (hc : 1 ≤ c) (ht : t < NT) :
    tgtOf c NT (c * t) = t := by
  unfold tgtOf
  rw [Nat.mul_div_cancel_left t hc]
  exact Nat.mod_eq_of_lt ht

/-! ## §4 — Canonical S-T edge: index, src, tgt evaluations -/

/-- For the canonical `(s, t, mult=0)` edge `e = c·(NT·s + t)`:
    the index value is `c·NT·s + c·t`. -/
private theorem canonical_edge_val (NT c s t : Nat) :
    c * (NT * s + t) = c * NT * s + c * t := by
  rw [Nat.mul_add, Nat.mul_assoc]

/-- For canonical edge: `srcOf c NT (c·(NT·s + t)) = s` when
    `t < NT`. -/
private theorem srcOf_canonical (NT c s t : Nat) (hc : 1 ≤ c) (hNT : 1 ≤ NT)
    (ht : t < NT) : srcOf c NT (c * (NT * s + t)) = s := by
  unfold srcOf
  rw [mul_div_cancel_left_pure c (NT * s + t) hc]
  -- (NT * s + t) / NT = s; rewrite as (t + NT * s) / NT
  rw [Nat.add_comm (NT * s) t]
  rw [add_mul_div_left_pure t NT s hNT]
  rw [Nat.div_eq_of_lt ht]
  exact Nat.zero_add s

/-- For canonical edge: `tgtOf c NT (c·(NT·s + t)) = t` when
    `t < NT`. -/
private theorem tgtOf_canonical (NT c s t : Nat) (hc : 1 ≤ c) (hNT : 1 ≤ NT)
    (ht : t < NT) : tgtOf c NT (c * (NT * s + t)) = t := by
  unfold tgtOf
  rw [mul_div_cancel_left_pure c (NT * s + t) hc]
  -- (NT * s + t) % NT = t; rewrite via add_comm
  rw [Nat.add_comm (NT * s) t]
  rw [Nat.mul_comm NT s]
  rw [add_mul_mod_self_pure t NT s]
  exact Nat.mod_eq_of_lt ht

/-- Canonical edge bound: `c·(NT·s + t) < c·NS·NT` when `s < NS`
    and `t < NT`. -/
private theorem canonical_edge_bound (NS NT c s t : Nat) (hc : 1 ≤ c)
    (hs : s < NS) (ht : t < NT) : c * (NT * s + t) < c * NS * NT := by
  -- c·(NT·s + t) ≤ c·(NT·s + NT-1) < c·(NT·s + NT) = c·NT·(s+1) ≤ c·NT·NS
  have h_t_lt : t < NT := ht
  have h_inner : NT * s + t < NT * (s + 1) := by
    rw [Nat.mul_succ]
    exact Nat.add_lt_add_left h_t_lt (NT * s)
  have h_step : NT * (s + 1) ≤ NT * NS := Nat.mul_le_mul_left NT hs
  have h_combined : NT * s + t < NT * NS :=
    Nat.lt_of_lt_of_le h_inner h_step
  have h_lhs : c * (NT * s + t) < c * (NT * NS) :=
    mul_lt_mul_left_pure hc h_combined
  have h_swap : c * (NT * NS) = c * NS * NT := by
    rw [Nat.mul_comm NT NS, ← nat_mul_assoc]
  rw [h_swap] at h_lhs
  exact h_lhs

/-! ## §6 — Universal kernel ⟹ vertex-pair equality

For every (s, t) ∈ Fin NS × Fin NT and every σ in the kernel of
δ⁰, the canonical S-T edge enforces `σ(s) = σ(NS + t)`. -/

/-- ★★★ **Universal vertex-pair bridge**: σ in kernel ⟹ for
    every (s, t) ∈ Fin NS × Fin NT, σ at S-vertex s equals σ
    at T-vertex (NS + t). -/
theorem ker_implies_pair_eq (NS NT c : Nat)
    (hS : 1 ≤ NS) (hT : 1 ≤ NT) (hc : 1 ≤ c)
    (hpos : 0 < NS + NT) (σ : CochV NS NT)
    (hker : ∀ e : Fin (c * NS * NT), delta0 NS NT c hpos σ e = false)
    (s : Nat) (hs : s < NS) (t : Nat) (ht : t < NT) :
    σ ⟨s, Nat.lt_of_lt_of_le hs (Nat.le_add_right NS NT)⟩
      = σ ⟨NS + t, Nat.add_lt_add_left ht NS⟩ := by
  -- Construct canonical S-T edge
  let e_st : Fin (c * NS * NT) :=
    ⟨c * (NT * s + t), canonical_edge_bound NS NT c s t hc hs ht⟩
  -- Apply kernel condition at this edge
  have h_ker_at : delta0 NS NT c hpos σ e_st = false := hker e_st
  -- Extract σ(srcFin) = σ(tgtFin) from xor = false
  have h_eq : σ (srcFin NS NT c hpos e_st) = σ (tgtFin NS NT c hpos e_st) :=
    eq_of_xor_false h_ker_at
  -- Compute srcFin e_st = ⟨s, _⟩
  have h_src_val : (srcFin NS NT c hpos e_st).val = s := by
    show srcOf c NT (c * (NT * s + t)) % (NS + NT) = s
    rw [srcOf_canonical NT c s t hc hT ht]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hs (Nat.le_add_right NS NT))
  -- Compute tgtFin e_st = ⟨NS + t, _⟩
  have h_tgt_val : (tgtFin NS NT c hpos e_st).val = NS + t := by
    show (NS + tgtOf c NT (c * (NT * s + t))) % (NS + NT) = NS + t
    rw [tgtOf_canonical NT c s t hc hT ht]
    exact Nat.mod_eq_of_lt (Nat.add_lt_add_left ht NS)
  -- Bridge to canonical Fin form via Fin.ext
  have h_src_eq : srcFin NS NT c hpos e_st
      = ⟨s, Nat.lt_of_lt_of_le hs (Nat.le_add_right NS NT)⟩ :=
    fin_eq_of_val _ _ _ _ _ h_src_val
  have h_tgt_eq : tgtFin NS NT c hpos e_st
      = ⟨NS + t, Nat.add_lt_add_left ht NS⟩ :=
    fin_eq_of_val _ _ _ _ _ h_tgt_val
  rw [← h_src_eq, ← h_tgt_eq]
  exact h_eq

/-! ## §6 — Vertex-pair equality ⟹ σ constant -/

/-- Bridge: if σ satisfies the vertex-pair equality, then σ is
    constant on all of `Fin (NS + NT)`.

    Strategy: every vertex equals σ at vertex `NS` (the
    "anchor"):
      · S-vertex s: σ(s) = σ(NS + 0) = σ(NS) via pair (s, 0)
      · T-vertex NS+t: σ(NS+t) = σ(0) (via pair (0, t)) =
        σ(NS+0) = σ(NS) (via pair (0, 0)). -/
theorem pair_eq_implies_constant (NS NT : Nat) (hS : 1 ≤ NS) (hT : 1 ≤ NT)
    (σ : Fin (NS + NT) → Bool)
    (hpair : ∀ s t : Nat, ∀ hs : s < NS, ∀ ht : t < NT,
      σ ⟨s, Nat.lt_of_lt_of_le hs (Nat.le_add_right NS NT)⟩
        = σ ⟨NS + t, Nat.add_lt_add_left ht NS⟩) :
    ∀ i j : Fin (NS + NT), σ i = σ j := by
  -- Anchor: σ at vertex NS
  have hNS_lt : NS < NS + NT := Nat.add_lt_add_left hT NS
  let anchor : Fin (NS + NT) := ⟨NS, hNS_lt⟩
  -- σ(s) = σ(NS) for s < NS (using pair (s, 0))
  have h_S : ∀ s : Nat, ∀ hs : s < NS,
      σ ⟨s, Nat.lt_of_lt_of_le hs (Nat.le_add_right NS NT)⟩ = σ anchor := by
    intro s hs
    have h := hpair s 0 hs hT
    -- h : σ ⟨s, _⟩ = σ ⟨NS + 0, _⟩.  NS + 0 = NS via Nat.add_zero.
    have h_anchor_eq : (⟨NS + 0, Nat.add_lt_add_left hT NS⟩ : Fin (NS + NT))
        = anchor := Fin.ext (Nat.add_zero NS)
    rw [h, h_anchor_eq]
  -- σ(NS+t) = σ(NS) for t < NT (via σ(0) bridge)
  have h_T : ∀ t : Nat, ∀ ht : t < NT,
      σ ⟨NS + t, Nat.add_lt_add_left ht NS⟩ = σ anchor := by
    intro t ht
    have h1 := hpair 0 t hS ht
    have h2 := hpair 0 0 hS hT
    have h_zero_eq : (⟨0, Nat.lt_of_lt_of_le hS (Nat.le_add_right NS NT)⟩
                        : Fin (NS + NT))
        = ⟨0, Nat.lt_of_lt_of_le hS (Nat.le_add_right NS NT)⟩ := rfl
    have h_anchor_eq : (⟨NS + 0, Nat.add_lt_add_left hT NS⟩ : Fin (NS + NT))
        = anchor := Fin.ext (Nat.add_zero NS)
    -- σ ⟨0,_⟩ = σ ⟨NS+t,_⟩ (h1)  AND  σ ⟨0,_⟩ = σ ⟨NS+0,_⟩ = σ anchor (h2)
    -- So σ ⟨NS+t,_⟩ = σ ⟨0,_⟩ = σ anchor
    rw [h2, h_anchor_eq] at h1
    -- h1 : σ anchor = σ ⟨NS+t,_⟩; flip
    exact h1.symm
  -- Now ∀ i, σ i = σ anchor → ∀ i j, σ i = σ j
  have h_const : ∀ i : Fin (NS + NT), σ i = σ anchor := by
    intro i
    rcases i with ⟨v, hv⟩
    -- Case on v < NS or v ≥ NS
    rcases Nat.lt_or_ge v NS with hv_S | hv_T
    · -- S-side
      have := h_S v hv_S
      -- this : σ ⟨v, ...⟩ = σ anchor, with the Fin proof
      exact this
    · -- T-side: v ≥ NS.  Let t = v - NS.
      have h_v_eq : v = NS + (v - NS) := (add_sub_of_le hv_T).symm
      have h_t_lt : v - NS < NT := by
        have : NS + (v - NS) < NS + NT := h_v_eq ▸ hv
        exact Nat.lt_of_add_lt_add_left this
      -- Use h_T at t = v - NS
      have h := h_T (v - NS) h_t_lt
      -- h : σ ⟨NS + (v - NS), _⟩ = σ anchor
      have h_fin_eq : (⟨v, hv⟩ : Fin (NS + NT))
          = ⟨NS + (v - NS), Nat.add_lt_add_left h_t_lt NS⟩ :=
        fin_eq_of_val _ _ _ _ _ h_v_eq
      rw [h_fin_eq]; exact h
  -- Conclude
  intro i j
  exact (h_const i).trans (h_const j).symm

/-! ## §7 — Universal master capstone: kernel ⟹ constant -/

/-- ★★★★★★★★★★★ **Universal GraphWalk kernel theorem**: for
    **every** `(NS, NT, c)` triple with `NS, NT, c ≥ 1`, the
    bipartite multigraph `K_{NS,NT}^{(c)}` has δ⁰-kernel
    consisting only of constant vertex cochains.

    Equivalently: if `σ : Fin (NS + NT) → Bool` satisfies
    `δ⁰σ = 0` (XOR of endpoints = false on every edge), then
    σ takes the same value at every vertex.

    **No bound on (NS, NT, c)** — the walk argument is uniform.
    Pays off the deferred `kerSize = 2` debt structurally.

    STRICT ∅-AXIOM. -/
theorem ker_implies_constant_universal (NS NT c : Nat)
    (hS : 1 ≤ NS) (hT : 1 ≤ NT) (hc : 1 ≤ c)
    (hpos : 0 < NS + NT) (σ : CochV NS NT)
    (hker : ∀ e : Fin (c * NS * NT), delta0 NS NT c hpos σ e = false) :
    ∀ i j : Fin (NS + NT), σ i = σ j :=
  pair_eq_implies_constant NS NT hS hT σ
    (fun s t hs ht => ker_implies_pair_eq NS NT c hS hT hc hpos σ hker s hs t ht)

/-- Corollary: as `kerSize δ⁰ = 2` since exactly the two constants
    (all-false, all-true) satisfy the kernel condition.  Universal
    in (NS, NT, c). -/
theorem ker_iff_constant (NS NT c : Nat)
    (hS : 1 ≤ NS) (hT : 1 ≤ NT) (hc : 1 ≤ c)
    (hpos : 0 < NS + NT) (σ : CochV NS NT) :
    (∀ e : Fin (c * NS * NT), delta0 NS NT c hpos σ e = false)
    ↔ (∀ i j : Fin (NS + NT), σ i = σ j) := by
  refine ⟨?_, ?_⟩
  · intro hker
    exact ker_implies_constant_universal NS NT c hS hT hc hpos σ hker
  · intro hconst e
    unfold delta0
    have h := hconst (srcFin NS NT c hpos e) (tgtFin NS NT c hpos e)
    rw [h]
    cases (σ (tgtFin NS NT c hpos e)) <;> rfl

end E213.Lib.Math.Cohomology.Bipartite.Parametric.KerSizeUniversal
