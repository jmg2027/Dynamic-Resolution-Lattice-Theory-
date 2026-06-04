import E213.Lib.Math.Analysis.Cauchy.DepthPRecursive
import E213.Lib.Math.Analysis.Cauchy.HurwitzianCF
import E213.Meta.Tactic.NatHelper

/-!
# A positive top finite-difference forces unboundedness (with an explicit witness)

The continued-fraction holonomicity tier (`HurwitzianCF`) lives on the partial-quotient
sequence `(aᵢ)`, and a Hurwitzian real's CF is quasi-polynomial — a genuine *polynomial* on
each residue class.  This file isolates a structural fact about such polynomial sections:

> **`positive_floor_unbounded`** — if the `(m+1)`-th iterated finite difference `Δ^{m+1}s` of
> a sequence is a *constant* (`polyDepth (m+1) s`) and that constant is `≥ 1`
> (`liftK (m+1) s 0 ≥ 1`), then `s` is **unbounded**: for every bound `B` there is an
> *explicit* index `n` with `B < s n`.

The proof is fully constructive — no LPO/LEM/choice.  A positive constant top difference makes
`Δᵐs` strictly increasing *everywhere*; one anti-difference at a time, "eventually strictly
increasing" descends to `s` itself (`evStrictMono_descend`); telescoping then names the
explicit index that exceeds any bound (`evStrictMono_unbounded`).  This is the
constructively-honest half of the monotone story (see the scope note below).

## What it does, and what it does **not**, say

The contrapositive (`bounded_floor_zero`, decidable on `ℕ`) says a **bounded** sequence of
finite difference-depth `m+1 ≥ 1` has *vanishing* top difference `Δ^{m+1}s(0) = 0`.

Applied to continued fractions, the honest scope is narrow and exact:

  * A Hurwitzian real with a **genuine positive-degree polynomial residue section** — e's
    linear `2k+2` section (`e_section_unbounded`, `ePQ_unbounded`) — necessarily has
    **unbounded** partial quotients.  This is `positive_floor_unbounded` on one section.
  * It says **nothing** about the periodic floor (tier 0, `φ`, `√2`): a non-constant periodic
    section is *not* of finite difference-depth at all (its differences stay periodic, never
    settling to a constant), so the hypothesis does not apply — consistent with `φ`, `√2`
    having bounded partial quotients.
  * It does **not** cover the geometric `2ⁿ` gap (`HurwitzianCF.geometric_not_quasipoly`):
    `2ⁿ` is exponential, hence has **no** finite difference-depth, so this lemma's hypothesis
    fails for it.  `2ⁿ` is unbounded for the separate (elementary) reason of geometric
    growth, not because of this theorem.

So the precise statement is: *positive-degree polynomial partial-quotient growth forces
unboundedness.*  The broader slogan "every tier above periodic needs unbounded p.q." is **not**
proved here — periodic and exponential sections lie outside the hypothesis class.

**Constructive-scope honesty.**  We do **not** prove "bounded `⟹` eventually constant": over
`ℕ` that is the monotone-sequence principle, equivalent to the limited principle of
omniscience (LPO; Mandelkern 1988), hence not ∅-axiom — mirroring the deliberate LEM-refusal
in `MonotonicBounded.lean`.  Constructively we get only the witnessed direction
(`positive_floor_unbounded`) and, by a decidable `ℕ` case split, the vanishing of the *top*
coefficient (`bounded_floor_zero`) — never the collapse to a constant.

A sharper companion (`positive_linear_exact`) closes the depth-1 positive case to the *exact*
linear formula `s n = s 0 + c·n` — the ∅-axiom positive-linear instance of the otherwise
Newton–Gregory-blocked `QuasiPolyCF ⟹ polynomially-bounded` bridge (truncation, the blocker
over `ℕ`, vanishes once `c ≥ 1`).

All ∅-axiom (`13 pure / 0 dirty`).
-/

namespace E213.Lib.Math.Analysis.Cauchy.PositiveFloorUnbounded

open E213.Lib.Math.Analysis.Cauchy.DivergenceLadder (diff liftK isConst)
open E213.Lib.Math.Analysis.Cauchy.DepthPRecursive
  (polyDepth polyDepth_succ_iff const_polyDepth0)
open E213.Lib.Math.Analysis.Cauchy.HurwitzianCF (ePQ polyDepth_congr resP_mod res3_div)

/-! ## §1 — from `1 ≤ a - b` to `b < a` (constructive, decidable case split) -/

/-- A positive truncated difference reveals strict order: `1 ≤ a - b ⟹ b < a`.  Proved by a
    decidable trichotomy split (no `propext`, no classical contradiction). -/
theorem lt_of_one_le_sub {a b : Nat} (h : 1 ≤ a - b) : b < a := by
  rcases Nat.lt_or_ge b a with hlt | hge
  · exact hlt
  · -- `hge : a ≤ b` ⟹ `a - b ≤ b - b = 0`, contradicting `1 ≤ a - b`
    have h1 : a - b ≤ b - b := Nat.sub_le_sub_right hge b
    rw [Nat.sub_self] at h1
    exact absurd (Nat.le_trans h h1) (Nat.not_succ_le_zero 0)

/-! ## §2 — "eventually strictly increasing" and its unboundedness -/

/-- `s` is **strictly increasing from index `N` on**. -/
def EvStrictMono (N : Nat) (s : Nat → Nat) : Prop := ∀ n, N ≤ n → s n < s (n + 1)

/-- Telescoping bound: from `N` on, `s (N + i) ≥ s N + i`. -/
theorem evStrictMono_ge {N : Nat} {s : Nat → Nat} (h : EvStrictMono N s) :
    ∀ i, s N + i ≤ s (N + i) := by
  intro i
  induction i with
  | zero => exact Nat.le_refl _
  | succ i ih =>
    have hstep : s (N + i) < s (N + i + 1) := h (N + i) (Nat.le_add_right N i)
    have a1 : s N + (i + 1) = (s N + i) + 1 := (Nat.add_assoc (s N) i 1).symm
    have a2 : (s N + i) + 1 ≤ s (N + i) + 1 := Nat.add_le_add_right ih 1
    have a3 : s (N + i) + 1 ≤ s (N + i + 1) := hstep
    have a4 : N + i + 1 = N + (i + 1) := Nat.add_assoc N i 1
    rw [a1, ← a4]
    exact Nat.le_trans a2 a3

/-- **Eventually strictly increasing ⟹ unbounded**, with the explicit witness
    `n = N + (B + 1)`. -/
theorem evStrictMono_unbounded {N : Nat} {s : Nat → Nat} (h : EvStrictMono N s) :
    ∀ B, ∃ n, B < s n := by
  intro B
  refine ⟨N + (B + 1), ?_⟩
  have hge := evStrictMono_ge h (B + 1)
  exact Nat.lt_of_lt_of_le
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self B) (Nat.le_add_left (B + 1) (s N))) hge

/-! ## §3 — anti-difference preserves "eventually strictly increasing" -/

/-- One anti-difference step: if `Δ(Δʲs) = Δ^{j+1}s` is eventually strictly increasing from
    `N`, then `Δʲs` is eventually strictly increasing from `N + 1`.  (A strictly-increasing
    difference is eventually `≥ 1`, and a `≥ 1` difference is a strict increase of the
    anti-difference.) -/
theorem evStrictMono_down (j N : Nat) (s : Nat → Nat)
    (h : EvStrictMono N (liftK (j + 1) s)) : EvStrictMono (N + 1) (liftK j s) := by
  intro n hn
  have hpos : 1 ≤ liftK (j + 1) s n := by
    have hNn : N ≤ n := Nat.le_of_succ_le hn
    have hi1 : 1 ≤ n - N := E213.Tactic.NatHelper.le_pred_of_succ_le hn
    have hge := evStrictMono_ge h (n - N)
    rw [E213.Tactic.NatHelper.add_sub_of_le hNn] at hge
    exact Nat.le_trans hi1
      (Nat.le_trans (Nat.le_add_left (n - N) (liftK (j + 1) s N)) hge)
  show liftK j s n < liftK j s (n + 1)
  have hdef : liftK (j + 1) s n = liftK j s (n + 1) - liftK j s n := rfl
  rw [hdef] at hpos
  exact lt_of_one_le_sub hpos

/-- Descend the anti-difference all the way to `s`: a finite difference `Δᵐs` that is
    eventually strictly increasing forces `s` itself to be eventually strictly increasing
    (from some index).  The index is existential — its exact value is irrelevant for
    unboundedness. -/
theorem evStrictMono_descend : ∀ (m N : Nat) (s : Nat → Nat),
    EvStrictMono N (liftK m s) → ∃ N', EvStrictMono N' s := by
  intro m
  induction m with
  | zero => intro N s h; exact ⟨N, h⟩
  | succ m ih => intro N s h; exact ih (N + 1) s (evStrictMono_down m N s h)

/-! ## §4 — the headline: a positive top finite-difference forces unboundedness -/

/-- ★★★ **Positive top finite-difference ⟹ unbounded (constructive, explicit witness).**
    If the `(m+1)`-th iterated
    finite difference of `s` is a *positive* constant (`polyDepth (m+1) s` and
    `liftK (m+1) s 0 ≥ 1`), then `s` is **unbounded** — for every `B` there is an explicit
    index `n` with `B < s n`.  No LPO/LEM: the witness is produced by descent. -/
theorem positive_floor_unbounded (m : Nat) (s : Nat → Nat)
    (hpoly : polyDepth (m + 1) s) (hpos : 1 ≤ liftK (m + 1) s 0) :
    ∀ B, ∃ n, B < s n := by
  have hbase : EvStrictMono 0 (liftK m s) := by
    intro n _
    have hc : liftK (m + 1) s n = liftK (m + 1) s 0 := hpoly n
    have h1 : 1 ≤ liftK (m + 1) s n := by rw [hc]; exact hpos
    have hdef : liftK (m + 1) s n = liftK m s (n + 1) - liftK m s n := rfl
    rw [hdef] at h1
    exact lt_of_one_le_sub h1
  obtain ⟨N', hN'⟩ := evStrictMono_descend m 0 s hbase
  exact evStrictMono_unbounded hN'

/-- ★★★ **The contrapositive — a bounded discrete-polynomial has vanishing top difference.**
    A sequence bounded by `B` with finite difference-depth `m+1 ≥ 1` has `Δ^{m+1}s(0) = 0`;
    it cannot be a genuine positive-degree polynomial.  (Decidable case split, ∅-axiom.) -/
theorem bounded_floor_zero (m : Nat) (s : Nat → Nat)
    (hpoly : polyDepth (m + 1) s) (B : Nat) (hb : ∀ n, s n ≤ B) :
    liftK (m + 1) s 0 = 0 := by
  rcases Nat.eq_zero_or_pos (liftK (m + 1) s 0) with h | h
  · exact h
  · obtain ⟨n, hn⟩ := positive_floor_unbounded m s hpoly h B
    exact absurd (Nat.lt_of_lt_of_le hn (hb n)) (Nat.lt_irrefl B)

/-! ## §4b — exact linear growth: a positive-floor depth-1 sequence is `s 0 + c·n`

For `polyDepth 1 s` with a *positive* constant difference `c = Δs(0) ≥ 1`, the truncated
subtraction never truncates (`Δs n = c ≥ 1 ⟹ s(n+1) = s n + c` genuinely), so the discrete
antiderivative closes to an **exact** linear formula — sharper than mere unboundedness, and
the ∅-axiom witness that such sections are linearly bounded (⟹ irrationality measure `μ = 2`,
cited).  This is the positive-linear case of the otherwise Newton–Gregory-blocked
`QuasiPolyCF ⟹ polynomially-bounded` (truncated subtraction is what blocks the general `ℕ`
version; positivity removes it here). -/

/-- `a - b = c` with `c ≥ 1` is genuine subtraction: `a = b + c`. -/
theorem eq_add_of_sub_eq {a b c : Nat} (hc : 1 ≤ c) (h : a - b = c) : a = b + c := by
  have hab : 1 ≤ a - b := by rw [h]; exact hc
  have hba : b < a := lt_of_one_le_sub hab
  have he : b + (a - b) = a := E213.Tactic.NatHelper.add_sub_of_le (Nat.le_of_lt hba)
  rw [h] at he
  exact he.symm

/-- ★★★ **Exact linear growth.**  A depth-1 sequence with positive constant difference
    `c = liftK 1 s 0 ≥ 1` is exactly `s n = s 0 + c · n` — the discrete antiderivative closes
    with no `ℕ` truncation.  (e's `2k+2` section: `s 0 = 2`, `c = 2`.) -/
theorem positive_linear_exact (s : Nat → Nat) (hpoly : polyDepth 1 s)
    (hpos : 1 ≤ liftK 1 s 0) : ∀ n, s n = s 0 + liftK 1 s 0 * n := by
  intro n
  induction n with
  | zero => rw [Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    have hc : liftK 1 s n = liftK 1 s 0 := hpoly n
    have hdef : liftK 1 s n = s (n + 1) - s n := rfl
    have hstep : s (n + 1) = s n + liftK 1 s 0 :=
      eq_add_of_sub_eq hpos (by rw [← hdef, hc])
    rw [hstep, ih, Nat.add_assoc, ← Nat.mul_succ]

/-! ## §5 — the CF instance: a genuine positive-degree section forces unbounded p.q. (e) -/

/-- e's residue-`1 (mod 3)` partial-quotient section is `2k + 2`, of difference-depth `1`. -/
theorem two_k_two_polyDepth1 : polyDepth 1 (fun k => 2 * k + 2) := by
  apply (polyDepth_succ_iff 0 (fun k => 2 * k + 2)).mpr
  refine polyDepth_congr (s := fun _ => 2) ?_ (const_polyDepth0 2)
  intro k
  show (2 : Nat) = 2 * (k + 1) + 2 - (2 * k + 2)
  rw [Nat.mul_succ, Nat.add_comm (2 * k + 2) 2,
      E213.Tactic.NatHelper.add_sub_cancel_right]

/-- ★★ **e's continued fraction has unbounded partial quotients — via the structural theorem.**
    The linear section `2k+2` has constant top difference `2 ≥ 1`, so `positive_floor_unbounded`
    yields it unbounded.  (Elementary classically; here it is the positive-degree-section
    theorem at work, pinning e in the unbounded regime — a genuine polynomial section forces
    unbounded partial quotients.) -/
theorem e_section_unbounded : ∀ B, ∃ k, B < 2 * k + 2 := by
  apply positive_floor_unbounded 0 (fun k => 2 * k + 2) two_k_two_polyDepth1
  decide

/-- e's partial quotients `ePQ` are unbounded: the residue-`1 (mod 3)` indices `3k+1` carry
    the unbounded section `2k+2`. -/
theorem ePQ_unbounded : ∀ B, ∃ i, B < ePQ i := by
  intro B
  obtain ⟨k, hk⟩ := e_section_unbounded B
  refine ⟨3 * k + 1, ?_⟩
  have hval : ePQ (3 * k + 1) = 2 * k + 2 := by
    show (if (3 * k + 1) % 3 == 1 then 2 * ((3 * k + 1) / 3) + 2 else 1) = 2 * k + 2
    rw [if_pos (by rw [resP_mod]; decide), res3_div]
  rw [hval]; exact hk

end E213.Lib.Math.Analysis.Cauchy.PositiveFloorUnbounded
