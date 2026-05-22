import E213.Lib.Math.Padic.Foundation
import E213.Meta.Tactic.NatHelper
/-!
# Real213-p-adic Valuation

The p-adic valuation `v_p(x)` of a nonzero `x : ZpSeq p` is the
index of the first nonzero digit:

  v_p(x) = min { k : (x.digits k).val ≠ 0 }

For `x = 0` (all digits zero), `v_p(0) = ∞`.  We avoid `WithTop`
(which brings axiom cost via its typeclass machinery) and instead
use a predicate-based approach:

  · `valAtLeast x n` — "all digits below `n` are zero"
    (equivalently `x.trunc n = 0`).

The valuation itself is then characterized by `valAtLeast`
membership, without ever forming an actual `WithTop` value.
-/

namespace E213.Lib.Math.Padic

/-- `valAtLeast x n` — every digit `< n` is zero.  Equivalently
    (via `Foundation.trunc_eq_of_eq_mod_pn`-style reasoning),
    `x.trunc n = 0`. -/
def Zp.valAtLeast {p : Nat} (x : ZpSeq p) (n : Nat) : Prop :=
  ∀ k, k < n → (x.digits k).val = 0

/-- `valAtLeast` at 0 is vacuously true. -/
theorem Zp.valAtLeast_zero {p : Nat} (x : ZpSeq p) :
    Zp.valAtLeast x 0 := fun _ hk => absurd hk (Nat.not_lt_zero _)

/-- `valAtLeast` is downward closed in `n`. -/
theorem Zp.valAtLeast_mono {p : Nat} {x : ZpSeq p} {m n : Nat}
    (h : m ≤ n) (hv : Zp.valAtLeast x n) : Zp.valAtLeast x m :=
  fun k hk => hv k (Nat.lt_of_lt_of_le hk h)

/-- `valAtLeast` equivalent to truncation being zero. -/
theorem Zp.valAtLeast_iff_trunc {p : Nat} (hp : 0 < p) (x : ZpSeq p)
    (n : Nat) : Zp.valAtLeast x n ↔ x.trunc n = 0 := by
  constructor
  · intro hv
    have hpair : Zp.valAtLeast x n
                  ↔ ZpSeq.eq_mod_pn x (ZpSeq.zero p hp) n := by
      apply Iff.intro
      · intro h k hk
        apply Fin.eq_of_val_eq
        show (x.digits k).val = (0 : Nat)
        exact h k hk
      · intro h k hk
        have := h k hk
        exact congrArg Fin.val this
    have hem := hpair.mp hv
    have htrunc := ZpSeq.trunc_eq_of_eq_mod_pn n hem
    rw [htrunc, ZpSeq.trunc_zero]
  · intro htr
    intro k hk
    have hem : ZpSeq.eq_mod_pn x (ZpSeq.zero p hp) n := by
      apply ZpSeq.eq_mod_pn_of_trunc_eq hp n
      rw [ZpSeq.trunc_zero]; exact htr
    have := hem k hk
    exact congrArg Fin.val this

/-! ## Smokes -/

theorem Zp.valAtLeast_zero_5_any (n : Nat) :
    Zp.valAtLeast (ZpSeq.zero 5 (by decide)) n :=
  fun _ _ => rfl

theorem Zp.not_valAtLeast_one_5_at_1 :
    ¬ Zp.valAtLeast (ZpSeq.one 5 (by decide)) 1 := by
  intro hv
  have h0 := hv 0 Nat.one_pos
  -- ((ZpSeq.one 5 _).digits 0).val = 1, but valAtLeast claims = 0
  exact absurd h0 (by decide)

/-! ## Valuation-exact predicate

`valEq x n` — the p-adic valuation of `x` is exactly `n`:
all digits below `n` are zero AND the digit at `n` is nonzero.
This is the constructive characterization of `v_p(x) = n`
without forming an actual numeric valuation.
-/

/-- `valEq x n` — `v_p(x) = n`.  -/
def Zp.valEq {p : Nat} (x : ZpSeq p) (n : Nat) : Prop :=
  Zp.valAtLeast x n ∧ (x.digits n).val ≠ 0

/-- If `valEq x n` holds, then `valAtLeast x n` also holds. -/
theorem Zp.valAtLeast_of_valEq {p : Nat} {x : ZpSeq p} {n : Nat}
    (h : Zp.valEq x n) : Zp.valAtLeast x n := h.1

/-- `valEq x n` and `valEq x m` are incompatible for `n ≠ m`.
    (Uniqueness of the valuation.) -/
theorem Zp.valEq_unique {p : Nat} {x : ZpSeq p} {n m : Nat}
    (hn : Zp.valEq x n) (hm : Zp.valEq x m) : n = m := by
  -- WLOG n ≤ m.  If n < m, then valAtLeast x m ⟹ (x.digits n).val = 0,
  -- contradicting hn.2.
  match Nat.lt_or_ge n m with
  | .inl hlt =>
    have hnz := hm.1 n hlt
    exact absurd hnz hn.2
  | .inr hge =>
    match Nat.lt_or_eq_of_le hge with
    | .inl hgt =>
      have hnz := hn.1 m hgt
      exact absurd hnz hm.2
    | .inr heq => exact heq.symm

/-! ## Valuation of canonical elements -/

/-- `valAtLeast (zero) n` for any n. -/
theorem Zp.valAtLeast_zero_seq (p : Nat) (hp : 0 < p) (n : Nat) :
    Zp.valAtLeast (ZpSeq.zero p hp) n :=
  fun _ _ => rfl

/-- `valEq (one) 0` — the multiplicative identity has valuation 0. -/
theorem Zp.valEq_one (p : Nat) (hp : 1 < p) :
    Zp.valEq (ZpSeq.one p hp) 0 := by
  refine ⟨?_, ?_⟩
  · exact fun _ hk => absurd hk (Nat.not_lt_zero _)
  · show ((ZpSeq.one p hp).digits 0).val ≠ 0
    show (if (0 : Nat) = 0 then (1 : Nat) else 0) ≠ 0
    rw [if_pos rfl]
    exact fun h => Nat.noConfusion h

/-- `valEq (neg_one) 0` — `-1` also has valuation 0 (its digit-0
    is `p - 1 ≠ 0` for `1 < p`). -/
theorem Zp.valEq_neg_one (p : Nat) (hp : 1 < p) :
    Zp.valEq (ZpSeq.neg_one p (Nat.lt_of_succ_lt hp)) 0 := by
  refine ⟨?_, ?_⟩
  · exact fun _ hk => absurd hk (Nat.not_lt_zero _)
  · show ((ZpSeq.neg_one p (Nat.lt_of_succ_lt hp)).digits 0).val ≠ 0
    show (p - 1 : Nat) ≠ 0
    -- p - 1 ≠ 0 since p > 1 means p ≥ 2 means p - 1 ≥ 1 ≠ 0.
    intro hp1
    have h_p_le_1 : p ≤ 1 := by
      have := E213.Tactic.NatHelper.sub_add_cancel
                (Nat.le_of_lt hp)
      rw [hp1, Nat.zero_add] at this
      exact this.symm ▸ Nat.le_refl 1
    exact absurd h_p_le_1 (Nat.not_le_of_gt hp)

end E213.Lib.Math.Padic
