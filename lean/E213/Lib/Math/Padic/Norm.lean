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

end E213.Lib.Math.Padic
