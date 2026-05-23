import E213.Lib.Math.Padic.Foundation
import E213.Lib.Math.Padic.Arith
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

/-! ## Ultrametric inequalities

The non-Archimedean nature of the p-adic norm: addition preserves
or *increases* the valuation, and multiplication's valuation is
the sum of valuations.

In `valAtLeast` form:
- `valAtLeast x n ∧ valAtLeast y n → valAtLeast (x + y) n`
  (additive ultrametric, equal-level version).
- `valAtLeast x m ∧ valAtLeast y n → valAtLeast (x · y) (m + n)`
  (valuation additivity).

The general unequal-level form for addition follows by composing
with `valAtLeast_mono`.
-/

/-- **Additive ultrametric** (equal-level): if both `x` and `y`
    have valuation ≥ n, so does `x + y`. -/
theorem Zp.valAtLeast_add (p : Nat) (hp : 0 < p) (x y : ZpSeq p) (n : Nat)
    (hx : Zp.valAtLeast x n) (hy : Zp.valAtLeast y n) :
    Zp.valAtLeast (Zp.add p hp x y) n := by
  have h_xn : x.trunc n = 0 := (Zp.valAtLeast_iff_trunc hp x n).mp hx
  have h_yn : y.trunc n = 0 := (Zp.valAtLeast_iff_trunc hp y n).mp hy
  have h_addn : (Zp.add p hp x y).trunc n = 0 := by
    rw [Zp.add_trunc p hp x y n, h_xn, h_yn]
    show (0 + 0) % p^n = 0
    rw [Nat.zero_add]
    exact E213.Tactic.NatHelper.zero_mod _
  exact (Zp.valAtLeast_iff_trunc hp _ n).mpr h_addn

/-- **Additive ultrametric** (asymmetric): if `x` has valuation
    ≥ m, `y` has valuation ≥ n, and `m ≤ n`, then `x + y` has
    valuation ≥ m. -/
theorem Zp.valAtLeast_add_of_le (p : Nat) (hp : 0 < p) (x y : ZpSeq p)
    {m n : Nat} (hmn : m ≤ n)
    (hx : Zp.valAtLeast x m) (hy : Zp.valAtLeast y n) :
    Zp.valAtLeast (Zp.add p hp x y) m :=
  Zp.valAtLeast_add p hp x y m hx (Zp.valAtLeast_mono hmn hy)

/-- **Multiplicative absorbing**: if `x` has valuation ≥ m,
    then `x · y` has valuation ≥ m for any `y`.  This is the weak
    one-sided version of the multiplicative ultrametric. -/
theorem Zp.valAtLeast_mul_of_left (p : Nat) (hp : 0 < p) (x y : ZpSeq p) (m : Nat)
    (hx : Zp.valAtLeast x m) :
    Zp.valAtLeast (Zp.mul p hp x y) m := by
  have h_xm : x.trunc m = 0 := (Zp.valAtLeast_iff_trunc hp x m).mp hx
  have h_mulm : (Zp.mul p hp x y).trunc m = 0 := by
    rw [Zp.mul_trunc p hp x y m, h_xm, Nat.zero_mul]
    exact E213.Tactic.NatHelper.zero_mod _
  exact (Zp.valAtLeast_iff_trunc hp _ m).mpr h_mulm

/-- **Negation preserves valuation**: `val(-x) = val(x)`.
    In `valAtLeast` form: `valAtLeast x n → valAtLeast (-x) n`. -/
theorem Zp.valAtLeast_neg (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    ∀ n, Zp.valAtLeast x n → Zp.valAtLeast (Zp.neg p hp x) n
  | 0, _ => Zp.valAtLeast_zero _
  | n + 1, hx => by
    have hp' : 0 < p := Nat.lt_of_succ_lt hp
    have h_x_trunc : x.trunc (n + 1) = 0 :=
      (Zp.valAtLeast_iff_trunc hp' x (n + 1)).mp hx
    -- (x + (-x)).trunc (n+1) = 0 always; combined with x.trunc = 0
    -- forces (-x).trunc = 0.
    have h_self : (Zp.add p hp' x (Zp.neg p hp x)).trunc (n + 1) = 0 :=
      Zp.add_neg_self_trunc p hp x n
    have h_add : (x.trunc (n + 1) + (Zp.neg p hp x).trunc (n + 1)) % p^(n + 1) = 0 := by
      rw [← Zp.add_trunc p hp' x (Zp.neg p hp x) (n + 1)]
      exact h_self
    rw [h_x_trunc, Nat.zero_add] at h_add
    have h_neg_lt : (Zp.neg p hp x).trunc (n + 1) < p^(n + 1) :=
      ZpSeq.trunc_lt_p_pow hp' _ (n + 1)
    have h_neg_trunc : (Zp.neg p hp x).trunc (n + 1) = 0 := by
      rw [Nat.mod_eq_of_lt h_neg_lt] at h_add
      exact h_add
    exact (Zp.valAtLeast_iff_trunc hp' _ (n + 1)).mpr h_neg_trunc

/-- **Precise negation valuation**: `valEq x n → valEq (-x) n`. -/
theorem Zp.valEq_neg (p : Nat) (hp : 1 < p) (x : ZpSeq p) (n : Nat)
    (hx : Zp.valEq x n) :
    Zp.valEq (Zp.neg p hp x) n := by
  have hp' : 0 < p := Nat.lt_of_succ_lt hp
  have h_pn_pos : 0 < p^n := Nat.pos_pow_of_pos n hp'
  refine ⟨Zp.valAtLeast_neg p hp x n hx.1, ?_⟩
  intro h_neg_dig_zero
  have h_x_n : x.trunc n = 0 := (Zp.valAtLeast_iff_trunc hp' x n).mp hx.1
  have h_nx_n : (Zp.neg p hp x).trunc n = 0 :=
    (Zp.valAtLeast_iff_trunc hp' _ n).mp (Zp.valAtLeast_neg p hp x n hx.1)
  have h_nx_n1 : (Zp.neg p hp x).trunc (n + 1) = 0 := by
    show (Zp.neg p hp x).trunc n + ((Zp.neg p hp x).digits n).val * p^n = 0
    rw [h_nx_n, h_neg_dig_zero, Nat.zero_mul]
  have h_x_n1 : x.trunc (n + 1) = (x.digits n).val * p^n := by
    show x.trunc n + (x.digits n).val * p^n = (x.digits n).val * p^n
    rw [h_x_n, Nat.zero_add]
  have h_sum : (Zp.add p hp' x (Zp.neg p hp x)).trunc (n + 1) = 0 :=
    Zp.add_neg_self_trunc p hp x n
  rw [Zp.add_trunc p hp' x _ (n + 1), h_x_n1, h_nx_n1, Nat.add_zero] at h_sum
  have h_xn_lt : (x.digits n).val < p := (x.digits n).isLt
  have h_lt : (x.digits n).val * p^n < p^(n + 1) := by
    rw [show p^(n + 1) = p * p^n from by rw [Nat.pow_succ, Nat.mul_comm]]
    exact Nat.mul_lt_mul_of_pos_right h_xn_lt h_pn_pos
  rw [Nat.mod_eq_of_lt h_lt] at h_sum
  have h_xn_eq_zero : (x.digits n).val = 0 := by
    cases h_case : (x.digits n).val with
    | zero => rfl
    | succ k =>
      rw [h_case] at h_sum
      have hmul_pos : 0 < (k + 1) * p^n := Nat.mul_pos (Nat.succ_pos k) h_pn_pos
      exact absurd h_sum (Nat.pos_iff_ne_zero.mp hmul_pos)
  exact hx.2 h_xn_eq_zero

/-- **Multiplicative absorbing** (right): if `y` has valuation ≥ n,
    then `x · y` has valuation ≥ n for any `x`. -/
theorem Zp.valAtLeast_mul_of_right (p : Nat) (hp : 0 < p) (x y : ZpSeq p) (n : Nat)
    (hy : Zp.valAtLeast y n) :
    Zp.valAtLeast (Zp.mul p hp x y) n := by
  have h_yn : y.trunc n = 0 := (Zp.valAtLeast_iff_trunc hp y n).mp hy
  have h_muln : (Zp.mul p hp x y).trunc n = 0 := by
    rw [Zp.mul_trunc p hp x y n, h_yn, Nat.mul_zero]
    exact E213.Tactic.NatHelper.zero_mod _
  exact (Zp.valAtLeast_iff_trunc hp _ n).mpr h_muln

/-! ### Full multiplicative ultrametric

`val(x · y) = val(x) + val(y)`.  In `valAtLeast` form:
`valAtLeast x m ∧ valAtLeast y n → valAtLeast (x · y) (m + n)`.
-/

/-- PURE: `p^a · p^b = p^(a + b)` by induction. -/
private theorem pow_add_pure_norm (p : Nat) :
    ∀ m n, p^m * p^n = p^(m + n)
  | _, 0 => by rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | m, n + 1 => by
    rw [Nat.pow_succ, ← E213.Tactic.NatHelper.mul_assoc,
        pow_add_pure_norm p m n]
    show p^(m + n) * p = p^(m + (n + 1))
    rw [← Nat.add_assoc, ← Nat.pow_succ]

/-- PURE: extending trunc beyond m preserves `% p^m`. -/
private theorem trunc_extension_mod (p : Nat) (hp : 0 < p) (x : ZpSeq p) (m : Nat) :
    ∀ k, x.trunc (m + k) % p^m = x.trunc m % p^m
  | 0 => by rw [Nat.add_zero]
  | k + 1 => by
    have ih : x.trunc (m + k) % p^m = x.trunc m % p^m :=
      trunc_extension_mod p hp x m k
    show (x.trunc (m + k) + (x.digits (m + k)).val * p^(m + k)) % p^m
         = x.trunc m % p^m
    rw [E213.Meta.Nat.AddMod213.add_mod (Nat.pos_pow_of_pos _ hp), ih]
    -- ((x.trunc m % p^m) + (digits.val * p^(m+k)) % p^m) % p^m = x.trunc m % p^m
    -- Show (digits.val * p^(m+k)) % p^m = 0.
    have h_zero : ((x.digits (m + k)).val * p^(m + k)) % p^m = 0 := by
      rw [show p^(m + k) = p^m * p^k from (pow_add_pure_norm p m k).symm]
      rw [show (x.digits (m + k)).val * (p^m * p^k)
              = p^m * ((x.digits (m + k)).val * p^k) by
            rw [Nat.mul_comm (p^m) (p^k),
                ← E213.Tactic.NatHelper.mul_assoc (x.digits (m + k)).val (p^k) (p^m),
                Nat.mul_comm ((x.digits (m + k)).val * p^k) (p^m)]]
      exact E213.Tactic.NatHelper.mul_mod_right (p^m) _
    rw [h_zero, Nat.add_zero, E213.Tactic.NatHelper.mod_mod_pure]

/-- **Full multiplicative ultrametric**: `val(x · y) ≥ val(x) + val(y)`. -/
theorem Zp.valAtLeast_mul (p : Nat) (hp : 0 < p) (x y : ZpSeq p) (m n : Nat)
    (hx : Zp.valAtLeast x m) (hy : Zp.valAtLeast y n) :
    Zp.valAtLeast (Zp.mul p hp x y) (m + n) := by
  have h_xm : x.trunc m = 0 := (Zp.valAtLeast_iff_trunc hp x m).mp hx
  have h_yn : y.trunc n = 0 := (Zp.valAtLeast_iff_trunc hp y n).mp hy
  -- x.trunc (m + n) % p^m = 0
  have h_x_mod : x.trunc (m + n) % p^m = 0 := by
    rw [trunc_extension_mod p hp x m n, h_xm]
    exact E213.Tactic.NatHelper.zero_mod _
  -- y.trunc (m + n) % p^n = 0
  have h_y_mod : y.trunc (m + n) % p^n = 0 := by
    rw [Nat.add_comm m n, trunc_extension_mod p hp y n m, h_yn]
    exact E213.Tactic.NatHelper.zero_mod _
  -- (Zp.mul x y).trunc (m + n) = (x.trunc(m+n) * y.trunc(m+n)) % p^(m+n) = 0
  have h_muln : (Zp.mul p hp x y).trunc (m + n) = 0 := by
    rw [Zp.mul_trunc p hp x y (m + n)]
    -- (x.trunc(m+n) · y.trunc(m+n)) % p^(m+n) = 0
    -- Write x.trunc(m+n) = p^m · A, y.trunc(m+n) = p^n · B; product = p^(m+n) · (A·B).
    have hdmx := E213.Meta.Nat.AddMod213.div_add_mod (x.trunc (m + n)) (p^m)
    have hdmy := E213.Meta.Nat.AddMod213.div_add_mod (y.trunc (m + n)) (p^n)
    rw [h_x_mod, Nat.add_zero] at hdmx
    rw [h_y_mod, Nat.add_zero] at hdmy
    -- hdmx : p^m · (x.trunc(m+n) / p^m) = x.trunc(m+n)
    -- hdmy : p^n · (y.trunc(m+n) / p^n) = y.trunc(m+n)
    rw [← hdmx, ← hdmy]
    -- (p^m · A · (p^n · B)) % p^(m+n) = 0
    -- = (p^m · p^n · A · B) % p^(m+n) (by associativity/commutativity)
    -- = (p^(m+n) · (A · B)) % p^(m+n) = 0
    rw [E213.Tactic.NatHelper.mul_mul_mul_comm_213
          (p^m) (x.trunc (m + n) / p^m) (p^n) (y.trunc (m + n) / p^n),
        pow_add_pure_norm p m n]
    exact E213.Tactic.NatHelper.mul_mod_right (p^(m + n)) _
  exact (Zp.valAtLeast_iff_trunc hp _ (m + n)).mpr h_muln

/-- **Strong additive ultrametric**: when valuations differ, the
    sum has the lower valuation.  Specifically: if `valEq x m`,
    `valEq y n`, and `m < n`, then `valEq (x + y) m`. -/
theorem Zp.valEq_add_of_lt (p : Nat) (hp : 0 < p) (x y : ZpSeq p)
    {m n : Nat} (hmn : m < n)
    (hx : Zp.valEq x m) (hy : Zp.valEq y n) :
    Zp.valEq (Zp.add p hp x y) m := by
  refine ⟨?_, ?_⟩
  · -- valAtLeast (x + y) m: from valAtLeast x m + valAtLeast y m (since m ≤ n).
    exact Zp.valAtLeast_add p hp x y m hx.1
            (Zp.valAtLeast_mono (Nat.le_of_lt hmn) hy.1)
  · -- ((x + y).digits m).val ≠ 0: equals (x.digits m).val.
    have hx_trunc : x.trunc m = 0 := (Zp.valAtLeast_iff_trunc hp x m).mp hx.1
    have hy_trunc_m : y.trunc m = 0 :=
      (Zp.valAtLeast_iff_trunc hp y m).mp
        (Zp.valAtLeast_mono (Nat.le_of_lt hmn) hy.1)
    have hy_trunc_m1 : y.trunc (m + 1) = 0 :=
      (Zp.valAtLeast_iff_trunc hp y (m + 1)).mp
        (Zp.valAtLeast_mono hmn hy.1)
    have hxy_trunc_m : (Zp.add p hp x y).trunc m = 0 :=
      (Zp.valAtLeast_iff_trunc hp _ m).mp
        (Zp.valAtLeast_add p hp x y m hx.1
          (Zp.valAtLeast_mono (Nat.le_of_lt hmn) hy.1))
    -- (x + y).trunc (m + 1) via add_trunc.
    have h_addm1 : (Zp.add p hp x y).trunc (m + 1)
                  = (x.digits m).val * p^m := by
      rw [Zp.add_trunc p hp x y (m + 1)]
      show (x.trunc (m + 1) + y.trunc (m + 1)) % p^(m + 1)
           = (x.digits m).val * p^m
      rw [show x.trunc (m + 1) = (x.digits m).val * p^m by
            show x.trunc m + (x.digits m).val * p^m = _
            rw [hx_trunc, Nat.zero_add]]
      rw [hy_trunc_m1, Nat.add_zero]
      -- ((x.digits m).val * p^m) % p^(m + 1) = (x.digits m).val * p^m
      apply Nat.mod_eq_of_lt
      show (x.digits m).val * p^m < p^(m + 1)
      rw [show p^(m + 1) = p * p^m from by rw [Nat.pow_succ, Nat.mul_comm]]
      exact Nat.mul_lt_mul_of_pos_right (x.digits m).isLt
              (Nat.pos_pow_of_pos m hp)
    -- (x + y).trunc (m + 1) = (x + y).trunc m + ((x + y).digits m).val * p^m
    --                       = 0 + (digits.val) * p^m
    -- So (digits.val) * p^m = (x.digits m).val * p^m, hence digits.val = x.digits m val.
    have h_eq : ((Zp.add p hp x y).digits m).val * p^m
              = (x.digits m).val * p^m := by
      have h1 : (Zp.add p hp x y).trunc (m + 1)
                = (Zp.add p hp x y).trunc m
                  + ((Zp.add p hp x y).digits m).val * p^m := rfl
      rw [h_addm1, hxy_trunc_m, Nat.zero_add] at h1
      exact h1.symm
    have h_pm_pos : 0 < p^m := Nat.pos_pow_of_pos m hp
    have h_digits_eq : ((Zp.add p hp x y).digits m).val = (x.digits m).val :=
      Nat.eq_of_mul_eq_mul_right h_pm_pos h_eq
    rw [h_digits_eq]
    exact hx.2

end E213.Lib.Math.Padic
