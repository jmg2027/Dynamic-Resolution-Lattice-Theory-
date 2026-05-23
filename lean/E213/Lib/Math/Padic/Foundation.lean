import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
import E213.Meta.Tactic.NatHelper
/-!
# Real213-p-adic Foundation

Foundational types for the 213-native, ∅-axiom construction of the
p-adic integers `ℤ_p` and (later) p-adic numbers `ℚ_p`.  Built on
top of the `F_p` arithmetic / Bezout / FLT / `F_{p²}` infrastructure
in `Lib/Math/ModularArithmetic/` without introducing new axioms.

Chapter: `theory/math/padic_real213.md`.

## Contents

  · `ZpDigit p` — single p-adic digit (= `Fin p`)
  · `ZpSeq p`   — p-adic integer as infinite digit sequence
  · `ZpSeq.trunc` — truncation to ℤ/p^n
  · `ZpSeq.zero`, `ZpSeq.one`, `ZpSeq.neg_one` — canonical elements
  · `ZpSeq.eq_mod_pn` — equality up to truncation

Module path: `E213.Lib.Math.Padic.Foundation`
Namespace:   `E213.Lib.Math.Padic`

All declarations PURE.
-/

namespace E213.Lib.Math.Padic

/-- A single p-adic digit: an element of {0, 1, ..., p-1}.
    PURE (definitionally `Fin p`). -/
abbrev ZpDigit (p : Nat) : Type := Fin p

/-- A p-adic integer as an infinite digit sequence (least-significant
    digit first).  `digits k : ZpDigit p` is the k-th digit
    in the base-p expansion.

    Conceptually: `x = Σ_{k=0}^{∞} digits k · p^k` in ℤ_p.

    PURE structure (just a function Nat → Fin p). -/
structure ZpSeq (p : Nat) where
  digits : Nat → ZpDigit p

/-- Truncation: read the first `n` digits and assemble as
    `Σ_{k=0}^{n-1} digits k · p^k ∈ ℤ/p^n` (encoded as Nat).

    By induction on `n`:
      · `trunc x 0 = 0`
      · `trunc x (n+1) = trunc x n + digits n · p^n`

    PURE. -/
def ZpSeq.trunc {p : Nat} (x : ZpSeq p) : Nat → Nat
  | 0 => 0
  | n + 1 => x.trunc n + (x.digits n).val * p^n

/-! ## Canonical p-adic integers

`zero`, `one`, `neg_one` (which is `(p-1, p-1, p-1, ...)` in our
encoding, i.e., the "all-digits-(p-1)" sequence corresponding to
the formal sum `Σ (p-1)·p^k = -1` in ℤ_p).
-/

/-- The p-adic zero: all digits zero. -/
def ZpSeq.zero (p : Nat) (hp : 0 < p) : ZpSeq p where
  digits := fun _ => ⟨0, hp⟩

/-- The p-adic one: first digit 1, rest zero.  Requires `1 < p`. -/
def ZpSeq.one (p : Nat) (hp : 1 < p) : ZpSeq p where
  digits := fun k => if k = 0 then ⟨1, hp⟩ else ⟨0, Nat.lt_of_succ_lt hp⟩

/-- The p-adic `-1`: all digits `p-1`.  In ℤ_p, this represents
    `Σ (p-1)·p^k = (p-1)/(1-p) = -1` (formal sum).

    Requires `0 < p` so `p - 1 < p`. -/
def ZpSeq.neg_one (p : Nat) (hp : 0 < p) : ZpSeq p where
  digits := fun _ => ⟨p - 1, Nat.sub_lt hp Nat.one_pos⟩

/-! ## Equality up to truncation -/

/-- Two p-adic integers agree to `n` digits if their first `n`
    digits match.  Equivalent to `x.trunc n = y.trunc n`. -/
def ZpSeq.eq_mod_pn {p : Nat} (x y : ZpSeq p) (n : Nat) : Prop :=
  ∀ k, k < n → x.digits k = y.digits k

/-! ## Sanity / smoke -/

/-- Smoke: `zero 5 (by decide)` truncates to 0 at all levels. -/
theorem ZpSeq.trunc_zero (p : Nat) (hp : 0 < p) :
    ∀ n, (ZpSeq.zero p hp).trunc n = 0
  | 0 => rfl
  | n + 1 => by
    show (ZpSeq.zero p hp).trunc n + ((ZpSeq.zero p hp).digits n).val * p^n = 0
    rw [trunc_zero p hp n]
    show 0 + 0 * p^n = 0
    rw [Nat.zero_mul, Nat.add_zero]

/-- Smoke: `one 5 (by decide)` truncates to 1 at level ≥ 1. -/
theorem ZpSeq.trunc_one_at_one (p : Nat) (hp : 1 < p) :
    (ZpSeq.one p hp).trunc 1 = 1 := by
  show 0 + ((ZpSeq.one p hp).digits 0).val * p^0 = 1
  show 0 + 1 * p^0 = 1
  rw [Nat.pow_zero, Nat.mul_one, Nat.zero_add]

/-- `(neg_one).trunc n + 1 = p^n`.  Avoids Nat subtraction; encodes
    the fact that the all-`(p-1)` sequence truncated to `n` digits
    is `p^n - 1`. -/
theorem ZpSeq.trunc_neg_one_succ (p : Nat) (hp : 0 < p) :
    ∀ n, (ZpSeq.neg_one p hp).trunc n + 1 = p^n
  | 0 => by show (0 : Nat) + 1 = p^0; rw [Nat.pow_zero]
  | n + 1 => by
    have ih : (ZpSeq.neg_one p hp).trunc n + 1 = p^n :=
      ZpSeq.trunc_neg_one_succ p hp n
    show ((ZpSeq.neg_one p hp).trunc n
            + ((ZpSeq.neg_one p hp).digits n).val * p^n) + 1
        = p^(n+1)
    show ((ZpSeq.neg_one p hp).trunc n + (p - 1) * p^n) + 1 = p^(n+1)
    -- Rearrange `(a + b * pn) + 1 = (a + 1) + b * pn = p^n + (p-1)*p^n
    --         = (1 + (p-1)) * p^n = p * p^n = p^(n+1)`.
    rw [Nat.add_right_comm, ih]
    rw [Nat.add_comm (p^n) ((p - 1) * p^n)]
    rw [← Nat.succ_mul]
    show ((p - 1) + 1) * p^n = p^(n+1)
    rw [E213.Tactic.NatHelper.sub_add_cancel hp]
    rw [Nat.pow_succ, Nat.mul_comm]

/-- `(one).trunc (n+1) = 1` — `one`'s only nonzero digit (at position 0)
    contributes `1`; higher truncations don't add new bits. -/
theorem ZpSeq.trunc_one_succ (p : Nat) (hp : 1 < p) :
    ∀ n, (ZpSeq.one p hp).trunc (n + 1) = 1
  | 0 => ZpSeq.trunc_one_at_one p hp
  | n + 1 => by
    show (ZpSeq.one p hp).trunc (n + 1)
          + ((ZpSeq.one p hp).digits (n + 1)).val * p^(n + 1) = 1
    rw [ZpSeq.trunc_one_succ p hp n]
    show (1 : Nat)
          + ((ZpSeq.one p hp).digits (n + 1)).val * p^(n + 1) = 1
    show (1 : Nat)
          + (if (n + 1 : Nat) = 0 then (1 : Nat) else 0) * p^(n + 1) = 1
    rw [if_neg (fun h => Nat.noConfusion h),
        Nat.zero_mul, Nat.add_zero]

/-! ## Truncation bound

Each truncation `x.trunc n` lies in `[0, p^n)` — justifying the
"ℤ/p^n" interpretation.  The bound is the structural reason
`ZpSeq` is a faithful pre-image of the inverse limit
`lim_n ℤ/p^n = ℤ_p`.
-/

/-- `x.trunc n < p^n` for any digit sequence and any `0 < p`.

    Inductive on `n`.  Base: `trunc 0 = 0 < 1 = p^0`.
    Step: by the IH `trunc x n < p^n` and `(x.digits n).val + 1 ≤ p`,
    we get `trunc x n + (x.digits n).val · p^n < ((digit)+1) · p^n
    ≤ p · p^n = p^(n+1)`. -/
theorem ZpSeq.trunc_lt_p_pow {p : Nat} (hp : 0 < p) (x : ZpSeq p) :
    ∀ n, x.trunc n < p^n
  | 0 => Nat.one_pos
  | n + 1 => by
    have ih : x.trunc n < p^n := ZpSeq.trunc_lt_p_pow hp x n
    have hd : (x.digits n).val + 1 ≤ p :=
      Nat.succ_le_of_lt (x.digits n).isLt
    show x.trunc n + (x.digits n).val * p^n < p^(n+1)
    calc x.trunc n + (x.digits n).val * p^n
        < p^n + (x.digits n).val * p^n :=
              Nat.add_lt_add_right ih _
      _ = ((x.digits n).val + 1) * p^n := by
              rw [Nat.succ_mul]; exact Nat.add_comm _ _
      _ ≤ p * p^n := Nat.mul_le_mul_right _ hd
      _ = p^(n+1) := by rw [Nat.pow_succ]; exact Nat.mul_comm _ _

/-! ## Equality up to truncation ↔ truncation equality

The two natural notions of "agreement to `n` digits" coincide:
digit-by-digit (`eq_mod_pn`) and truncation-value
(`trunc x n = trunc y n`).  Forward is structural; backward uses
the `trunc < p^n` bound to extract digits via mod-cancellation.
-/

/-- Forward: if digits agree for all `k < n`, the truncations agree.
    Pure structural induction on `n`. -/
theorem ZpSeq.trunc_eq_of_eq_mod_pn {p : Nat} {x y : ZpSeq p} :
    ∀ n, ZpSeq.eq_mod_pn x y n → x.trunc n = y.trunc n
  | 0, _ => rfl
  | n + 1, h => by
    have hbelow : ZpSeq.eq_mod_pn x y n :=
      fun k hk => h k (Nat.lt_succ_of_lt hk)
    have ih : x.trunc n = y.trunc n :=
      ZpSeq.trunc_eq_of_eq_mod_pn n hbelow
    have hkn : x.digits n = y.digits n := h n (Nat.lt_succ_self n)
    show x.trunc n + (x.digits n).val * p^n
          = y.trunc n + (y.digits n).val * p^n
    rw [ih, hkn]

/-- Backward: if `x.trunc (n+1) = y.trunc (n+1)`, then `x.digits n =
    y.digits n` and `x.trunc n = y.trunc n`.  This is the
    "extract one digit" lemma: take both sides mod `p^n` and use
    `trunc_lt_p_pow` + `add_mul_mod_self_pure`. -/
theorem ZpSeq.trunc_succ_inj {p : Nat} (hp : 0 < p) {x y : ZpSeq p}
    (n : Nat) (h : x.trunc (n+1) = y.trunc (n+1)) :
    x.trunc n = y.trunc n ∧ x.digits n = y.digits n := by
  have hxlt : x.trunc n < p^n := ZpSeq.trunc_lt_p_pow hp x n
  have hylt : y.trunc n < p^n := ZpSeq.trunc_lt_p_pow hp y n
  have hp_pow : 0 < p^n := Nat.pos_pow_of_pos n hp
  have hxmod : x.trunc (n+1) % p^n = x.trunc n := by
    show (x.trunc n + (x.digits n).val * p^n) % p^n = x.trunc n
    rw [E213.Tactic.NatHelper.add_mul_mod_self_pure]
    exact Nat.mod_eq_of_lt hxlt
  have hymod : y.trunc (n+1) % p^n = y.trunc n := by
    show (y.trunc n + (y.digits n).val * p^n) % p^n = y.trunc n
    rw [E213.Tactic.NatHelper.add_mul_mod_self_pure]
    exact Nat.mod_eq_of_lt hylt
  have htrunc_eq : x.trunc n = y.trunc n :=
    hxmod.symm.trans ((congrArg (· % p^n) h).trans hymod)
  have hmul_eq : (x.digits n).val * p^n = (y.digits n).val * p^n := by
    have h' : x.trunc n + (x.digits n).val * p^n
              = y.trunc n + (y.digits n).val * p^n := h
    rw [htrunc_eq] at h'
    exact E213.Tactic.NatHelper.add_left_cancel h'
  have hcomm1 : (x.digits n).val * p^n = p^n * (x.digits n).val :=
    Nat.mul_comm _ _
  have hcomm2 : (y.digits n).val * p^n = p^n * (y.digits n).val :=
    Nat.mul_comm _ _
  have hmul_eq' : p^n * (x.digits n).val = p^n * (y.digits n).val := by
    rw [← hcomm1, ← hcomm2]; exact hmul_eq
  have hdig_val : (x.digits n).val = (y.digits n).val :=
    E213.Tactic.NatHelper.mul_left_cancel_pos hp_pow hmul_eq'
  exact ⟨htrunc_eq, Fin.eq_of_val_eq hdig_val⟩

/-- Backward (full): if truncations agree at level `n`, then digits
    agree for all `k < n`.  By induction iterating `trunc_succ_inj`. -/
theorem ZpSeq.eq_mod_pn_of_trunc_eq {p : Nat} (hp : 0 < p) {x y : ZpSeq p} :
    ∀ n, x.trunc n = y.trunc n → ZpSeq.eq_mod_pn x y n
  | 0, _ => fun k hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h => by
    have hpair := ZpSeq.trunc_succ_inj hp n h
    have htn : x.trunc n = y.trunc n := hpair.1
    have hdn : x.digits n = y.digits n := hpair.2
    have ih : ZpSeq.eq_mod_pn x y n :=
      ZpSeq.eq_mod_pn_of_trunc_eq hp n htn
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ hk
    match Nat.lt_or_eq_of_le hkn with
    | .inl hlt => exact ih k hlt
    | .inr heq => exact heq ▸ hdn

/-- The two notions of "agreement to `n` digits" coincide. -/
theorem ZpSeq.eq_mod_pn_iff_trunc {p : Nat} (hp : 0 < p) {x y : ZpSeq p}
    (n : Nat) : ZpSeq.eq_mod_pn x y n ↔ x.trunc n = y.trunc n :=
  ⟨ZpSeq.trunc_eq_of_eq_mod_pn n, ZpSeq.eq_mod_pn_of_trunc_eq hp n⟩

/-! ## Embedding ℕ ↪ ZpSeq via base-p expansion

Every Nat `n` has a canonical p-adic representation: the k-th
digit is `(n / p^k) % p ∈ {0, …, p-1}`.  For `k > log_p n` all
digits are zero, so the sequence terminates (in value).

This gives a faithful map ℕ → ZpSeq p ≅ ℤ_p; injectivity reduces
to `Nat`'s base-p expansion uniqueness.
-/

/-- Embedding `Nat → ZpSeq p`: the k-th digit of `n` in base `p`. -/
def ZpSeq.digits_of_nat (p : Nat) (hp : 0 < p) (n : Nat) : ZpSeq p where
  digits := fun k => ⟨(n / p^k) % p, Nat.mod_lt _ hp⟩

/-- Digit unfolding: by `rfl`, definitionally. -/
theorem ZpSeq.digits_of_nat_val (p : Nat) (hp : 0 < p) (n k : Nat) :
    ((ZpSeq.digits_of_nat p hp n).digits k).val = (n / p^k) % p := rfl

/-- 0 ↦ all-zero (per-digit, PURE).  Stated digit-by-digit to
    avoid the `funext`-on-structures that sequence-level equality
    would require. -/
theorem ZpSeq.digits_of_nat_zero (p : Nat) (hp : 0 < p) (k : Nat) :
    ((ZpSeq.digits_of_nat p hp 0).digits k).val = 0 := by
  show (0 / p^k) % p = 0
  rw [Nat.zero_div]
  exact E213.Tactic.NatHelper.zero_mod p

/-! ## Truncation correctness for the `digits_of_nat` embedding

Truncating the base-p expansion of `m` to `n` digits recovers
`m % p^n`.  This makes `digits_of_nat p hp m` the right p-adic
representation of the natural number `m`: at every truncation
level, the value matches the standard reduction.
-/

/-- `(m / p^n) % p · p^n + m % p^n = m % p^(n+1)` — the recursive
    formula for base-p truncation.  PURE. -/
private theorem mod_pow_succ_pure (p : Nat) (hp : 0 < p) (m n : Nat) :
    (m / p^n) % p * p^n + m % p^n = m % p^(n + 1) := by
  have hpn1 : 0 < p^(n + 1) := Nat.pos_pow_of_pos _ hp
  -- m = (m/p^n/p) · p^(n+1) + ((m/p^n) % p · p^n + m % p^n)
  have hsubst : m = (m / p^n / p) * p^(n + 1)
                  + ((m / p^n) % p * p^n + m % p^n) := by
    have hA := E213.Meta.Nat.AddMod213.div_add_mod m (p^n)
    have hB := E213.Meta.Nat.AddMod213.div_add_mod (m / p^n) p
    -- Rewrite m using hA and hB.
    calc m = p^n * (m / p^n) + m % p^n := hA.symm
      _   = p^n * (p * (m / p^n / p) + (m / p^n) % p) + m % p^n := by rw [hB]
      _   = p^n * (p * (m / p^n / p)) + p^n * ((m / p^n) % p) + m % p^n := by
            rw [Nat.mul_add]
      _   = (m / p^n / p) * (p^n * p) + (m / p^n) % p * p^n + m % p^n := by
            rw [show p^n * (p * (m / p^n / p))
                      = (m / p^n / p) * (p^n * p) from by
                  rw [← E213.Tactic.NatHelper.mul_assoc]
                  exact Nat.mul_comm (p^n * p) (m / p^n / p)]
            rw [show p^n * ((m / p^n) % p)
                      = (m / p^n) % p * p^n from
                  Nat.mul_comm (p^n) ((m / p^n) % p)]
      _   = (m / p^n / p) * p^(n + 1) + (m / p^n) % p * p^n + m % p^n := by
            rw [show p^n * p = p^(n + 1) from (Nat.pow_succ p n).symm]
      _   = (m / p^n / p) * p^(n + 1)
              + ((m / p^n) % p * p^n + m % p^n) := by
            rw [Nat.add_assoc]
  -- Bound: A < p^(n+1).
  have hbound : (m / p^n) % p * p^n + m % p^n < p^(n + 1) := by
    have h1 : (m / p^n) % p < p := Nat.mod_lt _ hp
    have h2 : m % p^n < p^n := Nat.mod_lt _ (Nat.pos_pow_of_pos _ hp)
    have h3 : (m / p^n) % p + 1 ≤ p := Nat.succ_le_of_lt h1
    calc (m / p^n) % p * p^n + m % p^n
        < (m / p^n) % p * p^n + p^n :=
              Nat.add_lt_add_left h2 _
      _ = ((m / p^n) % p + 1) * p^n := by
              rw [E213.Tactic.NatHelper.add_mul, Nat.one_mul]
      _ ≤ p * p^n :=
              Nat.mul_le_mul_right (p^n) h3
      _ = p^(n + 1) := by
              rw [Nat.mul_comm]; exact (Nat.pow_succ p n).symm
  -- Conclude via m = Q · p^(n+1) + A + add_mul_mod_self_pure + mod_eq_of_lt.
  have hm_eq : m % p^(n + 1)
                = ((m / p^n / p) * p^(n + 1)
                    + ((m / p^n) % p * p^n + m % p^n)) % p^(n + 1) :=
    congrArg (· % p^(n + 1)) hsubst
  rw [hm_eq, Nat.add_comm ((m / p^n / p) * p^(n + 1))
              ((m / p^n) % p * p^n + m % p^n),
      E213.Tactic.NatHelper.add_mul_mod_self_pure,
      Nat.mod_eq_of_lt hbound]

/-- `(digits_of_nat p hp m).trunc n = m % p^n` — the canonical
    embedding `ℕ ↪ ZpSeq p` is the standard base-p reduction at
    every truncation level. -/
theorem ZpSeq.digits_of_nat_trunc (p : Nat) (hp : 0 < p) (m : Nat) :
    ∀ n, (ZpSeq.digits_of_nat p hp m).trunc n = m % p^n
  | 0 => by
    show (0 : Nat) = m % p^0
    rw [Nat.pow_zero, Nat.mod_one]
  | n + 1 => by
    have ih := ZpSeq.digits_of_nat_trunc p hp m n
    show (ZpSeq.digits_of_nat p hp m).trunc n
          + ((ZpSeq.digits_of_nat p hp m).digits n).val * p^n
        = m % p^(n + 1)
    rw [ih]
    show m % p^n + (m / p^n) % p * p^n = m % p^(n + 1)
    rw [Nat.add_comm]
    exact mod_pow_succ_pure p hp m n

/-! ## Per-prime smoke tests

Verify canonical elements + the Nat embedding at concrete primes.
All reduce by `rfl` (closed numeric expressions, propext-free).
-/

theorem ZpSeq.smoke_zero_2 : (ZpSeq.zero 2 (by decide)).trunc 3 = 0 :=
  ZpSeq.trunc_zero 2 (by decide) 3
theorem ZpSeq.smoke_zero_3 : (ZpSeq.zero 3 (by decide)).trunc 3 = 0 :=
  ZpSeq.trunc_zero 3 (by decide) 3
theorem ZpSeq.smoke_zero_5 : (ZpSeq.zero 5 (by decide)).trunc 3 = 0 :=
  ZpSeq.trunc_zero 5 (by decide) 3
theorem ZpSeq.smoke_zero_7 : (ZpSeq.zero 7 (by decide)).trunc 3 = 0 :=
  ZpSeq.trunc_zero 7 (by decide) 3

theorem ZpSeq.smoke_one_2 : (ZpSeq.one 2 (by decide)).trunc 1 = 1 := rfl
theorem ZpSeq.smoke_one_3 : (ZpSeq.one 3 (by decide)).trunc 1 = 1 := rfl
theorem ZpSeq.smoke_one_5 : (ZpSeq.one 5 (by decide)).trunc 1 = 1 := rfl
theorem ZpSeq.smoke_one_7 : (ZpSeq.one 7 (by decide)).trunc 1 = 1 := rfl

-- neg_one trunc 2 = (p-1) + (p-1)·p = p² - 1.
theorem ZpSeq.smoke_neg_one_2_trunc_2 :
    (ZpSeq.neg_one 2 (by decide)).trunc 2 = 3 := rfl
theorem ZpSeq.smoke_neg_one_3_trunc_2 :
    (ZpSeq.neg_one 3 (by decide)).trunc 2 = 8 := rfl
theorem ZpSeq.smoke_neg_one_5_trunc_2 :
    (ZpSeq.neg_one 5 (by decide)).trunc 2 = 24 := rfl
theorem ZpSeq.smoke_neg_one_7_trunc_2 :
    (ZpSeq.neg_one 7 (by decide)).trunc 2 = 48 := rfl

-- digits_of_nat smokes: 7 in base 2 is 111₂; digit-by-digit.
theorem ZpSeq.smoke_digits_2_7_d0 :
    ((ZpSeq.digits_of_nat 2 (by decide) 7).digits 0).val = 1 := rfl
theorem ZpSeq.smoke_digits_2_7_d1 :
    ((ZpSeq.digits_of_nat 2 (by decide) 7).digits 1).val = 1 := rfl
theorem ZpSeq.smoke_digits_2_7_d2 :
    ((ZpSeq.digits_of_nat 2 (by decide) 7).digits 2).val = 1 := rfl
-- 24 in base 5 is 44₅: (4, 4, 0, ...).
theorem ZpSeq.smoke_digits_5_24_d0 :
    ((ZpSeq.digits_of_nat 5 (by decide) 24).digits 0).val = 4 := rfl
theorem ZpSeq.smoke_digits_5_24_d1 :
    ((ZpSeq.digits_of_nat 5 (by decide) 24).digits 1).val = 4 := rfl

/-! ## Per-prime smoke tests -/

/-- Smoke: at p = 2, `zero.trunc 5 = 0`. -/
theorem ZpSeq.smoke_zero_p2 : (ZpSeq.zero 2 Nat.zero_lt_two).trunc 5 = 0 :=
  ZpSeq.trunc_zero 2 Nat.zero_lt_two 5

/-- Smoke: at p = 3, `zero.trunc 4 = 0`. -/
theorem ZpSeq.smoke_zero_p3 : (ZpSeq.zero 3 (by decide)).trunc 4 = 0 :=
  ZpSeq.trunc_zero 3 (by decide) 4

/-- Smoke: at p = 5, `one.trunc 1 = 1`. -/
theorem ZpSeq.smoke_one_p5 : (ZpSeq.one 5 (by decide)).trunc 1 = 1 :=
  ZpSeq.trunc_one_at_one 5 (by decide)

/-- Smoke: at p = 7, `one.trunc 1 = 1`. -/
theorem ZpSeq.smoke_one_p7 : (ZpSeq.one 7 (by decide)).trunc 1 = 1 :=
  ZpSeq.trunc_one_at_one 7 (by decide)

/-- Smoke: `trunc_lt_p_pow` at p = 5, n = 3.  For any p-adic
    sequence, `x.trunc 3 < 125`. -/
theorem ZpSeq.smoke_trunc_lt_p3_p5 (x : ZpSeq 5) :
    x.trunc 3 < 125 :=
  ZpSeq.trunc_lt_p_pow (by decide) x 3

/-! ## Phase 2 preview (next file: Arith.lean)

Next-phase content:
  · `Zp.add p x y : ZpSeq p` with carry-propagation FSM
  · `Zp.add_trunc` : truncation respects addition mod p^n
  · `Zp.mul p x y : ZpSeq p` digit-by-digit multiplication
  · `Zp.neg p x : ZpSeq p`

The carry propagation will reuse:
  · `E213.Meta.Nat.AddMod213.add_mod_gen` for `(a + b) % p`

Multiplication will leverage:
  · `E213.Meta.Nat.MulMod213.mul_mod_pure` for `(a * b) % p`

Inverse (Hensel phase) will reuse:
  · `E213.Lib.Math.ModArith.ModBezoutInvariant.modInverseFromBezout`

All upstream ingredients are ∅-axiom PURE.
-/

end E213.Lib.Math.Padic
