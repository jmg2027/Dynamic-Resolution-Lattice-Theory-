import E213.Lib.Math.NumberTheory.ModArith.Frobenius
import E213.Meta.Nat.Gcd213
import E213.Meta.Tactic.NatHelper

/-!
# Frobenius number `ab − a − b` is NOT representable (∅-axiom)

Companion to `…ModArith.Frobenius.frobenius_representable` (the
"every `n ≥ (a−1)(b−1)` is representable" direction, already PURE).

This file closes the harder direction: for coprime `a, b ≥ 2`, the
Frobenius number `g = a·b − a − b` admits no `x, y : ℕ` with
`g = a·x + b·y`.

## Proof

Suppose `a·b − a − b = a·x + b·y`.  Since `2 ≤ a, 2 ≤ b` give
`a + b ≤ a·b`, add `a + b` to both sides:

    a·b = a·x + b·y + a + b = a·(x+1) + b·(y+1).

Reduce mod `a`: `b·(y+1) ≡ 0 (mod a)`, so `a ∣ b·(y+1)`.  Coprimality
(`coprime_dvd_of_dvd_mul`) gives `a ∣ (y+1)`.  As `y+1 > 0`, this
forces `a ≤ y+1`, hence `a·b ≤ a·(x+1)`-free bound: `b·(y+1) ≥ a·b`.
Symmetrically `a·(x+1) ≥ a·b`.  Their sum `a·b ≥ 2·a·b`, with
`a·b > 0`, is a contradiction.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.FrobeniusNonRepresentable

open E213.Tactic.NatHelper (gcd213 add_mul)

/-- `a ∣ m → 0 < m → a ≤ m` (PURE; Lean-core `Nat.le_of_dvd` brings propext). -/
theorem le_of_dvd_pure {a m : Nat} (hm : 0 < m) (h : a ∣ m) : a ≤ m := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero =>
    rw [Nat.mul_zero] at hk
    -- hk : m = 0, hm : 0 < m
    rw [hk] at hm; exact absurd hm (Nat.lt_irrefl 0)
  | succ k' =>
    rw [hk]
    calc a = a * 1 := (Nat.mul_one a).symm
      _ ≤ a * (k' + 1) := Nat.mul_le_mul_left a (Nat.succ_le_succ (Nat.zero_le k'))

/-- `2 ≤ a → 2 ≤ b → a + b ≤ a * b`.  PURE. -/
theorem add_le_mul_two {a b : Nat} (ha : 2 ≤ a) (hb : 2 ≤ b) : a + b ≤ a * b := by
  -- a*b = a*((b-2)+2) = a*(b-2) + 2*a ≥ 2*a = a+a ≥ a+b ... not quite; do directly.
  -- Use: a*b ≥ a*2 = a+a and a*b ≥ 2*b = b+b ; combine via halves is awkward.
  -- Cleaner: a*b - (a+b) = (a-1)(b-1) - 1 ≥ 0 since (a-1)(b-1) ≥ 1.
  have ha1 : 1 ≤ a - 1 := Nat.le_sub_one_of_lt ha
  have hb1 : 1 ≤ b - 1 := Nat.le_sub_one_of_lt hb
  have hprod : 1 ≤ (a - 1) * (b - 1) := by
    calc 1 = 1 * 1 := by rfl
      _ ≤ (a - 1) * (b - 1) := Nat.mul_le_mul ha1 hb1
  -- (a-1)*(b-1) = a*b - a - b + 1, so a + b ≤ a*b iff (a-1)(b-1) ≥ 1.
  -- Establish a*b = (a-1)*(b-1) + a + b - 1, then bound.
  have ha_ne : a ≠ 0 := by
    intro h; rw [h] at ha; exact absurd ha (by decide)
  have hb_ne : b ≠ 0 := by
    intro h; rw [h] at hb; exact absurd hb (by decide)
  have ha1' : (a - 1) + 1 = a := E213.Tactic.NatHelper.sub_one_add_one ha_ne
  have hb1' : (b - 1) + 1 = b := E213.Tactic.NatHelper.sub_one_add_one hb_ne
  -- a*b = ((a-1)+1)*((b-1)+1) = (a-1)(b-1) + (a-1) + (b-1) + 1
  have expand : a * b = (a - 1) * (b - 1) + ((a - 1) + (b - 1)) + 1 := by
    calc a * b = ((a - 1) + 1) * ((b - 1) + 1) := by rw [ha1', hb1']
      _ = (a - 1) * ((b - 1) + 1) + 1 * ((b - 1) + 1) := add_mul (a - 1) 1 ((b - 1) + 1)
      _ = ((a - 1) * (b - 1) + (a - 1) * 1) + (1 * (b - 1) + 1 * 1) := by
            rw [Nat.mul_add (a - 1) (b - 1) 1, Nat.mul_add 1 (b - 1) 1]
      _ = ((a - 1) * (b - 1) + (a - 1)) + ((b - 1) + 1) := by
            rw [Nat.mul_one, Nat.one_mul, Nat.one_mul]
      _ = (a - 1) * (b - 1) + ((a - 1) + (b - 1)) + 1 := by
            rw [Nat.add_assoc ((a - 1) * (b - 1)) (a - 1) ((b - 1) + 1),
                ← Nat.add_assoc (a - 1) (b - 1) 1,
                ← Nat.add_assoc ((a - 1) * (b - 1)) ((a - 1) + (b - 1)) 1]
  -- a + b = (a-1) + (b-1) + 2  (from ha1', hb1')
  have hab_sum : a + b = ((a - 1) + (b - 1)) + 2 := by
    calc a + b = ((a - 1) + 1) + ((b - 1) + 1) := by rw [ha1', hb1']
      _ = ((a - 1) + (b - 1)) + 2 := by
            rw [Nat.add_assoc (a - 1) 1 ((b - 1) + 1),
                ← Nat.add_assoc 1 (b - 1) 1, Nat.add_comm 1 (b - 1),
                Nat.add_assoc (b - 1) 1 1, ← Nat.add_assoc (a - 1) (b - 1) (1 + 1)]
  -- Goal: a + b ≤ a * b.  Rewrite both.
  rw [expand, hab_sum]
  -- ((a-1)+(b-1)) + 2 ≤ ((a-1)(b-1) + ((a-1)+(b-1))) + 1
  -- i.e. 2 ≤ (a-1)(b-1) + 1, i.e. 1 ≤ (a-1)(b-1).  via add_le_add_left commutation.
  have step : ((a - 1) + (b - 1)) + 2 ≤ ((a - 1) + (b - 1)) + ((a - 1) * (b - 1) + 1) := by
    apply Nat.add_le_add_left
    -- 2 ≤ (a-1)*(b-1) + 1
    calc 2 = 1 + 1 := by rfl
      _ ≤ (a - 1) * (b - 1) + 1 := Nat.add_le_add_right hprod 1
  -- RHS reassoc to match expand form
  have reassoc : ((a - 1) + (b - 1)) + ((a - 1) * (b - 1) + 1)
                  = ((a - 1) * (b - 1) + ((a - 1) + (b - 1))) + 1 := by
    rw [Nat.add_comm ((a - 1) * (b - 1)) ((a - 1) + (b - 1)),
        Nat.add_assoc ((a - 1) + (b - 1)) ((a - 1) * (b - 1)) 1]
  rw [reassoc] at step
  exact step

/-- ★★ **Frobenius number non-representability.**
    For coprime `a, b ≥ 2`, `a·b − a − b` is not of the form `a·x + b·y`. -/
theorem frobenius_number_not_representable (a b : Nat) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcop : gcd213 a b = 1) : ¬ ∃ x y : Nat, a * b - a - b = a * x + b * y := by
  rintro ⟨x, y, hrep⟩
  have ha1 : 1 ≤ a := Nat.le_trans (by decide) ha
  have hb1 : 1 ≤ b := Nat.le_trans (by decide) hb
  have ha_pos : 0 < a := ha1
  have hb_pos : 0 < b := hb1
  have hab_pos : 0 < a * b := Nat.mul_pos ha_pos hb_pos
  -- a + b ≤ a*b
  have hsum_le : a + b ≤ a * b := add_le_mul_two ha hb
  -- Add a+b to both sides of hrep: a*b = a*x + b*y + a + b = a*(x+1) + b*(y+1)
  -- First: a*b - a - b + (a + b) = a*b.
  have ha_le : a ≤ a * b := Nat.le_trans (Nat.le_add_right a b) hsum_le
  have hab_le : a + b ≤ a * b := hsum_le
  -- (a*b - a) - b : recover a*b by adding b then a.
  have recover : a * b = (a * b - a - b) + a + b := by
    have e1 : (a * b - a - b) + b = a * b - a :=
      E213.Tactic.NatHelper.sub_add_cancel
        (by
          -- b ≤ a*b - a, i.e. a + b ≤ a*b
          have : a + b ≤ a * b := hsum_le
          -- a*b - a ≥ b  from a + b ≤ a*b
          have h2 : (a + b) - a ≤ (a * b) - a := Nat.sub_le_sub_right this a
          have h3 : (a + b) - a = b := by
            rw [Nat.add_comm a b, E213.Tactic.NatHelper.add_sub_cancel_right b a]
          rw [h3] at h2; exact h2)
    have e2 : (a * b - a) + a = a * b :=
      E213.Tactic.NatHelper.sub_add_cancel ha_le
    calc a * b = (a * b - a) + a := e2.symm
      _ = ((a * b - a - b) + b) + a := by rw [e1]
      _ = (a * b - a - b) + a + b := by
            rw [Nat.add_assoc (a * b - a - b) b a, Nat.add_comm b a,
                ← Nat.add_assoc (a * b - a - b) a b]
  rw [hrep] at recover
  -- recover : a*b = a*x + b*y + a + b
  -- = a*(x+1) + b*(y+1)
  have factored : a * b = a * (x + 1) + b * (y + 1) := by
    rw [recover]
    rw [Nat.mul_add a x 1, Nat.mul_one, Nat.mul_add b y 1, Nat.mul_one]
    -- a*x + b*y + a + b  =  (a*x + a) + (b*y + b)
    rw [Nat.add_assoc (a * x) (b * y) a, Nat.add_comm (b * y) a,
        ← Nat.add_assoc (a * x) a (b * y),
        Nat.add_assoc (a * x + a) (b * y) b]
  -- Reduce mod a: b*(y+1) ≡ 0 (mod a) since a*(x+1) ≡ 0 and a*b ≡ 0.
  -- a ∣ a*b and a ∣ a*(x+1), so a ∣ b*(y+1) = a*b - a*(x+1).
  have hdvd_ab : a ∣ a * b := ⟨b, rfl⟩
  have hdvd_ax : a ∣ a * (x + 1) := ⟨x + 1, rfl⟩
  -- b*(y+1) = a*b - a*(x+1)
  have hax_le : a * (x + 1) ≤ a * b := by rw [factored]; exact Nat.le_add_right _ _
  have hby_eq : b * (y + 1) = a * b - a * (x + 1) := by
    have : a * (x + 1) + b * (y + 1) = a * b := factored.symm
    calc b * (y + 1) = (a * (x + 1) + b * (y + 1)) - a * (x + 1) := by
            rw [Nat.add_comm (a * (x + 1)) (b * (y + 1)),
                E213.Tactic.NatHelper.add_sub_cancel_right (b * (y + 1)) (a * (x + 1))]
      _ = a * b - a * (x + 1) := by rw [this]
  have hdvd_by : a ∣ b * (y + 1) := by
    rw [hby_eq]
    exact E213.Meta.Nat.Gcd213.dvd_sub_213 (a * (x + 1)) (a * b) a hax_le hdvd_ax hdvd_ab
  -- coprime a b ⇒ a ∣ (y+1)
  have hdvd_y1 : a ∣ (y + 1) :=
    E213.Meta.Nat.Gcd213.coprime_dvd_of_dvd_mul hcop hdvd_by
  -- y+1 > 0 ⇒ a ≤ y+1
  have hy1_pos : 0 < y + 1 := Nat.succ_pos y
  have ha_le_y1 : a ≤ y + 1 := le_of_dvd_pure hy1_pos hdvd_y1
  -- So b*(y+1) ≥ b*a = a*b
  have hby_ge : a * b ≤ b * (y + 1) := by
    calc a * b = b * a := Nat.mul_comm a b
      _ ≤ b * (y + 1) := Nat.mul_le_mul_left b ha_le_y1
  -- Also a*(x+1) ≥ 1*a... we need a*(x+1) ≥ a (since x+1 ≥ 1), giving a*b ≥ a*b + a > a*b?
  -- Actually need strict: a*(x+1) ≥ a*1 = a > 0.  Then a*b = a*(x+1)+b*(y+1) ≥ a + a*b.
  have hax_ge : a ≤ a * (x + 1) := by
    calc a = a * 1 := (Nat.mul_one a).symm
      _ ≤ a * (x + 1) := Nat.mul_le_mul_left a (Nat.succ_le_succ (Nat.zero_le x))
  -- a*b = a*(x+1) + b*(y+1) ≥ a + a*b
  have contra : a + a * b ≤ a * b := by
    calc a + a * b ≤ a * (x + 1) + b * (y + 1) := Nat.add_le_add hax_ge hby_ge
      _ = a * b := factored.symm
  -- a + a*b ≤ a*b with a > 0 ⇒ contradiction
  -- commute to a*b + a ≤ a*b + 0, then cancel on the left.
  have hcomm : a * b + a ≤ a * b + 0 := by
    rw [Nat.add_zero, Nat.add_comm (a * b) a]; exact contra
  have ha_zero : a ≤ 0 := E213.Tactic.NatHelper.le_of_add_le_add_left hcomm
  exact absurd (Nat.le_antisymm ha_zero (Nat.zero_le a)) (Nat.ne_of_gt ha_pos)

/-! ## Frobenius-number table (closed, by `decide`) -/

-- The bounded search `(List.range N).all (… ! (g == a*x+b*y))` is closed/decidable,
-- so `decide` is ∅-axiom here.  Any representation of `g = a*x+b*y` would need
-- `x ≤ g/a < N` and `y ≤ g/b < N`, so the bounded check witnesses non-representability.

/-- `g(3,5) = 7`: no `x, y < 8` give `7 = 3·x + 5·y`. -/
theorem frob_3_5 :
    ((List.range 8).all (fun x => (List.range 8).all
      (fun y => ! (7 == 3 * x + 5 * y)))) = true := by decide

/-- `g(4,5) = 11`: no `x, y < 12` give `11 = 4·x + 5·y`. -/
theorem frob_4_5 :
    ((List.range 12).all (fun x => (List.range 12).all
      (fun y => ! (11 == 4 * x + 5 * y)))) = true := by decide

/-- `g(3,7) = 11`: no `x, y < 12` give `11 = 3·x + 7·y`. -/
theorem frob_3_7 :
    ((List.range 12).all (fun x => (List.range 12).all
      (fun y => ! (11 == 3 * x + 7 * y)))) = true := by decide

end E213.Lib.Math.NumberTheory.ModArith.FrobeniusNonRepresentable
