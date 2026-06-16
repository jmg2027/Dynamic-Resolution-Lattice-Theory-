import E213.Meta.Int213.PolyIntMTactic

/-!
# Difference-of-powers divisibility `(a − b) ∣ (aⁿ − bⁿ)` (∅-axiom)

The classical divisibility behind the geometric-series factorization
`aⁿ − bⁿ = (a−b)·Σ aⁱbⁿ⁻¹⁻ⁱ`.  Induction on `n` via the step identity
`aⁿ⁺¹ − bⁿ⁺¹ = a·(aⁿ − bⁿ) + (a − b)·bⁿ` (a `ring_intZ` identity), with the
companion `(a − 1) ∣ (aⁿ − 1)`.  Genuinely absent.

`ipow` is a local PURE integer power (the corpus has no propext-clean Int `^`
fold suited here), and the Int `∣`-helpers are local explicit-witness lemmas.
Purity notes: `Int.sub_self` and `▸`/`rw` dividend-transport leak `propext`, so
the `n=0` base uses a `show`-narrowed `decide` and transport uses the
explicit-witness `dvd_of_eqZ`.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.DiffPowDvd

open E213.Meta.Int213.PolyIntM

/-- Local integer power, PURE structural recursion. -/
def ipow (x : Int) : Nat → Int
  | 0 => 1
  | n + 1 => ipow x n * x

@[simp] theorem ipow_zero (x : Int) : ipow x 0 = 1 := rfl
theorem ipow_succ (x : Int) (n : Nat) : ipow x (n + 1) = ipow x n * x := rfl

/-! ## Local Int `dvd` helpers (PURE, explicit witness + `ring_intZ`) -/

/-- `g ∣ x → g ∣ y → g ∣ (x + y)`. -/
theorem dvd_addZ {g x y : Int} (hx : g ∣ x) (hy : g ∣ y) : g ∣ (x + y) := by
  obtain ⟨w₁, hw₁⟩ := hx
  obtain ⟨w₂, hw₂⟩ := hy
  refine ⟨w₁ + w₂, ?_⟩
  rw [hw₁, hw₂]
  show g * w₁ + g * w₂ = g * (w₁ + w₂)
  ring_intZ

/-- `g ∣ x → g ∣ (b * x)` (witness `b * w`). -/
theorem dvd_mul_leftZ {g x : Int} (b : Int) (hx : g ∣ x) : g ∣ (b * x) := by
  obtain ⟨w, hw⟩ := hx
  refine ⟨b * w, ?_⟩
  rw [hw]
  show b * (g * w) = g * (b * w)
  ring_intZ

/-- `g ∣ (g * c)` (witness `c`). -/
theorem dvd_mul_selfZ (g c : Int) : g ∣ (g * c) := ⟨c, rfl⟩

/-- `g ∣ 0` (witness `0`). -/
theorem dvd_zeroZ (g : Int) : g ∣ (0 : Int) := ⟨0, (Int.mul_zero g).symm⟩

/-- Transport divisibility along an equality of the dividend, term-mode (no `rw`/`▸`). -/
theorem dvd_of_eqZ {g x y : Int} (hxy : x = y) (hgy : g ∣ y) : g ∣ x := by
  obtain ⟨w, hw⟩ := hgy
  exact ⟨w, Eq.trans hxy hw⟩

/-! ## Main theorem -/

/-- ★ **Difference-of-powers divisibility**: `(a − b) ∣ (aⁿ − bⁿ)`.
    Induction on `n`.  `n=0`: difference is `0`.  `n+1`: via
    `aⁿ⁺¹ − bⁿ⁺¹ = a·(aⁿ − bⁿ) + (a − b)·bⁿ` (a `ring_intZ` identity). -/
theorem sub_dvd_pow_sub_pow (a b : Int) (n : Nat) :
    (a - b) ∣ (ipow a n - ipow b n) := by
  induction n with
  | zero =>
      have h0 : ipow a 0 - ipow b 0 = (0 : Int) := by
        show (1 : Int) - 1 = 0; decide
      exact dvd_of_eqZ h0 (dvd_zeroZ _)
  | succ n ih =>
      have t1 : (a - b) ∣ a * (ipow a n - ipow b n) := dvd_mul_leftZ a ih
      have t2 : (a - b) ∣ (a - b) * ipow b n := dvd_mul_selfZ _ _
      have hsum : (a - b) ∣ (a * (ipow a n - ipow b n) + (a - b) * ipow b n) :=
        dvd_addZ t1 t2
      have key : ipow a (n + 1) - ipow b (n + 1)
          = a * (ipow a n - ipow b n) + (a - b) * ipow b n := by
        show ipow a n * a - ipow b n * b
            = a * (ipow a n - ipow b n) + (a - b) * ipow b n
        ring_intZ
      exact dvd_of_eqZ key hsum

/-! ## Companion: `(a − 1) ∣ (aⁿ − 1)` -/

/-- `ipow 1 n = 1`. -/
theorem ipow_one : ∀ n : Nat, ipow (1 : Int) n = 1
  | 0 => rfl
  | k + 1 => by rw [ipow_succ, ipow_one k]; decide

/-- `(a − 1) ∣ (aⁿ − 1)` (the `b = 1` specialization). -/
theorem one_dvd_pow_sub_one (a : Int) (n : Nat) : (a - 1) ∣ (ipow a n - 1) := by
  have h : (a - 1) ∣ (ipow a n - ipow (1 : Int) n) := sub_dvd_pow_sub_pow a 1 n
  have heq : ipow a n - 1 = ipow a n - ipow (1 : Int) n :=
    congrArg (fun t => ipow a n - t) (ipow_one n).symm
  exact dvd_of_eqZ heq h

/-- Smoke: `(3 − 1) ∣ (3⁴ − 1⁴)`, i.e. `2 ∣ 80`. -/
theorem smoke_two_dvd_eighty : (3 - 1 : Int) ∣ (ipow 3 4 - ipow 1 4) :=
  sub_dvd_pow_sub_pow 3 1 4

end E213.Lib.Math.NumberTheory.DiffPowDvd
