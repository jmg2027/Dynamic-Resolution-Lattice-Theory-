import E213.Lib.Math.NumberTheory.ModArith.GaussLemma

/-!
# SecondSupplement — toward the quadratic character of `2`

`gauss_qr` applied at `a = 2`: for `x ∈ [1..m]`, `2x ≤ 2m = p−1 < p`, so `(2x) % p = 2x` (no
wraparound) and the sign `sgFn 2 p m x = if 2x ≤ m then 1 else −1` depends only on `m`.  Hence

  `2` is a QR mod `p`  ⟺  `∏ₓ (if 2x ≤ m then 1 else −1) = 1`   (`two_qr_iff`).

`prodZ_sign_eq` evaluates a `±1`-product as `(−1)^(#negatives)`.  The remaining step (the count
`#{x : 2x > m} = m − ⌊m/2⌋`, its parity, and `p ≡ ±1 mod 8`) is recorded in
`research-notes/frontiers/second_supplement.md`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.SecondSupplement

open E213.Lib.Math.NumberTheory.ModArith.GaussLemma (seg mem_seg sgFn gauss_qr)
open E213.Lib.Math.Algebra.Linalg213.ProdLperm (prodZ)

/-! ## §1 — a `±1`-product is `(−1)^(#negatives)` -/

/-- Count of `−1`s in an `Int` list. -/
def countNeg : List Int → Nat
  | [] => 0
  | x :: xs => countNeg xs + (if x = -1 then 1 else 0)

/-- A `prodZ` of `±1`s equals `(−1)` to the number of `−1`s. -/
theorem prodZ_sign_eq : ∀ (L : List Int), (∀ z, z ∈ L → z = 1 ∨ z = -1) →
    prodZ L = (-1 : Int) ^ countNeg L
  | [], _ => rfl
  | x :: xs, h => by
    have hrec := prodZ_sign_eq xs (fun z hz => h z (List.Mem.tail x hz))
    show x * prodZ xs = (-1 : Int) ^ (countNeg xs + (if x = -1 then 1 else 0))
    rcases h x (List.Mem.head xs) with hx | hx
    · subst hx
      rw [show (if (1 : Int) = -1 then 1 else 0) = 0 from by decide, Nat.add_zero, hrec, Int.one_mul]
    · subst hx
      rw [show (if (-1 : Int) = -1 then 1 else 0) = 1 from by decide, hrec, Int.pow_succ]
      ring_intZ

/-! ## §2 — the `a = 2` reduction (no wraparound) -/

/-- ★★★★ **The quadratic character of `2`, reduced to an `m`-only sign product.**  `2` is a QR mod
    `p` iff `∏ₓ (if 2x ≤ m then 1 else −1) = 1`, the product over `[1..m]`.  Since `2x ≤ 2m = p−1 < p`
    there is no wraparound, so `sgFn 2 = (if 2x ≤ m …)`; then `gauss_qr`. -/
theorem two_qr_iff (p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (hp2 : 2 < p) :
    (∃ z : Nat, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = 2) ↔
      prodZ ((seg m).map (fun x => if 2 * x ≤ m then (1 : Int) else -1)) = 1 := by
  have hmap : (seg m).map (sgFn 2 p m)
      = (seg m).map (fun x => if 2 * x ≤ m then (1 : Int) else -1) := by
    apply E213.Tactic.List213.map_congr
    intro x hx
    obtain ⟨_, hxm⟩ := mem_seg.mp hx
    have h2xp : 2 * x < p := by
      have h1 : 2 * x ≤ 2 * m := Nat.mul_le_mul_left 2 hxm
      rw [h2m] at h1
      exact Nat.lt_of_le_of_lt h1
        (Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)) Nat.zero_lt_one)
    show (if (2 * x) % p ≤ m then (1 : Int) else -1) = (if 2 * x ≤ m then (1 : Int) else -1)
    rw [Nat.mod_eq_of_lt h2xp]
  rw [← hmap]
  exact gauss_qr 2 p m hp hpr h2m hm1 (by decide) hp2

end E213.Lib.Math.NumberTheory.ModArith.SecondSupplement
