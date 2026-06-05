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
open E213.Lib.Math.Algebra.Linalg213.ProdLperm (prodZ prodZ_append)
open E213.Lib.Math.Algebra.Linalg213.Laplace (map_append')
open E213.Lib.Math.Algebra.Linalg213.Permutation (iota)
open E213.Meta.Int213 (mul_one)
open E213.Meta.Nat.AddMod213 (div_add_mod)
open E213.Tactic.NatHelper (add_sub_of_le add_mul_mod_self_pure)

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

/-! ## §3 — evaluating the sign product (the `−1`-count over `[1..k]`) -/

/-- `#{x ∈ [1, k] : 2x > m}` (the `−1`s), recursion on `k` with `m` fixed. -/
def cnt2 (m : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => cnt2 m k + (if 2 * (k + 1) ≤ m then 0 else 1)

/-- `∏ₓ∈[1,k] (if 2x ≤ m then 1 else −1) = (−1)^(cnt2 m k)`, by induction on `k` (`seg` appends
    at the end, `m` fixed — so this telescopes). -/
theorem prodZ_seg_sign (m : Nat) : ∀ k,
    prodZ ((seg k).map (fun x => if 2 * x ≤ m then (1 : Int) else -1)) = (-1 : Int) ^ cnt2 m k
  | 0 => rfl
  | k + 1 => by
    have hseg : seg (k + 1) = seg k ++ [k + 1] := by
      show (iota (k + 1)).map (· + 1) = (iota k).map (· + 1) ++ [k + 1]
      rw [show iota (k + 1) = iota k ++ [k] from rfl, map_append',
          show ([k] : List Nat).map (· + 1) = [k + 1] from rfl]
    rw [hseg, map_append', prodZ_append, prodZ_seg_sign m k]
    show (-1 : Int) ^ cnt2 m k * ((if 2 * (k + 1) ≤ m then (1 : Int) else -1) * 1)
       = (-1 : Int) ^ (cnt2 m k + (if 2 * (k + 1) ≤ m then 0 else 1))
    rcases Nat.lt_or_ge (2 * (k + 1)) (m + 1) with hc | hc
    · have hle : 2 * (k + 1) ≤ m := Nat.le_of_lt_succ hc
      rw [if_pos hle, if_pos hle, Nat.add_zero, mul_one, mul_one]
    · have hnle : ¬ 2 * (k + 1) ≤ m := fun h => Nat.not_succ_le_self m (Nat.le_trans hc h)
      rw [if_neg hnle, if_neg hnle, Int.pow_succ, mul_one]

/-! ## §4 — `cnt2 m m = m − m/2` -/

/-- Below the threshold (`k ≤ m/2`) there are no `−1`s. -/
private theorem cnt2_zero_le (m : Nat) : ∀ k, k ≤ m / 2 → cnt2 m k = 0
  | 0, _ => rfl
  | k + 1, hk => by
    show cnt2 m k + (if 2 * (k + 1) ≤ m then 0 else 1) = 0
    have hk' : k ≤ m / 2 := Nat.le_of_succ_le hk
    have h2le : 2 * (k + 1) ≤ m :=
      Nat.le_trans (Nat.mul_le_mul_left 2 hk) (Nat.le.intro (div_add_mod m 2))
    rw [cnt2_zero_le m k hk', if_pos h2le, Nat.add_zero]

/-- Past the threshold, the count increases by `1` each step. -/
private theorem cnt2_past (m : Nat) : ∀ k, cnt2 m (m / 2 + k) = k
  | 0 => by rw [Nat.add_zero]; exact cnt2_zero_le m (m / 2) (Nat.le_refl _)
  | k + 1 => by
    show cnt2 m (m / 2 + k) + (if 2 * ((m / 2 + k) + 1) ≤ m then 0 else 1) = k + 1
    have hgt : ¬ 2 * ((m / 2 + k) + 1) ≤ m := by
      have hm : m = 2 * (m / 2) + m % 2 := (div_add_mod m 2).symm
      have hlt : m < 2 * ((m / 2 + k) + 1) := by
        rw [show 2 * ((m / 2 + k) + 1) = 2 * (m / 2) + 2 * (k + 1) from by ring_nat]
        calc m = 2 * (m / 2) + m % 2 := hm
          _ < 2 * (m / 2) + 2 * (k + 1) := Nat.add_lt_add_left
                (Nat.lt_of_lt_of_le (Nat.mod_lt m (by decide))
                  (Nat.le_mul_of_pos_right 2 (Nat.succ_pos k))) (2 * (m / 2))
      exact fun hle => absurd (Nat.lt_of_lt_of_le hlt hle) (Nat.lt_irrefl m)
    rw [cnt2_past m k, if_neg hgt]

private theorem cnt2_at_m (m : Nat) : cnt2 m m = m - m / 2 := by
  have hle : m / 2 ≤ m :=
    Nat.le_trans (Nat.le.intro (Nat.two_mul (m / 2)).symm) (Nat.le.intro (div_add_mod m 2))
  have heq : m / 2 + (m - m / 2) = m := add_sub_of_le hle
  have hpast := cnt2_past m (m - m / 2)
  rw [heq] at hpast; exact hpast

end E213.Lib.Math.NumberTheory.ModArith.SecondSupplement
