import E213.Lib.Math.NumberTheory.ModArith.GaussLemma
import E213.Meta.Nat.NatDiv213

/-!
# SecondSupplement — toward the quadratic character of `2`

`gauss_qr` applied at `a = 2`: for `x ∈ [1..m]`, `2x ≤ 2m = p−1 < p`, so `(2x) % p = 2x` (no
wraparound) and the sign `sgFn 2 p m x = if 2x ≤ m then 1 else −1` depends only on `m`.  Hence

  `2` is a QR mod `p`  ⟺  `∏ₓ (if 2x ≤ m then 1 else −1) = 1`   (`two_qr_iff`).

`prodZ_sign_eq` evaluates a `±1`-product as `(−1)^(#negatives)`.  The remaining step (the count
`#{x : 2x > m} = m − ⌊m/2⌋`, its parity, and `p ≡ ±1 mod 8`) is discharged below in
`second_supplement`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.SecondSupplement

open E213.Lib.Math.NumberTheory.ModArith.GaussLemma (seg mem_seg sgFn sgFn_pm gauss_qr)
open E213.Tactic.List213 (exists_of_mem_map)
open E213.Lib.Math.Algebra.Linalg213.ProdLperm (prodZ prodZ_append)
open E213.Lib.Math.Algebra.Linalg213.Laplace (map_append')
open E213.Lib.Math.Algebra.Linalg213.Permutation (iota)
open E213.Meta.Int213 (mul_one)
open E213.Meta.Nat.AddMod213 (div_add_mod)
open E213.Tactic.NatHelper (add_sub_of_le add_mul_mod_self_pure)
open E213.Tactic.NatHelper (sub_add_cancel add_sub_cancel_right)
open E213.Meta.Nat.NatDiv213 (add_mul_div_left_pure div_le_self_pos)

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

/-! ## §5 — `(−1)^n = 1 ⟺ n even`, and the supplement -/

private theorem neg_one_pow_two (k : Nat) : (-1 : Int) ^ (2 * k) = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.mul_succ, show 2 * k + 2 = (2 * k + 1) + 1 from rfl, Int.pow_succ, Int.pow_succ, ih]
    decide

private theorem neg_one_pow_iff (n : Nat) : (-1 : Int) ^ n = 1 ↔ n % 2 = 0 := by
  rcases Nat.eq_zero_or_pos (n % 2) with h0 | hpos
  · refine ⟨fun _ => h0, fun _ => ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, n = 2 * k :=
      ⟨n / 2, by have h := div_add_mod n 2; rw [h0, Nat.add_zero] at h; exact h.symm⟩
    rw [hk]; exact neg_one_pow_two k
  · have h1 : n % 2 = 1 := Nat.le_antisymm (Nat.le_of_lt_succ (Nat.mod_lt n (by decide))) hpos
    obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 :=
      ⟨n / 2, by have h := div_add_mod n 2; rw [h1] at h; exact h.symm⟩
    constructor
    · intro hpow
      exfalso
      rw [hk, Int.pow_succ, neg_one_pow_two, Int.one_mul] at hpow
      exact absurd hpow (by decide)
    · intro h; rw [h1] at h; exact absurd h (by decide)

/-- ★★★★★ **The quadratic character of `2` (`m`-form).**  `2` is a QR mod `p` ⟺ `m − ⌊m/2⌋` is even
    (`m = (p−1)/2`).  `two_qr_iff` ∘ `prodZ_seg_sign` (= `(−1)^(cnt2)`) ∘ `cnt2_at_m`
    (`= m − m/2`) ∘ `neg_one_pow_iff`. -/
theorem second_supplement_m (p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (hp2 : 2 < p) :
    (∃ z : Nat, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = 2) ↔ (m - m / 2) % 2 = 0 := by
  refine (two_qr_iff p m hp hpr h2m hm1 hp2).trans ?_
  rw [prodZ_seg_sign m m, cnt2_at_m]
  exact neg_one_pow_iff (m - m / 2)

/-- ★★★★★ **Second supplement to quadratic reciprocity.**  `2` is a QR mod a prime `p`
    **iff** `p ≡ ±1 (mod 8)`.  `second_supplement_m` (`2 QR ⟺ (m − m/2) even`) bridged through
    `m = 4q+r`: both `(m − m/2) % 2` and `p % 8 = 1 + 2(m%4)` are functions of `m % 4 ∈ {0,1,2,3}`. -/
theorem second_supplement (p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (hp2 : 2 < p) :
    (∃ z : Nat, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = 2) ↔ p % 8 = 1 ∨ p % 8 = 7 := by
  refine (second_supplement_m p m hp hpr h2m hm1 hp2).trans ?_
  have hp1 : p = 1 + 2 * m := by
    have h := add_sub_of_le (Nat.le_of_lt hp); rw [← h2m] at h; exact h.symm
  rw [hp1]
  obtain ⟨q, r, hr4, hmd⟩ : ∃ q r, r < 4 ∧ m = 4 * q + r :=
    ⟨m / 4, m % 4, Nat.mod_lt m (by decide), (div_add_mod m 4).symm⟩
  rw [hmd]
  have hdiv : (4 * q + r) / 2 = 2 * q + r / 2 := by
    rw [show 4 * q + r = r + 2 * (2 * q) from by ring_nat, add_mul_div_left_pure r 2 (2 * q) (by decide)]
    ring_nat
  have hrle : r / 2 ≤ r := div_le_self_pos r 2 (by decide)
  have hsub : (4 * q + r) - (2 * q + r / 2) = 2 * q + (r - r / 2) := by
    have hadd : (2 * q + (r - r / 2)) + (2 * q + r / 2) = 4 * q + r := by
      rw [show (2 * q + (r - r / 2)) + (2 * q + r / 2)
            = 4 * q + ((r - r / 2) + r / 2) from by ring_nat, sub_add_cancel hrle]
    rw [← hadd, add_sub_cancel_right]
  have hmod2 : (2 * q + (r - r / 2)) % 2 = (r - r / 2) % 2 := by
    rw [Nat.add_comm (2 * q) (r - r / 2),
        show (r - r / 2) + 2 * q = (r - r / 2) + q * 2 from by ring_nat, add_mul_mod_self_pure]
  have hp8 : (1 + 2 * (4 * q + r)) % 8 = 1 + 2 * r := by
    rw [show 1 + 2 * (4 * q + r) = (1 + 2 * r) + q * 8 from by ring_nat, add_mul_mod_self_pure]
    exact Nat.mod_eq_of_lt (by
      have hle3 : r ≤ 3 := Nat.le_of_lt_succ hr4
      calc 1 + 2 * r ≤ 1 + 2 * 3 := Nat.add_le_add_left (Nat.mul_le_mul_left 2 hle3) 1
        _ < 8 := by decide)
  rw [hdiv, hsub, hmod2, hp8]
  rcases r with _ | _ | _ | _ | r'
  · decide
  · decide
  · decide
  · decide
  · exact absurd (Nat.lt_of_le_of_lt (Nat.le_add_left 4 r') hr4) (Nat.lt_irrefl 4)

/-- ★★★★ **Gauss's lemma (μ-count form).**  `a` is a QR mod `p` ⟺ `μ` is even, where
    `μ = #{x ∈ [1,m] : (a·x) mod p > m}` (`= countNeg` of the sign list).  `gauss_qr` + `prodZ_sign_eq`
    (`∏signs = (−1)^μ`) + `neg_one_pow_iff`.  The recognizable Gauss-lemma statement; the engine for
    quadratic reciprocity. -/
theorem gauss_mu (a p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (ha1 : 1 ≤ a) (halt : a < p) :
    (∃ z : Nat, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = a) ↔ countNeg ((seg m).map (sgFn a p m)) % 2 = 0 := by
  refine (gauss_qr a p m hp hpr h2m hm1 ha1 halt).trans ?_
  rw [prodZ_sign_eq ((seg m).map (sgFn a p m)) (fun z hz => by
    obtain ⟨x, _, hxz⟩ := exists_of_mem_map hz; rw [← hxz]; exact sgFn_pm a p m x)]
  exact neg_one_pow_iff (countNeg ((seg m).map (sgFn a p m)))

end E213.Lib.Math.NumberTheory.ModArith.SecondSupplement
