import E213.Lib.Math.NumberTheory.SquareCharacterization
import E213.Lib.Math.NumberTheory.OddPartDecomposition
import E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.VpMul
import E213.Meta.Nat.VpSeparation

/-!
# Fermat's right-triangle theorem `x⁴+y⁴=z²` has no positive solution (∅-axiom)

Infinite descent re-cast as an **explicit strictly-`z`-decreasing constructor** +
strong induction on `z` (no well-ordering / LEM as a proof device).
-/

namespace E213.Lib.Math.NumberTheory.FermatQuartic

open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.Gcd213
open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
  (coprime_mul_of_coprime coprime_mul_iff coprime_pow_right coprime_pow_left
   coprime_pow_pow dvd_trans_213)
open E213.Lib.Math.NumberTheory.SquareCharacterization (IsSquare coprime_isSquare_mul)

/-! ## §0 — small Nat arithmetic helpers (all PURE) -/

theorem mul_assoc' (a b c : Nat) : (a * b) * c = a * (b * c) := mul_assoc_213 a b c

open E213.Meta.Nat.AddMod213 (mod_two_zero_or_one add_mod div_add_mod)

/-- Parity of a product: `(a*b) % 2 = (a%2) * (b%2) % 2`. -/
theorem mul_mod_two (a b : Nat) : (a * b) % 2 = (a % 2) * (b % 2) % 2 := by
  exact E213.Meta.Nat.MulMod213.mul_mod_pure a b 2

/-- A square is even iff its root is even. -/
theorem sq_mod_two (n : Nat) : (n * n) % 2 = n % 2 := by
  rw [mul_mod_two]
  rcases mod_two_zero_or_one n with h | h <;> rw [h] <;> decide

/-- `n` odd ⟹ `n*n` odd. -/
theorem sq_odd_of_odd {n : Nat} (h : n % 2 = 1) : (n * n) % 2 = 1 := by
  rw [sq_mod_two]; exact h

/-- `n` even ⟹ `n*n` even. -/
theorem sq_even_of_even {n : Nat} (h : n % 2 = 0) : (n * n) % 2 = 0 := by
  rw [sq_mod_two]; exact h

/-- An even number is `2*k`. -/
theorem even_eq_two_mul {n : Nat} (h : n % 2 = 0) : ∃ k, n = 2 * k := by
  refine ⟨n / 2, ?_⟩
  have hd : 2 * (n / 2) + n % 2 = n := div_add_mod n 2
  rw [h, Nat.add_zero] at hd; exact hd.symm

/-- An odd number is `2*k+1`. -/
theorem odd_eq_two_mul_add_one {n : Nat} (h : n % 2 = 1) : ∃ k, n = 2 * k + 1 := by
  refine ⟨n / 2, ?_⟩
  have hd : 2 * (n / 2) + n % 2 = n := div_add_mod n 2
  rw [h] at hd; exact hd.symm

/-- Difference of two odds is even: `a` odd, `c` odd, `a ≤ c` ⟹ `∃ u, c = a + 2*u`. -/
theorem odd_sub_odd_eq_two_mul {a c : Nat}
    (ha : a % 2 = 1) (hc : c % 2 = 1) (hle : a ≤ c) : ∃ u, c = a + 2 * u := by
  obtain ⟨i, hi⟩ := odd_eq_two_mul_add_one ha
  obtain ⟨j, hj⟩ := odd_eq_two_mul_add_one hc
  -- 2i+1 ≤ 2j+1 ⟹ i ≤ j
  have hij : i ≤ j := by
    rw [hi, hj] at hle
    exact E213.Meta.Nat.NatDiv213.two_cancel i j (Nat.le_of_succ_le_succ hle)
  refine ⟨j - i, ?_⟩
  rw [hi, hj]
  have hsub : 2 * (j - i) = 2 * j - 2 * i := E213.Tactic.NatHelper.mul_sub 2 j i
  rw [hsub]
  have h2 : 2 * i ≤ 2 * j := Nat.mul_le_mul_left 2 hij
  -- goal: 2*j+1 = (2*i+1) + (2*j - 2*i)
  -- (2*i+1) + (2*j - 2*i) = (2*j - 2*i) + (2*i+1) = ((2*j-2*i)+2*i)+1 = 2*j+1
  have hcancel : (2 * j - 2 * i) + 2 * i = 2 * j := E213.Tactic.NatHelper.sub_add_cancel h2
  calc 2 * j + 1 = ((2 * j - 2 * i) + 2 * i) + 1 := by rw [hcancel]
    _ = (2 * i + 1) + (2 * j - 2 * i) := by ring_nat

/-! ## §1 — Pythagorean converse over Nat -/

/-- If `g ∣ a` and `g ∣ b*b` while `gcd(a,b)=1`, then `g = 1`. -/
theorem eq_one_of_dvd_a_and_bb {g a b : Nat}
    (hco : gcd213 a b = 1) (hga : g ∣ a) (hgbb : g ∣ b * b) : g = 1 := by
  have hcoabb : gcd213 a (b * b) = 1 := coprime_mul_of_coprime hco hco
  have hg : g ∣ gcd213 a (b * b) := gcd213_greatest a (b * b) g hga hgbb
  rw [hcoabb] at hg
  obtain ⟨c, hc⟩ := hg
  exact mul_eq_one_left g c hc.symm

/-- Coprimality of the `(u, v)` factor pair: from `gcd(a,b)=1` and
    `b*b = 4*u*(a+u)`, with `v = a+u`, we get `gcd(u,v)=1`.
    A common divisor `g` of `u` and `v=a+u` divides `a` and (`g∣u ⟹ g∣4*u*v=b*b`). -/
theorem uv_coprime {a b u : Nat}
    (hco : gcd213 a b = 1) (hbb : b * b = 4 * u * (a + u)) :
    gcd213 u (a + u) = 1 := by
  have hgu : gcd213 u (a + u) ∣ u := gcd213_dvd_left u (a + u)
  have hgv : gcd213 u (a + u) ∣ (a + u) := gcd213_dvd_right u (a + u)
  -- g ∣ a  since g ∣ (a+u) and g ∣ u, and (a+u)-u = a
  have hga : gcd213 u (a + u) ∣ a := by
    have hle : u ≤ a + u := by
      have := Nat.zero_le a
      calc u = 0 + u := (Nat.zero_add u).symm
        _ ≤ a + u := Nat.add_le_add_right (Nat.zero_le a) u
    have h := dvd_sub_213 u (a + u) (gcd213 u (a + u)) hle hgu hgv
    rwa [E213.Tactic.NatHelper.add_sub_cancel_right a u] at h
  -- g ∣ b*b  since b*b = 4*u*v and g ∣ u
  have hgbb : gcd213 u (a + u) ∣ b * b := by
    rw [hbb]
    have hudvd : u ∣ 4 * u * (a + u) := ⟨4 * (a + u), by ring_nat⟩
    exact dvd_trans_213 hgu hudvd
  exact eq_one_of_dvd_a_and_bb hco hga hgbb

/-- `gcd(n*n, m*m) = 1 ⟹ gcd(n,m) = 1`. -/
theorem coprime_of_coprime_sq {n m : Nat} (h : gcd213 (n * n) (m * m) = 1) :
    gcd213 n m = 1 := by
  have hn : gcd213 n m ∣ n * n :=
    dvd_trans_213 (gcd213_dvd_left n m) ⟨n, rfl⟩
  have hm : gcd213 n m ∣ m * m :=
    dvd_trans_213 (gcd213_dvd_right n m) ⟨m, rfl⟩
  have hg : gcd213 n m ∣ gcd213 (n * n) (m * m) :=
    gcd213_greatest (n * n) (m * m) _ hn hm
  rw [h] at hg
  obtain ⟨c, hc⟩ := hg
  exact mul_eq_one_left _ c hc.symm

/-- `x*x = y*y ⟹ x = y` over `Nat`. -/
theorem sq_eq_imp_eq {x y : Nat} (h : x * x = y * y) : x = y := by
  rcases Nat.lt_trichotomy x y with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (Nat.mul_lt_mul_of_lt_of_le hlt (Nat.le_of_lt hlt)
      (Nat.lt_of_le_of_lt (Nat.zero_le x) hlt)))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (Nat.mul_lt_mul_of_lt_of_le hgt (Nat.le_of_lt hgt)
      (Nat.lt_of_le_of_lt (Nat.zero_le y) hgt)))

/-- Odd square is `1 mod 4`. -/
theorem odd_sq_mod_four {n : Nat} (h : n % 2 = 1) : (n * n) % 4 = 1 := by
  obtain ⟨k, hk⟩ := odd_eq_two_mul_add_one h
  -- (2k+1)² = 4(k²+k) + 1
  have : n * n = 4 * (k * k + k) + 1 := by rw [hk]; ring_nat
  rw [this, E213.Meta.Nat.AddMod213.add_mod_gen (4 * (k * k + k)) 1 4,
      E213.Meta.Nat.NatDiv213.mul_mod_self_pure 4 (k * k + k)]

/-- Even square is `0 mod 4`. -/
theorem even_sq_mod_four {n : Nat} (h : n % 2 = 0) : (n * n) % 4 = 0 := by
  obtain ⟨k, hk⟩ := even_eq_two_mul h
  have : n * n = 4 * (k * k) := by rw [hk]; ring_nat
  rw [this]; exact E213.Meta.Nat.NatDiv213.mul_mod_self_pure 4 (k * k)

/-- Any square is `0` or `1 mod 4`. -/
theorem sq_mod_four (n : Nat) : (n * n) % 4 = 0 ∨ (n * n) % 4 = 1 := by
  rcases mod_two_zero_or_one n with h | h
  · exact Or.inl (even_sq_mod_four h)
  · exact Or.inr (odd_sq_mod_four h)

/-- In a primitive triple, the two legs are not both odd. -/
theorem not_both_odd {a b c : Nat}
    (haodd : a % 2 = 1) (hbodd : b % 2 = 1) (heq : a * a + b * b = c * c) : False := by
  -- a²+b² ≡ 2 mod 4, but c² ≡ 0 or 1 mod 4.
  have hab : (a * a + b * b) % 4 = 2 := by
    rw [E213.Meta.Nat.AddMod213.add_mod_gen (a * a) (b * b) 4,
        odd_sq_mod_four haodd, odd_sq_mod_four hbodd]
  rw [heq] at hab
  rcases sq_mod_four c with h | h <;> rw [h] at hab <;> exact absurd hab (by decide)

/-- In a primitive triple `a*a + b*b = c*c` with `gcd(a,b)=1`, also `gcd(a,c)=1`. -/
theorem pyth_coprime_leg_hyp {a b c : Nat}
    (hco : gcd213 a b = 1) (heq : a * a + b * b = c * c) :
    gcd213 a c = 1 := by
  -- g := gcd(a,c) divides a and c; g ∣ c*c = a*a+b*b, g∣a ⟹ g∣b*b; coprime a b ⟹ g=1
  have hga : gcd213 a c ∣ a := gcd213_dvd_left a c
  have hgc : gcd213 a c ∣ c := gcd213_dvd_right a c
  have hgcc : gcd213 a c ∣ c * c := dvd_trans_213 hgc ⟨c, rfl⟩
  have hgaa : gcd213 a c ∣ a * a := dvd_trans_213 hga ⟨a, rfl⟩
  -- g ∣ b*b = c*c - a*a
  have hle : a * a ≤ c * c := heq ▸ Nat.le_add_right (a * a) (b * b)
  have hgbb : gcd213 a c ∣ b * b := by
    have hsub := dvd_sub_213 (a * a) (c * c) (gcd213 a c) hle hgaa hgcc
    have hbb_eq : c * c - a * a = b * b := by
      rw [← heq, Nat.add_comm (a*a) (b*b)]
      exact E213.Tactic.NatHelper.add_sub_cancel_right (b * b) (a * a)
    rwa [hbb_eq] at hsub
  exact eq_one_of_dvd_a_and_bb hco hga hgbb

/-- `gcd(r,s)=1 ⟹ gcd(r, r*r+s*s)=1`. -/
theorem coprime_leg_hyp_sum {r s : Nat} (h : gcd213 r s = 1) :
    gcd213 r (r * r + s * s) = 1 := by
  -- g ∣ r and g ∣ r²+s² ⟹ g ∣ s² ; gcd(r,s²)=1 ⟹ g=1
  have hgr : gcd213 r (r * r + s * s) ∣ r := gcd213_dvd_left r (r * r + s * s)
  have hgsum : gcd213 r (r * r + s * s) ∣ (r * r + s * s) :=
    gcd213_dvd_right r (r * r + s * s)
  have hgss : gcd213 r (r * r + s * s) ∣ s * s := by
    have hrr : gcd213 r (r * r + s * s) ∣ r * r := dvd_trans_213 hgr ⟨r, rfl⟩
    have hle : r * r ≤ r * r + s * s := Nat.le_add_right (r * r) (s * s)
    have hsub := dvd_sub_213 (r * r) (r * r + s * s) _ hle hrr hgsum
    -- (r*r+s*s) - (r*r) = s*s
    have heq2 : (r * r + s * s) - (r * r) = s * s := by
      rw [Nat.add_comm (r * r) (s * s)]
      exact E213.Tactic.NatHelper.add_sub_cancel_right (s * s) (r * r)
    rwa [heq2] at hsub
  -- gcd(r,s²)=1
  have hco_rss : gcd213 r (s * s) = 1 := coprime_mul_of_coprime h h
  have hg : gcd213 r (r * r + s * s) ∣ gcd213 r (s * s) :=
    gcd213_greatest r (s * s) _ hgr hgss
  rw [hco_rss] at hg
  obtain ⟨c, hc⟩ := hg
  exact mul_eq_one_left _ c hc.symm

/-- `gcd(r,s)=1 ⟹ gcd(r*s, r*r+s*s)=1`. -/
theorem coprime_prod_sum {r s : Nat} (h : gcd213 r s = 1) :
    gcd213 (r * s) (r * r + s * s) = 1 := by
  have hr : gcd213 r (r * r + s * s) = 1 := coprime_leg_hyp_sum h
  have hs : gcd213 s (r * r + s * s) = 1 := by
    have h' : gcd213 s (s * s + r * r) = 1 := coprime_leg_hyp_sum ((gcd213_comm s r).trans h)
    rwa [Nat.add_comm (s * s) (r * r)] at h'
  -- gcd(r*s, T) = gcd(T, r*s) = 1  from gcd(T,r)=1 ∧ gcd(T,s)=1
  rw [gcd213_comm (r * s) (r * r + s * s)]
  exact (coprime_mul_iff (r * r + s * s) r s).mpr
    ⟨(gcd213_comm (r * r + s * s) r).trans hr, (gcd213_comm (r * r + s * s) s).trans hs⟩

/-- **Pythagorean converse over Nat.**  Given a primitive triple with `a` odd,
    `b` even, `a*a + b*b = c*c` and all positive, there are coprime `m > n > 0`
    with `a + n*n = m*m` (i.e. `a = m²-n²`), `b = 2*(m*n)`, `c = m*m + n*n`. -/
theorem pyth_converse {a b c : Nat}
    (hapos : 0 < a) (hbpos : 0 < b)
    (hco : gcd213 a b = 1) (haodd : a % 2 = 1) (hbeven : b % 2 = 0)
    (heq : a * a + b * b = c * c) :
    ∃ m n, 0 < n ∧ n < m ∧ gcd213 m n = 1 ∧
      a + n * n = m * m ∧ b = 2 * (m * n) ∧ c = m * m + n * n := by
  -- c is odd and a < c.
  have hcodd : c % 2 = 1 := by
    have hcc : (c * c) % 2 = 1 := by
      rw [← heq, E213.Meta.Nat.AddMod213.add_mod_gen (a * a) (b * b) 2,
          sq_odd_of_odd haodd, sq_even_of_even hbeven]
    rw [sq_mod_two] at hcc; exact hcc
  -- a ≤ c  (since a*a ≤ a*a + b*b = c*c, and x ↦ x*x monotone).
  have hale : a ≤ c := by
    have h1 : a * a ≤ c * c := heq ▸ Nat.le_add_right (a * a) (b * b)
    rcases Nat.lt_trichotomy a c with hlt | heqac | hgt
    · exact Nat.le_of_lt hlt
    · exact Nat.le_of_eq heqac
    · exact absurd h1 (Nat.not_le_of_gt
        (Nat.mul_lt_mul_of_lt_of_le hgt (Nat.le_of_lt hgt)
          (Nat.lt_of_le_of_lt (Nat.zero_le c) hgt)))
  -- c = a + 2u
  obtain ⟨u, hu⟩ := odd_sub_odd_eq_two_mul haodd hcodd hale
  -- b*b = (a + 2u)² - a² = 4u(a+u) = 4*u*(a+u)
  have hbb : b * b = 4 * u * (a + u) := by
    have : c * c = a * a + 4 * u * (a + u) := by rw [hu]; ring_nat
    have h2 : a * a + b * b = a * a + 4 * u * (a + u) := by rw [heq, this]
    exact add_left_cancel_213 (a * a) h2
  -- u*v is a square: b = 2w, w² = u*v with v = a+u.
  obtain ⟨w, hw⟩ := even_eq_two_mul hbeven       -- b = 2*w
  have hwsq : w * w = u * (a + u) := by
    have hb4 : 4 * (w * w) = 4 * (u * (a + u)) := by
      have : b * b = 4 * (w * w) := by rw [hw]; ring_nat
      rw [this] at hbb; rw [hbb]; ring_nat
    exact Nat.eq_of_mul_eq_mul_left (by decide) hb4
  -- coprime split: u and (a+u) are both squares.
  have hcouv : gcd213 u (a + u) = 1 := uv_coprime hco hbb
  have hsplit := (coprime_isSquare_mul hcouv).mp ⟨w, hwsq⟩
  obtain ⟨n, hn⟩ := hsplit.1    -- n*n = u
  obtain ⟨m, hm⟩ := hsplit.2    -- m*m = a+u
  -- positivity / ordering
  have hupos : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h0 | hp
    · -- u=0 ⟹ b*b = 0 ⟹ b = 0, contradiction
      exfalso
      have hbb0 : b * b = 0 := by
        rw [hbb, h0]
        rw [Nat.mul_zero, Nat.zero_mul]
      rcases Nat.eq_zero_or_pos b with hb0 | hbp
      · exact absurd hb0 (Nat.ne_of_gt hbpos)
      · exact absurd hbb0 (Nat.ne_of_gt (Nat.mul_pos hbp hbp))
    · exact hp
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hp
    · rw [h0, Nat.mul_zero] at hn; exact absurd hn.symm (Nat.ne_of_gt hupos)
    · exact hp
  have hnm : n < m := by
    -- n*n = u < a + u = m*m, and squaring monotone
    have hlt : n * n < m * m := by
      rw [hn, hm]; exact Nat.lt_add_of_pos_left hapos
    rcases Nat.lt_trichotomy n m with h | h | h
    · exact h
    · exact absurd hlt (by rw [h]; exact Nat.lt_irrefl _)
    · exact absurd hlt (Nat.not_lt_of_le (Nat.mul_le_mul (Nat.le_of_lt h) (Nat.le_of_lt h)))
  -- gcd(m,n) = 1 from gcd(u, a+u) = 1 = gcd(n*n, m*m)
  have hcomn : gcd213 m n = 1 := by
    have h1 : gcd213 (n * n) (m * m) = 1 := by rw [hn, hm]; exact hcouv
    have h2 : gcd213 n m = 1 := coprime_of_coprime_sq h1
    rw [gcd213_comm m n]; exact h2
  refine ⟨m, n, hnpos, hnm, hcomn, ?_, ?_, ?_⟩
  · -- a + n*n = m*m :  n*n = u, m*m = a+u
    rw [hn, hm]
  · -- b = 2*(m*n) :  b = 2w, w² = u*(a+u) = (n*n)*(m*m) = (m*n)*(m*n)
    have hwmn : w = m * n := by
      have hww : w * w = (m * n) * (m * n) := by
        rw [hwsq, ← hm, ← hn]; ring_nat
      exact sq_eq_imp_eq hww
    rw [hw, hwmn]
  · -- c = m*m + n*n :  c = a + 2u, m*m = a+u, n*n = u
    calc c = a + 2 * u := hu
      _ = (a + u) + u := by ring_nat
      _ = m * m + n * n := by rw [hm, hn]

/-- From triple `x*x + n*n = m*m` with `gcd(m,n)=1`, get `gcd(x,n)=1`.
    A common divisor `g` of `x,n` divides `m*m` and `n`, coprime to `m`, so `g=1`. -/
theorem coprime_other_leg {x n m : Nat}
    (hco : gcd213 m n = 1) (heq : x * x + n * n = m * m) :
    gcd213 x n = 1 := by
  have hgx : gcd213 x n ∣ x := gcd213_dvd_left x n
  have hgn : gcd213 x n ∣ n := gcd213_dvd_right x n
  -- g ∣ x*x and g ∣ n*n ⟹ g ∣ m*m
  have hgmm : gcd213 x n ∣ m * m := by
    rw [← heq]
    exact dvd_add_213 _ _ _ (dvd_trans_213 hgx ⟨x, rfl⟩) (dvd_trans_213 hgn ⟨n, rfl⟩)
  -- g ∣ n and gcd(m,n)=1 ⟹ gcd(g,m)=1
  have hgm1 : gcd213 (gcd213 x n) m = 1 := by
    have hh : gcd213 (gcd213 x n) m ∣ gcd213 n m :=
      gcd213_greatest n m _ (dvd_trans_213 (gcd213_dvd_left (gcd213 x n) m) hgn)
        (gcd213_dvd_right (gcd213 x n) m)
    have hnm1 : gcd213 n m = 1 := (gcd213_comm n m).trans hco
    rw [hnm1] at hh
    obtain ⟨c, hc⟩ := hh
    exact mul_eq_one_left _ c hc.symm
  -- g ∣ m*m, gcd(g,m)=1 ⟹ g ∣ m (Euclid) repeatedly ⟹ g=1
  have hgm : gcd213 x n ∣ m := coprime_dvd_of_dvd_mul hgm1 hgmm
  -- g ∣ m and gcd(g,m)=1 ⟹ g ∣ gcd(g,m)... actually g∣m and gcd(g,m)=1 ⟹ g∣1
  have hg1 : gcd213 x n ∣ gcd213 (gcd213 x n) m :=
    gcd213_greatest (gcd213 x n) m _ ⟨1, (Nat.mul_one _).symm⟩ hgm
  rw [hgm1] at hg1
  obtain ⟨c, hc⟩ := hg1
  exact mul_eq_one_left _ c hc.symm

/-! ## §2 — assembly helpers -/

/-- `gcd(x,y)=1 ⟹ gcd(x*x, y*y)=1` (mul form). -/
theorem coprime_sq_mul {x y : Nat} (h : gcd213 x y = 1) :
    gcd213 (x * x) (y * y) = 1 := by
  have hyx : gcd213 y x = 1 := (gcd213_comm y x).trans h
  have h1 : gcd213 (x * x) y = 1 := by
    rw [gcd213_comm (x * x) y]
    exact coprime_mul_of_coprime hyx hyx
  exact coprime_mul_of_coprime h1 h1

/-- `n` is even given `x` odd and primitive triple `x*x + n*n = m*m`. -/
theorem second_leg_even {x n m : Nat}
    (hxodd : x % 2 = 1) (heq : x * x + n * n = m * m) : n % 2 = 0 := by
  rcases mod_two_zero_or_one n with h | h
  · exact h
  · exact absurd (not_both_odd hxodd h heq) (fun f => f.elim)

/-- `k ≤ k*k` for `0 < k`. -/
theorem le_self_mul {k : Nat} (hk : 0 < k) : k ≤ k * k := by
  have h := Nat.mul_le_mul_left k hk
  rwa [Nat.mul_one] at h

/-! ## §3 — the single descent step (the forcing content) -/

/-- **The single descent step.**  From a primitive solution `x⁴+y⁴=z²` with `x`
    odd (so `y` even), construct a strictly smaller primitive solution
    `x'⁴+y'⁴=z'²` with `z' < z`.  The witness `(x',y',z')` is *computed* by two
    applications of the Pythagorean converse and the coprime-square split. -/
theorem descent_step (x y z : Nat)
    (hx : 0 < x) (hy : 0 < y) (hco : gcd213 x y = 1) (hxodd : x % 2 = 1)
    (heq : (x * x) * (x * x) + (y * y) * (y * y) = z * z) :
    ∃ x' y' z', 0 < x' ∧ 0 < y' ∧ gcd213 x' y' = 1 ∧ x' % 2 = 1 ∧
      (x' * x') * (x' * x') + (y' * y') * (y' * y') = z' * z' ∧ z' < z := by
  -- (x², y², z) primitive Pythagorean triple, x² odd, y² even.
  have hx2 : 0 < x * x := Nat.mul_pos hx hx
  have hy2 : 0 < y * y := Nat.mul_pos hy hy
  have hco2 : gcd213 (x * x) (y * y) = 1 := coprime_sq_mul hco
  have hx2odd : (x * x) % 2 = 1 := sq_odd_of_odd hxodd
  have hy2even : (y * y) % 2 = 0 := second_leg_even hx2odd heq
  -- first converse: a=x², b=y², c=z ⟹ m,n.
  obtain ⟨m, n, hnpos, hnm, hcomn, hxn, hyy, hz⟩ :=
    pyth_converse hx2 hy2 hco2 hx2odd hy2even heq
  --   hxn : x*x + n*n = m*m ;  hyy : y*y = 2*(m*n) ;  hz : z = m*m + n*n
  have hmpos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le n) hnm
  -- triple (x, n, m): gcd(x,n)=1, x odd, n even.
  have hcoxn : gcd213 x n = 1 := coprime_other_leg hcomn hxn
  have hneven : n % 2 = 0 := second_leg_even hxodd hxn
  -- second converse: a=x, b=n, c=m ⟹ r,s.
  obtain ⟨r, s, hspos, hsr, hcors, hxs, hn2, hm2⟩ :=
    pyth_converse hx hnpos hcoxn hxodd hneven hxn
  --   hxs : x + s*s = r*r ;  hn2 : n = 2*(r*s) ;  hm2 : m = r*r + s*s
  have hrpos : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le s) hsr
  -- y even (y*y = 2*(m*n) is even).
  have hyeven : y % 2 = 0 := by
    have : (y * y) % 2 = 0 := by rw [hyy]; exact E213.Meta.Nat.NatDiv213.mul_mod_self_pure 2 (m * n)
    rwa [sq_mod_two] at this
  obtain ⟨w, hw⟩ := even_eq_two_mul hyeven      -- y = 2*w
  -- w*w = r*s*(r*r+s*s).
  have hwsq : w * w = r * s * (r * r + s * s) := by
    -- 4*(w*w) = y*y = 2*(m*n) = 2*((r*r+s*s)*(2*(r*s))) = 4*(r*s*(r*r+s*s))
    have h4 : 4 * (w * w) = 4 * (r * s * (r * r + s * s)) := by
      have e1 : y * y = 4 * (w * w) := by rw [hw]; ring_nat
      have e2 : y * y = 2 * (m * n) := hyy
      have e3 : 2 * (m * n) = 4 * (r * s * (r * r + s * s)) := by
        rw [hm2, hn2]; ring_nat
      rw [e1] at e2; rw [e2, e3]
    exact Nat.eq_of_mul_eq_mul_left (by decide) h4
  -- coprime split: r*s and (r²+s²) both squares; then r,s both squares.
  have hco_prod : gcd213 (r * s) (r * r + s * s) = 1 := coprime_prod_sum hcors
  have hsplit1 := (coprime_isSquare_mul hco_prod).mp ⟨w, hwsq⟩
  -- hsplit1.1 : IsSquare (r*s) ; hsplit1.2 : IsSquare (r²+s²)
  have hsplit2 := (coprime_isSquare_mul hcors).mp hsplit1.1
  obtain ⟨a, ha⟩ := hsplit2.1        -- a*a = r
  obtain ⟨b, hb⟩ := hsplit2.2        -- b*b = s
  obtain ⟨c, hc⟩ := hsplit1.2         -- c*c = r²+s²
  -- positivity of a, b.
  have hapos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | hp
    · rw [h0, Nat.mul_zero] at ha; exact absurd ha.symm (Nat.ne_of_gt hrpos)
    · exact hp
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h0 | hp
    · rw [h0, Nat.mul_zero] at hb; exact absurd hb.symm (Nat.ne_of_gt hspos)
    · exact hp
  -- new equation: (a²)² + (b²)² = c*c, since a²=r,b²=s,c²=r²+s².
  have hnewdq : (a * a) * (a * a) + (b * b) * (b * b) = c * c := by
    rw [ha, hb, hc]
  -- gcd(a,b)=1 from gcd(r,s)=1 = gcd(a²,b²).
  have hcoab : gcd213 a b = 1 := by
    have h1 : gcd213 (a * a) (b * b) = 1 := by rw [ha, hb]; exact hcors
    exact coprime_of_coprime_sq h1
  -- a odd: r = a² and r is odd? r,s opposite parity in primitive triple (x,n,m);
  -- x odd, n=2rs even ⟹ one of r,s even; r²+s²=m and gcd(r,s)=1.
  -- We do NOT need a odd for the recursive solution shape required here, but the
  -- wrapper re-derives parity.  Provide a odd via: a*a = r, and r odd OR even.
  -- Establish a odd: in triple (x,n,m), x = r²-s² odd, so r,s opposite parity;
  -- exactly one of a,b is odd.  We may have a even.  To keep the existential's
  -- `x' % 2 = 1` slot, pick the odd one of (a,b).  r²+s² = c² with r,s coprime
  -- opposite parity ⟹ c odd; and a,b opposite parity (a²=r,b²=s).
  -- We branch on parity of a.
  -- c*c = r²+s² = m, so c ≤ m (c ≤ c*c), m ≤ m*m < z.
  have hcm : c * c = m := by rw [hc, hm2]
  have hcle_z : c < z := by
    -- c ≤ c*c = m ≤ m*m < m*m + n*n = z
    have hc_pos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | hp
      · rw [h0, Nat.mul_zero] at hcm
        exact absurd hcm.symm (Nat.ne_of_gt hmpos)
      · exact hp
    have h1 : c ≤ c * c := le_self_mul hc_pos
    have h2 : c * c ≤ m * m := by rw [hcm]; exact le_self_mul hmpos
    have h3 : m * m < m * m + n * n := by
      have hnn : 0 < n * n := Nat.mul_pos hnpos hnpos
      exact Nat.lt_add_of_pos_right hnn
    have h4 : m * m + n * n = z := hz.symm
    calc c ≤ c * c := h1
      _ ≤ m * m := h2
      _ < m * m + n * n := h3
      _ = z := h4
  -- Branch on parity of a to fill the `x' odd` slot.
  rcases mod_two_zero_or_one a with haeven | haodd
  · -- a even ⟹ b odd (a,b opposite parity since a²=r,b²=s opposite parity).
    have hbodd : b % 2 = 1 := by
      -- a even ⟹ a*a=r even; r²+s²=c² ; if b even then a,b both even ⟹ gcd≥2.
      rcases mod_two_zero_or_one b with hbev | hbod
      · exfalso
        -- gcd(a,b) ≥ 2 contradiction
        have h2a : (2 : Nat) ∣ a := E213.Meta.Nat.AddMod213.dvd_of_mod_eq_zero haeven
        have h2b : (2 : Nat) ∣ b := E213.Meta.Nat.AddMod213.dvd_of_mod_eq_zero hbev
        have hg2 : (2 : Nat) ∣ gcd213 a b := gcd213_greatest a b 2 h2a h2b
        rw [hcoab] at hg2
        -- 2 ∣ 1 is impossible
        obtain ⟨k, hk⟩ := hg2     -- 1 = 2 * k
        cases k with
        | zero => exact absurd hk (by decide)
        | succ k' =>
          have : (2 : Nat) ≤ 1 := hk ▸ Nat.le_mul_of_pos_right 2 (Nat.succ_pos k')
          exact absurd this (by decide)
      · exact hbod
    -- swap: use (b, a, c) as (x', y', z'); gcd symmetric.
    refine ⟨b, a, c, hbpos, hapos, (gcd213_comm b a).trans hcoab, hbodd, ?_, hcle_z⟩
    -- (b²)²+(a²)² = c*c
    calc (b * b) * (b * b) + (a * a) * (a * a)
        = (a * a) * (a * a) + (b * b) * (b * b) := by ring_nat
      _ = c * c := hnewdq
  · -- a odd: use (a, b, c).
    exact ⟨a, b, c, hapos, hbpos, hcoab, haodd, hnewdq, hcle_z⟩

/-! ## §4 — strong-induction wrapper: no primitive odd solution -/

/-- No primitive solution with `x` odd: strong induction on `z`, the descent map
    `descent_step` as the strictly-decreasing constructor. -/
theorem no_primitive_odd : ∀ z x y, 0 < x → 0 < y → gcd213 x y = 1 → x % 2 = 1 →
    (x * x) * (x * x) + (y * y) * (y * y) = z * z → False := by
  intro z
  induction z using Nat.strongRecOn with
  | ind z ih =>
    intro x y hx hy hco hxodd heq
    obtain ⟨x', y', z', hx', hy', hco', hx'odd, heq', hz'⟩ :=
      descent_step x y z hx hy hco hxodd heq
    exact ih z' hz' x' y' hx' hy' hco' hx'odd heq'

/-- No primitive solution (either parity): one of `x,y` is odd, swap to fit
    `no_primitive_odd`. -/
theorem no_primitive : ∀ x y z, 0 < x → 0 < y → gcd213 x y = 1 →
    (x * x) * (x * x) + (y * y) * (y * y) = z * z → False := by
  intro x y z hx hy hco heq
  -- not both even (coprime), not both odd (mod 4) ⟹ exactly one odd.
  rcases mod_two_zero_or_one x with hxe | hxo
  · -- x even ⟹ y odd (else both even, gcd ≥ 2).
    have hyo : y % 2 = 1 := by
      rcases mod_two_zero_or_one y with hye | hyo
      · exfalso
        have h2x : (2 : Nat) ∣ x := E213.Meta.Nat.AddMod213.dvd_of_mod_eq_zero hxe
        have h2y : (2 : Nat) ∣ y := E213.Meta.Nat.AddMod213.dvd_of_mod_eq_zero hye
        have hg2 : (2 : Nat) ∣ gcd213 x y := gcd213_greatest x y 2 h2x h2y
        rw [hco] at hg2
        obtain ⟨k, hk⟩ := hg2
        cases k with
        | zero => exact absurd hk (by decide)
        | succ k' =>
          exact absurd (hk ▸ Nat.le_mul_of_pos_right 2 (Nat.succ_pos k')) (by decide)
      · exact hyo
    -- swap x ↔ y
    exact no_primitive_odd z y x hy hx ((gcd213_comm y x).trans hco) hyo
      (by calc (y * y) * (y * y) + (x * x) * (x * x)
            = (x * x) * (x * x) + (y * y) * (y * y) := by ring_nat
          _ = z * z := heq)
  · exact no_primitive_odd z x y hx hy hco hxo heq

/-! ## §5 — gcd reduction + the full theorem -/

open E213.Meta.Nat.Valuation (vp pow_vp_dvd le_vp_iff)
open E213.Meta.Nat.VpMul (IsPrime213 vp_mul)
open E213.Meta.Nat.VpSeparation (dvd_of_forall_vp_le)

/-- `a*a ∣ b*b → a ∣ b` over `Nat` (via `vp`-comparison; ∅-axiom). -/
theorem sq_dvd_sq_imp_dvd {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (h : a * a ∣ b * b) : a ∣ b := by
  refine dvd_of_forall_vp_le ha hb (fun p hp => ?_)
  have hbb : 0 < b * b := Nat.mul_pos hb hb
  -- vp p (a*a) ≤ vp p (b*b)
  have hmono : vp p (a * a) ≤ vp p (b * b) :=
    (le_vp_iff p (b * b) (vp p (a * a)) hp.1 hbb).mp (dvd_trans_213 (pow_vp_dvd p (a * a)) h)
  rw [vp_mul hp ha ha, vp_mul hp hb hb] at hmono
  -- 2*(vp p a) ≤ 2*(vp p b) ⟹ vp p a ≤ vp p b
  exact E213.Meta.Nat.NatDiv213.two_cancel (vp p a) (vp p b)
    (by rw [Nat.two_mul, Nat.two_mul]; exact hmono)

/-- **Fermat's right-triangle theorem.**  No positive `x, y, z` with
    `x⁴ + y⁴ = z²` (the `Nat.mul` quartic form).  Reduce to a primitive solution
    (gcd-strip), then descent via `no_primitive`. -/
theorem no_quartic_sq : ∀ x y z : Nat, 0 < x → 0 < y →
    (x * x) * (x * x) + (y * y) * (y * y) ≠ z * z := by
  intro x y z hx hy heq
  -- g := gcd(x,y) > 0 ; x = g*x₁, y = g*y₁, gcd(x₁,y₁)=1.
  have hgpos : 0 < gcd213 x y := by
    rcases Nat.eq_zero_or_pos (gcd213 x y) with h0 | hp
    · obtain ⟨c, hc⟩ := gcd213_dvd_left x y
      rw [h0, Nat.zero_mul] at hc
      exact absurd (hc ▸ hx) (Nat.lt_irrefl 0)
    · exact hp
  -- abstract g := gcd213 x y
  obtain ⟨g, hg, hgp⟩ : ∃ g, gcd213 x y = g ∧ 0 < g := ⟨gcd213 x y, rfl, hgpos⟩
  obtain ⟨x1, hx1⟩ := gcd213_dvd_left x y    -- x = gcd * x1
  obtain ⟨y1, hy1⟩ := gcd213_dvd_right x y   -- y = gcd * y1
  rw [hg] at hx1 hy1                          -- x = g*x1, y = g*y1
  have hco1 : gcd213 x1 y1 = 1 :=
    gcd_strip_coprime hg hgp hx1 hy1
  have hx1pos : 0 < x1 := by
    rcases Nat.eq_zero_or_pos x1 with h0 | hp
    · rw [h0, Nat.mul_zero] at hx1; exact absurd (hx1 ▸ hx) (Nat.lt_irrefl 0)
    · exact hp
  have hy1pos : 0 < y1 := by
    rcases Nat.eq_zero_or_pos y1 with h0 | hp
    · rw [h0, Nat.mul_zero] at hy1; exact absurd (hy1 ▸ hy) (Nat.lt_irrefl 0)
    · exact hp
  -- LHS = (g²)² * (x1⁴ + y1⁴) = z*z ⟹ (g*g)*(g*g) ∣ z*z ⟹ g*g ∣ z.
  have hgg_pos : 0 < g * g := Nat.mul_pos hgp hgp
  have hbig : ((g * g) * (g * g)) *
      ((x1 * x1) * (x1 * x1) + (y1 * y1) * (y1 * y1)) = z * z := by
    rw [← heq, hx1, hy1]; ring_nat
  have hdvd_zz : (g * g) * (g * g) ∣ z * z := ⟨_, hbig.symm⟩
  have hgg_dvd_z : (g * g) ∣ z := by
    rcases Nat.eq_zero_or_pos z with hz0 | hzp
    · exact ⟨0, by rw [hz0, Nat.mul_zero]⟩
    · exact sq_dvd_sq_imp_dvd hgg_pos hzp hdvd_zz
  obtain ⟨z1, hz1⟩ := hgg_dvd_z       -- z = (g*g) * z1
  have hz1pos : 0 < z1 := by
    rcases Nat.eq_zero_or_pos z1 with h0 | hp
    · -- z = 0 ⟹ LHS = 0, but (g²)²·(x1⁴+y1⁴) > 0
      exfalso
      rw [h0, Nat.mul_zero] at hz1
      rw [hz1, Nat.mul_zero] at hbig
      have hpos1 : 0 < (x1 * x1) * (x1 * x1) + (y1 * y1) * (y1 * y1) :=
        Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.mul_pos hx1pos hx1pos)
          (Nat.mul_pos hx1pos hx1pos)) (Nat.le_add_right _ _)
      have hggsq : 0 < (g * g) * (g * g) := Nat.mul_pos hgg_pos hgg_pos
      exact absurd hbig (Nat.ne_of_gt (Nat.mul_pos hggsq hpos1))
    · exact hp
  -- cancel (g²)² to get x1⁴ + y1⁴ = z1².
  have heq1 : (x1 * x1) * (x1 * x1) + (y1 * y1) * (y1 * y1) = z1 * z1 := by
    have hggsq_pos : 0 < (g * g) * (g * g) := Nat.mul_pos hgg_pos hgg_pos
    apply Nat.eq_of_mul_eq_mul_left hggsq_pos
    rw [hbig, hz1]; ring_nat
  exact no_primitive x1 y1 z1 hx1pos hy1pos hco1 heq1

/-- **Fermat n=4.**  No positive `x, y, z` with `x⁴ + y⁴ = z⁴`
    (corollary: `z⁴ = (z²)²`). -/
theorem no_quartic_quartic : ∀ x y z : Nat, 0 < x → 0 < y →
    (x * x) * (x * x) + (y * y) * (y * y) ≠ (z * z) * (z * z) := by
  intro x y z hx hy heq
  exact no_quartic_sq x y (z * z) hx hy heq

end E213.Lib.Math.NumberTheory.FermatQuartic
