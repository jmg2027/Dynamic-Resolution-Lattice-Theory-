import E213.Lib.Math.NumberTheory.ModArith.EulerCriterion
import E213.Lib.Math.NumberTheory.ModArith.NonFixedExists
import E213.Lib.Math.NumberTheory.PolyRoot.RootBound
import E213.Lib.Math.NumberTheory.PolyRoot.CyclotomicPoly
import E213.Lib.Math.NumberTheory.PolyRoot.ResidueList

/-!
# EulerConverse — Euler's criterion, the converse (`aᵐ ≡ 1 ⟹ a` is a QR)

The landmark direction, by **root-count saturation** of Lagrange's bound (`RootBound.eval_zero`),
exactly the shape of `NonFixedExists.exists_nonfixed_gen` run on `Xᵐ − 1`:

- the `m` squares `[1², 2², …, m²]` are `m` pairwise-distinct-mod-`p` roots of `Xᵐ − 1`
  (each `(i²)ᵐ = i^(2m) = i^(p−1) ≡ 1` by FLT; distinct because `i²−j² = (i−j)(i+j)` with both
  factors in `(0, p)`, so `p` divides neither);
- if `a` (with `aᵐ ≡ 1`) were *not* a square, `↑a :: [the m squares]` would be `m+1` distinct
  roots of the length-`(m+1)` polynomial `Xᵐ − 1`, so `eval_zero` forces its constant
  coefficient `−1 ≡ 0 (mod p)` — impossible.  Hence `a` is a square.

The witness is produced constructively by a bounded search `firstSqrt`, whose `none`-branch is
refuted by the saturation contradiction.

  * ★★★★★ `euler_converse` — `aᵐ ≡ 1 (mod p)` ⟹ `∃ x, x² ≡ a (mod p)`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.EulerConverse

open E213.Lib.Math.NumberTheory.PolyRoot
open E213.Lib.Math.NumberTheory.PolyRoot
  (eval pmoSucc eval_pmoSucc pmoSucc_length eval_pmoSucc_zero eval_zero natCast_add
   nat_dvd_to_int int_dvd_to_nat)
open E213.Lib.Math.NumberTheory.ModArith.NonFixedExists (natCast_pow natCast_sub_one)
open E213.Lib.Math.NumberTheory.ModArith.EulerCriterion (euler_qr_pow_one)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
  (pow_mul_loc prime_coprime modBezout_gcd_one sq_expand)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)
open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT (dvd_sub_one_of_mod_one one_le_pow' pow_add_pure)
open E213.Lib.Math.NumberTheory.ModArith.UniversalFLT (universal_flt_main)
open E213.Meta.Nat.Gcd213 (gcd213_comm)
open E213.Tactic.NatHelper (gcd213 sub_add_cancel add_sub_cancel_right add_sub_of_le mul_mod_right)
open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod)
open E213.Lib.Math.NumberTheory.ModArith.ModBezout (modBezout)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-! ## §0 — local helpers (cast / mod bridges, re-derived prime-gcd) -/

/-- `QRNegOne.prime_gcd` (private), re-derived: a residue `0 < m < p` is coprime to a prime `p`. -/
private theorem prime_gcd (p : Nat) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    ∀ m, 0 < m → m < p → (modBezout m p).1 = 1 := by
  intro m hm0 hmlt
  have hnp : ¬ p ∣ m := fun hpm => absurd (le_of_dvd_pos p m hm0 hpm) (Nat.not_le.mpr hmlt)
  have hco' : gcd213 m p = 1 := by rw [gcd213_comm]; exact prime_coprime p m hpr hnp
  exact modBezout_gcd_one m p hco'

/-- `↑(a − b) = ↑a − ↑b` for `b ≤ a` (pure cast-of-subtraction). -/
theorem natCast_sub (a b : Nat) (h : b ≤ a) : ((a - b : Nat) : Int) = (a : Int) - (b : Int) := by
  have hc : ((a - b : Nat) : Int) + (b : Int) = (a : Int) := by
    rw [← natCast_add (a - b) b, sub_add_cancel h]
  rw [← hc]; ring_intZ

/-- `i² = i·i` (pure). -/
theorem sq_nat (i : Nat) : i ^ 2 = i * i := by
  rw [show (2 : Nat) = 1 + 1 from rfl, pow_add_pure i 1 1, Nat.pow_one]

/-- `n ∣ (a − b)`, `b ≤ a` ⟹ `a % n = b % n` (converse of `mod_eq_dvd_sub`). -/
theorem mod_eq_of_dvd_sub (n a b : Nat) (hab : b ≤ a) (hd : n ∣ (a - b)) : a % n = b % n := by
  obtain ⟨k, hk⟩ := hd
  have ha : a = b + n * k := by
    have h1 : (a - b) + b = a := sub_add_cancel hab
    rw [hk, Nat.add_comm (n * k) b] at h1; exact h1.symm
  rw [ha, add_mod_gen b (n * k) n, mul_mod_right n k, Nat.add_zero, mod_mod]

/-- `↑p ∣ (↑a − ↑b)` ⟹ `a % p = b % p`.  Sign-split on `a` vs `b`, then `mod_eq_of_dvd_sub`. -/
theorem dvd_int_sub_to_mod_eq (p a b : Nat) (hp : 0 < p)
    (h : (p : Int) ∣ ((a : Int) - (b : Int))) : a % p = b % p := by
  have hnat : p ∣ ((a : Int) - (b : Int)).natAbs := int_dvd_to_nat p _ h
  rcases Nat.le_total b a with hba | hab
  · have habs : ((a : Int) - (b : Int)).natAbs = a - b := by
      rw [← natCast_sub a b hba, Int.natAbs_ofNat]
    rw [habs] at hnat
    exact mod_eq_of_dvd_sub p a b hba hnat
  · have habs : ((a : Int) - (b : Int)).natAbs = b - a := by
      have e : (a : Int) - (b : Int) = -(((b - a : Nat)) : Int) := by
        rw [natCast_sub b a hab]; ring_intZ
      rw [e, Int.natAbs_neg, Int.natAbs_ofNat]
    rw [habs] at hnat
    exact (mod_eq_of_dvd_sub p b a hab hnat).symm

/-! ## §1 — the squares window `[lo², (lo+1)², …]` -/

/-- `[lo², (lo+1)², …, (lo+n−1)²]` as a list of `Int` (head = smallest). -/
def sqFrom (lo : Nat) : Nat → List Int
  | 0 => []
  | n + 1 => ((lo * lo : Nat) : Int) :: sqFrom (lo + 1) n

theorem sqFrom_length (lo : Nat) : ∀ n, (sqFrom lo n).length = n
  | 0 => rfl
  | n + 1 => by show (sqFrom (lo + 1) n).length + 1 = n + 1; rw [sqFrom_length]

/-- Every element of `sqFrom lo n` is `↑(i·i)` for `lo ≤ i < lo + n`. -/
theorem mem_sqFrom : ∀ (n lo : Nat) {x : Int},
    x ∈ sqFrom lo n → ∃ i : Nat, lo ≤ i ∧ i < lo + n ∧ x = ((i * i : Nat) : Int) := by
  intro n
  induction n with
  | zero => intro lo x h; exact absurd h (List.not_mem_nil x)
  | succ n ih =>
    intro lo x h
    have h' : x ∈ ((lo * lo : Nat) : Int) :: sqFrom (lo + 1) n := h
    cases h' with
    | head => exact ⟨lo, Nat.le_refl lo, Nat.lt_add_of_pos_right (Nat.succ_pos n), rfl⟩
    | tail _ hm =>
      obtain ⟨i, hge, hlt, hx⟩ := ih (lo + 1) hm
      refine ⟨i, Nat.le_of_succ_le hge, ?_, hx⟩
      have e1 : (lo + 1) + n = lo + (n + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 n]
      rw [← e1]; exact hlt

/-! ## §2 — two distinct squares differ by a non-multiple of `p` -/

/-- `i < j`, `1 ≤ i`, `i + j < p` ⟹ `p ∤ (i² − j²)` over `ℤ`: factor `j²−i² = (j−i)(j+i)`, both
    factors in `(0, p)`, so `p` (prime) divides neither (`nat_prime_dvd_mul`). -/
theorem sq_diff_not_dvd (p i j : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hi1 : 1 ≤ i) (hij : i < j) (hsum : i + j < p) :
    ¬ (p : Int) ∣ (((i * i : Nat) : Int) - ((j * j : Nat) : Int)) := by
  intro hd
  have hile : i * i ≤ j * j := Nat.mul_le_mul (Nat.le_of_lt hij) (Nat.le_of_lt hij)
  have hnat : p ∣ (((i * i : Nat) : Int) - ((j * j : Nat) : Int)).natAbs := int_dvd_to_nat p _ hd
  have habs : (((i * i : Nat) : Int) - ((j * j : Nat) : Int)).natAbs = j * j - i * i := by
    have e : ((i * i : Nat) : Int) - ((j * j : Nat) : Int) = -(((j * j - i * i : Nat)) : Int) := by
      rw [natCast_sub (j * j) (i * i) hile]; ring_intZ
    rw [e, Int.natAbs_neg, Int.natAbs_ofNat]
  rw [habs] at hnat
  have hfac : j * j - i * i = (j - i) * (j + i) := by
    obtain ⟨d, hd'⟩ : ∃ d, j = i + d := ⟨j - i, (add_sub_of_le (Nat.le_of_lt hij)).symm⟩
    subst hd'
    have hji : (i + d) - i = d := by rw [Nat.add_comm i d, add_sub_cancel_right]
    have hsum2 : (i + d) + i = 2 * i + d := by ring_nat
    rw [sq_expand i d, Nat.add_comm (i * i) (d * (2 * i + d)), add_sub_cancel_right, hji, hsum2]
  rw [hfac] at hnat
  have hi0 : 0 < i := Nat.lt_of_lt_of_le Nat.zero_lt_one hi1
  have hjp : j < p := by
    have hji' : j < i + j := by
      calc j = 0 + j := (Nat.zero_add j).symm
        _ < i + j := Nat.add_lt_add_right hi0 j
    exact Nat.lt_trans hji' hsum
  rcases nat_prime_dvd_mul p hp hpr (j - i) (j + i) hnat with h1 | h2
  · have hpos : 0 < j - i := by
      obtain ⟨e, he⟩ := Nat.le.dest (Nat.le_of_lt hij)
      have he1 : 1 ≤ e := by
        rcases Nat.eq_zero_or_pos e with h0 | h0
        · exfalso; rw [h0, Nat.add_zero] at he; exact Nat.lt_irrefl i (he ▸ hij)
        · exact h0
      rw [← he, Nat.add_comm i e, add_sub_cancel_right]; exact he1
    have hlt : j - i < p := Nat.lt_of_le_of_lt (Nat.sub_le j i) hjp
    exact absurd (le_of_dvd_pos p (j - i) hpos h1) (Nat.not_le.mpr hlt)
  · have hpos : 0 < j + i := Nat.le_trans hi1 (Nat.le_add_left i j)
    have hlt : j + i < p := by rw [Nat.add_comm]; exact hsum
    exact absurd (le_of_dvd_pos p (j + i) hpos h2) (Nat.not_le.mpr hlt)

/-! ## §3 — the squares window is pairwise-distinct mod `p` -/

theorem sqFrom_pairwise (p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) :
    ∀ (n lo : Nat), 1 ≤ lo → lo + n ≤ m + 1 →
      (sqFrom lo n).Pairwise (fun a b => ¬ (p : Int) ∣ (a - b)) := by
  intro n
  induction n with
  | zero => intro lo _ _; exact List.Pairwise.nil
  | succ n ih =>
    intro lo hlo hbound
    have hshow : sqFrom lo (n + 1) = ((lo * lo : Nat) : Int) :: sqFrom (lo + 1) n := rfl
    rw [hshow]
    have e1 : (lo + 1) + n = lo + (n + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 n]
    have hlom : lo ≤ m :=
      Nat.le_of_succ_le_succ (Nat.le_trans (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le n)) lo) hbound)
    refine List.pairwise_cons.mpr ⟨?_, ?_⟩
    · intro y hy
      obtain ⟨j, hjge, hjlt, hyj⟩ := mem_sqFrom n (lo + 1) hy
      have hloj : lo < j := Nat.lt_of_lt_of_le (Nat.lt_succ_self lo) hjge
      have hjm : j ≤ m := by
        have hj : j < lo + (n + 1) := e1 ▸ hjlt
        exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hj hbound)
      have hsum : lo + j < p := by
        have hle : lo + j ≤ 2 * m := by
          calc lo + j ≤ m + m := Nat.add_le_add hlom hjm
            _ = 2 * m := (Nat.two_mul m).symm
        rw [h2m] at hle
        exact Nat.lt_of_le_of_lt hle (Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)) Nat.zero_lt_one)
      rw [hyj]
      exact sq_diff_not_dvd p lo j hp hpr hlo hloj hsum
    · exact ih (lo + 1) (Nat.le_succ_of_le hlo) (by rw [e1]; exact hbound)

/-! ## §4 — each square is a root of `Xᵐ − 1` -/

theorem sqFrom_roots (p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) :
    ∀ r ∈ sqFrom 1 m, (p : Int) ∣ eval (pmoSucc (m - 1)) r := by
  intro r hr
  obtain ⟨i, hi1, hilt, hri⟩ := mem_sqFrom m 1 hr
  have hile : i ≤ m := Nat.le_of_lt_succ (by rw [Nat.add_comm] at hilt; exact hilt)
  have hm_le : m ≤ p - 1 := by rw [← h2m]; exact Nat.le_mul_of_pos_left m (by decide)
  have hmp : m < p :=
    Nat.lt_of_le_of_lt hm_le (Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)) Nat.zero_lt_one)
  have hilp : i < p := Nat.lt_of_le_of_lt hile hmp
  have hpg := prime_gcd p hpr
  have hsqm : (i * i) ^ m % p = 1 := by
    rw [← sq_nat i, ← pow_mul_loc i 2 m, h2m]
    have h := universal_flt_main i p hp hi1 hilp hpg
    rwa [Nat.mod_eq_of_lt hp] at h
  have hm1eq : (m - 1) + 1 = m := sub_add_cancel hm1
  rw [hri, eval_pmoSucc, hm1eq, ← natCast_pow (i * i) m,
      ← natCast_sub_one ((i * i) ^ m) (one_le_pow' (i * i) (Nat.mul_le_mul hi1 hi1) m)]
  exact nat_dvd_to_int p _ (by rw [Int.natAbs_ofNat]; exact dvd_sub_one_of_mod_one p ((i * i) ^ m) hsqm)

/-! ## §5 — the bounded square-root search + the saturation closure -/

/-- Search `bound, …, 1` for the first `x` with `x² % p = a`. -/
def firstSqrt (p a : Nat) : Nat → Option Nat
  | 0 => none
  | k + 1 => if (k + 1) ^ 2 % p = a then some (k + 1) else firstSqrt p a k

theorem firstSqrt_some (p a : Nat) : ∀ (bound x : Nat),
    firstSqrt p a bound = some x → 1 ≤ x ∧ x ≤ bound ∧ x ^ 2 % p = a := by
  intro bound
  induction bound with
  | zero => intro x h; exact Option.noConfusion h
  | succ k ih =>
    intro x h
    rw [firstSqrt] at h
    by_cases hc : (k + 1) ^ 2 % p = a
    · rw [if_pos hc] at h
      have hx : k + 1 = x := Option.some.inj h
      subst hx; exact ⟨Nat.succ_pos k, Nat.le_refl _, hc⟩
    · rw [if_neg hc] at h
      obtain ⟨h1, h2, h3⟩ := ih x h
      exact ⟨h1, Nat.le_succ_of_le h2, h3⟩

theorem firstSqrt_none (p a : Nat) : ∀ (bound : Nat),
    firstSqrt p a bound = none → ∀ i, 1 ≤ i → i ≤ bound → i ^ 2 % p ≠ a := by
  intro bound
  induction bound with
  | zero => intro _ i h1 h2; exact absurd (Nat.le_trans h1 h2) (by decide)
  | succ k ih =>
    intro h i h1 h2
    rw [firstSqrt] at h
    by_cases hc : (k + 1) ^ 2 % p = a
    · rw [if_pos hc] at h; exact Option.noConfusion h
    · rw [if_neg hc] at h
      rcases Nat.lt_or_eq_of_le h2 with hlt | heq
      · exact ih h i h1 (Nat.le_of_lt_succ hlt)
      · subst heq; exact hc

/-- ★★★★★ **Euler's criterion — the converse.**  `p` prime, `2m = p−1`, unit `1 ≤ a < p`,
    `p ∣ (aᵐ − 1)` (`aᵐ ≡ 1`) ⟹ `a` is a quadratic residue (`∃ x, 1 ≤ x ∧ x < p ∧ x² ≡ a`).
    Squares-list saturation of `RootBound.eval_zero`: a non-square `a` would give `m+1` distinct
    roots of `Xᵐ − 1` (length `m+1`), forcing its constant coefficient `−1 ≡ 0 mod p`. -/
theorem euler_converse (p m a : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (ha1 : 1 ≤ a) (halt : a < p)
    (hpow : p ∣ (a ^ m - 1)) :
    ∃ x : Nat, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = a := by
  have hp1lt : p - 1 < p :=
    Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)) Nat.zero_lt_one
  cases hfn : firstSqrt p a (p - 1) with
  | some x =>
    obtain ⟨h1, h2, h3⟩ := firstSqrt_some p a (p - 1) x hfn
    exact ⟨x, h1, Nat.lt_of_le_of_lt h2 hp1lt, h3⟩
  | none =>
    exfalso
    have hnone := firstSqrt_none p a (p - 1) hfn
    have hm1eq : (m - 1) + 1 = m := sub_add_cancel hm1
    -- the pairwise list ↑a :: [the m squares]
    have hsq_pw := sqFrom_pairwise p m hp hpr h2m m 1 (Nat.le_refl 1)
      (by rw [Nat.add_comm 1 m]; exact Nat.le_refl (m + 1))
    have hcross : ∀ y ∈ sqFrom 1 m, ¬ (p : Int) ∣ (((a : Nat) : Int) - y) := by
      intro y hy
      obtain ⟨i, hi1, hilt, hyi⟩ := mem_sqFrom m 1 hy
      have hile : i ≤ m := Nat.le_of_lt_succ (by rw [Nat.add_comm] at hilt; exact hilt)
      have hip : i ≤ p - 1 := Nat.le_trans hile (by rw [← h2m]; exact Nat.le_mul_of_pos_left m (by decide))
      intro hd
      rw [hyi] at hd
      have hmodeq : a % p = (i * i) % p :=
        dvd_int_sub_to_mod_eq p a (i * i) (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)) hd
      rw [Nat.mod_eq_of_lt halt] at hmodeq
      have hne : i ^ 2 % p ≠ a := hnone i hi1 hip
      rw [sq_nat i] at hne
      exact hne hmodeq.symm
    have hpw : (((a : Nat) : Int) :: sqFrom 1 m).Pairwise (fun u v => ¬ (p : Int) ∣ (u - v)) :=
      List.pairwise_cons.mpr ⟨hcross, hsq_pw⟩
    have hroots : ∀ r ∈ (((a : Nat) : Int) :: sqFrom 1 m), (p : Int) ∣ eval (pmoSucc (m - 1)) r := by
      intro r hr
      cases hr with
      | head =>
        rw [eval_pmoSucc, hm1eq, ← natCast_pow a m, ← natCast_sub_one (a ^ m) (one_le_pow' a ha1 m)]
        exact nat_dvd_to_int p _ (by rw [Int.natAbs_ofNat]; exact hpow)
      | tail _ hmem => exact sqFrom_roots p m hp hpr h2m hm1 r hmem
    have hlen : (pmoSucc (m - 1)).length ≤ (((a : Nat) : Int) :: sqFrom 1 m).length := by
      rw [pmoSucc_length, List.length_cons, sqFrom_length]
      exact Nat.le_of_eq (by rw [show (m - 1) + 2 = ((m - 1) + 1) + 1 from rfl, hm1eq])
    have hvanish := eval_zero p hp hpr (pmoSucc (m - 1)).length (pmoSucc (m - 1)) (Nat.le_refl _)
      (((a : Nat) : Int) :: sqFrom 1 m) hpw hroots hlen 0
    rw [eval_pmoSucc_zero] at hvanish
    have hd1 : p ∣ Int.natAbs (-1) := int_dvd_to_nat p (-1) hvanish
    have hple : p ≤ 1 := le_of_dvd_pos p (Int.natAbs (-1)) (by decide) hd1
    exact absurd hple (Nat.not_le.mpr hp)

/-- ★★★★★ **Euler's criterion (full).**  For a prime `p`, `2m = p − 1` (the odd-prime witness),
    and a unit `1 ≤ a < p`:  `aᵐ ≡ 1 (mod p)` **iff** `a` is a quadratic residue mod `p`.
    Forward = `euler_converse` (squares-list saturation of Lagrange's bound); backward =
    `euler_qr_pow_one` (the residue computes to `+1` by FLT). -/
theorem euler_criterion (p m a : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (ha1 : 1 ≤ a) (halt : a < p) :
    p ∣ (a ^ m - 1) ↔ ∃ x : Nat, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = a := by
  constructor
  · intro hpow; exact euler_converse p m a hp hpr h2m hm1 ha1 halt hpow
  · rintro ⟨x, hx1, hxlt, hx2⟩
    exact euler_qr_pow_one p m a hp hpr h2m x hx1 hxlt hx2

end E213.Lib.Math.NumberTheory.ModArith.EulerConverse
