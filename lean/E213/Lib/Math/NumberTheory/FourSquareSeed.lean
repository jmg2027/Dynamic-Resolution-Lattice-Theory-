import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid
import E213.Lib.Math.NumberTheory.PolyRoot.ResidueList
import E213.Lib.Math.Combinatorics.Pigeonhole
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.PolyNatMTactic

/-!
# FourSquareSeed — the additive pigeonhole `∃ x y, p ∣ x²+y²+1` (Pillar I of four-square)

The seed of Lagrange's four-square theorem, and the repo's first use of an **additive**
pigeonhole (vs the multiplicative Lagrange-root bound of `PolyRoot.RootBound`).  For an odd
prime `p = 2m+1`, the `m+1` squares `{x² mod p : 0 ≤ x ≤ m}` are pairwise distinct
(`sq_distinct`), and so are the `m+1` values `{(p−1−y²) mod p}`; together `p+1 > p` values in
`Fin p`, so two coincide — necessarily across the two families, giving `x² ≡ −1−y²`.

  * `nat_prime_dvd_mul` — `p` prime, `p ∣ a·b` ⟹ `p ∣ a ∨ p ∣ b` (∅-axiom; routes the dvd
    case-split through `a % p` to avoid the `propext`-dirty `Decidable (p ∣ a)`).
  * ★★★ `sq_distinct` — `x, x' ≤ m`, `x² ≡ x'² (mod p)` ⟹ `x = x'` (squares injective on `[0,m]`).

(The `Fin`-pigeonhole assembly to `∃ x y, p ∣ x²+y²+1` builds on these — see
`research-notes/frontiers/four_square_marathon.md`.)

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.FourSquareSeed

open E213.Lib.Math.NumberTheory.PolyRoot (mod_eq_imp_dvd_sub int_dvd_to_nat)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (prime_coprime euclid_of_coprime)
open E213.Meta.Nat.Gcd213 (gcd213_comm)
open E213.Tactic.NatHelper (gcd213 sub_add_cancel add_sub_cancel_right mul_mod_right)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Meta.Nat.AddMod213 (div_add_mod)

/-- `(↑(m+n) : ℤ) = ↑m + ↑n`. -/
private theorem ncast_add (m n : Nat) : ((m + n : Nat) : Int) = (m : Int) + (n : Int) := rfl

/-- `b ≤ a` ⟹ `(↑(a−b) : ℤ) = ↑a − ↑b`. -/
theorem natCast_sub {a b : Nat} (h : b ≤ a) : ((a - b : Nat) : Int) = (a : Int) - (b : Int) := by
  have hab : a - b + b = a := sub_add_cancel h
  have hc : ((a - b : Nat) : Int) + (b : Int) = (a : Int) := by rw [← ncast_add, hab]
  rw [← hc]; ring_intZ

/-- `a % p = 0 ⟹ p ∣ a`. -/
theorem dvd_of_mod_zero (a p : Nat) (h : a % p = 0) : p ∣ a := by
  have hdm := div_add_mod a p
  rw [h, Nat.add_zero] at hdm
  exact ⟨a / p, hdm.symm⟩

/-- `p ∣ a ⟹ a % p = 0`. -/
theorem mod_zero_of_dvd (a p : Nat) (h : p ∣ a) : a % p = 0 := by
  obtain ⟨k, hk⟩ := h
  rw [hk]; exact mul_mod_right p k

/-- `p` prime, `p ∣ a·b` ⟹ `p ∣ a ∨ p ∣ b` (∅-axiom Euclid). -/
theorem nat_prime_dvd_mul (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (a b : Nat) (hab : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  rcases Nat.eq_zero_or_pos (a % p) with ha | ha
  · exact Or.inl (dvd_of_mod_zero a p ha)
  · right
    have hnp : ¬ p ∣ a := by
      intro hd; rw [mod_zero_of_dvd a p hd] at ha; exact Nat.lt_irrefl 0 ha
    have hco : gcd213 a p = 1 := by rw [gcd213_comm]; exact prime_coprime p a hpr hnp
    exact euclid_of_coprime a b p hp hco hab

/-- ★★★ **Squares are injective on `[0, m]` modulo `p`** (for `2m < p`).  `x²≡x'²` ⟹
    `p ∣ (x−x')(x+x')`; both factors are `< p`, so (Euclid) one is `0`, forcing `x = x'`. -/
theorem sq_distinct (p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m < p) :
    ∀ x x', x ≤ m → x' ≤ m → x * x % p = x' * x' % p → x = x' := by
  have hmp : m < p := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left m (by decide)) h2m
  have key : ∀ x x', x' ≤ x → x ≤ m → x * x % p = x' * x' % p → x = x' := by
    intro x x' hle hxm heq
    have hxx : x' * x' ≤ x * x := Nat.mul_le_mul hle hle
    have hdvdI : (p : Int) ∣ ((x * x : Nat) : Int) - ((x' * x' : Nat) : Int) :=
      mod_eq_imp_dvd_sub _ _ p heq
    rw [← natCast_sub hxx] at hdvdI
    have hdvdN : p ∣ (x * x - x' * x') := by
      have := int_dvd_to_nat p _ hdvdI
      rwa [Int.natAbs_ofNat] at this
    obtain ⟨d, hd⟩ : ∃ d, x = d + x' := ⟨x - x', (sub_add_cancel hle).symm⟩
    have hfact : x * x - x' * x' = (x - x') * (x + x') := by
      rw [hd, add_sub_cancel_right]
      have hk : (d + x') * (d + x') = d * ((d + x') + x') + x' * x' := by ring_nat
      rw [hk, add_sub_cancel_right]
    rw [hfact] at hdvdN
    rcases nat_prime_dvd_mul p hp hpr _ _ hdvdN with hd1 | hd2
    · rcases Nat.eq_zero_or_pos (x - x') with hz | hpos
      · exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hz) hle
      · exfalso
        have hlt : x - x' < p := Nat.lt_of_le_of_lt (Nat.le_trans (Nat.sub_le x x') hxm) hmp
        exact absurd (le_of_dvd_pos p (x - x') hpos hd1) (Nat.not_le.mpr hlt)
    · rcases Nat.eq_zero_or_pos (x + x') with hz | hpos
      · have hx0 : x = 0 :=
          Nat.le_zero.mp (Nat.le_trans (Nat.le_add_right x x') (Nat.le_of_eq hz))
        have hx'0 : x' = 0 :=
          Nat.le_zero.mp (Nat.le_trans (Nat.le_add_left x' x) (Nat.le_of_eq hz))
        rw [hx0, hx'0]
      · exfalso
        have h2m' : m + m < p := by rw [← Nat.two_mul]; exact h2m
        have hlt : x + x' < p :=
          Nat.lt_of_le_of_lt (Nat.add_le_add hxm (Nat.le_trans hle hxm)) h2m'
        exact absurd (le_of_dvd_pos p (x + x') hpos hd2) (Nat.not_le.mpr hlt)
  intro x x' hxm hx'm heq
  rcases Nat.le_total x' x with h | h
  · exact key x x' h hxm heq
  · exact (key x' x h hx'm heq.symm).symm

end E213.Lib.Math.NumberTheory.FourSquareSeed
