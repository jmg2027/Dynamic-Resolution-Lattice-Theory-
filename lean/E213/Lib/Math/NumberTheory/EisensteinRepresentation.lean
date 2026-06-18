import E213.Lib.Math.NumberTheory.IntSqrt
import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid
import E213.Lib.Math.NumberTheory.PolyRoot.ResidueList
import E213.Lib.Math.Combinatorics.Pigeonhole
import E213.Lib.Math.NumberTheory.FourSquare
import E213.Lib.Math.NumberTheory.PerfectNumbers
import E213.Lib.Math.NumberTheory.ModArith.EisensteinCubeRoot
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.NatRing213
import E213.Lib.Math.NumberTheory.TwoSquareTheorem
import E213.Lib.Math.Algebra.CayleyDickson.Tower.DiscForcingObstruction
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConverse
import E213.Meta.Nat.PureNat

/-!
# Eisenstein form representation theorem (disc −3), ∅-axiom computed witness

`p` prime, `p ≡ 1 (mod 3)` ⟹ `∃ a b : Nat, p = a*a + a*b + b*b` (Eisenstein form `x²+xy+y²`).

Disc-`−3` analogue of Fermat's two-square theorem.  SAME Thue construction
(`Combinatorics.Pigeonhole.exists_collision_lt` box collision → signed differences → bounded
descent), no Eisenstein-integer ring `ℤ[ω]`.  Mirrors `TwoSquareTheorem.lean`.
-/

namespace E213.Lib.Math.NumberTheory.EisensteinRepresentation

open E213.Lib.Math.NumberTheory.PolyRoot (mod_eq_imp_dvd_sub int_dvd_to_nat nat_dvd_to_int)
open E213.Lib.Math.NumberTheory.FourSquareSeed (natCast_sub)
open E213.Lib.Math.NumberTheory.IntSqrt (isqrt isqrt_bracket isqrt_sq_le)
open E213.Lib.Math.NumberTheory.TwoSquareTheorem
  (boxVal thue_collision isqrt_sq_lt_of_prime decode_le natAbs_sub_le_of_lt decode_ne)

/-! ## §1 — the modular algebraic core (over `ℤ`)

`p ∣ X²+X+1` and `p ∣ A − X·B`  ⟹  `p ∣ A²+A·B+B²`.
Identity: `A²+AB+B² = (A − X·B)·(A + X·B + B) + B²·(X²+X+1)`. -/

/-- The disc-`−3` algebraic identity (pure `ring_intZ`). -/
theorem eis_decomp (A B X : Int) :
    A * A + A * B + B * B = (A - X * B) * (A + X * B + B) + B * B * (X * X + X + 1) := by
  ring_intZ

/-- ★ **Modular core.**  `↑p ∣ X²+X+1` and `↑p ∣ A − X·B` ⟹ `↑p ∣ A²+A·B+B²`. -/
theorem dvd_eis_form (p : Nat) (A B X : Int)
    (hX : (p : Int) ∣ (X * X + X + 1)) (hAB : (p : Int) ∣ (A - X * B)) :
    (p : Int) ∣ (A * A + A * B + B * B) := by
  rw [eis_decomp A B X]
  obtain ⟨u, hu⟩ := hAB
  obtain ⟨v, hv⟩ := hX
  refine ⟨(A + X * B + B) * u + B * B * v, ?_⟩
  rw [hu, hv]; ring_intZ

/-! ## §2 — Thue's lemma (computed small box pair, over `ℤ`)

From `cube_root_of_order3` (`p ∣ x²+x+1`) and the box collision, produce signed `A, B : Int`,
`|A|, |B| ≤ isqrt p`, not both zero, with `p ∣ A²+A·B+B²`. -/

/-- ★★★ **Thue's lemma (computed, `Int`).**  `p` prime with `∃ x, p ∣ x²+x+1` ⟹ signed
    `A B : Int`, `|A|,|B| ≤ isqrt p`, not both zero, `p ∣ A²+A·B+B²` — the small box pair
    from the constructive collision.  (`B` is the *negated* remainder-difference so the form
    lands on `x²+x+1`.) -/
theorem thue_lemma_int (p : Nat) (hp0 : 0 < p)
    (hroot : ∃ x : Nat, p ∣ (x * x + x + 1)) :
    ∃ A B : Int, A.natAbs ≤ isqrt p ∧ B.natAbs ≤ isqrt p ∧
      (A ≠ 0 ∨ B ≠ 0) ∧ (p : Int) ∣ (A * A + A * B + B * B) := by
  obtain ⟨x, hx⟩ := hroot
  -- the collision: boxVal p x q i = (i/q + x·(i%q)) % p
  obtain ⟨i, j, hi, hj, hij, hcol⟩ := thue_collision p x hp0
  have hq0 : 0 < isqrt p + 1 := Nat.zero_lt_succ _
  obtain ⟨ha1lt, hb1lt⟩ := decode_le hq0 hi
  obtain ⟨ha2lt, hb2lt⟩ := decode_le hq0 hj
  -- collision as a mod-equality
  have hcolmod : (i / (isqrt p + 1) + x * (i % (isqrt p + 1))) % p
               = (j / (isqrt p + 1) + x * (j % (isqrt p + 1))) % p := hcol
  -- p ∣ (i-side) − (j-side)  over Int
  have hAB0 : (p : Int) ∣
      (((i / (isqrt p + 1) + x * (i % (isqrt p + 1)) : Nat) : Int)
        - ((j / (isqrt p + 1) + x * (j % (isqrt p + 1)) : Nat) : Int)) :=
    mod_eq_imp_dvd_sub _ _ p hcolmod
  -- A = a1 - a2, B = b2 - b1  (B negated!)  so that the difference = A - X·B
  -- a1 = i/q, b1 = i%q, a2 = j/q, b2 = j%q
  -- rewrite the Nat-cast difference as A - X·B
  have hcast : (((i / (isqrt p + 1) + x * (i % (isqrt p + 1)) : Nat) : Int)
        - ((j / (isqrt p + 1) + x * (j % (isqrt p + 1)) : Nat) : Int))
      = ((((i / (isqrt p + 1) : Nat) : Int) - ((j / (isqrt p + 1) : Nat) : Int)))
        - (x : Int) * ((((j % (isqrt p + 1) : Nat) : Int) - ((i % (isqrt p + 1) : Nat) : Int))) := by
    show ((((i / (isqrt p + 1)) : Nat) : Int) + ((x : Int) * ((i % (isqrt p + 1) : Nat) : Int)))
        - (((j / (isqrt p + 1) : Nat) : Int) + ((x : Int) * ((j % (isqrt p + 1) : Nat) : Int)))
       = _
    ring_intZ
  rw [hcast] at hAB0
  -- p ∣ X²+X+1 over Int
  have hXint : (p : Int) ∣ ((x : Int) * (x : Int) + (x : Int) + 1) := by
    have h := nat_dvd_to_int p ((x * x + x + 1 : Nat) : Int)
      (by rw [Int.natAbs_ofNat]; exact hx)
    have he : (((x * x + x + 1 : Nat)) : Int) = (x : Int) * (x : Int) + (x : Int) + 1 := rfl
    rw [he] at h; exact h
  -- p ∣ A²+AB+B²
  have hsq := dvd_eis_form p
    (((i / (isqrt p + 1) : Nat) : Int) - ((j / (isqrt p + 1) : Nat) : Int))
    (((j % (isqrt p + 1) : Nat) : Int) - ((i % (isqrt p + 1) : Nat) : Int))
    (x : Int) hXint hAB0
  refine ⟨_, _, ?_, ?_, ?_, hsq⟩
  · -- |A| ≤ isqrt p
    exact natAbs_sub_le_of_lt ha1lt ha2lt
  · exact natAbs_sub_le_of_lt hb2lt hb1lt
  · -- not both zero: i ≠ j
    rcases decode_ne (q := isqrt p + 1) hij with hA | hB
    · left; intro h0; exact hA (by rw [h0]; rfl)
    · right; intro h0
      -- B = b2 - b1 = 0 ⟹ (b1 - b2) = -B = 0, so its natAbs is 0
      apply hB
      have hrel : (((i % (isqrt p + 1) : Nat) : Int) - ((j % (isqrt p + 1) : Nat) : Int))
          = -((((j % (isqrt p + 1) : Nat) : Int) - ((i % (isqrt p + 1) : Nat) : Int))) := by
        ring_intZ
      rw [hrel, h0]; rfl

/-! ## §3 — positive-definiteness and the bound -/

open E213.Lib.Math.NumberTheory.FourSquare (sq_nonneg nonpos_of_add_eq_zero)
open E213.Meta.Int213.OrderMul (natAbs_cast_of_nonneg)

/-- `x ≤ ↑x.natAbs` over `ℤ`. -/
theorem le_natAbs (x : Int) : x ≤ (x.natAbs : Int) := by
  -- 0 ≤ -x + ↑(-x).natAbs = -x + ↑x.natAbs  ⟹  x ≤ ↑x.natAbs
  rcases Int.natAbs_eq x with he | he
  · -- x = ↑x.natAbs
    rw [← he]; exact E213.Meta.Int213.Order.le_refl x
  · -- x = -↑x.natAbs, and ↑x.natAbs ≥ 0, so x = -↑n ≤ ↑n
    apply E213.Meta.Int213.Order.le_of_sub_nonneg
    show ((x.natAbs : Int) - x).NonNeg
    -- generalize n := x.natAbs so `rw [he]` does not loop on `x.natAbs`
    have hn : (0 : Int) ≤ (x.natAbs : Int) := Int.ofNat_nonneg _
    have key : ∀ n : Int, x = -n → (0:Int) ≤ n → (n - x).NonNeg := by
      intro n hxn hn'
      have h3 : n - x = n + n := by rw [hxn]; ring_intZ
      rw [h3]
      exact E213.Meta.Int213.Order.nonneg_of_le_zero (E213.Meta.Int213.add_nonneg hn' hn')
    exact key (x.natAbs : Int) he hn

/-- `A·A = ↑(|A|·|A|)`. -/
theorem mul_self_natAbs (A : Int) : A * A = ((A.natAbs * A.natAbs : Nat) : Int) :=
  (Int.natAbs_mul_self).symm

/-- `A·B ≤ ↑(|A|·|B|)`:  `A·B ≤ ↑(A·B).natAbs = ↑(|A|·|B|)`. -/
theorem mul_le_natAbs_mul (A B : Int) : A * B ≤ ((A.natAbs * B.natAbs : Nat) : Int) := by
  have h1 := le_natAbs (A * B)
  rw [E213.Lib.Math.NumberTheory.PolyRoot.natAbs_mul] at h1
  exact h1

/-- ★ **The bound.**  `|A|,|B| ≤ M` ⟹ `A²+A·B+B² ≤ ↑(3·(M·M))`. -/
theorem eis_le_bound (A B : Int) (M : Nat)
    (hA : A.natAbs ≤ M) (hB : B.natAbs ≤ M) :
    A * A + A * B + B * B ≤ ((3 * (M * M) : Nat) : Int) := by
  -- each term ≤ ↑(M*M)
  have hMM : ∀ k l : Nat, k ≤ M → l ≤ M → ((k * l : Nat) : Int) ≤ ((M * M : Nat) : Int) :=
    fun k l hk hl => E213.Meta.Int213.OrderMul.ofNat_le_of_le (Nat.mul_le_mul hk hl)
  have h1 : A * A ≤ ((M * M : Nat) : Int) := by
    rw [mul_self_natAbs A]; exact hMM _ _ hA hA
  have h2 : A * B ≤ ((M * M : Nat) : Int) :=
    E213.Meta.Int213.Order.le_trans (mul_le_natAbs_mul A B) (hMM _ _ hA hB)
  have h3 : B * B ≤ ((M * M : Nat) : Int) := by
    rw [mul_self_natAbs B]; exact hMM _ _ hB hB
  -- sum ≤ 3·(M*M)
  -- A*A + A*B ≤ MM + MM
  have hAB2 : A * A + A * B ≤ ((M * M : Nat) : Int) + ((M * M : Nat) : Int) :=
    E213.Meta.Int213.Order.le_trans
      (E213.Meta.Int213.Order.add_le_add_right h1 (A * B))
      (E213.Meta.Int213.Order.add_le_add_left h2 ((M * M : Nat) : Int))
  -- (A*A+A*B) + B*B ≤ (MM+MM) + MM
  have hsum : A * A + A * B + B * B
      ≤ ((M * M : Nat) : Int) + ((M * M : Nat) : Int) + ((M * M : Nat) : Int) :=
    E213.Meta.Int213.Order.le_trans
      (E213.Meta.Int213.Order.add_le_add_right hAB2 (B * B))
      (E213.Meta.Int213.Order.add_le_add_left h3 (((M * M : Nat) : Int) + ((M * M : Nat) : Int)))
  have hnat : (3 * (M * M) : Nat) = (M * M) + (M * M) + (M * M) := by ring_nat
  have hcast : ((M * M : Nat) : Int) + ((M * M : Nat) : Int) + ((M * M : Nat) : Int)
      = ((3 * (M * M) : Nat) : Int) := by
    rw [hnat, Int.ofNat_add, Int.ofNat_add]
  rw [← hcast]; exact hsum

/-! ## §4 — positive-definiteness:  `0 < A²+A·B+B²` unless `A=B=0` -/

/-- The Gauss identity `4·(A²+A·B+B²) = (2A+B)² + 3·B²` (pure `ring_intZ`). -/
theorem four_eis (A B : Int) :
    4 * (A * A + A * B + B * B) = (2 * A + B) * (2 * A + B) + 3 * (B * B) := by
  ring_intZ

/-- ★ **Positive-definiteness.**  Not both `A,B` zero ⟹ `0 < A²+A·B+B²`. -/
theorem eis_pos (A B : Int) (hne : A ≠ 0 ∨ B ≠ 0) :
    (0 : Int) < A * A + A * B + B * B := by
  -- abbreviate N
  -- 0 ≤ 4N  (from 4N = sq + 3·sq ≥ 0)
  have hsq2 : (0 : Int) ≤ 3 * (B * B) :=
    E213.Meta.Int213.OrderMul.mul_le_mul_left_nonneg (sq_nonneg B) 3 (by decide)
  have h4nonneg : (0 : Int) ≤ 4 * (A * A + A * B + B * B) := by
    rw [four_eis A B]
    exact E213.Meta.Int213.add_nonneg (sq_nonneg (2 * A + B)) hsq2
  -- N ≥ 0 :  0*4 ≤ N*4 ⟹ 0 ≤ N
  have hNnonneg : (0 : Int) ≤ A * A + A * B + B * B := by
    apply E213.Meta.Int213.OrderMul.le_of_mul_le_mul_right_pos
      (c := 4) (a := 0) (b := A * A + A * B + B * B)
    · -- 0 * 4 ≤ N * 4
      have h04 : (0 : Int) * 4 = 0 := by rw [E213.Meta.Int213.zero_mul]
      have hN4 : (A * A + A * B + B * B) * 4 = 4 * (A * A + A * B + B * B) :=
        E213.Meta.Int213.mul_comm _ _
      rw [h04, hN4]; exact h4nonneg
    · decide
  -- N ≠ 0
  have hNne : A * A + A * B + B * B ≠ 0 := by
    intro h0
    -- 4N = 0
    have h4 : (2 * A + B) * (2 * A + B) + 3 * (B * B) = 0 := by
      rw [← four_eis A B, h0]; exact E213.Meta.Int213.PolyIntM.mul_zeroZ 4
    have hsq1 : (0 : Int) ≤ (2 * A + B) * (2 * A + B) := sq_nonneg _
    -- (2A+B)² ≤ 0 and ≥ 0 ⟹ = 0
    have hz1 : (2 * A + B) * (2 * A + B) ≤ 0 := nonpos_of_add_eq_zero hsq2 h4
    have hBsq : (2 * A + B) * (2 * A + B) = 0 :=
      E213.Meta.Int213.Order.le_antisymm hz1 hsq1
    have hB0 : 2 * A + B = 0 := (E213.Meta.Nat.IntHelpers.mul_self_eq_zero).mp hBsq
    -- 3B² ≤ 0 and ≥ 0 ⟹ = 0 ;  then B*B = 0 (else 3·(B*B) > 0)
    have h3b : 3 * (B * B) = 0 := by
      rw [E213.Meta.Int213.add_comm] at h4
      have hz2 : 3 * (B * B) ≤ 0 := nonpos_of_add_eq_zero hsq1 h4
      exact E213.Meta.Int213.Order.le_antisymm hz2 hsq2
    have hBB0 : B * B = 0 := by
      rcases E213.Meta.Int213.OrderMul.int_sign (B * B) with hge | hlt
      · -- B*B ≥ 0; if B*B > 0 then 3*(B*B) > 0 contradiction; need B*B = 0
        rcases E213.Meta.Int213.Order.pos_zero_or_neg (B * B) with hp | hz | hn
        · exfalso
          have : (0 : Int) < 3 * (B * B) := E213.Meta.Int213.OrderMul.mul_pos (by decide) hp
          rw [h3b] at this; exact E213.Meta.Int213.OrderMul.int_lt_irrefl 0 this
        · exact hz
        · exact absurd hge (E213.Meta.Int213.Order.not_le_of_lt hn)
      · -- B*B < 0 impossible (sq_nonneg)
        exact absurd (sq_nonneg B) (E213.Meta.Int213.Order.not_le_of_lt hlt)
    have hBzero : B = 0 := (E213.Meta.Nat.IntHelpers.mul_self_eq_zero).mp hBB0
    have hA0 : 2 * A = 0 := by
      have he : 2 * A + B = 2 * A := by rw [hBzero, Int.add_zero]
      rw [he] at hB0; exact hB0
    have hAzero : A = 0 := E213.Meta.Int213.OrderMul.eq_zero_of_two_mul_eq_zero hA0
    rcases hne with hA | hB
    · exact hA hAzero
    · exact hB hBzero
  -- combine
  rcases E213.Meta.Int213.Order.pos_zero_or_neg (A * A + A * B + B * B) with h | h | h
  · exact h
  · exact absurd h hNne
  · exact absurd hNnonneg (E213.Meta.Int213.Order.not_le_of_lt h)

/-! ## §5 — ruling out `2p`:  `2 ∣ N ⟹ 4 ∣ N`

The form `A²+A·B+B²` is even only when `A,B` are both even, whence `4 ∣ N`.
A multiple `2p` (p odd) is `≡ 2 (mod 4)`, never `4 ∣`, so `N ≠ 2p`. -/

/-- `2·c = 2·m+1` is impossible over `ℤ`. -/
theorem two_not_dvd_odd (c m : Int) (h : 2 * c = 2 * m + 1) : False := by
  -- 2·(c - m) = 1  ⟹  natAbs:  2·|c-m| = 1, impossible
  have h1 : 2 * (c - m) = 1 := by
    have : 2 * c - 2 * m = 1 := by rw [h]; ring_intZ
    rw [E213.Meta.Int213.mul_sub]; exact this
  -- take natAbs
  have h2 : (2 * (c - m)).natAbs = (1 : Int).natAbs := by rw [h1]
  rw [E213.Lib.Math.NumberTheory.PolyRoot.natAbs_mul] at h2
  -- (2:Int).natAbs = 2 ;  so 2 * |c-m| = 1 in Nat, impossible
  have h3 : 2 * (c - m).natAbs = 1 := h2
  exact E213.Lib.Math.Algebra.CayleyDickson.Tower.DiscForcingObstruction.nat_two_mul_ne_one _ h3

/-- Int even/odd dichotomy:  `∀ x, (∃k, x = 2k) ∨ (∃k, x = 2k+1)`. -/
theorem int_even_or_odd (x : Int) :
    (∃ k : Int, x = 2 * k) ∨ (∃ k : Int, x = 2 * k + 1) := by
  -- ↑(2*j) = 2 * ↑j  and  ↑(2*j+1) = 2 * ↑j + 1  (cast normalization)
  have hcast2 : ∀ j : Nat, ((2 * j : Nat) : Int) = 2 * (j : Int) := by
    intro j; rw [Int.ofNat_mul]; rfl
  have hcast2' : ∀ j : Nat, ((2 * j + 1 : Nat) : Int) = 2 * (j : Int) + 1 := by
    intro j; rw [Int.ofNat_add, hcast2]; rfl
  rcases Int.natAbs_eq x with he | he
  · rcases E213.Meta.Nat.PureNat.nat_dichotomy x.natAbs with ⟨j, hj⟩ | ⟨j, hj⟩
    · left; exact ⟨(j : Int), by rw [he, hj, hcast2]⟩
    · right; exact ⟨(j : Int), by rw [he, hj, hcast2']⟩
  · rcases E213.Meta.Nat.PureNat.nat_dichotomy x.natAbs with ⟨j, hj⟩ | ⟨j, hj⟩
    · left; refine ⟨-(j : Int), ?_⟩
      rw [he, hj, hcast2]; ring_intZ
    · right; refine ⟨-(j : Int) - 1, ?_⟩
      rw [he, hj, hcast2']; ring_intZ

/-- ★ **Even ⟹ div-4.**  `2 ∣ A²+A·B+B² ⟹ 4 ∣ A²+A·B+B²` (the form is `≡ 2 mod 4`-free). -/
theorem eis_two_dvd_imp_four_dvd (A B : Int)
    (h2 : (2 : Int) ∣ (A * A + A * B + B * B)) :
    (4 : Int) ∣ (A * A + A * B + B * B) := by
  rcases int_even_or_odd A with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
    rcases int_even_or_odd B with ⟨b, hb⟩ | ⟨b, hb⟩
  · -- A,B even: N = 4·(a²+ab+b²)
    refine ⟨a * a + a * b + b * b, ?_⟩
    rw [ha, hb]; ring_intZ
  · -- A even, B odd: N odd ⟹ contradiction with 2 ∣ N
    exfalso
    obtain ⟨c, hc⟩ := h2
    -- N = 2·c  but N = 2·(…) + 1  ⟹ 2 ∣ 1
    have hodd : A * A + A * B + B * B
        = 2 * (2 * (a * a) + 2 * (a * b) + a + 2 * (b * b) + 2 * b) + 1 := by
      rw [ha, hb]; ring_intZ
    rw [hodd] at hc
    exact two_not_dvd_odd c _ hc.symm
  · exfalso
    obtain ⟨c, hc⟩ := h2
    have hodd : A * A + A * B + B * B
        = 2 * (2 * (a * a) + 2 * (a * b) + 2 * a + 2 * (b * b) + b) + 1 := by
      rw [ha, hb]; ring_intZ
    rw [hodd] at hc
    exact two_not_dvd_odd c _ hc.symm
  · exfalso
    obtain ⟨c, hc⟩ := h2
    have hodd : A * A + A * B + B * B
        = 2 * (2 * (a * a) + 2 * a + 2 * (a * b) + a + b + 2 * (b * b) + 2 * b + 1) + 1 := by
      rw [ha, hb]; ring_intZ
    rw [hodd] at hc
    exact two_not_dvd_odd c _ hc.symm

/-! ## §6 — the descent to `= p` -/

/-- A positive multiple of `p` strictly below `3p` is `p` or `2p`. -/
theorem p_or_two_p {p n : Nat} (hp : 0 < p) (hd : p ∣ n) (h0 : 0 < n)
    (hlt : n < 3 * p) : n = p ∨ n = 2 * p := by
  obtain ⟨c, hc⟩ := hd
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · exfalso; rw [h, Nat.mul_zero] at hc; rw [hc] at h0; exact Nat.lt_irrefl 0 h0
    · exact h
  have hc3 : c < 3 := by
    rcases Nat.lt_or_ge c 3 with h | hge
    · exact h
    · exfalso
      have hle : 3 * p ≤ c * p := Nat.mul_le_mul_right p hge
      have hcp : c * p = n := by rw [hc, Nat.mul_comm]
      rw [hcp] at hle
      exact absurd hle (Nat.not_le.mpr hlt)
  -- c ∈ {1,2}
  rcases Nat.lt_or_eq_of_le hc1 with hgt | h1
  · -- c ≥ 2 and < 3 ⟹ c = 2
    have hc2 : c = 2 := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hc3) with h | h
      · exfalso; exact absurd h (Nat.not_lt.mpr hgt)
      · exact h
    right; rw [hc, hc2, Nat.mul_comm]
  · left; rw [hc, ← h1, Nat.mul_one]

/-- `p` prime with `p % 3 = 1` is odd:  `¬ 2 ∣ p`  (so `¬ 4 ∣ 2·p`). -/
theorem prime_one_mod_three_odd (p : Nat) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hmod : p % 3 = 1) : ¬ (2 : Nat) ∣ p := by
  intro h2
  -- 2 ∣ p ⟹ 2 = 1 ∨ 2 = p
  rcases hpr 2 h2 with h | h
  · exact absurd h (by decide)
  · -- p = 2, but 2 % 3 = 2 ≠ 1
    rw [← h] at hmod; exact absurd hmod (by decide)

/-- `¬ 2 ∣ p ⟹ ¬ 4 ∣ 2·p` (over `ℤ`):  `4 ∣ 2p ⟹ 2 ∣ p`. -/
theorem not_four_dvd_two_p (p : Nat) (hodd : ¬ (2 : Nat) ∣ p) :
    ¬ (4 : Int) ∣ ((2 * p : Nat) : Int) := by
  intro h4
  apply hodd
  -- 4 ∣ 2p over Int ⟹ 4 ∣ 2p over Nat ⟹ 2 ∣ p
  have hnat : (4 : Nat) ∣ (2 * p) := by
    have := int_dvd_to_nat 4 ((2 * p : Nat) : Int) h4
    rw [Int.natAbs_ofNat] at this; exact this
  obtain ⟨k, hk⟩ := hnat
  -- 2*p = 4*k = 2*(2*k) ⟹ p = 2*k
  refine ⟨k, ?_⟩
  have h2 : 2 * p = 2 * (2 * k) := by rw [hk]; ring_nat
  exact E213.Tactic.NatHelper.mul_left_cancel_pos (by decide) h2

/-- `a < b` in `Nat` ⟹ `↑a < ↑b` over `ℤ`. -/
theorem ofNat_lt_of_lt {a b : Nat} (h : a < b) : (a : Int) < (b : Int) := by
  -- a + 1 ≤ b ⟹ ↑a + 1 ≤ ↑b ⟹ ↑a < ↑b
  have h1 : ((a + 1 : Nat) : Int) ≤ (b : Int) :=
    E213.Meta.Int213.OrderMul.ofNat_le_of_le h
  have h2 : (a : Int) + 1 ≤ (b : Int) := by rw [Int.ofNat_add] at h1; exact h1
  apply E213.Meta.Int213.Order.lt_of_sub_one_nonneg
  -- ((b:Int) - a - 1).NonNeg  from  (b - (a+1)).NonNeg
  have hsub := E213.Meta.Int213.Order.sub_nonneg_of_le h2  -- ((b) - (a+1)).NonNeg
  have he : (b : Int) - ((a : Int) + 1) = (b : Int) - (a : Int) - 1 := by ring_intZ
  rw [he] at hsub; exact hsub

/-! ## §7 — the representation theorems

The cube-root-of-unity input `∃ x, p ∣ x²+x+1` is closed in the corpus
(`EisensteinConverse.cube_root_exists` + `three_mul_eq_of_mod`, Pillar I, PURE), so the
representation is *unconditional* on `p ≡ 1 (mod 3)`. -/

/-- ★★★★ **Eisenstein representation (Thue), descended `Int` form.**  `p` prime, odd, with
    `∃ x, p ∣ x²+x+1` ⟹ `∃ a b : Int, ↑p = a²+a·b+b²` — the computed box-collision witness,
    descended to `= p` (positive-definite, `< 3p`, the `2p` case excluded by the form's
    `mod 4` parity). -/
theorem eisenstein_repr_of_root (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hodd : ¬ (2 : Nat) ∣ p) (hroot : ∃ x : Nat, p ∣ (x * x + x + 1)) :
    ∃ a b : Int, (p : Int) = a * a + a * b + b * b := by
  have hp0 : 0 < p := Nat.lt_trans (by decide) hp
  obtain ⟨A, B, hA, hB, hne, hdvd⟩ := thue_lemma_int p hp0 hroot
  have hpos : (0 : Int) < A * A + A * B + B * B := eis_pos A B hne
  have hNnonneg : (0 : Int) ≤ A * A + A * B + B * B := E213.Meta.Int213.Order.le_of_lt hpos
  have hbd : A * A + A * B + B * B ≤ ((3 * (isqrt p * isqrt p) : Nat) : Int) :=
    eis_le_bound A B (isqrt p) hA hB
  have hsqlt : isqrt p * isqrt p < p := isqrt_sq_lt_of_prime p hp hpr
  have h3lt : (3 * (isqrt p * isqrt p) : Nat) < 3 * p :=
    E213.Meta.Nat.NatRing213.nat_mul_lt_mul_left (by decide) hsqlt
  have hNlt : A * A + A * B + B * B < ((3 * p : Nat) : Int) :=
    E213.Meta.Int213.Order.lt_of_le_of_lt hbd (ofNat_lt_of_lt h3lt)
  have hcast : ((A * A + A * B + B * B).natAbs : Int) = A * A + A * B + B * B :=
    natAbs_cast_of_nonneg hNnonneg
  have hdvdn : p ∣ (A * A + A * B + B * B).natAbs := int_dvd_to_nat p _ hdvd
  have h0n : 0 < (A * A + A * B + B * B).natAbs := by
    rcases Nat.eq_zero_or_pos (A * A + A * B + B * B).natAbs with h | h
    · exfalso
      have hz : (A * A + A * B + B * B) = 0 := by rw [← hcast, h]; rfl
      rw [hz] at hpos; exact E213.Meta.Int213.OrderMul.int_lt_irrefl 0 hpos
    · exact h
  have hnlt : (A * A + A * B + B * B).natAbs < 3 * p := by
    have := E213.Meta.Int213.OrderMul.natAbs_lt_of_lt hNnonneg hNlt
    rwa [Int.natAbs_ofNat] at this
  rcases p_or_two_p hp0 hdvdn h0n hnlt with hep | he2p
  · refine ⟨A, B, ?_⟩
    rw [← hcast, hep]
  · exfalso
    have hN2p : A * A + A * B + B * B = ((2 * p : Nat) : Int) := by rw [← hcast, he2p]
    have h2dvd : (2 : Int) ∣ (A * A + A * B + B * B) := by
      rw [hN2p]; exact ⟨(p : Int), by rw [Int.ofNat_mul]; rfl⟩
    have h4dvd : (4 : Int) ∣ (A * A + A * B + B * B) := eis_two_dvd_imp_four_dvd A B h2dvd
    rw [hN2p] at h4dvd
    exact not_four_dvd_two_p p hodd h4dvd

/-- ★★★★★ **Eisenstein representation theorem (`Int` form).**  Every prime `p ≡ 1 (mod 3)` is
    represented by the disc-`−3` form `x²+xy+y²`:  `∃ a b : Int, ↑p = a²+a·b+b²`.  The cube root
    of unity (`∃ x, p ∣ x²+x+1`) is the corpus's PURE `cube_root_exists`; the witness is the
    computed Thue box collision, descended to `= p`. -/
theorem eisenstein_repr_int (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hmod : p % 3 = 1) :
    ∃ a b : Int, (p : Int) = a * a + a * b + b * b := by
  obtain ⟨m, hm⟩ :=
    E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConverse.three_mul_eq_of_mod p hmod
  have hroot :=
    E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConverse.cube_root_exists p m hp hpr hm
  exact eisenstein_repr_of_root p hp hpr (prime_one_mod_three_odd p hpr hmod) hroot

/-! ## §8 — `Nat` form (sign normalization)

`a²−a'b'+b'²` (cross-negative branch) is folded to a `Nat` representative by
`a'²−a'b'+b'² = (a'−b')² + (a'−b')·b' + b'²` (for `a' ≥ b'`), the form-preserving
shear `(a,b) ↦ (a−b, b)`. -/

/-- Nat shear identity:  `a ≥ b ⟹ a²+b²−ab = (a−b)² + (a−b)·b + b²`  (all `Nat`). -/
theorem nat_shear (a b : Nat) (hab : b ≤ a) :
    a * a + b * b - a * b = (a - b) * (a - b) + (a - b) * b + b * b := by
  obtain ⟨c, hc⟩ := Nat.le.dest hab  -- b + c = a
  subst hc
  -- (b+c) - b = c  (pure)
  have hbc : b + c - b = c := by
    rw [Nat.add_comm]; exact E213.Meta.Nat.NatRing213.nat_add_sub_self_right c b
  rw [hbc]
  -- now: (b+c)*(b+c) + b*b - (b+c)*b = c*c + c*b + b*b
  have hadd : c * c + c * b + b * b + (b + c) * b = (b + c) * (b + c) + b * b := by ring_nat
  -- LHS = (RHS-sum) + (b+c)*b - (b+c)*b = RHS-sum  via pure  X + Y - Y = X
  rw [← hadd, E213.Meta.Nat.NatRing213.nat_add_sub_self_right]

/-- ★ **Int → Nat normalization.**  `↑p = a²+a·b+b²` (Int) ⟹ `∃ a' b' : Nat, p = a'²+a'·b'+b'²`. -/
theorem int_eis_to_nat (p : Nat) (a b : Int) (h : (p : Int) = a * a + a * b + b * b) :
    ∃ a' b' : Nat, p = a' * a' + a' * b' + b' * b' := by
  rcases E213.Meta.Int213.OrderMul.int_sign (a * b) with hge | hlt
  · -- a*b ≥ 0:  a*b = ↑(|a|*|b|),  p = |a|²+|a||b|+|b|²
    refine ⟨a.natAbs, b.natAbs, ?_⟩
    have hab : a * b = ((a.natAbs * b.natAbs : Nat) : Int) := by
      rw [← E213.Lib.Math.NumberTheory.PolyRoot.natAbs_mul]
      exact (natAbs_cast_of_nonneg hge).symm
    have hcast : (p : Int) = ((a.natAbs * a.natAbs + a.natAbs * b.natAbs + b.natAbs * b.natAbs : Nat) : Int) := by
      rw [h, mul_self_natAbs a, mul_self_natAbs b, hab, Int.ofNat_add, Int.ofNat_add]
    exact Int.ofNat.inj hcast
  · -- a*b < 0:  a*b = -↑(|a|*|b|),  p = |a|²-|a||b|+|b|²
    have hab : a * b = -((a.natAbs * b.natAbs : Nat) : Int) := by
      rw [← E213.Lib.Math.NumberTheory.PolyRoot.natAbs_mul]
      rcases Int.natAbs_eq (a * b) with he | he
      · exfalso
        -- a*b = ↑|a*b| ≥ 0, contradicting a*b < 0
        have hge : (0 : Int) ≤ a * b := by rw [he]; exact Int.ofNat_nonneg _
        exact E213.Meta.Int213.Order.not_le_of_lt hlt hge
      · exact he
    -- ↑p = ↑(|a|²+|b|²) - ↑(|a||b|)
    have hpInt : (p : Int) = ((a.natAbs * a.natAbs + b.natAbs * b.natAbs : Nat) : Int)
        - ((a.natAbs * b.natAbs : Nat) : Int) := by
      rw [h, mul_self_natAbs a, mul_self_natAbs b, hab, Int.ofNat_add]; ring_intZ
    -- so p = (|a|²+|b|²) - |a||b|   (Nat),  with  |a||b| ≤ |a|²+|b|²
    have hle : a.natAbs * b.natAbs ≤ a.natAbs * a.natAbs + b.natAbs * b.natAbs := by
      rcases Nat.le_total a.natAbs b.natAbs with h1 | h1
      · -- A ≤ B:  A*B ≤ B*B ≤ A*A+B*B
        exact Nat.le_trans (Nat.mul_le_mul h1 (Nat.le_refl b.natAbs)) (Nat.le_add_left _ _)
      · -- B ≤ A:  A*B ≤ A*A ≤ A*A+B*B
        exact Nat.le_trans (Nat.mul_le_mul (Nat.le_refl a.natAbs) h1) (Nat.le_add_right _ _)
    have hpNat : p = a.natAbs * a.natAbs + b.natAbs * b.natAbs - a.natAbs * b.natAbs := by
      have hcast2 : (p : Int)
          = (((a.natAbs * a.natAbs + b.natAbs * b.natAbs) - a.natAbs * b.natAbs : Nat) : Int) := by
        rw [hpInt, natCast_sub hle]
      exact Int.ofNat.inj hcast2
    -- fold:  A*A+B*B-A*B = c²+c·d+d²  with {c,d} = {A-B,B} or {B-A,A}
    rcases Nat.le_total b.natAbs a.natAbs with hBA | hAB2
    · refine ⟨a.natAbs - b.natAbs, b.natAbs, ?_⟩
      rw [hpNat]; exact nat_shear a.natAbs b.natAbs hBA
    · refine ⟨b.natAbs - a.natAbs, a.natAbs, ?_⟩
      rw [hpNat]
      have hcomm : a.natAbs * a.natAbs + b.natAbs * b.natAbs - a.natAbs * b.natAbs
          = b.natAbs * b.natAbs + a.natAbs * a.natAbs - b.natAbs * a.natAbs := by
        rw [Nat.add_comm (a.natAbs * a.natAbs) (b.natAbs * b.natAbs), Nat.mul_comm a.natAbs b.natAbs]
      rw [hcomm]; exact nat_shear b.natAbs a.natAbs hAB2

/-- ★★★★★ **Eisenstein representation theorem (`Nat` form).**  Every prime `p ≡ 1 (mod 3)` is
    represented by `x²+xy+y²`:  `∃ a b : Nat, p = a*a + a*b + b*b`. -/
theorem eisenstein_repr (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hmod : p % 3 = 1) : ∃ a b : Nat, p = a * a + a * b + b * b := by
  obtain ⟨a, b, hab⟩ := eisenstein_repr_int p hp hpr hmod
  exact int_eis_to_nat p a b hab

/-! ## §9 — concrete smokes (closed numerals) -/

open E213.Lib.Math.NumberTheory.PerfectNumbers (prime_of_bounded)

/-- `7` is prime (divisor dichotomy), bounded check `B = 3`. -/
theorem dich_7 : ∀ d, d ∣ (7 : Nat) → d = 1 ∨ d = 7 :=
  (prime_of_bounded (q := 7) (by decide) (B := 3) (by decide) (by decide)).2

/-- `13` is prime (divisor dichotomy), bounded check `B = 4`. -/
theorem dich_13 : ∀ d, d ∣ (13 : Nat) → d = 1 ∨ d = 13 :=
  (prime_of_bounded (q := 13) (by decide) (B := 4) (by decide) (by decide)).2

/-- `7 = 1² + 1·2 + 2²` via the representation theorem. -/
theorem smoke_7 : ∃ a b : Nat, (7 : Nat) = a * a + a * b + b * b :=
  eisenstein_repr 7 (by decide) dich_7 (by decide)

/-- `13 = 1² + 1·3 + 3²` via the representation theorem. -/
theorem smoke_13 : ∃ a b : Nat, (13 : Nat) = a * a + a * b + b * b :=
  eisenstein_repr 13 (by decide) dich_13 (by decide)

/-- Direct numeric checks the form lands correctly. -/
theorem smoke_7_value : (7 : Nat) = 1 * 1 + 1 * 2 + 2 * 2 := by decide
theorem smoke_13_value : (13 : Nat) = 1 * 1 + 1 * 3 + 3 * 3 := by decide

end E213.Lib.Math.NumberTheory.EisensteinRepresentation
