import E213.Lib.Math.NumberTheory.ModArith.QRNegOne
import E213.Lib.Math.NumberTheory.SumTwoSquares
import E213.Lib.Math.NumberTheory.IntSqrt
import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid
import E213.Lib.Math.NumberTheory.PolyRoot.ResidueList
import E213.Lib.Math.Combinatorics.Pigeonhole
import E213.Lib.Math.NumberTheory.FourSquare
import E213.Lib.Math.NumberTheory.PerfectNumbers
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.NatDiv213

/-!
# Fermat's two-square theorem, hard direction (∅-axiom, computed witness)

`p` prime, `p ≡ 1 (mod 4)` ⟹ `∃ a b : Nat, p = a*a + b*b` (and the `Int`/`isSumTwoSq` form).

Classical proof = Thue's lemma (a `⌊√p⌋`-box pigeonhole giving a small `(a,b)` with
`a ≡ x·b (mod p)`) + a bounded descent.  ∅-axiom forces the colliding pair to be **computed**
(`Combinatorics.Pigeonhole.exists_collision_lt`) rather than an abstract `∃`.
-/

namespace E213.Lib.Math.NumberTheory.TwoSquareTheorem

open E213.Lib.Math.NumberTheory.PolyRoot (mod_eq_imp_dvd_sub int_dvd_to_nat nat_dvd_to_int natAbs_mul)
open E213.Lib.Math.NumberTheory.FourSquareSeed (natCast_sub dvd_of_mod_zero mod_zero_of_dvd)
open E213.Lib.Math.NumberTheory.IntSqrt (isqrt isqrt_bracket isqrt_sq_le)
open E213.Lib.Math.NumberTheory.FourSquare (natCast_natAbs_nonneg natAbs_pos_of_ne natCast_lt_imp sq_nonneg)
open E213.Meta.Int213 (add_nonneg)

/-! ## §1 — the modular algebraic core (over `ℤ`)

`p ∣ X²+1` and `p ∣ A + X·B`  ⟹  `p ∣ A²+B²`.
Identity: `A²+B² = (A − X·B)·(A + X·B) + B²·(X²+1)`. -/

/-- The Brahmagupta-style algebraic identity (pure `ring_intZ`). -/
theorem sq_sum_decomp (A B X : Int) :
    A * A + B * B = (A - X * B) * (A + X * B) + B * B * (X * X + 1) := by
  ring_intZ

/-- ★ **Modular core.**  `↑p ∣ X²+1` and `↑p ∣ A + X·B` ⟹ `↑p ∣ A²+B²`. -/
theorem dvd_sq_sum (p : Nat) (A B X : Int)
    (hX : (p : Int) ∣ (X * X + 1)) (hAB : (p : Int) ∣ (A + X * B)) :
    (p : Int) ∣ (A * A + B * B) := by
  rw [sq_sum_decomp A B X]
  obtain ⟨u, hu⟩ := hAB
  obtain ⟨v, hv⟩ := hX
  refine ⟨(A - X * B) * u + B * B * v, ?_⟩
  rw [hu, hv]; ring_intZ

/-! ## §2 — the Thue box collision (computed)

`q = isqrt p + 1`, so the box of pairs `(a,b)` with `a,b < q` has `q² > p` elements.
Map each pair to `(a + x·b) % p ∈ Fin p`; `exists_collision_lt` returns the colliding pair. -/

/-- Box-map value: `(a + x·b) % p`, bounded by `p`. -/
def boxVal (p x q i : Nat) : Nat := (i / q + x * (i % q)) % p

/-- ★★ **Thue collision (computed).**  For `q = isqrt p + 1` (so `p < q²`), the box map
    `i ↦ (i/q + x·(i%q)) % p : Fin (q*q) → Fin p` has two distinct indices `i ≠ j` colliding —
    *exhibited* by `exists_collision_lt`.  No `Classical`. -/
theorem thue_collision (p x : Nat) (hp0 : 0 < p) :
    ∃ i j : Nat, i < (isqrt p + 1) * (isqrt p + 1) ∧ j < (isqrt p + 1) * (isqrt p + 1) ∧
      i ≠ j ∧ boxVal p x (isqrt p + 1) i = boxVal p x (isqrt p + 1) j := by
  -- p < q*q  where  q = isqrt p + 1
  have hpq : p < (isqrt p + 1) * (isqrt p + 1) := (isqrt_bracket p).2
  -- the box map into Fin p
  let g : Fin ((isqrt p + 1) * (isqrt p + 1)) → Fin p :=
    fun i => ⟨boxVal p x (isqrt p + 1) i.val, Nat.mod_lt _ hp0⟩
  obtain ⟨i, j, hij, hgij⟩ :=
    E213.Lib.Math.Combinatorics.Pigeonhole.exists_collision_lt hpq g
  refine ⟨i.val, j.val, i.isLt, j.isLt, ?_, ?_⟩
  · intro h; exact hij (Fin.ext h)
  · exact congrArg Fin.val hgij

/-! ## §3 — small arithmetic helpers for the descent -/

/-- A prime `p` is not a perfect square: `isqrt p · isqrt p < p`. -/
theorem isqrt_sq_lt_of_prime (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    isqrt p * isqrt p < p := by
  rcases Nat.lt_or_eq_of_le (isqrt_sq_le p) with hlt | heq
  · exact hlt
  · exfalso
    -- isqrt p * isqrt p = p ⟹ isqrt p ∣ p ⟹ isqrt p = 1 ∨ isqrt p = p
    have hpne : p ≠ 1 := Nat.ne_of_gt hp
    have hdvd : isqrt p ∣ p := ⟨isqrt p, heq.symm⟩
    rcases hpr (isqrt p) hdvd with h1 | hpp
    · rw [h1, Nat.one_mul] at heq; exact hpne heq.symm
    · -- isqrt p = p ⟹ p*p = p ⟹ p = 1
      rw [hpp] at heq
      have hmul : p * 1 = p * p := by rw [Nat.mul_one]; exact heq.symm
      have hp1 : (1 : Nat) = p :=
        E213.Tactic.NatHelper.mul_left_cancel_pos (Nat.lt_trans (by decide) hp) hmul
      exact hpne hp1.symm

/-- A positive multiple of `p` strictly below `2p` is exactly `p`. -/
theorem eq_p_of_dvd_lt_two_mul {p n : Nat} (hp : 0 < p) (hd : p ∣ n) (h0 : 0 < n)
    (hlt : n < 2 * p) : n = p := by
  obtain ⟨c, hc⟩ := hd
  -- c ≥ 1 (else n = 0)
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · exfalso; rw [h, Nat.mul_zero] at hc; rw [hc] at h0; exact Nat.lt_irrefl 0 h0
    · exact h
  -- c < 2  (from p*c < 2*p = p*2 and p > 0)
  have hc2 : c < 2 := by
    rcases Nat.lt_or_ge c 2 with h | hge
    · exact h
    · exfalso
      -- c ≥ 2 ⟹ 2*p ≤ c*p = n, contradicting n < 2*p
      have hle : 2 * p ≤ c * p := Nat.mul_le_mul_right p hge
      have hcp : c * p = n := by rw [hc, Nat.mul_comm]
      rw [hcp] at hle
      exact absurd hle (Nat.not_le.mpr hlt)
  have hceq : c = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hc2) hc1
  rw [hc, hceq, Nat.mul_one]

/-- `A²` as a `Nat` cast: `A*A = ↑(A.natAbs * A.natAbs)`. -/
theorem sq_cast_natAbs (A : Int) : A * A = ((A.natAbs * A.natAbs : Nat) : Int) := by
  rw [← Int.natAbs_mul_self (a := A)]

/-- ★ **natAbs of a sum of two squares.**  `(A²+B²).natAbs = |A|² + |B|²`. -/
theorem natAbs_sq_sum (A B : Int) :
    (A * A + B * B).natAbs = A.natAbs * A.natAbs + B.natAbs * B.natAbs := by
  rw [sq_cast_natAbs A, sq_cast_natAbs B]
  exact Int.natAbs_ofNat _

/-! ## §4 — Thue's lemma (the small box pair, divisibility, computed)

From `qr_neg_one` (`p ∣ x²+1`) and the box collision, produce `a, b ≤ isqrt p`, not both `0`,
with `p ∣ a²+b²`.  This is the FALLBACK result — the full descent without the final `= p` step. -/

/-- `i < q*q` ⟹ `i/q ≤ q-1` and `i%q ≤ q-1`, i.e. both `≤ isqrt p` when `q = isqrt p + 1`. -/
theorem decode_le {q i : Nat} (hq : 0 < q) (hi : i < q * q) :
    i / q < q ∧ i % q < q :=
  ⟨E213.Meta.Nat.NatDiv213.div_lt_of_lt_mul hi, Nat.mod_lt _ hq⟩

/-- `(↑a - ↑c).natAbs ≤ a ⊔ c`; with `a, c < q` it is `≤ q-1`.  Here as: `a < q+1`, `c < q+1`
    (i.e. `≤ q`) ⟹ `(↑a-↑c).natAbs ≤ q`. -/
theorem natAbs_sub_le_of_lt {a c k : Nat} (ha : a < k + 1) (hc : c < k + 1) :
    ((a : Int) - (c : Int)).natAbs ≤ k := by
  have ha' : a ≤ k := Nat.le_of_lt_succ ha
  have hc' : c ≤ k := Nat.le_of_lt_succ hc
  rcases Nat.le_total c a with h | h
  · -- a ≥ c: ↑a - ↑c = ↑(a-c), natAbs = a - c ≤ a ≤ k
    have he : (a : Int) - (c : Int) = ((a - c : Nat) : Int) := (natCast_sub h).symm
    rw [he, Int.natAbs_ofNat]
    exact Nat.le_trans (Nat.sub_le a c) ha'
  · -- c ≥ a: ↑a - ↑c = -(↑(c-a)), natAbs = c - a ≤ c ≤ k
    have he : (a : Int) - (c : Int) = -(((c - a : Nat) : Int)) := by
      rw [natCast_sub h]; ring_intZ
    rw [he, Int.natAbs_neg, Int.natAbs_ofNat]
    exact Nat.le_trans (Nat.sub_le c a) hc'

/-- For `m ≠ n : Nat`, `(↑m - ↑n).natAbs ≠ 0`. -/
theorem natAbs_sub_ne_zero {m n : Nat} (h : m ≠ n) :
    ((m : Int) - (n : Int)).natAbs ≠ 0 := by
  intro h0
  have hz : (m : Int) - (n : Int) = 0 :=
    E213.Lib.Math.NumberTheory.FourSquare.natAbs_zero_imp h0
  have he : (m : Int) = (n : Int) := E213.Meta.Int213.Order.eq_of_sub_eq_zero hz
  exact h (Int.ofNat.inj he)

/-- `i ≠ j` ⟹ the two decoded differences are not both zero. -/
theorem decode_ne {q i j : Nat} (hij : i ≠ j) :
    (((i / q : Nat) : Int) - ((j / q : Nat) : Int)).natAbs ≠ 0
    ∨ (((i % q : Nat) : Int) - ((j % q : Nat) : Int)).natAbs ≠ 0 := by
  by_cases hdiv : i / q = j / q
  · -- divisions agree ⟹ remainders differ (else i = j)
    right
    refine natAbs_sub_ne_zero (fun hmod => ?_)
    have hi := (E213.Meta.Nat.AddMod213.div_add_mod i q)
    have hj := (E213.Meta.Nat.AddMod213.div_add_mod j q)
    rw [hdiv, hmod] at hi
    exact hij (hi.symm.trans hj)
  · exact Or.inl (natAbs_sub_ne_zero hdiv)

/-- ★★★ **Thue's lemma (computed).**  `p` prime, `p ≡ 1 (mod 4)` ⟹ there are `a, b ≤ isqrt p`,
    not both zero, with `p ∣ a² + b²` — the small box pair, produced by the constructive
    collision.  (The full two-square theorem adds the descent `a²+b² = p`.) -/
theorem thue_lemma (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hmod : p % 4 = 1) :
    ∃ a b : Nat, a ≤ isqrt p ∧ b ≤ isqrt p ∧ (a ≠ 0 ∨ b ≠ 0) ∧ p ∣ (a * a + b * b) := by
  have hp0 : 0 < p := Nat.lt_trans (by decide) hp
  -- x with p ∣ x²+1
  obtain ⟨x, hx⟩ := E213.Lib.Math.NumberTheory.ModArith.QRNegOne.qr_neg_one p hp hpr hmod
  -- the collision
  obtain ⟨i, j, hi, hj, hij, hcol⟩ := thue_collision p x hp0
  -- q = isqrt p + 1
  have hq0 : 0 < isqrt p + 1 := Nat.zero_lt_succ _
  -- decode bounds
  obtain ⟨ha1lt, hb1lt⟩ := decode_le hq0 hi
  obtain ⟨ha2lt, hb2lt⟩ := decode_le hq0 hj
  -- the four coordinates (Nat)
  -- a1 = i / q, b1 = i % q, a2 = j / q, b2 = j % q
  -- Over Int: A = a1 - a2, B = b1 - b2.  WLOG by symmetry handle via case on order.
  -- collision rewritten as a mod-equality
  have hcolmod : (i / (isqrt p + 1) + x * (i % (isqrt p + 1))) % p
               = (j / (isqrt p + 1) + x * (j % (isqrt p + 1))) % p := hcol
  -- abbreviations
  -- We work over Int with A,B and prove p ∣ A²+B², then take natAbs.
  -- A + X*B = (a1 + x*b1) - (a2 + x*b2) over Int.
  -- p ∣ that, from mod_eq_imp_dvd_sub.
  have hAB : (p : Int) ∣
      (((i / (isqrt p + 1) + x * (i % (isqrt p + 1)) : Nat) : Int)
        - ((j / (isqrt p + 1) + x * (j % (isqrt p + 1)) : Nat) : Int)) :=
    mod_eq_imp_dvd_sub _ _ p hcolmod
  -- rewrite the Int difference into A + X*B with A = ↑a1 - ↑a2, B = ↑b1 - ↑b2
  have hcast : (((i / (isqrt p + 1) + x * (i % (isqrt p + 1)) : Nat) : Int)
        - ((j / (isqrt p + 1) + x * (j % (isqrt p + 1)) : Nat) : Int))
      = (((i / (isqrt p + 1) : Nat) : Int) - ((j / (isqrt p + 1) : Nat) : Int))
        + (x : Int) * (((i % (isqrt p + 1) : Nat) : Int) - ((j % (isqrt p + 1) : Nat) : Int)) := by
    show ((((i / (isqrt p + 1)) : Nat) : Int) + ((x : Int) * ((i % (isqrt p + 1) : Nat) : Int)))
        - (((j / (isqrt p + 1) : Nat) : Int) + ((x : Int) * ((j % (isqrt p + 1) : Nat) : Int)))
       = _
    ring_intZ
  rw [hcast] at hAB
  -- p ∣ X²+1 over Int
  have hXint : (p : Int) ∣ ((x : Int) * (x : Int) + 1) := by
    have h := nat_dvd_to_int p ((x * x + 1 : Nat) : Int)
      (by rw [Int.natAbs_ofNat]; exact hx)
    have he : (((x * x + 1 : Nat)) : Int) = (x : Int) * (x : Int) + 1 := rfl
    rw [he] at h; exact h
  -- p ∣ A²+B²
  have hsq := dvd_sq_sum p
    (((i / (isqrt p + 1) : Nat) : Int) - ((j / (isqrt p + 1) : Nat) : Int))
    (((i % (isqrt p + 1) : Nat) : Int) - ((j % (isqrt p + 1) : Nat) : Int))
    (x : Int) hXint hAB
  -- take natAbs:  n = a²+b² with a = |A|, b = |B|
  have hnat : p ∣ ((((i / (isqrt p + 1) : Nat) : Int) - ((j / (isqrt p + 1) : Nat) : Int))
      * (((i / (isqrt p + 1) : Nat) : Int) - ((j / (isqrt p + 1) : Nat) : Int))
      + (((i % (isqrt p + 1) : Nat) : Int) - ((j % (isqrt p + 1) : Nat) : Int))
      * (((i % (isqrt p + 1) : Nat) : Int) - ((j % (isqrt p + 1) : Nat) : Int))).natAbs :=
    int_dvd_to_nat p _ hsq
  rw [natAbs_sq_sum] at hnat
  -- the witnesses
  refine ⟨(((i / (isqrt p + 1) : Nat) : Int) - ((j / (isqrt p + 1) : Nat) : Int)).natAbs,
          (((i % (isqrt p + 1) : Nat) : Int) - ((j % (isqrt p + 1) : Nat) : Int)).natAbs,
          ?_, ?_, ?_, hnat⟩
  · -- |a1 - a2| ≤ isqrt p :  both a1,a2 < q = isqrt p + 1, so ≤ isqrt p, diff abs ≤ isqrt p
    exact natAbs_sub_le_of_lt ha1lt ha2lt
  · exact natAbs_sub_le_of_lt hb1lt hb2lt
  · -- not both zero: i ≠ j and decode is injective
    exact decode_ne hij

/-! ## §5 — the descent: `a²+b² = p` -/

/-- ★★★★★ **Fermat's two-square theorem, hard direction (Nat form).**
    Every prime `p ≡ 1 (mod 4)` is a sum of two squares: `∃ a b, p = a*a + b*b`.
    The witnesses are the **computed** Thue box pair (via `exists_collision_lt`), descended:
    `a, b ≤ isqrt p` with `p ∣ a²+b²` and `0 < a²+b² ≤ 2·isqrt² p < 2p`, so `a²+b² = p`. -/
theorem two_square (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hmod : p % 4 = 1) : ∃ a b : Nat, p = a * a + b * b := by
  have hp0 : 0 < p := Nat.lt_trans (by decide) hp
  obtain ⟨a, b, ha, hb, hne, hdvd⟩ := thue_lemma p hp hpr hmod
  refine ⟨a, b, ?_⟩
  -- n = a²+b² is positive
  have hpos : 0 < a * a + b * b := by
    rcases hne with hA | hB
    · have : 0 < a * a := Nat.mul_pos (Nat.pos_of_ne_zero hA) (Nat.pos_of_ne_zero hA)
      exact Nat.lt_of_lt_of_le this (Nat.le_add_right _ _)
    · have : 0 < b * b := Nat.mul_pos (Nat.pos_of_ne_zero hB) (Nat.pos_of_ne_zero hB)
      exact Nat.lt_of_lt_of_le this (Nat.le_add_left _ _)
  -- n ≤ 2·isqrt²p
  have hbnd : a * a + b * b ≤ 2 * (isqrt p * isqrt p) := by
    have haa : a * a ≤ isqrt p * isqrt p := Nat.mul_le_mul ha ha
    have hbb : b * b ≤ isqrt p * isqrt p := Nat.mul_le_mul hb hb
    have : a * a + b * b ≤ isqrt p * isqrt p + isqrt p * isqrt p := Nat.add_le_add haa hbb
    rwa [← Nat.two_mul] at this
  -- isqrt²p < p, so 2·isqrt²p < 2p
  have hsqlt : isqrt p * isqrt p < p := isqrt_sq_lt_of_prime p hp hpr
  have h2lt : 2 * (isqrt p * isqrt p) < 2 * p :=
    E213.Meta.Nat.NatRing213.nat_mul_lt_mul_left (by decide) hsqlt
  have hlt : a * a + b * b < 2 * p := Nat.lt_of_le_of_lt hbnd h2lt
  exact (eq_p_of_dvd_lt_two_mul hp0 hdvd hpos hlt).symm

/-- ★★★★ **Two-square theorem, `Int` / `isSumTwoSq` form.**  Every prime `p ≡ 1 (mod 4)` is a
    sum of two integer squares (`isSumTwoSq ↑p`), reusing the corpus predicate. -/
theorem two_square_isSumTwoSq (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hmod : p % 4 = 1) : E213.Lib.Math.NumberTheory.SumTwoSquares.isSumTwoSq (p : Int) := by
  obtain ⟨a, b, hab⟩ := two_square p hp hpr hmod
  refine ⟨(a : Int), (b : Int), ?_⟩
  -- ↑p = ↑a*↑a + ↑b*↑b  from  p = a*a + b*b
  have he : ((p : Nat) : Int) = (((a * a + b * b : Nat)) : Int) := by rw [hab]
  rw [he]
  show ((a * a : Nat) : Int) + ((b * b : Nat) : Int) = (a : Int) * (a : Int) + (b : Int) * (b : Int)
  rfl

/-! ## §6 — concrete smokes (closed numerals)

Divisor dichotomy for the small primes via the bounded `prime_of_no_small_factor`. -/

open E213.Lib.Math.NumberTheory.PerfectNumbers (prime_of_bounded)

/-- `5` is prime (divisor dichotomy), bounded check `B = 3`. -/
theorem dich_5 : ∀ d, d ∣ (5 : Nat) → d = 1 ∨ d = 5 :=
  (prime_of_bounded (q := 5) (by decide) (B := 3) (by decide) (by decide)).2

/-- `13` is prime (divisor dichotomy), bounded check `B = 4`. -/
theorem dich_13 : ∀ d, d ∣ (13 : Nat) → d = 1 ∨ d = 13 :=
  (prime_of_bounded (q := 13) (by decide) (B := 4) (by decide) (by decide)).2

/-- `5 = a² + b²`, witnessed by the descent. -/
theorem smoke_5 : ∃ a b : Nat, (5 : Nat) = a * a + b * b :=
  two_square 5 (by decide) dich_5 (by decide)

/-- `13 = a² + b²`, witnessed by the descent. -/
theorem smoke_13 : ∃ a b : Nat, (13 : Nat) = a * a + b * b :=
  two_square 13 (by decide) dich_13 (by decide)

end E213.Lib.Math.NumberTheory.TwoSquareTheorem
