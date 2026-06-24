import E213.Lib.Math.NumberTheory.VpMulGrounded
import E213.Lib.Math.NumberTheory.PrimeFactorization

/-!
# FTA uniqueness as valuation-count invariance — fully grounded (∅-axiom)

`FTAUniqueness.factorization_unique` already states FTA uniqueness as valuation-count invariance, but
on the `Nat.mod`-based `vp`/`vp_mul` (`#print axioms`-clean, yet closure carries `Nat.mod`/
`Nat.lt_wfRel`).  This regrounds the *whole* statement on the structural `vpSub`/`vpSub_mul`
(`subMod`-based) and the grounded `prime_dvd_mul` — so the multiplicity of each prime is read off the
product with **no borrowed `Nat` division or well-foundedness anywhere in the closure**.

  * `vpSub_self_pow` — `vpSub q (qᵏ) = k` (`q ≥ 2`).
  * `vpSub_prodL_eq_countOcc` — `vpSub q (prodL l) = countOcc q l` for a prime list `l`.
  * `factorization_unique` — two prime lists with equal product have equal `countOcc` at every prime.
    **This IS FTA uniqueness** (same prime multiset), grounded end to end.

∅-axiom; closure free of `Nat.div`/`Nat.mod`/`Nat.lt_wfRel`.
-/

namespace E213.Lib.Math.NumberTheory.FTAUniquenessGrounded

open E213.Lib.Math.NumberTheory.PrimeFactorization (prodL prodL_cons)
open E213.Lib.Math.NumberTheory.VpMulGrounded (vpSub_mul)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Meta.Nat.VpSub213 (vpSub le_vpSub_iff)
open E213.Meta.Nat.Valuation (drefl)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-! ## §0 — structural occurrence count (PURE; no `List.count`) -/

/-- Number of times `q` appears in `l`.  Structural `List` recursion. -/
def countOcc (q : Nat) : List Nat → Nat
  | []      => 0
  | x :: xs => (if x = q then 1 else 0) + countOcc q xs

theorem countOcc_cons (q x : Nat) (xs : List Nat) :
    countOcc q (x :: xs) = (if x = q then 1 else 0) + countOcc q xs := rfl

/-- Product of a list of positive primes is positive. -/
theorem prodL_pos : ∀ l : List Nat, (∀ x, x ∈ l → Prime213 x) → 0 < prodL l
  | [],      _ => (by decide : (0:Nat) < 1)
  | y :: ys, hall => by
    have hy : Prime213 y := hall y (List.Mem.head ys)
    have hypos : 0 < y := Nat.lt_of_lt_of_le (by decide) hy.1
    have hys : ∀ x, x ∈ ys → Prime213 x := fun x hx => hall x (List.Mem.tail y hx)
    rw [prodL_cons]
    exact Nat.mul_pos hypos (prodL_pos ys hys)

/-! ## §1 — `vpSub` of a prime power and a single prime -/

/-- `vpSub q (qᵏ) = k` (`q ≥ 2`).  Lower bound `qᵏ ∣ qᵏ`; upper bound `q^{k+1} ∤ qᵏ` (since
    `q^{k+1} > qᵏ`).  Grounded analogue of `VpMul.vp_self_pow`. -/
theorem vpSub_self_pow {q : Nat} (hq : 2 ≤ q) (k : Nat) : vpSub q (q ^ k) = k := by
  have hq0 : 0 < q := Nat.lt_of_lt_of_le (by decide) hq
  have hpk : 0 < q ^ k := Nat.pos_pow_of_pos k hq0
  -- q^k < q^(k+1)
  have hgt : q ^ k < q ^ (k + 1) := by
    rw [Nat.pow_succ]
    have h1 : q ^ k * 2 ≤ q ^ k * q := Nat.mul_le_mul (Nat.le_refl _) hq
    have h2 : q ^ k < q ^ k * 2 := by rw [Nat.mul_two]; exact Nat.lt_add_of_pos_right hpk
    exact Nat.lt_of_lt_of_le h2 h1
  refine Nat.le_antisymm ?_ ((le_vpSub_iff q (q ^ k) k hq hpk).mp (drefl _))
  -- vpSub ≤ k : else q^(k+1) ∣ q^k forces q^(k+1) ≤ q^k, contra
  apply Nat.le_of_lt_succ
  apply Nat.lt_of_not_le
  intro hge
  have hdvd : q ^ (k + 1) ∣ q ^ k := (le_vpSub_iff q (q ^ k) (k + 1) hq hpk).mpr hge
  exact absurd (le_of_dvd_pos (q ^ (k + 1)) (q ^ k) hpk hdvd) (Nat.not_le_of_lt hgt)

/-- `vpSub q p` for primes `q`, `p`: `1` if `p = q`, else `0` (`q ∤ p`).  No `FoldCriterion` import —
    `q ∤ p` is inlined from primality of `p` (`q = 1 ∨ q = p`, both excluded). -/
theorem vpSub_prime_single {q p : Nat} (hq : Prime213 q) (hp : Prime213 p) :
    vpSub q p = (if p = q then 1 else 0) := by
  by_cases hpq : p = q
  · rw [if_pos hpq, hpq]
    have h := vpSub_self_pow hq.1 1
    rwa [Nat.pow_one] at h
  · rw [if_neg hpq]
    have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
    -- q ∤ p
    have hnd : ¬ q ∣ p := by
      intro hqp
      rcases hp.2 q hqp with h1 | hpe
      · exact absurd h1 (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hq.1))
      · exact hpq hpe.symm
    -- vpSub q p = 0
    rcases Nat.eq_zero_or_pos (vpSub q p) with h0 | hpos
    · exact h0
    · exact absurd ((le_vpSub_iff q p 1 hq.1 hppos).mpr hpos) (by rwa [Nat.pow_one])

/-! ## §2 — valuation reads occurrence count -/

/-- ★ **Valuation = occurrence count, grounded.**  For a list `l` of primes,
    `vpSub q (prodL l) = countOcc q l` (`q` prime).  Induction on `l` via `vpSub_mul`. -/
theorem vpSub_prodL_eq_countOcc {q : Nat} (hq : Prime213 q) :
    ∀ l : List Nat, (∀ x, x ∈ l → Prime213 x) → vpSub q (prodL l) = countOcc q l := by
  intro l
  induction l with
  | nil =>
    intro _
    show vpSub q (prodL []) = countOcc q []
    have h0 := vpSub_self_pow hq.1 0
    rw [Nat.pow_zero] at h0
    exact h0
  | cons p rest ih =>
    intro hall
    have hp : Prime213 p := hall p (List.Mem.head rest)
    have hrest : ∀ x, x ∈ rest → Prime213 x := fun x hx => hall x (List.Mem.tail p hx)
    have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
    have hprodpos : 0 < prodL rest := prodL_pos rest hrest
    rw [prodL_cons, vpSub_mul hq hppos hprodpos, vpSub_prime_single hq hp, ih hrest, countOcc_cons]

/-! ## §3 — FTA uniqueness -/

/-- ★★★ **FTA uniqueness = valuation-count invariance, grounded.**  Two prime lists `l1`, `l2` with
    `prodL l1 = prodL l2` have equal occurrence count at every prime `q` — both equal `vpSub q n`.
    No multiset-permutation bookkeeping, no UFD; the multiplicity of each prime is read off the
    product, and the whole chain (valuation, multiplicativity, Euclid's lemma, Bézout, division) is
    `subMod`-grounded — no `Nat.div`/`Nat.mod`/`Nat.lt_wfRel`. -/
theorem factorization_unique {l1 l2 : List Nat}
    (h1 : ∀ x, x ∈ l1 → Prime213 x) (h2 : ∀ x, x ∈ l2 → Prime213 x)
    (heq : prodL l1 = prodL l2) :
    ∀ q, Prime213 q → countOcc q l1 = countOcc q l2 := by
  intro q hq
  calc countOcc q l1 = vpSub q (prodL l1) := (vpSub_prodL_eq_countOcc hq l1 h1).symm
    _ = vpSub q (prodL l2) := by rw [heq]
    _ = countOcc q l2 := vpSub_prodL_eq_countOcc hq l2 h2

end E213.Lib.Math.NumberTheory.FTAUniquenessGrounded
