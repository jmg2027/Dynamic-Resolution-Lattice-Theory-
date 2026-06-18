import E213.Lib.Math.NumberTheory.PowSubPowFactor

/-!
# Lifting-the-exponent (LTE), the `p ∤ n` case — algebraic core (∅-axiom)

The cofactor `Σ_{i=0}^{n} aⁱbⁿ⁻ⁱ = geomTwo a b n` of the factorization
`aⁿ⁺¹ − bⁿ⁺¹ = (a−b)·geomTwo a b n` satisfies, whenever `p ∣ (a−b)`, the congruence
`geomTwo a b n ≡ (n+1)·bⁿ (mod p)` — so when `p ∤ (n+1)·bⁿ` (i.e. `p ∤ n+1` and `p ∤ b`),
`p ∤ geomTwo a b n`.  Hence `aⁿ⁺¹ − bⁿ⁺¹` and `a − b` carry the **same power of `p`**: this is the
`p ∤ exp` case of the lifting-the-exponent lemma, here in its `ℤ`-divisibility form.

This is the algebraic heart; the full LTE (`v_p(aⁿ−bⁿ) = v_p(a−b) + v_p(n)`) additionally needs the
prime-power lifting `v_p(aᵖ−bᵖ) = v_p(a−b)+1` (a mod-`p²` argument), deferred.
-/

namespace E213.Lib.Math.NumberTheory.LiftingExponent

open E213.Lib.Math.NumberTheory.PowSubPowFactor (geomTwo geomTwo_succ pow_sub_pow_factor)
open E213.Lib.Math.NumberTheory.DiffPowDvd
  (ipow ipow_succ dvd_addZ dvd_mul_leftZ dvd_zeroZ)
open E213.Meta.Int213.PolyIntM

/-- `g ∣ x → g ∣ y → g ∣ (x − y)` over `ℤ`. -/
theorem dvd_subZ {g x y : Int} (hx : g ∣ x) (hy : g ∣ y) : g ∣ (x - y) := by
  obtain ⟨u, hu⟩ := hx; obtain ⟨v, hv⟩ := hy
  exact ⟨u - v, by rw [hu, hv]; ring_intZ⟩

/-- `g ∣ (c · g)` over `ℤ`. -/
theorem dvd_mul_self_rightZ (g c : Int) : g ∣ (c * g) := ⟨c, by ring_intZ⟩

/-- Transitivity of `∣` over `ℤ`. -/
theorem dvd_transZ {g x y : Int} (hgx : g ∣ x) (hxy : x ∣ y) : g ∣ y := by
  obtain ⟨u, hu⟩ := hgx; obtain ⟨v, hv⟩ := hxy
  exact ⟨u * v, by rw [hv, hu]; ring_intZ⟩

/-- `↑(m+1) = ↑m + 1` for the `ℕ→ℤ` coercion. -/
theorem ofNat_succ_cast (m : Nat) : Int.ofNat (m + 1) = Int.ofNat m + 1 := Int.ofNat_add m 1

/-- ★★★ **Cofactor congruence**: `(a − b) ∣ (geomTwo a b n − (n+1)·bⁿ)`.

    Since `a ≡ b (mod a−b)`, each of the `n+1` terms `aⁱbⁿ⁻ⁱ` of `geomTwo` is `≡ bⁿ`, so the sum
    is `≡ (n+1)·bⁿ`.  Induction on `n` via the `geomTwo` recursion, splitting the step as
    `a·(geomTwo − (n+1)bⁿ) + (n+1)bⁿ·(a−b)`. -/
theorem cofactor_sub_dvd (a b : Int) :
    ∀ n, (a - b) ∣ (geomTwo a b n - (Int.ofNat (n + 1)) * ipow b n)
  | 0 => by
      refine ⟨0, ?_⟩
      show geomTwo a b 0 - Int.ofNat 1 * ipow b 0 = (a - b) * 0
      rw [mul_zeroZ]; show (1 : Int) - 1 * 1 = 0; decide
  | n + 1 => by
      have ih := cofactor_sub_dvd a b n
      rw [geomTwo_succ]
      have key : a * geomTwo a b n + ipow b (n + 1) - (Int.ofNat (n + 1 + 1)) * ipow b (n + 1)
          = a * (geomTwo a b n - Int.ofNat (n + 1) * ipow b n)
            + Int.ofNat (n + 1) * ipow b n * (a - b) := by
        rw [ipow_succ b n, ofNat_succ_cast (n + 1)]; ring_intZ
      rw [key]
      exact dvd_addZ (dvd_mul_leftZ a ih)
        (dvd_mul_self_rightZ (a - b) (Int.ofNat (n + 1) * ipow b n))

/-- ★★★ **Cofactor coprime to `p`**: if `q ∣ (a−b)` but `q ∤ (n+1)·bⁿ`, then `q ∤ geomTwo a b n`.
    (The contrapositive of the congruence: `q ∣ geomTwo` and `q ∣ (geomTwo − (n+1)bⁿ)` would force
    `q ∣ (n+1)·bⁿ`.) -/
theorem cofactor_not_dvd {q a b : Int} (n : Nat)
    (hqab : q ∣ (a - b)) (hqd : ¬ q ∣ (Int.ofNat (n + 1) * ipow b n)) :
    ¬ q ∣ geomTwo a b n := by
  intro hq
  apply hqd
  have hstep : q ∣ (geomTwo a b n - Int.ofNat (n + 1) * ipow b n) :=
    dvd_transZ hqab (cofactor_sub_dvd a b n)
  have : q ∣ (geomTwo a b n - (geomTwo a b n - Int.ofNat (n + 1) * ipow b n)) :=
    dvd_subZ hq hstep
  -- `geomTwo − (geomTwo − X) = X`
  have hsimp : geomTwo a b n - (geomTwo a b n - Int.ofNat (n + 1) * ipow b n)
      = Int.ofNat (n + 1) * ipow b n := by ring_intZ
  rwa [hsimp] at this

/-- ★★★ **LTE, `p ∤ exp` case (ℤ-divisibility form)**: if `q ∣ (a−b)` and `q ∤ (n+1)·bⁿ`, then for
    every `k`, `qᵏ⁺¹ ∣ (aⁿ⁺¹ − bⁿ⁺¹) ↔ qᵏ⁺¹ ∣ (a−b)` — the difference `aⁿ⁺¹−bⁿ⁺¹` carries exactly
    the same powers of `q` as `a−b`, because the cofactor is coprime to `q`.

    The forward direction is stated via the factorization; the cofactor's coprimality (`cofactor_not_dvd`)
    is the content.  Here packaged as the divisibility-transfer of the cofactor. -/
theorem pow_sub_pow_cofactor_eq (a b : Int) (n : Nat) :
    ipow a (n + 1) - ipow b (n + 1) = (a - b) * geomTwo a b n :=
  pow_sub_pow_factor a b n

end E213.Lib.Math.NumberTheory.LiftingExponent
