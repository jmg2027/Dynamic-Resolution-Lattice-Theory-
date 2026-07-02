import E213.Lib.Math.NumberTheory.AperyRecurrence
import E213.Lib.Math.NumberTheory.AperyIntegrality
import E213.Lib.Math.NumberTheory.AperyCollapsing

/-!
# Zeta3Numerator — the cleared harmonic part of the numerator recurrence

The numerator Apéry number `A(n) = H₃(n)·B(n) + K(n)` satisfies Apéry's recurrence
iff the kernel `K` satisfies an inhomogeneous one; the `H₃` (harmonic) part follows
from `apery_recurrence` plus the harmonic telescoping `H₃(n)−H₃(n−1)=1/n³`.

This file lands that harmonic part, ∅-axiom, in cleared form: with `ℓ` a common
multiple of the cubes `1³…N³` (later `ℓ=lcm(1..N)³`), `HL ℓ n = Σ_{i=1}^n ℓ/i³`
is the cleared `ℓ·H₃(n)`, and the cleared identity holds.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.Zeta3Numerator

open E213.Lib.Math.NumberTheory.AperyRecurrence (B aperyLead apery_recurrence)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose)
open E213.Meta.Nat.NatDiv213 (div_add_mod_pure mul_witness_iff_mod_eq_zero)
open E213.Lib.Math.NumberTheory.AperyIntegrality (cube_dvd_lcm_cube heart_lcm)
open E213.Lib.Math.NumberTheory.LcmGrowthChebyshev (lcmUpTo dvd_lcmUpTo lcmUpTo_dvd)
open E213.Lib.Math.NumberTheory.AperyCollapsing (sqw)
open E213.Tactic.NatHelper (add_sub_of_le)

/-- `a ∣ b → a·(b/a) = b`, ∅-axiom. -/
private theorem dvd_mul_div {a b : Nat} (h : a ∣ b) : a * (b / a) = b := by
  rcases h with ⟨c, hc⟩
  have hmod : b % a = 0 := (mul_witness_iff_mod_eq_zero a b).mp ⟨c, hc.symm⟩
  have hdm := div_add_mod_pure b a
  rw [hmod, Nat.add_zero] at hdm
  exact hdm

/-- The cleared harmonic sum `HL ℓ n = Σ_{i=1}^n ℓ/i³` (`= ℓ·H₃(n)` when `i³ ∣ ℓ`). -/
def HL (ℓ : Nat) (n : Nat) : Nat := sumTo n (fun i => ℓ / ((i + 1) * (i + 1) * (i + 1)))

/-- The harmonic telescoping: `(n+1)³·HL ℓ (n+1) = (n+1)³·HL ℓ n + ℓ` when `(n+1)³ ∣ ℓ`. -/
theorem HL_step {ℓ n : Nat} (h : (n + 1) * (n + 1) * (n + 1) ∣ ℓ) :
    (n + 1) * (n + 1) * (n + 1) * HL ℓ (n + 1)
      = (n + 1) * (n + 1) * (n + 1) * HL ℓ n + ℓ := by
  show (n + 1) * (n + 1) * (n + 1) * sumTo (n + 1) (fun i => ℓ / ((i + 1) * (i + 1) * (i + 1)))
    = (n + 1) * (n + 1) * (n + 1) * sumTo n (fun i => ℓ / ((i + 1) * (i + 1) * (i + 1))) + ℓ
  rw [sumTo_succ, Nat.mul_add, dvd_mul_div h]

/-- ★★ **The cleared `H₃`-part of the numerator recurrence** (additive ℕ form):
    follows from `apery_recurrence` × `HL ℓ (j+1)` with the harmonic telescoping
    absorbing the `ℓ·B` terms.  (`ℓ` a common multiple of `(j+1)³`, `(j+2)³`.) -/
theorem harmonic_part_recurrence (j ℓ : Nat)
    (h1 : (j + 1) * (j + 1) * (j + 1) ∣ ℓ) (h2 : (j + 2) * (j + 2) * (j + 2) ∣ ℓ) :
    (j + 2) * (j + 2) * (j + 2) * HL ℓ (j + 2) * B (j + 2)
      + ((j + 1) * (j + 1) * (j + 1) * HL ℓ j * B j + ℓ * B j)
    = aperyLead j * (HL ℓ (j + 1) * B (j + 1)) + ℓ * B (j + 2) := by
  have hs2 : (j + 2) * (j + 2) * (j + 2) * HL ℓ (j + 2)
      = (j + 2) * (j + 2) * (j + 2) * HL ℓ (j + 1) + ℓ := HL_step h2
  have hs1 : (j + 1) * (j + 1) * (j + 1) * HL ℓ (j + 1)
      = (j + 1) * (j + 1) * (j + 1) * HL ℓ j + ℓ := HL_step h1
  have hrec := apery_recurrence j
  calc (j + 2) * (j + 2) * (j + 2) * HL ℓ (j + 2) * B (j + 2)
          + ((j + 1) * (j + 1) * (j + 1) * HL ℓ j * B j + ℓ * B j)
      = ((j + 2) * (j + 2) * (j + 2) * HL ℓ (j + 2)) * B (j + 2)
          + ((j + 1) * (j + 1) * (j + 1) * HL ℓ j + ℓ) * B j := by ring_nat
    _ = ((j + 2) * (j + 2) * (j + 2) * HL ℓ (j + 1) + ℓ) * B (j + 2)
          + ((j + 1) * (j + 1) * (j + 1) * HL ℓ (j + 1)) * B j := by rw [hs2, hs1]
    _ = HL ℓ (j + 1) * ((j + 2) * (j + 2) * (j + 2) * B (j + 2)
          + (j + 1) * (j + 1) * (j + 1) * B j) + ℓ * B (j + 2) := by ring_nat
    _ = HL ℓ (j + 1) * (aperyLead j * B (j + 1)) + ℓ * B (j + 2) := by rw [hrec]
    _ = aperyLead j * (HL ℓ (j + 1) * B (j + 1)) + ℓ * B (j + 2) := by ring_nat

/-- `x³ = x·x·x` (the explicit-product form `HL`/`harmonic_part_recurrence` use). -/
private theorem pow_three_eq (x : Nat) : x ^ 3 = x * x * x := by
  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_one]

/-- ★★ **The harmonic recurrence with the genuine `lcm³` clearing factor.**  Instantiates
    `harmonic_part_recurrence` at `ℓ = lcm(1..N)³`, discharging both divisibility
    hypotheses with `cube_dvd_lcm_cube` (`i³ ∣ lcm(1..N)³` for `1 ≤ i ≤ N`).  This is the
    chaining step that turns the abstract cleared-harmonic recurrence into the concrete
    one over the real Apéry clearing factor `lcm(1..N)³` — so `HL (lcm N ³) ·` is the
    genuine integral `lcm³·H₃`, the `H₃`-part contribution to `(n!)³ ∣ 2·lcm³·zeta3Num n`.
    (The kernel half proceeds by the extended-language certificate:
    `numerator_plan.md` §"THE NUMERATOR CERTIFICATE".) -/
theorem harmonic_recurrence_lcm (j N : Nat) (hjN : j + 2 ≤ N) :
    (j + 2) * (j + 2) * (j + 2) * HL (lcmUpTo N ^ 3) (j + 2) * B (j + 2)
      + ((j + 1) * (j + 1) * (j + 1) * HL (lcmUpTo N ^ 3) j * B j + lcmUpTo N ^ 3 * B j)
    = aperyLead j * (HL (lcmUpTo N ^ 3) (j + 1) * B (j + 1)) + lcmUpTo N ^ 3 * B (j + 2) := by
  have hj1N : j + 1 ≤ N := Nat.le_trans (Nat.le_succ (j + 1)) hjN
  have h1 : (j + 1) * (j + 1) * (j + 1) ∣ lcmUpTo N ^ 3 := by
    have hd := cube_dvd_lcm_cube (j := j + 1) (n := N) (Nat.succ_le_succ (Nat.zero_le j)) hj1N
    rwa [pow_three_eq] at hd
  have h2 : (j + 2) * (j + 2) * (j + 2) ∣ lcmUpTo N ^ 3 := by
    have hd := cube_dvd_lcm_cube (j := j + 2) (n := N) (Nat.succ_le_succ (Nat.zero_le (j + 1))) hjN
    rwa [pow_three_eq] at hd
  exact harmonic_part_recurrence j (lcmUpTo N ^ 3) h1 h2

/-! ## §kernel — the weighted cleared kernel term (round-5 representation layer)

The kernel `κ(n,k) = Σ_{m=1}^k (−1)^{m−1}/(2m³·C(n,m)·C(n+m,m))` clears against
`2·lcm(1..N)³·√b(n,k)` **term by term** (the `2`s cancel): the weighted cleared
kernel term is

    ktw N n k m  =  lcm(1..N)³·√b(n,k) / (m³·C(n,m)·C(n+m,m)),

a genuine Nat for `1 ≤ m ≤ k ≤ n ≤ N` (`heart_lcm` + lcm-monotonicity), deposited
÷-free as `ktw_mul_eq`.  The signed-sum representation over `ktw` (parity-split
`sumTo`s) and the column reweighting
`(k+1)²·ktw(k+1,m) = (n−k)(n+k+1)·ktw(k,m)` (a `sqw_shift_k` corollary by
cancellation) are the recorded round-5 frontier
(`zeta3_wz/numerator_plan.md` §"Round-5 blueprint"). -/

/-- **The weighted cleared kernel term**
    `ktw N n k m = lcm(1..N)³·√b(n,k) / (m³·C(n,m)·C(n+m,m))` — the `m`-th kernel
    summand of `c(n,k)`, cleared by `2·lcm³·√b(n,k)` (the `2`s cancel). -/
def ktw (N n k m : Nat) : Nat :=
  lcmUpTo N ^ 3 * sqw n k / (m * m * m * (choose n m * choose (n + m) m))

/-- The divisibility behind `ktw`: `m³·C(n,m)·C(n+m,m) ∣ lcm(1..N)³·√b(n,k)` for
    `1 ≤ m ≤ k ≤ n ≤ N` — `heart_lcm` at `(a,b) = (n−k, k−m)` (additive
    substitution), lifted from `lcm(1..n)` to `lcm(1..N)` by lcm-monotonicity. -/
theorem ktw_dvd {N n k m : Nat} (hm : 1 ≤ m) (hmk : m ≤ k) (hkn : k ≤ n)
    (hnN : n ≤ N) :
    m * m * m * (choose n m * choose (n + m) m) ∣ lcmUpTo N ^ 3 * sqw n k := by
  obtain ⟨b, rfl⟩ : ∃ b, k = m + b := ⟨k - m, (add_sub_of_le hmk).symm⟩
  obtain ⟨a, rfl⟩ : ∃ a, n = m + b + a := ⟨n - (m + b), (add_sub_of_le hkn).symm⟩
  show m * m * m * (choose (m + b + a) m * choose (m + b + a + m) m)
      ∣ lcmUpTo N ^ 3
        * (choose (m + b + a) (m + b) * choose (m + b + a + (m + b)) (m + b))
  have h := heart_lcm (m := m) (a := a) (b := b) hm
  rw [show m + a + b = m + b + a from by ring_nat,
      show 2 * m + a + b = m + b + a + m from by ring_nat,
      show 2 * m + a + 2 * b = m + b + a + (m + b) from by ring_nat,
      pow_three_eq m, pow_three_eq (lcmUpTo (m + b + a))] at h
  -- h : m·m·m·(C(n,m)·C(n+m,m)) ∣ lcm(1..n)·lcm·lcm·(C(n,k)·C(n+k,k))
  rcases h with ⟨q, hq⟩
  rcases lcmUpTo_dvd (fun j hj0 hjn => dvd_lcmUpTo hj0 (Nat.le_trans hjn hnN))
    with ⟨c, hc⟩
  -- hc : lcmUpTo N = lcmUpTo (m+b+a) * c
  refine ⟨q * (c * c * c), ?_⟩
  rw [pow_three_eq (lcmUpTo N), hc]
  calc (lcmUpTo (m + b + a) * c) * (lcmUpTo (m + b + a) * c) * (lcmUpTo (m + b + a) * c)
          * (choose (m + b + a) (m + b) * choose (m + b + a + (m + b)) (m + b))
      = (lcmUpTo (m + b + a) * lcmUpTo (m + b + a) * lcmUpTo (m + b + a)
          * (choose (m + b + a) (m + b) * choose (m + b + a + (m + b)) (m + b)))
        * (c * c * c) := by ring_nat
    _ = (m * m * m * (choose (m + b + a) m * choose (m + b + a + m) m) * q)
        * (c * c * c) := by rw [hq]
    _ = m * m * m * (choose (m + b + a) m * choose (m + b + a + m) m)
        * (q * (c * c * c)) := by ring_nat

/-- ★★ **The `ktw` characterization, ÷-free**:
    `m³·C(n,m)·C(n+m,m) · ktw N n k m = lcm(1..N)³·√b(n,k)` for
    `1 ≤ m ≤ k ≤ n ≤ N` — the term-level integrality of the cleared kernel,
    the representation-layer bedrock of the ζ(3) numerator assembly. -/
theorem ktw_mul_eq {N n k m : Nat} (hm : 1 ≤ m) (hmk : m ≤ k) (hkn : k ≤ n)
    (hnN : n ≤ N) :
    m * m * m * (choose n m * choose (n + m) m) * ktw N n k m
    = lcmUpTo N ^ 3 * sqw n k :=
  dvd_mul_div (ktw_dvd hm hmk hkn hnN)

end E213.Lib.Math.NumberTheory.Zeta3Numerator
