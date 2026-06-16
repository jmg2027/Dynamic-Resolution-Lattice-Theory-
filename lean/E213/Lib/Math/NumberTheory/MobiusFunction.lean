import E213.Lib.Math.NumberTheory.EulerTotient

/-!
# Number-theoretic Möbius function μ + Möbius identities (∅-axiom)

Companion to `EulerTotient.lean`.  Introduces the **number-theoretic** Möbius
function μ (Int-valued: −1 is possible) as a ∅-axiom computable definition and
verifies the two core Möbius identities over a range.

  * `mu n`               — μ(n) = 0 if n not squarefree, else (−1)^(#distinct primes).
  * `divisorSumZ n f`    — Int-valued `Σ_{d ∣ n, 1 ≤ d ≤ n} f d`.
  * `mobiusSum n`        — `Σ_{d ∣ n} μ(d)`.
  * `mobiusTotientSum n` — `Σ_{d ∣ n} μ(d)·(n/d)` (Möbius inversion of the Gauss sum).
  * ★ `mobius_divisor_sum_table` — `Σ_{d∣n} μ(d) = [n=1]`, verified n = 1..24.
  * ★ `mobius_totient_table`     — `Σ_{d∣n} μ(d)·(n/d) = φ(n)`, verified n = 1..20.

`mu` is **general-computable** (not a lookup table): fuel-bounded trial division
that strips the smallest prime factor, detects a squared factor (→ 0) and tracks
the sign parity.  PURE (propext-free): branching is `cond`/`Bool.toNat` (no
`if`/`ite`), recursion is structural on the fuel argument (no termination proof),
Int signs explicit.  Tables close by `decide`.

The general theorems (all n) use the partition-by-divisor toolkit (Möbius inversion
is the dual of the Gauss sum, sharing the same `count_partition_by_key` toolkit).
The corpus had no number-theoretic `mu`/`mobius` (the NumberSystems hits are
poset/p-adic Möbius — a different object).
-/

namespace E213.Lib.Math.NumberTheory.MobiusFunction

open E213.Lib.Math.NumberTheory.EulerTotient (totient dvdInd)

/-- Int-valued Σ over `[0, n)` (local; corpus `sumTo` is `Nat → Nat`). -/
def sumZ : Nat → (Nat → Int) → Int
  | 0,     _ => 0
  | n + 1, f => sumZ n f + f n

/-! ## Möbius function (general-computable, fuel-bounded trial division) -/

/-- Fuel-bounded core of μ.  `muAux fuel m d sign`: strips prime factors of the
    remaining value `m`, scanning candidate divisors from `d` upward, with
    accumulated `sign`.
    * `fuel = 0`  → return accumulated `sign` (callers supply enough fuel that this
      is only reached once `m` is exhausted).
    * `m == 1`    → done; return `sign`.
    * `d ∣ m`     → `d` is the smallest prime factor; strip it:
        if `d ∣ (m/d)` (i.e. `d² ∣ m`) → not squarefree, return `0`;
        else flip the sign and recurse on `m/d` from candidate `d+1`.
    * otherwise   → advance the candidate `d → d+1`.
    propext-free: every branch via `cond` on a `Bool`. -/
def muAux : Nat → Nat → Nat → Int → Int
  | 0,        _, _, sign => sign
  | fuel + 1, m, d, sign =>
    cond (m == 1)
      sign
      (cond (m % d == 0)
        (cond ((m / d) % d == 0)
          0
          (muAux fuel (m / d) (d + 1) (- sign)))
        (muAux fuel m (d + 1) sign))

/-- Number-theoretic Möbius function.
    `mu 0 = 0`, `mu 1 = 1`, otherwise trial-division from the smallest candidate
    `2` with fuel `n` (more than enough scans). -/
def mu : Nat → Int
  | 0     => 0
  | 1     => 1
  | n + 2 => muAux (n + 2) (n + 2) 2 1

/-! ## Int-valued divisor sum -/

/-- Int-valued divisor sum `Σ_{d ∣ n, 1 ≤ d ≤ n} f d`, mirroring
    `EulerTotient.divisorSum` but Int-valued (casts the `Bool` indicator). -/
def divisorSumZ (n : Nat) (f : Nat → Int) : Int :=
  sumZ n (fun j => (dvdInd j n : Int) * f (j + 1))

/-- `Σ_{d ∣ n} μ(d)`. -/
def mobiusSum (n : Nat) : Int := divisorSumZ n mu

/-- `Σ_{d ∣ n} μ(d)·(n/d)` — Möbius inversion of the Gauss sum `Σ φ = n`. -/
def mobiusTotientSum (n : Nat) : Int :=
  divisorSumZ n (fun d => mu d * (n / d : Nat))

/-! ## Tables (∅-axiom, by `decide`) -/

/-- μ(1..12) = 1, −1, −1, 0, −1, 1, −1, 0, 0, 1, −1, 0. -/
theorem mobius_table :
    mu 1 = 1 ∧ mu 2 = -1 ∧ mu 3 = -1 ∧ mu 4 = 0 ∧
    mu 5 = -1 ∧ mu 6 = 1 ∧ mu 7 = -1 ∧ mu 8 = 0 ∧
    mu 9 = 0 ∧ mu 10 = 1 ∧ mu 11 = -1 ∧ mu 12 = 0 := by
  decide

/-- ★ **Möbius divisor-sum identity**, verified n = 1..24:
    `Σ_{d∣n} μ(d) = [n=1]` (1 if n = 1, else 0). -/
theorem mobius_divisor_sum_table :
    mobiusSum 1 = 1 ∧ mobiusSum 2 = 0 ∧ mobiusSum 3 = 0 ∧ mobiusSum 4 = 0 ∧
    mobiusSum 5 = 0 ∧ mobiusSum 6 = 0 ∧ mobiusSum 7 = 0 ∧ mobiusSum 8 = 0 ∧
    mobiusSum 9 = 0 ∧ mobiusSum 10 = 0 ∧ mobiusSum 11 = 0 ∧ mobiusSum 12 = 0 ∧
    mobiusSum 13 = 0 ∧ mobiusSum 14 = 0 ∧ mobiusSum 15 = 0 ∧ mobiusSum 16 = 0 ∧
    mobiusSum 17 = 0 ∧ mobiusSum 18 = 0 ∧ mobiusSum 19 = 0 ∧ mobiusSum 20 = 0 ∧
    mobiusSum 21 = 0 ∧ mobiusSum 22 = 0 ∧ mobiusSum 23 = 0 ∧ mobiusSum 24 = 0 := by
  decide

/-- ★ **Möbius inversion of the Gauss sum**, verified n = 1..20:
    `Σ_{d∣n} μ(d)·(n/d) = φ(n)`. -/
theorem mobius_totient_table :
    mobiusTotientSum 1 = (totient 1 : Int) ∧ mobiusTotientSum 2 = (totient 2 : Int) ∧
    mobiusTotientSum 3 = (totient 3 : Int) ∧ mobiusTotientSum 4 = (totient 4 : Int) ∧
    mobiusTotientSum 5 = (totient 5 : Int) ∧ mobiusTotientSum 6 = (totient 6 : Int) ∧
    mobiusTotientSum 7 = (totient 7 : Int) ∧ mobiusTotientSum 8 = (totient 8 : Int) ∧
    mobiusTotientSum 9 = (totient 9 : Int) ∧ mobiusTotientSum 10 = (totient 10 : Int) ∧
    mobiusTotientSum 11 = (totient 11 : Int) ∧ mobiusTotientSum 12 = (totient 12 : Int) ∧
    mobiusTotientSum 13 = (totient 13 : Int) ∧ mobiusTotientSum 14 = (totient 14 : Int) ∧
    mobiusTotientSum 15 = (totient 15 : Int) ∧ mobiusTotientSum 16 = (totient 16 : Int) ∧
    mobiusTotientSum 17 = (totient 17 : Int) ∧ mobiusTotientSum 18 = (totient 18 : Int) ∧
    mobiusTotientSum 19 = (totient 19 : Int) ∧ mobiusTotientSum 20 = (totient 20 : Int) := by
  decide

end E213.Lib.Math.NumberTheory.MobiusFunction
