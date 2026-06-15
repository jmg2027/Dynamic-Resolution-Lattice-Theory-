import E213.Lib.Math.NumberTheory.MobiusFunction

/-!
# Liouville function `λ(n) = (−1)^Ω(n)` (∅-axiom)

Companion to `MobiusFunction.lean`.  λ is **completely multiplicative** and counts
prime factors *with multiplicity* (Ω), so unlike μ it never returns 0.  Trial
division identical to `muAux` except: every prime factor found (including repeats)
flips the sign, recursing from the same candidate `d` (not `d+1`).

  * `liouville n` — λ (general-computable, propext-free `cond`/`Bool` branching).
  * ★★ `liouville_divisor_sum_table` — `Σ_{d∣n} λ(d) = [n is a perfect square]` (n=1..16).
  * `liouville_completely_multiplicative_table` — `λ(m·n)=λ(m)·λ(n)` (all m,n, incl. non-coprime).

The general complete-multiplicativity shares the open `muStruct = mu`-style scan
invariant (`research-notes/frontiers/mobius_divisor_sum_general.md`); verified by
table here.  The corpus `Liouville` elsewhere is the transcendence constant — a
different object.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.LiouvilleFunction

open E213.Lib.Math.NumberTheory.MobiusFunction (sumZ divisorSumZ)

/-- Fuel-bounded core of λ.  `liouvilleAux fuel m d sign` strips prime factors of `m`
    scanning candidates from `d` upward: `d ∣ m` flips the sign and recurses on `m/d`
    from the SAME candidate `d` (so repeated factors are counted with multiplicity);
    otherwise advance `d → d+1`.  propext-free (`cond` on `Bool`). -/
def liouvilleAux : Nat → Nat → Nat → Int → Int
  | 0,        _, _, sign => sign
  | fuel + 1, m, d, sign =>
    cond (m == 1)
      sign
      (cond (m % d == 0)
        (liouvilleAux fuel (m / d) d (- sign))
        (liouvilleAux fuel m (d + 1) sign))

/-- Liouville function `λ(n) = (−1)^Ω(n)`.  `λ 0 = 0`, `λ 1 = 1`, otherwise
    trial division from `2` with fuel `2·(n+2)` (each scan strips a factor or advances). -/
def liouville : Nat → Int
  | 0     => 0
  | 1     => 1
  | n + 2 => liouvilleAux (2 * (n + 2)) (n + 2) 2 1

/-- `Σ_{d ∣ n} λ(d)`. -/
def liouvilleSum (n : Nat) : Int := divisorSumZ n liouville

/-! ## Tables (∅-axiom, by `decide`) -/

/-- λ(1..13): 1,−1,−1,1,−1,1,−1,−1,1,_,−1,−1,−1. -/
theorem liouville_table :
    liouville 1 = 1 ∧ liouville 2 = -1 ∧ liouville 3 = -1 ∧ liouville 4 = 1 ∧
    liouville 5 = -1 ∧ liouville 6 = 1 ∧ liouville 7 = -1 ∧ liouville 8 = -1 ∧
    liouville 9 = 1 ∧ liouville 11 = -1 ∧ liouville 12 = -1 ∧ liouville 13 = -1 := by
  decide

/-- ★★ **Liouville divisor-sum identity**, verified n = 1..16:
    `Σ_{d∣n} λ(d) = [n is a perfect square]` (1 iff n ∈ {1,4,9,16}). -/
theorem liouville_divisor_sum_table :
    liouvilleSum 1 = 1 ∧ liouvilleSum 2 = 0 ∧ liouvilleSum 3 = 0 ∧ liouvilleSum 4 = 1 ∧
    liouvilleSum 5 = 0 ∧ liouvilleSum 6 = 0 ∧ liouvilleSum 7 = 0 ∧ liouvilleSum 8 = 0 ∧
    liouvilleSum 9 = 1 ∧ liouvilleSum 10 = 0 ∧ liouvilleSum 11 = 0 ∧ liouvilleSum 12 = 0 ∧
    liouvilleSum 13 = 0 ∧ liouvilleSum 14 = 0 ∧ liouvilleSum 15 = 0 ∧ liouvilleSum 16 = 1 := by
  decide

/-- ★ **Complete multiplicativity (table)**: `λ(m·n) = λ(m)·λ(n)` for ALL pairs
    (unlike μ — incl. non-coprime 2·2, 2·4, 3·3, 4·4, 6·6, 12·12). -/
theorem liouville_completely_multiplicative_table :
    liouville (2 * 2) = liouville 2 * liouville 2 ∧
    liouville (2 * 4) = liouville 2 * liouville 4 ∧
    liouville (2 * 6) = liouville 2 * liouville 6 ∧
    liouville (3 * 3) = liouville 3 * liouville 3 ∧
    liouville (2 * 3) = liouville 2 * liouville 3 ∧
    liouville (4 * 4) = liouville 4 * liouville 4 ∧
    liouville (6 * 6) = liouville 6 * liouville 6 ∧
    liouville (4 * 9) = liouville 4 * liouville 9 ∧
    liouville (3 * 5) = liouville 3 * liouville 5 ∧
    liouville (12 * 12) = liouville 12 * liouville 12 := by
  decide

end E213.Lib.Math.NumberTheory.LiouvilleFunction
