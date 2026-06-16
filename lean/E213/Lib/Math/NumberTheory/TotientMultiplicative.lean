import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.EncodePair213
import E213.Meta.Nat.Beq213
import E213.Lib.Math.Combinatorics.SumReshape
import E213.Lib.Math.NumberTheory.EulerTotient
import E213.Lib.Math.NumberTheory.GaussTotient
import E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
import E213.Lib.Math.NumberTheory.ModArith.CRTReconstruction
import E213.Lib.Math.NumberTheory.EulerTheorem
import E213.Lib.Math.NumberTheory.DivisorProductReindex
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Lib.Math.NumberTheory.FactorialLcmIdentity

/-!
# Euler totient is multiplicative (∅-axiom, PURE)

`totient (m*n) = totient m * totient n` for coprime `m, n`.

The forcing: classically a corollary of the CRT ring iso `ℤ/mn ≅ ℤ/m × ℤ/n`
(units ↦ unit-pairs), riding on `Quot.sound`.  ∅-axiom forces the explicit
**counting bijection** `x ↦ (x%m, x%n)` on coprime residues: φ multiplicative is
the Fubini reindex of the coprimality-indicator sum, computed.
-/

namespace E213.Lib.Math.NumberTheory.TotientMultiplicative

open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.NumberTheory.EulerTotient (totient coprimeInd)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_congr sumTo_mul_left sumTo_add_func)
open E213.Lib.Math.NumberTheory.FactorialLcmIdentity (sumTo_const_zero sumTo_fubini)
open E213.Lib.Math.Combinatorics.SumReshape (sumTo_reshape)
open E213.Lib.Math.NumberTheory.GaussTotient (eqInd eqInd_self eqInd_ne)
open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative (coprime_mul_iff)
open E213.Meta.Nat.Beq213 (nat_beq_op_eq_false_of_ne)
open E213.Meta.Nat.EncodePair213 (encode_div encode_mod)

/-! ## §1 — the coprimality-indicator product split -/

/-- `coprimeInd k n = 1` iff `gcd213 (k+1) n = 1` (the indicator is a Bool.toNat). -/
theorem coprimeInd_one_iff (k n : Nat) :
    coprimeInd k n = 1 ↔ gcd213 (k + 1) n = 1 := by
  show (gcd213 (k + 1) n == 1).toNat = 1 ↔ gcd213 (k + 1) n = 1
  constructor
  · intro h
    by_cases hg : gcd213 (k + 1) n = 1
    · exact hg
    · rw [nat_beq_op_eq_false_of_ne hg] at h; exact absurd h (by decide)
  · intro h
    rw [h, show ((1 : Nat) == 1) = true from decide_eq_true rfl]; rfl

/-- `coprimeInd k n = 0` when `gcd213 (k+1) n ≠ 1`. -/
theorem coprimeInd_zero_of {k n : Nat} (h : gcd213 (k + 1) n ≠ 1) :
    coprimeInd k n = 0 := by
  show (gcd213 (k + 1) n == 1).toNat = 0
  rw [nat_beq_op_eq_false_of_ne h]; rfl

/-- `coprimeInd k n = 1` when `gcd213 (k+1) n = 1`. -/
theorem coprimeInd_one_of {k n : Nat} (h : gcd213 (k + 1) n = 1) :
    coprimeInd k n = 1 := (coprimeInd_one_iff k n).mpr h

/-- ★ **Coprimality-indicator product split**: `coprime_mul_iff` is fully
    general (no `gcd m n = 1` needed), so the indicators multiply for every
    `m, n`: `coprimeInd x (m*n) = coprimeInd x m * coprimeInd x n`. -/
theorem coprimeInd_mul_split (m n x : Nat) :
    coprimeInd x (m * n) = coprimeInd x m * coprimeInd x n := by
  by_cases hg : gcd213 (x + 1) (m * n) = 1
  · -- both factors are 1
    obtain ⟨hm, hn⟩ := (coprime_mul_iff (x + 1) m n).mp hg
    rw [coprimeInd_one_of hg, coprimeInd_one_of hm, coprimeInd_one_of hn]
  · -- product is 0; one factor must be 0
    rw [coprimeInd_zero_of hg]
    by_cases hm : gcd213 (x + 1) m = 1
    · by_cases hn : gcd213 (x + 1) n = 1
      · exact absurd ((coprime_mul_iff (x + 1) m n).mpr ⟨hm, hn⟩) hg
      · rw [coprimeInd_zero_of hn, Nat.mul_zero]
    · rw [coprimeInd_zero_of hm, Nat.zero_mul]

/-! ## §2 — a unique-witness indicator sum equals 1 -/

/-- If a key misses value `v` on the whole range `[0,N)`, the indicator sum is 0. -/
theorem sum_eqInd_key_zero (key : Nat → Nat) (v : Nat) :
    ∀ N, (∀ x, x < N → key x ≠ v) → sumTo N (fun x => eqInd (key x) v) = 0
  | 0, _ => rfl
  | N + 1, h => by
    rw [sumTo_succ, sum_eqInd_key_zero key v N (fun x hx => h x (Nat.lt_succ_of_lt hx)),
        Nat.zero_add, eqInd_ne (h N (Nat.lt_succ_self N))]

/-- ★ **Unique-witness indicator sum = 1**: if exactly one index `x₀ < N` has
    `key x₀ = v` (others miss), `Σ_{x<N} [key x = v] = 1`. -/
theorem sum_eqInd_key_unique (key : Nat → Nat) (v x₀ : Nat) :
    ∀ N, x₀ < N → key x₀ = v → (∀ x, x < N → key x = v → x = x₀) →
      sumTo N (fun x => eqInd (key x) v) = 1
  | 0, hlt, _, _ => absurd hlt (Nat.not_lt_zero x₀)
  | N + 1, hlt, hkey, huniq => by
    rw [sumTo_succ]
    by_cases hN : x₀ = N
    · -- the hit is the last index
      subst hN
      have hzero : sumTo x₀ (fun x => eqInd (key x) v) = 0 :=
        sum_eqInd_key_zero key v x₀ (fun x hx hxv =>
          absurd (huniq x (Nat.lt_succ_of_lt hx) hxv) (Nat.ne_of_lt hx))
      rw [hzero, Nat.zero_add, hkey, eqInd_self]
    · -- last index is not the hit; recurse
      have hx₀N : x₀ < N := by
        rcases Nat.lt_or_ge x₀ N with h | h
        · exact h
        · exact absurd (Nat.le_antisymm (Nat.le_of_lt_succ hlt) h) hN
      have hlast : key N ≠ v := by
        intro hkN
        exact hN (huniq N (Nat.lt_succ_self N) hkN).symm
      rw [sum_eqInd_key_unique key v x₀ N hx₀N hkey
          (fun x hx hxv => huniq x (Nat.lt_succ_of_lt hx) hxv),
          eqInd_ne hlast, Nat.add_zero]

/-! ## §3 — the CRT counting bijection: each pair value is hit exactly once -/

open E213.Lib.Math.NumberTheory.ModArith.CRTReconstruction (crtSolve crt_solve_residues crt_unique)

/-- The residue-encoding key `x ↦ (x%m)*n + (x%n)`. -/
def rkey (m n x : Nat) : Nat := (x % m) * n + (x % n)

/-- **`rkey` decodes uniquely** (for `b < n`): `rkey m n x = a*n + b → x%m = a ∧ x%n = b`. -/
theorem rkey_decode {m n a b x : Nat} (hb : b < n) (h : rkey m n x = a * n + b) :
    x % m = a ∧ x % n = b := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le b) hb
  have hxn : x % n < n := Nat.mod_lt x hn
  -- (x%m)*n + (x%n) = a*n + b, with both x%n < n and b < n
  constructor
  · have := encode_div hn (x % m) (x % n) hxn
    -- ((x%m)*n + (x%n)) / n = x%m  and  (a*n+b)/n = a
    rw [show (x % m) * n + (x % n) = rkey m n x from rfl, h, encode_div hn a b hb] at this
    exact this.symm
  · have := encode_mod hn (x % m) (x % n) hxn
    rw [show (x % m) * n + (x % n) = rkey m n x from rfl, h, encode_mod hn a b hb] at this
    exact this.symm

/-- ★★★ **Each pair value is hit exactly once** (the CRT counting bijection):
    for coprime `m, n` and `a < m`, `b < n`,
    `Σ_{x<mn} [rkey m n x = a*n + b] = 1`. -/
theorem crt_count_one {m n : Nat} (hco : gcd213 m n = 1) (hm : 0 < m) (hn : 0 < n)
    {a b : Nat} (ha : a < m) (hb : b < n) :
    sumTo (m * n) (fun x => eqInd (rkey m n x) (a * n + b)) = 1 := by
  -- witness: x₀ = crtSolve m n a b
  obtain ⟨hres_m, hres_n⟩ := crt_solve_residues hco hm hn a b
  -- crtSolve % m = a % m = a, crtSolve % n = b % n = b
  have hsm : crtSolve m n a b % m = a := by rw [hres_m, Nat.mod_eq_of_lt ha]
  have hsn : crtSolve m n a b % n = b := by rw [hres_n, Nat.mod_eq_of_lt hb]
  have hx₀lt : crtSolve m n a b < m * n := Nat.mod_lt _ (Nat.mul_pos hm hn)
  have hkey0 : rkey m n (crtSolve m n a b) = a * n + b := by
    show (crtSolve m n a b % m) * n + (crtSolve m n a b % n) = a * n + b
    rw [hsm, hsn]
  refine sum_eqInd_key_unique (rkey m n) (a * n + b) (crtSolve m n a b) (m * n)
    hx₀lt hkey0 (fun x hx hxv => ?_)
  -- uniqueness: rkey x = a*n+b ⟹ x%m=a, x%n=b ⟹ x = x₀ via crt_unique
  obtain ⟨hxm, hxn⟩ := rkey_decode hb hxv
  refine crt_unique hco hm hn hx hx₀lt ?_ ?_
  · rw [hxm, hsm]
  · rw [hxn, hsn]

/-! ## §4 — coprimeInd depends only on the residue of its first slot -/

open E213.Lib.Math.NumberTheory.EulerTheorem (gcd_mod_left)
open E213.Meta.Nat.AddMod213 (add_mod_gen)

/-- **`coprimeInd` is mod-invariant in its first slot** (`0 < m`):
    `s % m = a % m → coprimeInd s m = coprimeInd a m`.
    `gcd(s+1,m) = gcd((s+1)%m, m)` and `(s+1)%m = (a+1)%m` from `s%m = a%m`. -/
theorem coprimeInd_mod_eq {m : Nat} (hm : 0 < m) {s a : Nat} (h : s % m = a % m) :
    coprimeInd s m = coprimeInd a m := by
  have hgcd : gcd213 (s + 1) m = gcd213 (a + 1) m := by
    rw [← gcd_mod_left (s + 1) m hm, ← gcd_mod_left (a + 1) m hm,
        add_mod_gen s 1 m, add_mod_gen a 1 m, h]
  show (gcd213 (s + 1) m == 1).toNat = (gcd213 (a + 1) m == 1).toNat
  rw [hgcd]

/-! ## §5 — `Σ_a Σ_b g a · h b = (Σ_a g a)·(Σ_b h b)` -/

/-- ★ **Product of sums = double sum**: `(Σ_{a<m} g a)·(Σ_{b<n} h b) =
    Σ_{a<m} Σ_{b<n} g a · h b`. -/
theorem sum_mul_sum (m n : Nat) (g h : Nat → Nat) :
    sumTo m g * sumTo n h = sumTo m (fun a => sumTo n (fun b => g a * h b)) := by
  rw [Nat.mul_comm (sumTo m g) (sumTo n h),
      sumTo_mul_left (sumTo n h) m g]
  refine sumTo_congr m _ _ (fun a _ => ?_)
  rw [Nat.mul_comm (sumTo n h) (g a), sumTo_mul_left (g a) n h]

/-! ## §6 — the reindex and the multiplicativity theorem -/

open E213.Lib.Math.NumberTheory.DivisorProductReindex (weighted_partition_by_key)
open E213.Meta.Nat.NatDiv213 (div_add_mod_pure)

/-- `a * n + b < m * n` when `a < m`, `b < n`. -/
theorem encode_lt {m n a b : Nat} (ha : a < m) (hb : b < n) : a * n + b < m * n := by
  have hstep : a * n + b < a * n + n := Nat.add_lt_add_left hb (a * n)
  have hcollapse : a * n + n = (a + 1) * n := by rw [Nat.succ_mul]
  have hbound : (a + 1) * n ≤ m * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt ha)
  exact Nat.lt_of_lt_of_le (hcollapse ▸ hstep) hbound

/-- `rkey m n x < m * n` for positive `m, n`. -/
theorem rkey_lt {m n : Nat} (hm : 0 < m) (hn : 0 < n) (x : Nat) :
    rkey m n x < m * n :=
  encode_lt (Nat.mod_lt x hm) (Nat.mod_lt x hn)

/-- **The fiber value**: for `v = a*n + b` with `a < m`, `b < n` (coprime `m,n`),
    the fiber sum collapses to `coprimeInd a m · coprimeInd b n` — the CRT
    counting bijection (`crt_count_one`) times the constant fiber weight. -/
theorem fiber_value {m n : Nat} (hco : gcd213 m n = 1) (hm : 0 < m) (hn : 0 < n)
    {a b : Nat} (ha : a < m) (hb : b < n) :
    sumTo (m * n) (fun x => eqInd (rkey m n x) (a * n + b) * coprimeInd x (m * n))
      = coprimeInd a m * coprimeInd b n := by
  have hpt : ∀ x, x < m * n →
      eqInd (rkey m n x) (a * n + b) * coprimeInd x (m * n)
        = (coprimeInd a m * coprimeInd b n) * eqInd (rkey m n x) (a * n + b) := by
    intro x _
    by_cases hxv : rkey m n x = a * n + b
    · obtain ⟨hxm, hxn⟩ := rkey_decode hb hxv
      have hcx : coprimeInd x (m * n) = coprimeInd a m * coprimeInd b n := by
        rw [coprimeInd_mul_split m n x]
        have e1 : coprimeInd x m = coprimeInd a m :=
          coprimeInd_mod_eq hm (by rw [hxm, Nat.mod_eq_of_lt ha])
        have e2 : coprimeInd x n = coprimeInd b n :=
          coprimeInd_mod_eq hn (by rw [hxn, Nat.mod_eq_of_lt hb])
        rw [e1, e2]
      rw [hcx, Nat.mul_comm]
    · rw [eqInd_ne hxv, Nat.zero_mul, Nat.mul_zero]
  rw [sumTo_congr (m * n) _ _ hpt]
  rw [← sumTo_mul_left (coprimeInd a m * coprimeInd b n) (m * n)
        (fun x => eqInd (rkey m n x) (a * n + b))]
  rw [crt_count_one hco hm hn ha hb, Nat.mul_one]

/-- **The reindex**: `Σ_{x<mn} coprimeInd x (mn) = Σ_{a<m} Σ_{b<n} cop a m · cop b n`.
    Weighted partition by `rkey`, then the fiber value, then `sumTo_reshape`
    rewrites the value-axis sum back into the `(a,b)` grid. -/
theorem totient_mul_reindex {m n : Nat} (hco : gcd213 m n = 1) (hm : 0 < m) (hn : 0 < n) :
    sumTo (m * n) (fun x => coprimeInd x (m * n))
      = sumTo m (fun a => sumTo n (fun b => coprimeInd a m * coprimeInd b n)) := by
  -- partition by rkey over the value range [0, m*n)
  rw [weighted_partition_by_key (rkey m n) (fun x => coprimeInd x (m * n)) (m * n) (m * n)
        (fun x _ => rkey_lt hm hn x)]
  -- reshape the value axis v ∈ [0, m*n) into the (a,b) grid via v = a*n + b
  rw [sumTo_reshape
        (fun v => sumTo (m * n) (fun x => eqInd (rkey m n x) v * coprimeInd x (m * n))) n m]
  -- each grid cell (a,b) ↦ fiber_value
  refine sumTo_congr m _ _ (fun a ha => ?_)
  refine sumTo_congr n _ _ (fun b hb => ?_)
  exact fiber_value hco hm hn ha hb

/-! ## §7 — ★★★ the theorem -/

/-- ★★★ **Euler's totient is multiplicative**: for coprime `m, n`,
    `totient (m*n) = totient m * totient n`.

    The forcing: classically a corollary of the CRT ring iso `ℤ/mn ≅ ℤ/m × ℤ/n`
    (units ↦ unit-pairs), riding on `Quot.sound`.  ∅-axiom forces the explicit
    counting bijection `x ↦ (x%m, x%n)` on coprime residues — φ multiplicative is
    the Fubini reindex of the coprimality-indicator sum, *computed*. -/
theorem totient_mul {m n : Nat} (hco : gcd213 m n = 1) (hm : 0 < m) (hn : 0 < n) :
    totient (m * n) = totient m * totient n := by
  show sumTo (m * n) (fun x => coprimeInd x (m * n))
     = sumTo m (fun a => coprimeInd a m) * sumTo n (fun b => coprimeInd b n)
  rw [totient_mul_reindex hco hm hn]
  exact (sum_mul_sum m n (fun a => coprimeInd a m) (fun b => coprimeInd b n)).symm

/-! ## §8 — numeric smokes -/

theorem smoke_15 : totient 15 = totient 3 * totient 5 := by decide
theorem smoke_21 : totient 21 = totient 3 * totient 7 := by decide
theorem smoke_35 : totient 35 = totient 5 * totient 7 := by decide
theorem smoke_eval : totient 15 = 8 ∧ totient 3 * totient 5 = 8 := by decide

end E213.Lib.Math.NumberTheory.TotientMultiplicative
