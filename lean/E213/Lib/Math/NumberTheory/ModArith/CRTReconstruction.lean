import E213.Lib.Math.NumberTheory.ModArith.ModBezoutInvariant
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Lib.Math.NumberTheory.DivisorProductReindex
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213

/-!
# Chinese Remainder Theorem as an explicit reconstruction bijection (∅-axiom, PURE)

The classical CRT is the quotient-ring isomorphism `ℤ/mn ≅ ℤ/m × ℤ/n`,
an abstract map whose construction rides on `Quot.sound`.  Under the
∅-axiom contract no quotient is available, so CRT is forced into a
different, more revealing shape: an **explicit, computable invertible
formula on the representatives** `{0,…,mn−1}`.

  · `crtMap m n x = (x % m, x % n)`               — forward (residues)
  · `crtSolve m n a b = (a·n·n⁻¹ + b·m·m⁻¹) % mn` — explicit reconstruction
    where `n⁻¹` is the Bezout inverse of `n` mod `m` (`inverse_of_coprime`)
    and `m⁻¹` the Bezout inverse of `m` mod `n`.

What the ∅-axiom route reveals: **the CRT isomorphism is literally the
reconstruction algorithm `crtSolve`** — the quotient was packaging, the
round-trip (`crt_solve_residues` + `crt_unique`) is the content.

All declarations PURE (`#print axioms` → no axioms).
-/

namespace E213.Lib.Math.NumberTheory.ModArith.CRTReconstruction

open E213.Lib.Math.NumberTheory.ModArith.ModBezout (modBezout)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (inverse_of_coprime)
open E213.Lib.Math.NumberTheory.DivisorProductReindex (coprime_mul_dvd)
open E213.Meta.Nat.Gcd213 (mod_eq_dvd_sub gcd213_comm)
open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod mod_mod_of_dvd zero_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure mul_mod_pure)
open E213.Tactic.NatHelper (gcd213 mul_assoc mul_mod_right)

/-! ## The forward map and the explicit reconstruction -/

/-- Forward CRT map: `x ↦ (x mod m, x mod n)`. -/
def crtMap (m n x : Nat) : Nat × Nat := (x % m, x % n)

/-- Explicit CRT reconstruction (closed-form inverse via Bezout).
    `n⁻¹ = (modBezout n m).2` is the inverse of `n` mod `m`;
    `m⁻¹ = (modBezout m n).2` is the inverse of `m` mod `n`. -/
def crtSolve (m n a b : Nat) : Nat :=
  (a * n * (modBezout n m).2 + b * m * (modBezout m n).2) % (m * n)

/-! ## Reconstruction correctness (the surjectivity core) -/

/-- The `b·m·m⁻¹` summand vanishes mod `m`. -/
private theorem term2_mod_m (m b w : Nat) : (b * m * w) % m = 0 := by
  -- b * m * w = m * (b * w)
  have h : b * m * w = m * (b * w) := by
    rw [mul_assoc b m w, Nat.mul_comm b (m * w), mul_assoc m w b,
        Nat.mul_comm w b]
  rw [h]; exact mul_mod_right m (b * w)

/-- The `a·n·n⁻¹` summand is `≡ a` mod `m` (using `n·n⁻¹ ≡ 1 mod m`). -/
private theorem term1_mod_m (m n a : Nat) (hm : 0 < m)
    (hco : gcd213 n m = 1) : (a * n * (modBezout n m).2) % m = a % m := by
  -- a * n * n⁻¹ = a * (n * n⁻¹)
  have hassoc : a * n * (modBezout n m).2 = a * (n * (modBezout n m).2) :=
    mul_assoc a n (modBezout n m).2
  rw [hassoc]
  -- (a * (n*n⁻¹)) % m = (a * ((n*n⁻¹) % m)) % m
  rw [mul_mod_right_pure a (n * (modBezout n m).2) m]
  -- (n*n⁻¹) % m = 1 % m
  have hinv : (n * (modBezout n m).2) % m = 1 % m :=
    inverse_of_coprime n m hm hco
  rw [hinv]
  -- (a * (1 % m)) % m = (a * 1) % m = a % m
  rw [← mul_mod_right_pure a 1 m, Nat.mul_one]

/-- ★★★ **Reconstruction hits the prescribed residues** (the surjectivity /
    correctness core).  `crtSolve m n a b` reduces to `a` mod `m` and to
    `b` mod `n`. -/
theorem crt_solve_residues (hmn : gcd213 m n = 1) (hm : 0 < m) (hn : 0 < n)
    (a b : Nat) :
    crtSolve m n a b % m = a % m ∧ crtSolve m n a b % n = b % n := by
  have hmn_pos : 0 < m * n := Nat.mul_pos hm hn
  refine ⟨?_, ?_⟩
  · -- mod m
    show (a * n * (modBezout n m).2 + b * m * (modBezout m n).2) % (m * n) % m
       = a % m
    -- drop the outer % (m*n) since m ∣ m*n
    rw [mod_mod_of_dvd _ ⟨n, rfl⟩]
    -- split the sum
    rw [add_mod_gen]
    have hco_nm : gcd213 n m = 1 := (gcd213_comm m n).symm ▸ hmn
    rw [term1_mod_m m n a hm hco_nm, term2_mod_m m b (modBezout m n).2]
    -- (a % m + 0) % m = a % m
    rw [Nat.add_zero, mod_mod]
  · -- mod n
    show (a * n * (modBezout n m).2 + b * m * (modBezout m n).2) % (m * n) % n
       = b % n
    -- n ∣ m*n  (m*n = n*m)
    have hdvd : n ∣ m * n := ⟨m, Nat.mul_comm m n⟩
    rw [mod_mod_of_dvd _ hdvd]
    -- swap the summands so the b-term is first
    rw [Nat.add_comm (a * n * (modBezout n m).2) (b * m * (modBezout m n).2)]
    rw [add_mod_gen]
    have hco_mn : gcd213 m n = 1 := hmn
    rw [term1_mod_m n m b hn hco_mn, term2_mod_m n a (modBezout n m).2]
    rw [Nat.add_zero, mod_mod]

/-! ## Uniqueness (injectivity — the part classically riding on the quotient) -/

/-- ★★★ **Uniqueness / injectivity**: two representatives below `mn` with the
    same residue mod `m` and mod `n` are equal.  Via `m ∣ (x−y)` and
    `n ∣ (x−y)` plus coprimality giving `mn ∣ (x−y)`, then `x−y < mn ⟹
    x = y`.  This is the content the classical statement packages in the
    quotient ring. -/
theorem crt_unique (hmn : gcd213 m n = 1) (hm : 0 < m) (hn : 0 < n)
    {x y : Nat} (hx : x < m * n) (hy : y < m * n)
    (ha : x % m = y % m) (hb : x % n = y % n) : x = y := by
  -- WLOG y ≤ x via trichotomy
  rcases Nat.le_total y x with hyx | hxy
  · -- y ≤ x: show m*n ∣ (x - y), and x - y < m*n ⟹ x - y = 0
    have hdm : m ∣ (x - y) := mod_eq_dvd_sub x y m hm hyx ha
    have hdn : n ∣ (x - y) := mod_eq_dvd_sub x y n hn hyx hb
    have hdmn : m * n ∣ (x - y) := coprime_mul_dvd hdm hdn hmn
    -- x - y < m*n
    have hlt : x - y < m * n := Nat.lt_of_le_of_lt (Nat.sub_le x y) hx
    -- divisor ≤ dividend unless dividend = 0
    obtain ⟨k, hk⟩ := hdmn
    have hxy0 : x - y = 0 := by
      cases k with
      | zero => rw [hk, Nat.mul_zero]
      | succ k' =>
        exfalso
        have hge : m * n ≤ x - y := by
          rw [hk]
          calc m * n = m * n * 1 := (Nat.mul_one _).symm
            _ ≤ m * n * (k' + 1) :=
                Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le k'))
        exact absurd hge (Nat.not_le.mpr hlt)
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hxy0) hyx
  · -- x ≤ y: symmetric
    have hdm : m ∣ (y - x) := mod_eq_dvd_sub y x m hm hxy ha.symm
    have hdn : n ∣ (y - x) := mod_eq_dvd_sub y x n hn hxy hb.symm
    have hdmn : m * n ∣ (y - x) := coprime_mul_dvd hdm hdn hmn
    have hlt : y - x < m * n := Nat.lt_of_le_of_lt (Nat.sub_le y x) hy
    obtain ⟨k, hk⟩ := hdmn
    have hyx0 : y - x = 0 := by
      cases k with
      | zero => rw [hk, Nat.mul_zero]
      | succ k' =>
        exfalso
        have hge : m * n ≤ y - x := by
          rw [hk]
          calc m * n = m * n * 1 := (Nat.mul_one _).symm
            _ ≤ m * n * (k' + 1) :=
                Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le k'))
        exact absurd hge (Nat.not_le.mpr hlt)
    exact Nat.le_antisymm hxy (Nat.le_of_sub_eq_zero hyx0)

/-! ## Bijection package (round-trips both ways) -/

/-- ★★ **Forward round-trip**: feeding `(a % m, b % n)` through `crtSolve`
    and reading residues recovers `(a % m, b % n)`.  i.e. `crtMap` of the
    reconstruction equals the prescribed residues. -/
theorem crt_map_solve (hmn : gcd213 m n = 1) (hm : 0 < m) (hn : 0 < n)
    (a b : Nat) :
    crtMap m n (crtSolve m n a b) = (a % m, b % n) := by
  obtain ⟨h1, h2⟩ := crt_solve_residues hmn hm hn a b
  show (crtSolve m n a b % m, crtSolve m n a b % n) = (a % m, b % n)
  rw [h1, h2]

/-- ★★ **Backward round-trip**: reconstructing from the residues of any
    `x < mn` recovers `x`.  `crtSolve (x % m) (x % n) = x`.  This is the
    full bijection: `crtMap` restricted to `{0,…,mn−1}` is invertible with
    explicit inverse `crtSolve`. -/
theorem crt_solve_map (hmn : gcd213 m n = 1) (hm : 0 < m) (hn : 0 < n)
    {x : Nat} (hx : x < m * n) :
    crtSolve m n (x % m) (x % n) = x := by
  have hmn_pos : 0 < m * n := Nat.mul_pos hm hn
  -- crtSolve _ _ (x%m) (x%n) < m*n, and its residues match x's residues
  obtain ⟨h1, h2⟩ := crt_solve_residues hmn hm hn (x % m) (x % n)
  -- crtSolve value is itself < m*n (it is a `% (m*n)`)
  have hlt : crtSolve m n (x % m) (x % n) < m * n := Nat.mod_lt _ hmn_pos
  -- residues: crtSolve%m = (x%m)%m = x%m, etc.
  have hr1 : crtSolve m n (x % m) (x % n) % m = x % m := by
    rw [h1, mod_mod]
  have hr2 : crtSolve m n (x % m) (x % n) % n = x % n := by
    rw [h2, mod_mod]
  exact crt_unique hmn hm hn hlt hx hr1 hr2

/-! ## Concrete smokes (m = 3, n = 5) -/

/-- gcd(3,5) = 1. -/
theorem smoke_gcd_3_5 : gcd213 3 5 = 1 := by decide

/-- The classic puzzle: `x ≡ 2 (mod 3)`, `x ≡ 3 (mod 5)` ⟹ `x = 8`.
    `crtSolve 3 5 2 3` is the explicit answer. -/
theorem smoke_solve_2_3 : crtSolve 3 5 2 3 = 8 := by decide

/-- Residue check on the puzzle answer. -/
theorem smoke_residues_2_3 :
    crtSolve 3 5 2 3 % 3 = 2 ∧ crtSolve 3 5 2 3 % 5 = 3 := by decide

/-- Round-trip forward at (a,b) = (1,4): residues recovered. -/
theorem smoke_map_solve_1_4 : crtMap 3 5 (crtSolve 3 5 1 4) = (1, 4) := by decide

/-- Round-trip backward at x = 11 (< 15): reconstruct from its residues. -/
theorem smoke_solve_map_11 : crtSolve 3 5 (11 % 3) (11 % 5) = 11 := by decide

/-- A second reconstruction: `x ≡ 0 (mod 3)`, `x ≡ 1 (mod 5)` ⟹ `x = 6`. -/
theorem smoke_solve_0_1 : crtSolve 3 5 0 1 = 6 := by decide

end E213.Lib.Math.NumberTheory.ModArith.CRTReconstruction
