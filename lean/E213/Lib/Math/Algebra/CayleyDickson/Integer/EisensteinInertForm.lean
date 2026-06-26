import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega
import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid
import E213.Lib.Math.NumberTheory.ModArith.EisensteinFormCharacter
import E213.Meta.Int213.Bound
import E213.Meta.Int213.OrderMul
import E213.Meta.Tactic.Pow213

/-!
# The inert obstruction over `ℤ` — `‖d‖² ≠ q` for a rational prime `q ≡ 2 (mod 3)` (∅-axiom)

★★★★ `normSq_ne_of_mod3_two` : no Eisenstein integer `d ∈ ℤ[ω]` has norm `q` when `q ≡ 2 (mod 3)`.

The disc-`−3` norm form `‖d‖² = a² − ab + b²` (`a = d.re`, `b = d.im`) satisfies the identity

  `a² − ab + b² = (a+b)² − 3·ab`,

so `‖d‖² ≡ (a+b)² (mod 3)`.  A square is never `≡ 2 (mod 3)` (`int_sq_mod3`, the form fingerprint
`EisensteinFormCharacter.eisCyc_mod3_ne_two` at `b = 0`), so `‖d‖² mod 3 ∈ {0,1}` and never equals a
`q ≡ 2 (mod 3)`.

This is the **inert obstruction**: `q ≡ 2 (mod 3)` is represented by no value of the norm form, hence
has no proper divisor of norm `q` in `ℤ[ω]` — the missing fact that makes `q` *prime* in `ℤ[ω]`
(`ℤ[ω]/(q) ≅ 𝔽_{q²}`), the field the cubic residue symbol `(π/q)₃` lives in.  ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinInertForm

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.NumberTheory.PolyRoot (natAbs_mul int_dvd_to_nat)
open E213.Lib.Math.NumberTheory.ModArith.EisensteinFormCharacter
  (eisCyc_mod3_ne_two mod3_decomp mod3_range)
open E213.Lib.Math.NumberTheory.ModArith.PureNatMod3 (mod3)
open E213.Meta.Int213 (int_sq_nonneg)
open E213.Meta.Int213.OrderMul (natAbs_cast_of_nonneg)
open E213.Meta.Nat.AddMod213 (div_add_mod)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-- **A square is never `≡ 2 (mod 3)`** — `mod3 (m·m) ≠ 2`.  The single-variable
    `eisCyc_mod3_ne_two` (`a²+ab+b² ≠ 2 mod 3`) at `b = 0` (`m·m + m·0 + 0·0 = m·m` definitionally). -/
theorem mod3_sq_ne_two (m : Nat) : mod3 (m * m) ≠ 2 := eisCyc_mod3_ne_two m 0

/-- `↑(3·k) = 3·↑k` — a `rfl` cast (`Int.ofNat` distributes over `·` definitionally). -/
private theorem ncast_mul3 (k : Nat) : ((3 * k : Nat) : Int) = 3 * (k : Int) := rfl
/-- `↑(3·k + 1) = 3·↑k + 1` — a `rfl` cast. -/
private theorem ncast_mul3_one (k : Nat) : ((3 * k + 1 : Nat) : Int) = 3 * (k : Int) + 1 := rfl

/-- **A square mod `3` is `0` or `1`** (divisibility form) — `3 ∣ s·s` or `3 ∣ (s·s − 1)` over `ℤ`.
    Reflect `s·s = ↑(|s|²)` to `ℕ` (`natAbs_mul` + nonneg), then `mod3_decomp` splits on
    `mod3 (|s|²) ∈ {0,1}` (`mod3_sq_ne_two` kills `2`).  ∅-axiom. -/
theorem int_sq_mod3 (s : Int) : (3 : Int) ∣ (s * s) ∨ (3 : Int) ∣ (s * s - 1) := by
  have hnn : 0 ≤ s * s := int_sq_nonneg s
  have hcast : s * s = ((s.natAbs * s.natAbs : Nat) : Int) := by
    rw [← natAbs_mul s s, natAbs_cast_of_nonneg hnn]
  obtain ⟨k, hk⟩ := mod3_decomp (s.natAbs * s.natAbs)
  rcases mod3_range (s.natAbs * s.natAbs) with h0 | h1 | h2
  · refine Or.inl ⟨(k : Int), ?_⟩
    rw [hcast, hk, h0]; exact ncast_mul3 k
  · refine Or.inr ⟨(k : Int), ?_⟩
    rw [hcast, hk, h1, ncast_mul3_one k]; ring_intZ
  · exact absurd h2 (mod3_sq_ne_two s.natAbs)

/-- `↑3 ∤ c` for `c ∈ {1,2}` — reflect to `ℕ` (`int_dvd_to_nat`, `c.natAbs ∈ {1,2}`), where `3 ∤ 1`
    and `3 ∤ 2` are decidable. -/
private theorem not_three_dvd_small {c : Int} (hc : c.natAbs = 1 ∨ c.natAbs = 2)
    (h : (3 : Int) ∣ c) : False := by
  have hd : (3 : Nat) ∣ c.natAbs := int_dvd_to_nat 3 c h
  rcases hc with h1 | h1
  · rw [h1] at hd; exact absurd (le_of_dvd_pos 3 1 (by decide) hd) (by decide)
  · rw [h1] at hd; exact absurd (le_of_dvd_pos 3 2 (by decide) hd) (by decide)

/-- From `3·W + 2 = 3·k` extract `3 ∣ 2` (witness `k − W`). -/
private theorem dvd_two_of (W k : Int) (hk : 3 * W + 2 = 3 * k) : (3 : Int) ∣ 2 :=
  ⟨k - W, by
    calc (2 : Int) = (3 * W + 2) - 3 * W := by ring_intZ
      _ = 3 * k - 3 * W := by rw [hk]
      _ = 3 * (k - W) := by ring_intZ⟩

/-- From `3·W + 2 − 1 = 3·k` extract `3 ∣ 1` (witness `k − W`). -/
private theorem dvd_one_of (W k : Int) (hk : 3 * W + 2 - 1 = 3 * k) : (3 : Int) ∣ 1 :=
  ⟨k - W, by
    calc (1 : Int) = (3 * W + 2 - 1) - 3 * W := by ring_intZ
      _ = 3 * k - 3 * W := by rw [hk]
      _ = 3 * (k - W) := by ring_intZ⟩

/-- ★★★★ **The inert obstruction over `ℤ`** — `‖d‖² ≠ q` for any `d ∈ ℤ[ω]` and rational `q ≡ 2 (mod 3)`.
    `‖d‖² = (a+b)² − 3ab ≡ (a+b)² (mod 3)`, a square, never `≡ 2`; but `q ≡ 2`.  ∅-axiom (PURE). -/
theorem normSq_ne_of_mod3_two {q : Nat} (hq3 : q % 3 = 2) (d : ZOmega) : d.normSq ≠ (q : Int) := by
  intro heq
  have hqInt : (q : Int) = 3 * ((q / 3 : Nat) : Int) + 2 := by
    have hnat : 3 * (q / 3) + 2 = q := by have h := div_add_mod q 3; rwa [hq3] at h
    have hc : ((3 * (q / 3) + 2 : Nat) : Int) = ((q : Nat) : Int) := by rw [hnat]
    rw [← hc]; rfl
  have hW : (d.re + d.im) * (d.re + d.im)
      = 3 * (((q / 3 : Nat) : Int) + d.re * d.im) + 2 := by
    have key : (d.re + d.im) * (d.re + d.im) = (q : Int) + 3 * (d.re * d.im) := by
      have hq' : (q : Int) = d.normSq := heq.symm
      rw [hq']
      show (d.re + d.im) * (d.re + d.im)
          = (d.re * d.re - d.re * d.im + d.im * d.im) + 3 * (d.re * d.im)
      ring_intZ
    rw [key, hqInt]; ring_intZ
  rcases int_sq_mod3 (d.re + d.im) with hdvd | hdvd
  · -- 3 ∣ (a+b)² = 3W + 2  ⟹  3 ∣ 2
    rw [hW] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    exact not_three_dvd_small (c := 2) (Or.inr rfl) (dvd_two_of _ k hk)
  · -- 3 ∣ ((a+b)² − 1) = 3W + 1  ⟹  3 ∣ 1
    rw [hW] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    exact not_three_dvd_small (c := 1) (Or.inl rfl) (dvd_one_of _ k hk)

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinInertForm
