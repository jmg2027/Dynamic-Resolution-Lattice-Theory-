import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpModulus

/-!
# Real213 — sin / cos Taylor convergence modulus (by comparison to exp, ∅-axiom)

**Marathon T2** (`research-notes/frontiers/transcendentals/transcendental_functions_ladder.md`).

The `sin` / `cos` Taylor terms are *exactly* the `exp` Taylor terms restricted to odd /
even indices:

  `cos`'s `k`-th term magnitude  `M^{2k}/(2k)!`   = `exp` term at index `2k`,
  `sin`'s `k`-th term magnitude  `M^{2k+1}/(2k+1)!` = `exp` term at index `2k+1`.

So the whole convergence engine of `CutExpModulus` transfers by **comparison**: the
geometric majorant `expTerm_geom_majorant` and the gap-antitone `expTerm_le_of_ge`
instantiate at the even / odd sub-sequences.  This gives the "alternating + factorial"
convergence modulus the T2 rung asks for, *at the term-magnitude level*, ∅-axiom — the
same rate the `exp` series enjoys, only sampled.

(The signed cut-level series `sinCut x N = Σ(−1)ᵏ x^{2k+1}/(2k+1)!` and `cosCut` —
replacing the `Core/Functions.lean` stubs — are the remaining T2 work; their alternating
partial sums bracket the limit precisely because the term magnitudes proven here are
non-increasing past the threshold `M`, the alternating series test's only hypothesis.)

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.CutTrigModulus

open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpModulus
  (expTerm_geom_majorant expTerm_le_of_ge)

/-! ## §1 — cos: even-index Taylor terms inherit the geometric majorant -/

/-- ★★ **cos term geometric decay.**  Past the threshold `m` (so `2M ≤ 2m+1`), the
    `(m+k)`-th cos term `M^{2(m+k)}/(2(m+k))!` is at most `cos-term(m)/2^{2k}` — even
    faster than `exp` (the even sampling squares the ratio).  Direct instance of
    `expTerm_geom_majorant` at base `2m`, step `2k`. -/
theorem cosTerm_geom_decay (M m k : Nat) (hM : 2 * M ≤ 2 * m + 1) :
    2 ^ (2 * k) * M ^ (2 * (m + k)) * factorial (2 * m)
      ≤ M ^ (2 * m) * factorial (2 * (m + k)) := by
  have h := expTerm_geom_majorant M (2 * m) hM (2 * k)
  have e : 2 * m + 2 * k = 2 * (m + k) := by ring_nat
  rw [e] at h; exact h

/-- ★ **cos terms non-increasing past the threshold** (the alternating-series-test input
    for `cosCut`).  `cos-term(m+k) ≤ cos-term(m)`, cross-multiplied. -/
theorem cosTerm_antitone (M m k : Nat) (hM : 2 * M ≤ 2 * m + 1) :
    M ^ (2 * (m + k)) * factorial (2 * m) ≤ M ^ (2 * m) * factorial (2 * (m + k)) := by
  have h := expTerm_le_of_ge M (2 * m) hM (2 * k)
  have e : 2 * m + 2 * k = 2 * (m + k) := by ring_nat
  rw [e] at h; exact h

/-! ## §2 — sin: odd-index Taylor terms inherit the geometric majorant -/

/-- ★★ **sin term geometric decay.**  Past the threshold (so `2M ≤ 2m+2`), the
    `(m+k)`-th sin term `M^{2(m+k)+1}/(2(m+k)+1)!` is at most `sin-term(m)/2^{2k}`.
    Instance of `expTerm_geom_majorant` at the odd base `2m+1`, step `2k`. -/
theorem sinTerm_geom_decay (M m k : Nat) (hM : 2 * M ≤ 2 * m + 2) :
    2 ^ (2 * k) * M ^ (2 * (m + k) + 1) * factorial (2 * m + 1)
      ≤ M ^ (2 * m + 1) * factorial (2 * (m + k) + 1) := by
  have h := expTerm_geom_majorant M (2 * m + 1) hM (2 * k)
  have e : 2 * m + 1 + 2 * k = 2 * (m + k) + 1 := by ring_nat
  rw [e] at h; exact h

/-- ★ **sin terms non-increasing past the threshold** (the alternating-series-test input
    for `sinCut`). -/
theorem sinTerm_antitone (M m k : Nat) (hM : 2 * M ≤ 2 * m + 2) :
    M ^ (2 * (m + k) + 1) * factorial (2 * m + 1)
      ≤ M ^ (2 * m + 1) * factorial (2 * (m + k) + 1) := by
  have h := expTerm_le_of_ge M (2 * m + 1) hM (2 * k)
  have e : 2 * m + 1 + 2 * k = 2 * (m + k) + 1 := by ring_nat
  rw [e] at h; exact h

end E213.Lib.Math.NumberSystems.Real213.ExpLog.CutTrigModulus
