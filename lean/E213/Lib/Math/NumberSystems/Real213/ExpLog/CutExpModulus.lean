import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial
import E213.Meta.Nat.PolyNatMTactic

/-!
# Real213 — exp Taylor convergence modulus (ratio-test core, ∅-axiom)

**Marathon T1** (`research-notes/frontiers/transcendentals/transcendental_functions_ladder.md`).

`CutExpSeries` builds `expPartialSum x N = Σ_{k<N} xᵏ/k!`; the open follow-up was the
**convergence modulus** — the ratio-test argument that the geometric majorant `Mⁿ/n!`
forces the tail to vanish.  This file delivers that analytic core as pure `Nat`
inequalities on the *term magnitudes* `Mᵏ/k!` (numerator `Mᵏ`, denominator `k!`),
where `M` bounds `|x|`.

The ratio test in one line: once `2M ≤ k+1`, the `(k+1)`-th Taylor term is at most
**half** the `k`-th — because

  `M^{k+1}/(k+1)!  =  (M/(k+1)) · Mᵏ/k!  ≤  (1/2) · Mᵏ/k!`   (since `M/(k+1) ≤ 1/2`).

Cross-multiplied (both denominators positive) this is a clean `Nat` statement, with no
division and no `Real213` cut comparison.  Iterating gives the **geometric majorant**:
for `N ≥ 2M`, `term(N+j) ≤ term(N)/2ʲ` — the tail decays geometrically, so the partial
sums are Cauchy with an explicit modulus (the dyadic `2ʲ` rate).

This is the honest ratio-test certificate `CutExpSeries` deferred.  Packaging it as a
full `CauchyCutSeq` over the cut-level `expPartialSum` is the T1→T2 bridge (next rung);
the *rate* — the hard analytic content — is proven here.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpModulus

open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial factorial_succ)

/-! ## §1 — single-step ratio: the `(k+1)`-th term is ≤ half the `k`-th -/

/-- The power half-step: once `2M ≤ k+1`, `2·M^{k+1} ≤ Mᵏ·(k+1)`.  This is the
    numerator of "the next Taylor term is at most half the current one" (the factorial
    denominator grows by the matching factor `k+1`, supplied in `expTerm_ratio_half`). -/
theorem pow_half_step (M k : Nat) (h : 2 * M ≤ k + 1) :
    2 * M ^ (k + 1) ≤ M ^ k * (k + 1) := by
  calc 2 * M ^ (k + 1)
      = M ^ k * (2 * M) := by rw [Nat.pow_succ]; ring_nat
    _ ≤ M ^ k * (k + 1) := Nat.mul_le_mul_left (M ^ k) h

/-- ★ **Ratio test, one step (cross-multiplied).**  Once `2M ≤ k+1`, the `(k+1)`-th
    Taylor term `M^{k+1}/(k+1)!` is at most **half** the `k`-th term `Mᵏ/k!`:

      `2 · M^{k+1} · k!  ≤  Mᵏ · (k+1)!`.

    (Both denominators `k!`, `(k+1)!` are positive, so this cross-multiplication is the
    faithful `Nat` reading of `term(k+1) ≤ (1/2)·term(k)`.) -/
theorem expTerm_ratio_half (M k : Nat) (h : 2 * M ≤ k + 1) :
    2 * M ^ (k + 1) * factorial k ≤ M ^ k * factorial (k + 1) := by
  rw [factorial_succ k]
  calc 2 * M ^ (k + 1) * factorial k
      = (2 * M ^ (k + 1)) * factorial k := by ring_nat
    _ ≤ (M ^ k * (k + 1)) * factorial k :=
        Nat.mul_le_mul_right (factorial k) (pow_half_step M k h)
    _ = M ^ k * ((k + 1) * factorial k) := by ring_nat

/-! ## §2 — geometric majorant: `term(N+j) ≤ term(N)/2ʲ` for `N ≥ 2M` -/

/-- ★★ **Geometric majorant (the convergence rate).**  Fix a base `N` with `2M ≤ N+1`
    (so the half-step holds from `N` on).  Then for every `j`,

      `2ʲ · M^{N+j} · N!  ≤  Mᴺ · (N+j)!`,

    i.e. the `(N+j)`-th Taylor term is at most `term(N)/2ʲ`.  The Taylor tail past `N`
    is dominated by a geometric series with ratio `1/2`: the **ratio-test convergence
    certificate** for `exp`, ∅-axiom.  Proof: induction on `j`, each step the half-step
    `pow_half_step` at `k = N+j` (whose hypothesis `2M ≤ N+j+1` follows from `2M ≤ N+1`). -/
theorem expTerm_geom_majorant (M N : Nat) (hM : 2 * M ≤ N + 1) :
    ∀ j, 2 ^ j * M ^ (N + j) * factorial N ≤ M ^ N * factorial (N + j) := by
  intro j
  induction j with
  | zero => rw [Nat.pow_zero, Nat.one_mul, Nat.add_zero]; exact Nat.le_refl _
  | succ j ih =>
    -- half-step hypothesis at k = N + j
    have hk : 2 * M ≤ (N + j) + 1 :=
      Nat.le_trans hM (Nat.add_le_add_right (Nat.le_add_right N j) 1)
    -- (A) IH × (N+j+1):  2ʲ·M^{N+j}·N!·(N+j+1) ≤ Mᴺ·(N+j+1)!
    have hA : 2 ^ j * M ^ (N + j) * factorial N * (N + j + 1)
            ≤ M ^ N * factorial (N + j + 1) := by
      have hc := Nat.mul_le_mul_right (N + j + 1) ih
      have eR : M ^ N * factorial (N + j) * (N + j + 1) = M ^ N * factorial (N + j + 1) := by
        rw [factorial_succ (N + j)]; ring_nat
      rw [eR] at hc; exact hc
    -- (B) the half-step lifts to:  2^{j+1}·M^{N+j+1}·N! ≤ 2ʲ·M^{N+j}·N!·(N+j+1)
    have hB : 2 ^ (j + 1) * M ^ (N + j + 1) * factorial N
            ≤ 2 ^ j * M ^ (N + j) * factorial N * (N + j + 1) := by
      have hmul := Nat.mul_le_mul_left (2 ^ j * factorial N) (pow_half_step M (N + j) hk)
      calc 2 ^ (j + 1) * M ^ (N + j + 1) * factorial N
          = (2 ^ j * factorial N) * (2 * M ^ (N + j + 1)) := by rw [Nat.pow_succ]; ring_nat
        _ ≤ (2 ^ j * factorial N) * (M ^ (N + j) * (N + j + 1)) := hmul
        _ = 2 ^ j * M ^ (N + j) * factorial N * (N + j + 1) := by ring_nat
    exact Nat.le_trans hB hA

/-- **Gap antitone**: the exp term at *any* later index is ≤ the term at the base `N`
    (cross-multiplied `M^{N+j}·N! ≤ Mᴺ·(N+j)!`).  Drops the geometric factor `2ʲ` from
    `expTerm_geom_majorant` — the bound any sub-sequence (`sin`/`cos` at odd/even indices,
    T2) inherits. -/
theorem expTerm_le_of_ge (M N : Nat) (hM : 2 * M ≤ N + 1) (j : Nat) :
    M ^ (N + j) * factorial N ≤ M ^ N * factorial (N + j) := by
  have h1 : M ^ (N + j) * factorial N ≤ 2 ^ j * (M ^ (N + j) * factorial N) :=
    Nat.le_mul_of_pos_left _ (Nat.pos_pow_of_pos j (by decide))
  have h2 : 2 ^ j * (M ^ (N + j) * factorial N) = 2 ^ j * M ^ (N + j) * factorial N := by ring_nat
  exact Nat.le_trans h1 (h2 ▸ expTerm_geom_majorant M N hM j)

/-- ★ **Terms are non-increasing past the threshold** (the alternating-series-test
    input).  For `2M ≤ k+1`, `term(k+1) ≤ term(k)` (cross-multiplied
    `M^{k+1}·k! ≤ Mᵏ·(k+1)!`) — immediate from `expTerm_ratio_half` since `a ≤ 2a`.
    This is exactly the hypothesis the alternating series test for `sin`/`cos` (T2) needs:
    once the Taylor terms decrease monotonically the alternating partial sums bracket the
    limit. -/
theorem expTerm_antitone (M k : Nat) (h : 2 * M ≤ k + 1) :
    M ^ (k + 1) * factorial k ≤ M ^ k * factorial (k + 1) := by
  have hle : M ^ (k + 1) * factorial k ≤ 2 * M ^ (k + 1) * factorial k :=
    calc M ^ (k + 1) * factorial k
        ≤ 2 * (M ^ (k + 1) * factorial k) := Nat.le_mul_of_pos_left _ (by decide)
      _ = 2 * M ^ (k + 1) * factorial k := by ring_nat
  exact Nat.le_trans hle (expTerm_ratio_half M k h)

/-! ## §3 — the tail vanishes: term magnitudes → 0 with a dyadic modulus -/

/-- ★★★ **The Taylor tail decays geometrically from the threshold `2M`.**  Taking the
    base `N = 2M` (where `2M ≤ 2M+1` is automatic), for every `j`

      `2ʲ · M^{2M+j} · (2M)!  ≤  M^{2M} · (2M+j)!`,

    i.e. `term(2M+j) ≤ term(2M)/2ʲ`.  The right side is a *fixed* constant `term(2M)`
    times the geometric factor `2^{-j}`: the term magnitudes are squeezed below any
    dyadic `1/2ᵖ` once `j` is large, so the exp Taylor series converges with the explicit
    dyadic modulus `j ↦ 2ʲ`.  This is the ratio-test conclusion the `CutExpSeries`
    follow-up asked for. -/
theorem expTail_geom_decay (M : Nat) :
    ∀ j, 2 ^ j * M ^ (2 * M + j) * factorial (2 * M)
       ≤ M ^ (2 * M) * factorial (2 * M + j) :=
  expTerm_geom_majorant M (2 * M) (Nat.le_succ (2 * M))

end E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpModulus
