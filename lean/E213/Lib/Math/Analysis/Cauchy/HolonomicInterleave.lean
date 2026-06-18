import E213.Lib.Math.Analysis.Cauchy.QuasiPolyBound
import E213.Meta.Nat.AddMod213

/-!
# HolonomicInterleave — Hurwitzian ⟹ holonomic, the interleaving closure made internal

`HurwitzianCF` proves a Hurwitzian real is `QuasiPolyCF p` (partial quotients
quasi-polynomial: each residue section `k ↦ a(p·k+r)` is a discrete polynomial,
`polyDepth dᵣ`), and `polyDepth_diff_recurrence` gives each section a
constant-coefficient recurrence `Δ^{dᵣ+1} = 0`.  The step "a finite interleaving of
C-finite sections is P-recursive (holonomic)" was the one classical fact the
framework *cited* rather than proved — `polyDepth_diff_recurrence`'s docstring says so.

This file closes it ∅-axiom: a `QuasiPolyCF p` sequence satisfies **one** homogeneous
constant-coefficient recurrence on the whole index `n`, namely

>  ★★★ `quasipoly_whole_recurrence` :  `∃ D, ∀ n, liftKP p (D+1) a n = 0`,

where `liftKP p` is the **`p`-shift** finite difference `(Δ_p s)(n) = s(n+p) − s(n)`,
i.e. the operator `(E^p − 1)`.  The annihilator is `(E^p − 1)^{D+1}` (order `p·(D+1)`),
**not** the ordinary `(E−1)^{p(D+1)} = Δ^{p(D+1)}`: an interleaving of polynomials is a
quasi-polynomial, which the ordinary difference never kills (e.g. `0,1,0,1,…` survives
every `Δ`, but `Δ_2` annihilates it).  The single combinatorial identity is

  `liftKP p j a (p·k+r) = liftK j (k ↦ a(p·k+r)) k`     (`liftKP_section`),

the `p`-shift difference restricted to a residue class **is** the ordinary difference of
that section; iterated `D+1` times it lands inside each section's `Δ^{D+1} = 0`.

Corollary `e_cf_whole_recurrence`: e's partial quotients satisfy one homogeneous
`(E³ − 1)`-difference recurrence — e is holonomic with **zero** external citation.

All zero-axiom.
-/

namespace E213.Lib.Math.Analysis.Cauchy.HolonomicInterleave

open E213.Lib.Math.Analysis.Cauchy.DivergenceLadder (diff liftK isConst)
open E213.Lib.Math.Analysis.Cauchy.DepthPRecursive (polyDepth)
open E213.Lib.Math.Analysis.Cauchy.HurwitzianCF (QuasiPolyCF isConst_diff_zero ePQ e_cf_quasipoly)
open E213.Lib.Math.Analysis.Cauchy.QuasiPolyBound (nmax le_nmax_left le_nmax_right)

/-! ## §1 — the `p`-shift finite difference and its iterate -/

/-- The `p`-shift finite difference `(Δ_p s)(n) = s(n+p) − s n` — the operator `E^p − 1`. -/
def diffP (p : Nat) (s : Nat → Nat) : Nat → Nat := fun n => s (n + p) - s n

/-- `k`-fold `p`-shift difference — the operator `(E^p − 1)^k`. -/
def liftKP (p : Nat) : Nat → (Nat → Nat) → (Nat → Nat)
  | 0,     s => s
  | k + 1, s => diffP p (liftKP p k s)

/-! ## §2 — the residue identity: `(E^p−1)` on a class is the section's `(E−1)` -/

/-- ★★★ The `p`-shift difference, restricted to the residue class `r (mod p)`, **is** the
    ordinary finite difference of that section `t ↦ a(p·t+r)`.  Iterated `j` times:
    `liftKP p j a (p·k+r) = liftK j (section r) k`. -/
theorem liftKP_section (p r : Nat) (a : Nat → Nat) (j : Nat) :
    ∀ k, liftKP p j a (p * k + r) = liftK j (fun t => a (p * t + r)) k := by
  induction j with
  | zero => intro k; rfl
  | succ j ih =>
    intro k
    have harith : p * k + r + p = p * (k + 1) + r := by
      rw [Nat.mul_succ, Nat.add_right_comm (p * k) p r]
    show liftKP p j a (p * k + r + p) - liftKP p j a (p * k + r)
        = liftK j (fun t => a (p * t + r)) (k + 1) - liftK j (fun t => a (p * t + r)) k
    rw [harith, ih (k + 1), ih k]

/-! ## §3 — `polyDepth` monotonicity (lift all sections to one common depth) -/

/-- A constant `d`-th difference stays constant after one more difference (it is `0`). -/
theorem polyDepth_succ {d : Nat} {s : Nat → Nat} (h : polyDepth d s) : polyDepth (d + 1) s := by
  intro n
  show diff (liftK d s) n = diff (liftK d s) 0
  rw [isConst_diff_zero h n, isConst_diff_zero h 0]

/-- `polyDepth` is monotone in the degree: `polyDepth d s → d ≤ d' → polyDepth d' s`. -/
theorem polyDepth_mono {d d' : Nat} {s : Nat → Nat} (h : polyDepth d s) (hdd : d ≤ d') :
    polyDepth d' s := by
  obtain ⟨t, rfl⟩ := Nat.le.dest hdd
  clear hdd
  induction t with
  | zero => exact h
  | succ t ih => exact polyDepth_succ ih

/-! ## §4 — collect the `p` per-residue depths into one common `D` -/

/-- Bounded collection: a common depth `D` working for every residue `r < q` (`q ≤ p`). -/
theorem common_depth_aux (p : Nat) (a : Nat → Nat)
    (h : ∀ r, r < p → ∃ d, polyDepth d (fun k => a (p * k + r))) :
    ∀ q, q ≤ p → ∃ D, ∀ r, r < q → polyDepth D (fun k => a (p * k + r)) := by
  intro q
  induction q with
  | zero => intro _; exact ⟨0, fun r hr => absurd hr (Nat.not_lt_zero r)⟩
  | succ q ih =>
    intro hq
    obtain ⟨D₀, hD₀⟩ := ih (Nat.le_of_succ_le hq)
    obtain ⟨dq, hdq⟩ := h q (Nat.lt_of_lt_of_le (Nat.lt_succ_self q) hq)
    refine ⟨nmax D₀ dq, fun r hr => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr) with hlt | heq
    · exact polyDepth_mono (hD₀ r hlt) (le_nmax_left D₀ dq)
    · subst heq; exact polyDepth_mono hdq (le_nmax_right D₀ dq)

/-- A common depth `D` for **all** residues of a `QuasiPolyCF p` sequence. -/
theorem common_depth (p : Nat) (a : Nat → Nat) (h : QuasiPolyCF p a) :
    ∃ D, ∀ r, r < p → polyDepth D (fun k => a (p * k + r)) :=
  common_depth_aux p a h p (Nat.le_refl p)

/-! ## §5 — the whole-sequence homogeneous recurrence -/

/-- ★★★ **The interleaving closure.**  A `QuasiPolyCF p` sequence satisfies one homogeneous
    constant-coefficient recurrence on the whole index: `(E^p − 1)^{D+1} a = 0`, i.e.
    `liftKP p (D+1) a n = 0` for all `n`, with `D` the common residue depth.  This is the
    ∅-axiom replacement for the cited "interleaving of C-finite sections is P-recursive":
    every `n = p·(n/p) + n%p` lands in a residue class, where the `p`-shift difference is the
    section's ordinary difference, killed by `Δ^{D+1}`. -/
theorem quasipoly_whole_recurrence (p : Nat) (hp : 1 ≤ p) (a : Nat → Nat)
    (h : QuasiPolyCF p a) :
    ∃ D, ∀ n, liftKP p (D + 1) a n = 0 := by
  obtain ⟨D, hD⟩ := common_depth p a h
  refine ⟨D, fun n => ?_⟩
  have hr : n % p < p := Nat.mod_lt n hp
  have hdiv : p * (n / p) + n % p = n := E213.Meta.Nat.AddMod213.div_add_mod n p
  rw [← hdiv, liftKP_section p (n % p) a (D + 1) (n / p)]
  exact isConst_diff_zero (hD (n % p) hr) (n / p)

/-- ★★★ **e is holonomic, citation-free.**  e's partial quotients `ePQ` satisfy one
    homogeneous `(E³ − 1)`-difference recurrence — the interleaving closure applied to the
    `QuasiPolyCF 3` witness `e_cf_quasipoly`. -/
theorem e_cf_whole_recurrence : ∃ D, ∀ n, liftKP 3 (D + 1) ePQ n = 0 :=
  quasipoly_whole_recurrence 3 (by decide) ePQ e_cf_quasipoly

end E213.Lib.Math.Analysis.Cauchy.HolonomicInterleave
