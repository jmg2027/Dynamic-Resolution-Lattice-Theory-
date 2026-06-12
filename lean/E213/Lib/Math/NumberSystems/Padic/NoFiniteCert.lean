import E213.Lib.Math.NumberSystems.Padic.SetoidFramework

/-!
# NoFiniteCert — p-adic equality has no finite certificate (a second continuum witness)

The meta-analysis readout grid (program finding C5) classifies a number
system's equality readout on two axes — *faithfulness*
and, among faithful readouts, *support-finiteness*.  ℤ/ℕ (the `vp` readout) is
the unique **faithful + finite** cell (a finite equality certificate,
`FoldCriterion.vp_eq_zero_of_gt`); every completion is **faithful + infinite**.

This file makes the `p`-adic cell a *theorem*, not an assertion — the second
continuum-side witness (after the reals' `CutNoFiniteCert`), confirming axis B is
real across genuinely different completions:

  * ★★ `zpseq_no_finite_certificate` — for every resolution bound `N`, two
    *distinct* `p`-adic integers agree on the first `N` digits yet are not
    `ZpSeqEquiv`.  (`x` is all-zeros; `y` is zero except a `1` at digit `N`.)
    So no finite digit-prefix certifies `p`-adic equality: `ZpSeqEquiv := ∀ k,
    digits agree` does not collapse to a finite check.

Together with the integer side (finite support) and the real side
(`cut_no_finite_certificate`), this pins bridge 1's distinction across three
number systems: **the equality certificate is finite for ℤ/ℕ alone; every
completion (real, `p`-adic, …) is unbounded.**  Discrete vs continuum =
reconstructible-from-finitely-many-readouts or not.

All ∅-axiom: bare `Fin p` digit construction (`0 ≠ 1` for `p ≥ 2`), the decidable
`k = N` test, no `funext` (`ZpSeqEquiv` is a `∀`-`Prop`, not function equality).
-/

namespace E213.Lib.Math.NumberSystems.Padic.NoFiniteCert

open E213.Lib.Math.NumberSystems.Padic (ZpSeq ZpDigit)
open E213.Lib.Math.NumberSystems.Padic.SetoidFramework (ZpSeqEquiv)

/-- ★★ **`p`-adic equality has no finite certificate.**  For every digit bound
    `N` (and any base `p ≥ 2`), the all-zeros `p`-adic integer and the one that
    is zero except for a single `1` at digit `N` **agree on every digit `k < N`**
    yet are **not** `ZpSeqEquiv` (they differ at digit `N`).  So agreement on any
    finite digit-prefix never certifies `p`-adic equality — the readout carries
    information at *every* depth, exactly like the real cut and unlike the finite
    prime-support of ℤ.  This is the second continuum-side witness of bridge 1's
    certificate-size distinction (cf. `Real213.Core.CutNoFiniteCert`). -/
theorem zpseq_no_finite_certificate {p : Nat} (hp : 2 ≤ p) (N : Nat) :
    ∃ x y : ZpSeq p,
      (∀ k, k < N → x.digits k = y.digits k) ∧ ¬ ZpSeqEquiv x y := by
  have h0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp
  have h1 : 1 < p := Nat.lt_of_lt_of_le (by decide) hp
  refine ⟨⟨fun _ => ⟨0, h0⟩⟩, ⟨fun k => if k = N then ⟨1, h1⟩ else ⟨0, h0⟩⟩, ?_, ?_⟩
  · -- agree below N: at k < N, k ≠ N, so the second sequence reads `0` too.
    intro k hk
    show (⟨0, h0⟩ : ZpDigit p) = if k = N then ⟨1, h1⟩ else ⟨0, h0⟩
    rw [if_neg (Nat.ne_of_lt hk)]
  · -- differ at N: `0 ≠ 1` in `Fin p`.
    intro heq
    have hN := heq N
    have hcontra : (⟨0, h0⟩ : ZpDigit p) = ⟨1, h1⟩ := by
      have e : (⟨fun k => if k = N then (⟨1, h1⟩ : ZpDigit p) else ⟨0, h0⟩⟩ : ZpSeq p).digits N
             = (⟨1, h1⟩ : ZpDigit p) := by
        show (if N = N then (⟨1, h1⟩ : ZpDigit p) else ⟨0, h0⟩) = _
        rw [if_pos rfl]
      rw [e] at hN; exact hN
    exact Nat.noConfusion (congrArg Fin.val hcontra)

end E213.Lib.Math.NumberSystems.Padic.NoFiniteCert
