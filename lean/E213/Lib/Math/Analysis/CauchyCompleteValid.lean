import E213.Lib.Math.Analysis.CauchyComplete
import E213.Lib.Math.NumberSystems.Real213.Core.ValidCut

/-!
# CauchyCompleteValid — the cut space is *closed* under Cauchy limits

`CauchyComplete` builds, for any Cauchy sequence of cuts, an explicit limit cut
(`CauchyCutSeq.limit`) and shows it agrees with every term past the modulus
(`limit_eq_at`).  That construction is generic in the underlying `cs`, but says
nothing about whether the limit is a *real* — a `ValidCut` — when the terms are.

This file closes that gap: **completeness proper**.  If every term `cs i` is a
`ValidCut` (resp. `RatioCut`), so is `limit` — the residue's real-cut space is
closed under Cauchy limits, with no per-instance argument.  The proof is uniform:
to compare the limit at two arguments, pick **one** index past *both* of their
moduli, collapse both points to that single term via `limit_eq_at`, then apply
the term's own monotonicity.  The Cauchy modulus does all the work of making
"different arguments use different sampling indices" harmless.

The common index is `N₁ + N₂` (each summand `≤` the sum, PURE via
`Nat.le_add_{right,left}`) — *not* `Nat.max`, whose lemmas pull `propext`.
Function-level equality (`limit_unique`) is stated **pointwise** (`∀ m k, … = …`)
to stay clear of `funext`/`Quot.sound`, matching the repo's cut-equality
convention.  All ∅-axiom.
-/

namespace E213.Lib.Math.Analysis.CauchyComplete

open E213.Lib.Math.NumberSystems.Real213.Core.ValidCut (ValidCut RatioCut)

/-- ★★★ **Completeness (monotone form)**: the Cauchy limit of a sequence of
    `ValidCut`s is a `ValidCut`.  The cut space is closed under Cauchy limits.

    Both monotonicity directions reduce to the same move: the two compared points
    `limit · ·` sample at *different* indices `N`, so pull both to a common index
    `N₁ + N₂` past both moduli (`limit_eq_at`), where the single term `cs i` —
    itself valid — supplies the monotonicity. -/
theorem CauchyCutSeq.limit_valid (ccs : CauchyCutSeq)
    (hv : ∀ i, ValidCut (ccs.cs i)) : ValidCut ccs.limit where
  upM := by
    intro m1 m2 k hm h
    have e1 : ccs.limit m1 k = ccs.cs (ccs.N m1 k + ccs.N m2 k) m1 k :=
      ccs.limit_eq_at m1 k _ (Nat.le_add_right _ _)
    have e2 : ccs.limit m2 k = ccs.cs (ccs.N m1 k + ccs.N m2 k) m2 k :=
      ccs.limit_eq_at m2 k _ (Nat.le_add_left _ _)
    rw [e2]
    rw [e1] at h
    exact (hv _).upM m1 m2 k hm h
  dnK := by
    intro m k1 k2 hk h
    have e1 : ccs.limit m k1 = ccs.cs (ccs.N m k1 + ccs.N m k2) m k1 :=
      ccs.limit_eq_at m k1 _ (Nat.le_add_right _ _)
    have e2 : ccs.limit m k2 = ccs.cs (ccs.N m k1 + ccs.N m k2) m k2 :=
      ccs.limit_eq_at m k2 _ (Nat.le_add_left _ _)
    rw [e1]
    rw [e2] at h
    exact (hv _).dnK m k1 k2 hk h

/-- ★★★ **Completeness (ratio form)**: the Cauchy limit of a sequence of
    `RatioCut`s is a `RatioCut`.  Same one-common-index reduction, but the two
    points may differ in both numerator and denominator, so the shared index is
    `N m1 k1 + N m2 k2`. -/
theorem CauchyCutSeq.limit_ratio (ccs : CauchyCutSeq)
    (hr : ∀ i, RatioCut (ccs.cs i)) : RatioCut ccs.limit where
  ratioMono := by
    intro m1 k1 m2 k2 hk1 hratio h
    have e1 : ccs.limit m1 k1 = ccs.cs (ccs.N m1 k1 + ccs.N m2 k2) m1 k1 :=
      ccs.limit_eq_at m1 k1 _ (Nat.le_add_right _ _)
    have e2 : ccs.limit m2 k2 = ccs.cs (ccs.N m1 k1 + ccs.N m2 k2) m2 k2 :=
      ccs.limit_eq_at m2 k2 _ (Nat.le_add_left _ _)
    rw [e2]
    rw [e1] at h
    exact (hr _).ratioMono m1 k1 m2 k2 hk1 hratio h

/-- ★★ **Modulus-independence (pointwise)**: the limit depends only on the
    underlying sequence `cs`, not on the chosen modulus.  Two `CauchyCutSeq` that
    agree on `cs` have the same limit at every `(m, k)` — pull both limits to a
    common index `N₁ + N₂` past *both* moduli, where they read the same term.
    Stated pointwise to avoid `funext` (which pulls `Quot.sound`). -/
theorem CauchyCutSeq.limit_unique (c1 c2 : CauchyCutSeq)
    (hcs : ∀ i m k, c1.cs i m k = c2.cs i m k) (m k : Nat) :
    c1.limit m k = c2.limit m k := by
  have e1 : c1.limit m k = c1.cs (c1.N m k + c2.N m k) m k :=
    c1.limit_eq_at m k _ (Nat.le_add_right _ _)
  have e2 : c2.limit m k = c2.cs (c1.N m k + c2.N m k) m k :=
    c2.limit_eq_at m k _ (Nat.le_add_left _ _)
  rw [e1, e2, hcs]

end E213.Lib.Math.Analysis.CauchyComplete
