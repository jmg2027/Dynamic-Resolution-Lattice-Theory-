/-!
# StagedLimit — the forward stabilization map (∅-axiom)

The **internal-reach** form of a limit: a staged reading `s : Nat → C → V` whose
per-coordinate reading **settles past a per-coordinate modulus** `N` has a limit
obtained by reading each coordinate off *its own* modulus stage,
`limit c := s (N c) c`, and that limit **equals every late stage**
(`limit_eq_late`).  The limit is *reached* — assembled from genuinely attained
per-coordinate values — not asserted by a completion axiom.

This is the positive / internal-reach complement to "reached by none"
(`Lens/Foundations/FlatOntologyClosure.object1_not_surjective`): there the self-cover misses
its residue; here the staged reading, once each coordinate stabilizes, *is* its
limit at every late index.  It is the forward (eventual-constancy) sibling of the
well-founded descent schema `Lib/Math/Foundations/MonovariantFlow` (which reaches
a *normal form* by strict decrease) — both are well-founded maps to a fixed
reading, one backward (descent), one forward (stabilization).

**Scope (honest).**  This abstracts the **modulus-limit** common to the Real213
cut / Cauchy family (`Analysis.CauchyComplete.CauchyCutSeq` routes its
`limit_eq_at` through `limit_eq_late`, `StagedLimitCauchy`).  It does **not**
subsume the p-adic diagonal `Padic.Foundation.Zp.diagLimit`: that object's content
is the *trunc-assembly* fold `diagLimit_trunc_succ` under a *trunc-level* one-step
hypothesis, which does not reduce to this per-coordinate stabilization — the
digit-level fit would be trivial.  So `StagedLimit` is the cut/modulus-limit
abstracted, not a cross-domain (Padic ⊥ Real213) unifier.
-/

namespace E213.Meta.StagedLimit

/-- A staged reading `s i c` of coordinate `c` at stage `i`, settling past a
    per-coordinate modulus `N c`. -/
structure StagedLimit (C V : Type _) where
  s : Nat → C → V
  N : C → Nat
  stable : ∀ c i j, N c ≤ i → N c ≤ j → s i c = s j c

/-- The limit: read each coordinate off its own modulus stage. -/
def StagedLimit.limit {C V : Type _} (sl : StagedLimit C V) : C → V :=
  fun c => sl.s (sl.N c) c

/-- ★★★ **The limit equals every late stage.**  The internal-reach witness: past
    its modulus, every coordinate's reading is already the limit's. -/
theorem StagedLimit.limit_eq_late {C V : Type _} (sl : StagedLimit C V)
    (c : C) (i : Nat) (h : sl.N c ≤ i) : sl.limit c = sl.s i c :=
  sl.stable c (sl.N c) i (Nat.le_refl _) h

end E213.Meta.StagedLimit
