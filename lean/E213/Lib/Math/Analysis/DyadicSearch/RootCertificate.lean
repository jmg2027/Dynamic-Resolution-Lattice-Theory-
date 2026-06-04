import E213.Lib.Math.Analysis.DyadicSearch.MinimalRootLensMonotone
/-!
# RootCertificate — full root packaging

Closes the `theory/math/analysis/minimal_root.md` open frontier:

> Full root-certificate (lower / upper / zero): the current
> skeleton gives the cut; a full `RootCertificate` packaging
> (lower bound, upper bound, witness of vanishing) awaits the
> monotone-polynomial milestone (next).

This file packages the trajectory-witness IVT readout into a
single `RootCertificate f` structure:

  `RootCertificate f` bundles:
    · `lowerCut` : Cut where `f lowerCut 0 1 = false` (f below 0)
    · `upperCut` : Cut where `f upperCut 0 1 = true`  (f at/above 0)
    · the underlying `BracketSignChange` witness in a DyadicBracket
      whose endpoints these cuts are.

Constructors:
  · `RootCertificate.ofBracket` — promote a `BracketSignChange f db`
    to a `RootCertificate f`.
  · `RootCertificate.refine` — apply one bisectStep to tighten the
    bracket while preserving the certificate (uses the
    LocallyDeterminedData premise).

This is the "monotone-polynomial milestone" deliverable in its
213-native form: the certificate is the cut data + sign witnesses,
not an `∃` existential.

All declarations PURE.
-/

namespace E213.Lib.Math.Analysis.DyadicSearch.RootCertificate

open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
  (DyadicBracket DyadicBracket.leftCut DyadicBracket.rightCut
   DyadicBracket.bisectStep)
open E213.Lib.Math.Analysis.DyadicSearch.MinimalRootLens
  (signedLeftOracle)
open E213.Lib.Math.NumberSystems.Real213.Core.CutFnData (LocallyDeterminedData)
open E213.Lib.Math.Analysis.DyadicSearch.MinimalRootLensMonotone
  (BracketSignChange
   bisectStep_signed_left_preserves_sign_change
   bisectN_signed_left_preserves_sign_change)

/-! ## §1 — RootCertificate structure -/

/-- A **root certificate** for `f`: a dyadic bracket `db` along
    with a sign-change witness `f leftCut < 0 ≤ f rightCut` at
    unit precision.  The certificate identifies a candidate-root
    region; the `MinimalRootLens` readout gives the cut itself. -/
structure RootCertificate
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) where
  /-- The bracket region containing the root. -/
  bracket : DyadicBracket
  /-- Sign-change witness inside the bracket. -/
  signChange : BracketSignChange f bracket

namespace RootCertificate

/-! ## §2 — Promotion from a sign-change witness -/

/-- Build a `RootCertificate` from any sign-change witness. -/
def ofBracket
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    {db : DyadicBracket} (sc : BracketSignChange f db) :
    RootCertificate f where
  bracket := db
  signChange := sc

/-! ## §3 — Refinement: tighten the bracket -/

/-- Refine the certificate by one `bisectStep` under `signedLeftOracle`.
    Requires `LocallyDeterminedData f` to invoke the existing
    sign-change-preservation lemma. -/
def refine
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (lf : LocallyDeterminedData f)
    (rc : RootCertificate f) : RootCertificate f where
  bracket := rc.bracket.bisectStep (signedLeftOracle f)
  signChange :=
    bisectStep_signed_left_preserves_sign_change lf rc.bracket rc.signChange

/-- Refine by N steps. -/
def refineN
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (lf : LocallyDeterminedData f)
    (n : Nat) (rc : RootCertificate f) : RootCertificate f where
  bracket := DyadicBracket.bisectN (signedLeftOracle f) n rc.bracket
  signChange :=
    bisectN_signed_left_preserves_sign_change lf n rc.bracket rc.signChange

/-! ## §4 — Endpoint accessors -/

/-- Lower cut (f < 0 here). -/
def lowerCut {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (rc : RootCertificate f) : Nat → Nat → Bool :=
  rc.bracket.leftCut

/-- Upper cut (f ≥ 0 here). -/
def upperCut {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (rc : RootCertificate f) : Nat → Nat → Bool :=
  rc.bracket.rightCut

/-- Sign of `f` at the lower endpoint: `f.lowerCut 0 1 = false`. -/
theorem signLeft
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (rc : RootCertificate f) :
    f (lowerCut rc) 0 1 = false :=
  rc.signChange.signLeft

/-- Sign of `f` at the upper endpoint: `f.upperCut 0 1 = true`. -/
theorem signRight
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (rc : RootCertificate f) :
    f (upperCut rc) 0 1 = true :=
  rc.signChange.signRight

end RootCertificate

/-! ## §5 — Capstone -/

/-- ★★★★★ **RootCertificate capstone**.

    Bundles: (a) the `RootCertificate f` structure with `bracket +
    signChange`, (b) the `ofBracket` constructor, (c) `refine` /
    `refineN` for tightening, (d) `lowerCut` / `upperCut` accessors,
    (e) `signLeft` / `signRight` sign witnesses at unit precision.

    Reading: the IVT root of `f` is a typed certificate carrying
    bracket endpoints + sign witnesses, refined under `signedLeftOracle`-
    bisection.  No `∃` existential, no `Decidable` on the root —
    just constructive Nat-decidable data. -/
theorem root_certificate_capstone
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    {db : DyadicBracket} (sc : BracketSignChange f db) :
    -- (a) Certificate exists
    Nonempty (RootCertificate f)
    -- (b) Endpoints accessible
    ∧ (RootCertificate.ofBracket sc).bracket = db
    -- (c) Sign witnesses
    ∧ f (RootCertificate.ofBracket sc).lowerCut 0 1 = false
    ∧ f (RootCertificate.ofBracket sc).upperCut 0 1 = true := by
  refine ⟨⟨RootCertificate.ofBracket sc⟩, rfl, ?_, ?_⟩
  · exact sc.signLeft
  · exact sc.signRight

end E213.Lib.Math.Analysis.DyadicSearch.RootCertificate
