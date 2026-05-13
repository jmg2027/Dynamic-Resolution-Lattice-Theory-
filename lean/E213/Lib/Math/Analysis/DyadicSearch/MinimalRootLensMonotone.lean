import E213.Lib.Math.Analysis.DyadicSearch.MinimalRootLens
import E213.Lib.Math.Real213.Core.Core.CutFnData
import E213.Lib.Math.Real213.Core.Core.Dyadic
import E213.Lib.Math.Real213.Core.Core.ValidCut
import E213.Lib.Math.Real213.Core.Core.CutPoset
import E213.Meta.Tactic.Nat213
import E213.Meta.Tactic.Pow213

/-!
# MinimalRootLensMonotone — sign-change invariance under bisection

Layer 2 of the trajectory-as-witness IVT (G31).  Builds the
sign-change preservation lemma for the `signedLeftOracle`-driven
bisection, given a locally-determined cut function `f`.

## Components

  * `dyadicCut_double_eq` — pointwise equality
    `dyadicCut (2*M) (E+1) m k = dyadicCut M E m k` (resolution
    doubling preserves the rational).
  * `BracketSignChange f db` — the precondition `f leftCut < 0 ≤ f rightCut`
    expressed at unit precision (m=0, k=1).
  * `bisectStep_signed_left_preserves_sign_change` — sign change
    propagates through one bisection step under `signedLeftOracle f`,
    given `LocallyDeterminedData f`.
  * `bisectN_signed_left_preserves_sign_change` — same, under n steps.

## Next milestone (Layer 3)

`monotonicConsistentOracle` — combine sign-change preservation with
`dyadic_bracket_cauchy_modulus` to construct the full
`ConsistentOracle db`, yielding the IVTRoot via the G31 readout.
-/

namespace E213.Lib.Math.Analysis.DyadicSearch.MinimalRootLensMonotone

open E213.Theory E213.Lens
open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
open E213.Lib.Math.Analysis.DyadicSearch.MinimalRootLens (signedLeftOracle)
open E213.Lib.Math.Real213.Core.Core.Dyadic (dyadicCut)
open E213.Lib.Math.Real213.Core.Core.CutFnData (LocallyDeterminedData)

/-- **Resolution-doubling preserves the rational pointwise**:
    `dyadicCut (2*M) (E+1) m k = dyadicCut M E m k`.

The two cuts represent the same rational `M / 2^E = 2M / 2^(E+1)`,
so they agree at every query precision `(m, k)`.  Pure cut algebra
via `decide` + `Nat.le_of_mul_le_mul_left` cancellation, no funext. -/
theorem dyadicCut_double_eq (M E m k : Nat) :
    dyadicCut (2 * M) (E + 1) m k = dyadicCut M E m k := by
  show decide (2 * M * k ≤ 2^(E + 1) * m) = decide (M * k ≤ 2^E * m)
  -- 2^(E+1) = 2^E * 2
  have hpow : (2:Nat)^(E + 1) = 2^E * 2 := by
    rw [E213.Tactic.Pow213.pow_add_two E 1]
  rw [hpow]
  -- reorder both sides to the form `2 * x ≤ 2 * y`
  have e1 : 2 * M * k = 2 * (M * k) := E213.Tactic.Nat213.mul_assoc 2 M k
  have e2 : 2^E * 2 * m = 2 * (2^E * m) := by
    rw [Nat.mul_comm (2^E) 2, E213.Tactic.Nat213.mul_assoc]
  rw [e1, e2]
  -- 2*x ≤ 2*y ↔ x ≤ y via mul_le_mul_left cancellation
  rcases Nat.lt_or_ge (2^E * m) (M * k) with hlt | hge
  · have h1 : ¬ (M * k ≤ 2^E * m) := Nat.not_le_of_lt hlt
    have h2 : ¬ (2 * (M * k) ≤ 2 * (2^E * m)) := by
      intro habs
      exact h1 (Nat.le_of_mul_le_mul_left habs (by decide))
    rw [decide_eq_false h1, decide_eq_false h2]
  · have h2 : 2 * (M * k) ≤ 2 * (2^E * m) := Nat.mul_le_mul_left 2 hge
    rw [decide_eq_true hge, decide_eq_true h2]

/-- **BracketSignChange**: the precondition for IVT —
    `f leftCut < 0 ≤ f rightCut` at unit precision (m=0, k=1).

`signLeft`: `f db.leftCut 0 1 = false` ↔ "f at left endpoint is
*below* 0 in cut sense at unit precision".
`signRight`: `f db.rightCut 0 1 = true` ↔ "f at right endpoint is
*at or above* 0".

This is the type-level precondition that the bisection trajectory
preserves under `signedLeftOracle f` (Layer 2 result below). -/
structure BracketSignChange
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (db : DyadicBracket) : Prop where
  signLeft : f db.leftCut 0 1 = false
  signRight : f db.rightCut 0 1 = true

/-- Helper: under `LocallyDeterminedData f`, two pointwise-equal cuts
    yield the same f-value at any single precision query.  This is
    the "no funext required" form of cut-equality preservation. -/
theorem ldd_pointwise_eq_at
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (lf : LocallyDeterminedData f) (cx cy : Nat → Nat → Bool)
    (heq : ∀ m' k', cx m' k' = cy m' k') (m k : Nat) :
    f cx m k = f cy m k :=
  lf.prop m k cx cy (fun m' k' _ _ => heq m' k')

/-- **bisectStep preserves sign change under `signedLeftOracle`**.

Given `BracketSignChange f db` (sign change at unit precision over
[a, b]) and `LocallyDeterminedData f`, one bisection step under the
always-prefer-left signed oracle preserves the sign change on the
sub-bracket.

Proof: case-split on `f db.midCut 0 1`.
  * `true` → bracket = leftHalf; new rightCut = midCut (definitional)
    so signRight from `hmid`; new leftCut = `dyadicCut (2*numA) (E+1)`
    pointwise-equals db.leftCut by `dyadicCut_double_eq`, so signLeft
    follows from old signLeft via `LocallyDeterminedData`.
  * `false` → bracket = rightHalf; symmetric. -/
theorem bisectStep_signed_left_preserves_sign_change
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (lf : LocallyDeterminedData f) (db : DyadicBracket)
    (sc : BracketSignChange f db) :
    BracketSignChange f (db.bisectStep (signedLeftOracle f)) := by
  show BracketSignChange f (bif f db.midCut 0 1 then db.leftHalf else db.rightHalf)
  cases hmid : f db.midCut 0 1 with
  | false =>
    show BracketSignChange f db.rightHalf
    refine ⟨?_, ?_⟩
    · show f db.midCut 0 1 = false
      exact hmid
    · show f (dyadicCut (2 * db.numB) (db.expE + 1)) 0 1 = true
      have heq : ∀ m' k',
          dyadicCut (2 * db.numB) (db.expE + 1) m' k' = db.rightCut m' k' :=
        fun m' k' => dyadicCut_double_eq db.numB db.expE m' k'
      rw [ldd_pointwise_eq_at lf _ db.rightCut heq 0 1]
      exact sc.signRight
  | true =>
    show BracketSignChange f db.leftHalf
    refine ⟨?_, ?_⟩
    · show f (dyadicCut (2 * db.numA) (db.expE + 1)) 0 1 = false
      have heq : ∀ m' k',
          dyadicCut (2 * db.numA) (db.expE + 1) m' k' = db.leftCut m' k' :=
        fun m' k' => dyadicCut_double_eq db.numA db.expE m' k'
      rw [ldd_pointwise_eq_at lf _ db.leftCut heq 0 1]
      exact sc.signLeft
    · show f db.midCut 0 1 = true
      exact hmid

/-- **bisectN preserves sign change under `signedLeftOracle`**.

By structural induction on n: every depth of the trajectory under
the always-prefer-left signed oracle keeps the sign change at unit
precision over its current sub-bracket.

This is the invariant that, combined with `dyadic_bracket_cauchy_modulus`
(quantitative bracket halving), will close the `consistency` field
of `monotonicConsistentOracle` in Layer 3. -/
theorem bisectN_signed_left_preserves_sign_change
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (lf : LocallyDeterminedData f) :
    ∀ n db, BracketSignChange f db →
      BracketSignChange f (DyadicBracket.bisectN (signedLeftOracle f) n db)
  | 0, _, sc => sc
  | n+1, db, sc => by
    show BracketSignChange f
      (DyadicBracket.bisectN (signedLeftOracle f) n
        (db.bisectStep (signedLeftOracle f)))
    exact bisectN_signed_left_preserves_sign_change lf n
            (db.bisectStep (signedLeftOracle f))
            (bisectStep_signed_left_preserves_sign_change lf db sc)

/-! ### Dual policy lens: `BracketSignChangeUp` for `f` increasing

The opposite sign convention: `f leftCut 0 1 = true` and
`f rightCut 0 1 = false` (f *increasing* with `f(a) ≤ 0 ≤ f(b)`).
Pairs with `signedRightOracle` from `MinimalRootLens.lean`.

This is the **policy-lens enumeration insight**: the choice of
oracle (signedLeft vs signedRight) is itself a finite-cardinality
lens; together they cover the two boundary preferences within
the d=5 finite-policy ladder. -/

open E213.Lib.Math.Analysis.DyadicSearch.MinimalRootLens (signedRightOracle)

/-- **BracketSignChangeUp**: dual precondition for the `signedRightOracle`
    policy.  `f leftCut 0 1 = true` (f at left ≤ 0) and
    `f rightCut 0 1 = false` (f at right > 0).  This matches the
    standard IVT sign convention (f increasing). -/
structure BracketSignChangeUp
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (db : DyadicBracket) : Prop where
  signLeft : f db.leftCut 0 1 = true
  signRight : f db.rightCut 0 1 = false

/-- **One-step preservation under `signedRightOracle`**.  Same
    structural pattern as the `signedLeftOracle` case (Layer 2),
    via `dyadicCut_double_eq` + `LocallyDeterminedData`. -/
theorem bisectStep_signed_right_preserves_sign_change_up
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (lf : LocallyDeterminedData f) (db : DyadicBracket)
    (sc : BracketSignChangeUp f db) :
    BracketSignChangeUp f (db.bisectStep (signedRightOracle f)) := by
  show BracketSignChangeUp f
    (bif !(f db.midCut 0 1) then db.leftHalf else db.rightHalf)
  cases hmid : f db.midCut 0 1 with
  | false =>
    show BracketSignChangeUp f db.leftHalf
    refine ⟨?_, ?_⟩
    · show f (dyadicCut (2 * db.numA) (db.expE + 1)) 0 1 = true
      have heq : ∀ m' k',
          dyadicCut (2 * db.numA) (db.expE + 1) m' k' = db.leftCut m' k' :=
        fun m' k' => dyadicCut_double_eq db.numA db.expE m' k'
      rw [ldd_pointwise_eq_at lf _ db.leftCut heq 0 1]
      exact sc.signLeft
    · show f db.midCut 0 1 = false
      exact hmid
  | true =>
    show BracketSignChangeUp f db.rightHalf
    refine ⟨?_, ?_⟩
    · show f db.midCut 0 1 = true
      exact hmid
    · show f (dyadicCut (2 * db.numB) (db.expE + 1)) 0 1 = false
      have heq : ∀ m' k',
          dyadicCut (2 * db.numB) (db.expE + 1) m' k' = db.rightCut m' k' :=
        fun m' k' => dyadicCut_double_eq db.numB db.expE m' k'
      rw [ldd_pointwise_eq_at lf _ db.rightCut heq 0 1]
      exact sc.signRight

/-- **n-step preservation** for `BracketSignChangeUp`.  Structural
    induction on n. -/
theorem bisectN_signed_right_preserves_sign_change_up
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (lf : LocallyDeterminedData f) :
    ∀ n db, BracketSignChangeUp f db →
      BracketSignChangeUp f
        (DyadicBracket.bisectN (signedRightOracle f) n db)
  | 0, _, sc => sc
  | n+1, db, sc => by
    show BracketSignChangeUp f
      (DyadicBracket.bisectN (signedRightOracle f) n
        (db.bisectStep (signedRightOracle f)))
    exact bisectN_signed_right_preserves_sign_change_up lf n
            (db.bisectStep (signedRightOracle f))
            (bisectStep_signed_right_preserves_sign_change_up lf db sc)

/-! ### Resolution-residue → cutEq bridge (Layer 3b core)

The 213-native form of "f(c) = 0".  In the cut algebra, the
proposition `cutEq x (constCut 0 1)` reduces to "x is true at every
(m, k)".  For a `RatioCut` x (cuts respecting cross-multiplied
rational ordering — including all `dyadicCut`s), it suffices to
verify x's value at the single unit-precision query (0, 1).

This is the Layer 3b structural translation: the user's
"부호 변화 불변량을 cutEq라는 렌즈의 언어로 번역" — the unit-precision
sign change `f rightCut 0 1 = true`, when paired with `RatioCut`
on the f-image, is *automatically* a global cutEq with the zero cut. -/

open E213.Lib.Math.Real213.Core.Core.ValidCut (RatioCut)
open E213.Lib.Math.Real213.Core.Core.CutPoset (cutEq)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)

/-- **constCut 0 1 is the always-true cut**: at every query `(m, k)`,
    `constCut 0 1 m k = true`.  Pure decide-reduction. -/
theorem constCut_zero_one_true (m k : Nat) :
    constCut 0 1 m k = true := by
  show decide (0 * k ≤ 1 * m) = true
  apply decide_eq_true
  rw [Nat.zero_mul]
  exact Nat.zero_le _

/-- **★ The Layer 3b bridge**: a `RatioCut` that is true at the
    unit-precision query `(0, 1)` is *globally* the zero cut.

Proof: `RatioCut`'s `ratioMono` lifts the unit query to any (m, k)
since `0 / 1 ≤ m / k` always (cross-multiplied: `0 * k ≤ m * 1`,
which is `0 ≤ m`).  This is the structural equivalent of "value ≤ 0
at unit precision implies value ≤ m/k at every precision" —
because in 213 the cut for value 0 *is* the always-true cut. -/
theorem cutEq_zero_of_ratioCut_at_unit
    (x : Nat → Nat → Bool) (hr : RatioCut x) (hu : x 0 1 = true) :
    cutEq x (constCut 0 1) := by
  intro m k
  rw [constCut_zero_one_true]
  -- ratioMono: 0/1 ≤ m/k via 0*k ≤ m*1 = m
  exact hr.ratioMono 0 1 m k (by decide)
    (by rw [Nat.zero_mul, Nat.mul_one]; exact Nat.zero_le _) hu

open E213.Lib.Math.Analysis.DyadicSearch.MinimalRootLens
  (signedLeftOracle MinimalRootCut)
open E213.Lib.Math.Analysis.DyadicSearch.ConsistentOracle (ConsistentOracle)
open E213.Lib.Math.Analysis.DyadicSearch.IVT (IVTHypothesis IVTRoot)

/-- **★ Layer 3b closure** — the IVTRoot certificate from the
    minimum 213-native data:

  1. `lf : LocallyDeterminedData f` — the f's modulus.
  2. `co : ConsistentOracle db` — the typed protocol witness.
  3. `h_ratio : RatioCut (f (MinimalRootCut co))` — f-image inherits
     the structural cut-coherence (would discharge for any
     RatioCut-preserving f, e.g., polynomials).
  4. `h_zero_unit : f (MinimalRootCut co) 0 1 = true` — the
     unit-precision sign witness at the limit; future Layer 3c
     work derives this from `BracketSignChange` + LDD-stability
     at unit precision.

The four pieces *exactly* match the four 213 axes — modulus,
trajectory, structural coherence, finite-resolution residue.  No
additional hypothesis enters.  The `lower` and `upper` bounds come
free from `MinimalRootCut_{lower,upper}`; `zero` comes from the
`cutEq_zero_of_ratioCut_at_unit` bridge.

This is the structural equivalent of Bishop locatedness made
explicit: each piece is a typed datum the user supplies, not an
external classical assumption. -/
def IVTRoot.fromConsistentOracleRatio
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (lf : LocallyDeterminedData f) {db : DyadicBracket}
    (co : ConsistentOracle db)
    (h_ratio : RatioCut (f (MinimalRootCut co)))
    (h_zero_unit : f (MinimalRootCut co) 0 1 = true) :
    IVTRoot { f := f, isLDD := lf,
              a := db.leftCut, b := db.rightCut } :=
  E213.Lib.Math.Analysis.DyadicSearch.MinimalRootLens.IVTRoot.fromConsistentOracle
    lf co (cutEq_zero_of_ratioCut_at_unit _ h_ratio h_zero_unit)

end E213.Lib.Math.Analysis.DyadicSearch.MinimalRootLensMonotone
