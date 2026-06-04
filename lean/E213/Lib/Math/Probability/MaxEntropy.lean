import E213.Lib.Math.Foundations.CeilingSchema
import E213.Lib.Math.Analysis.Cauchy.GoldenPiFaces

/-!
# Maximum entropy as a positive intrinsic property

The ceiling has been written *negatively* throughout: a witness escapes the finite-difference ring
(`¬ ∃ d, polyDepthZ d s`), the residue is outside every view's image (`¬ Function.Surjective`).  That
negative bookkeeping reads structurelessness as a *privation* — "no handle".  This module flips it to
the **positive** reading the residue actually carries (`seed/AXIOM/05_no_exterior.md` §5): being outside every enclosure is not poverty but **maximal lack of
constraint** — *source-without-enclosure*.  Named in information terms, that is **maximum entropy**.

So the structurelessness of the non-holonomic pole is not a hole to leave blank; it is a *property*,
and a positive one:

> `MaxEntropy s := ¬ ∃ d, polyDepthZ d s`  — no finite holonomic certificate generates `s`.

Two cautions are built into the form, not added on top.

* **The reading of "entropy" is forced.**  Classical entropy needs a *measure* (Gauss–Kuzmin is a
  measure on continued-fraction digits); deploying it would smuggle an exterior ruler (the
  `External-ruler smuggling` failure mode — no exterior exists, §5.1).  The only 213-native reading is
  the *incompressibility* (algorithmic) one: maximal entropy = compressed by no finite handle.  That
  is **measure-free** — it quantifies over generators, not over a probability space.

* **The class of generators is the finite-handle class, not "all generators".**  Naively "escapes
  every generator" is false (the constant generator `g ≡ s` reaches `s`).  The honest quantifier is
  over the **finite holonomic** class — finite difference-depth, equivalently the Newton-polynomial
  generators (`DepthCharacterization.finite_depthZ_iff`).  `MaxEntropy s` is exactly: no Newton stage
  reaches `s`, i.e. the universal Newton generator **misses** `s` — the ceiling's own non-surjectivity
  (`CeilingSchema.ceilings_are_nonsurjectivity`), now stated as a property of `s` rather than of a
  tactic.

The witnesses already proven `¬ ∃ d, polyDepthZ d` are thereby collected under one positive
predicate: the dense automatic counter (`s2Z`, popcount / Thue–Morse) and the `det = −1` sign face
(the golden/Fibonacci Cassini sequence) are both **maximum-entropy** distinguishings, and each one on
its own forces the universal finite-handle generator to be non-surjective.  This is not stipulated:
the residue's genericity is the *theorem* `object1_not_surjective`; a `MaxEntropy` sequence is a
constructive realizer of that one non-surjection.
-/

namespace E213.Lib.Math.Probability.MaxEntropy

open E213.Lib.Math.Analysis.Cauchy.NewtonGregory (polyDepthZ newtonZ)
open E213.Lib.Math.Analysis.Cauchy.DepthCharacterization (finite_depthZ_iff)
open E213.Lib.Math.Foundations.CeilingSchema (ReachedByNoStage not_surjective_of_reachedByNoStage)
open E213.Lib.Math.Analysis.Cauchy.ThueMorseRingEscape (s2Z s2Z_not_polyDepthZ)
open E213.Lib.Math.Analysis.Cauchy.DetZeroCollapse (cas)
open E213.Lib.Math.Analysis.Cauchy.GoldenPiFaces (golden_cassini_no_finite_depth)

/-- A sequence carries a **finite holonomic handle** when it has some finite difference-depth —
    equivalently (`finite_depthZ_iff`) it equals a Newton polynomial `newtonZ c d`.  This is the
    finite-compression / generating-ring membership. -/
def FiniteHandle (s : Nat → Int) : Prop := ∃ d, polyDepthZ d s

/-- ★★ **Maximum entropy = no finite handle.**  The positive intrinsic property of
    structurelessness: no finite holonomic certificate generates `s`.  The *incompressibility*
    (algorithmic) reading of maximal entropy — measure-free, so no exterior ruler is imported. -/
def MaxEntropy (s : Nat → Int) : Prop := ¬ FiniteHandle s

/-- The universal finite-handle generator: a degree/coefficient pair `(d, c)` to its Newton
    polynomial.  Its range is exactly the finite-handle class (`finite_depthZ_iff`). -/
def newtonGen (dc : Nat × (Nat → Int)) : Nat → Int := fun n => newtonZ dc.2 dc.1 n

/-! ## Maximum entropy is the ceiling's non-surjectivity, read on the sequence -/

/-- ★★★ **A max-entropy sequence is reached by no Newton stage.**  If `s` has no finite handle then
    the universal Newton generator misses it: `∀ (d, c), newtonGen (d, c) ≠ s`.  (Forward direction
    only — it needs `congrFun`, never `funext`, so it stays ∅-axiom.) -/
theorem maxEntropy_reachedByNoStage (s : Nat → Int) (h : MaxEntropy s) :
    ReachedByNoStage newtonGen s := by
  intro dc heq
  exact h ⟨dc.1, finite_depthZ_iff.mpr ⟨dc.2, fun n => (congrFun heq n).symm⟩⟩

/-- ★★★★ **Maximum entropy ⟹ the universal finite-handle generator is non-surjective.**  Each
    max-entropy distinguishing is a *constructive realizer* of the ceiling
    (`CeilingSchema.ceilings_are_nonsurjectivity`): it pins one point the finite-handle generator
    cannot reach.  Structurelessness, stated positively, *is* the non-surjection — read as a property
    of the sequence, not of a proof tactic. -/
theorem maxEntropy_not_surjective (s : Nat → Int) (h : MaxEntropy s) :
    ¬ Function.Surjective newtonGen :=
  not_surjective_of_reachedByNoStage (maxEntropy_reachedByNoStage s h)

/-! ## The proven escapes, collected under the one positive predicate -/

/-- **The dense automatic counter is maximum-entropy.**  The popcount / Thue–Morse counter `s2Z`
    (unbounded yet returning to its minimum at every power of two) carries no finite handle. -/
theorem thueMorse_maxEntropy : MaxEntropy s2Z := s2Z_not_polyDepthZ

/-- **The `det = −1` sign face is maximum-entropy.**  Any golden/Fibonacci orbit's Cassini sequence
    `cas s` (the period-2 sign-unit `(−1)^{n+1}`, with nonzero initial Cassini) carries no finite
    handle — the additively-maximal unit face is a maximum-entropy distinguishing. -/
theorem golden_cassini_maxEntropy (s : Nat → Int) (hrec : ∀ n, s (n + 2) = s (n + 1) + s n)
    (h0 : cas s 0 ≠ 0) : MaxEntropy (cas s) :=
  golden_cassini_no_finite_depth s hrec h0

/-- ★★★★ **Two faces, one positive property.**  The dense face (automatic counter) and the
    `det = −1` sign face (golden Cassini) are both maximum-entropy distinguishings, and each on its
    own forces the universal finite-handle generator to be non-surjective.  The non-holonomic pole is
    not a blank left open: it is the *presence* of maximal genericity — source-without-enclosure named
    in information terms. -/
theorem maxEntropy_two_faces (s : Nat → Int) (hrec : ∀ n, s (n + 2) = s (n + 1) + s n)
    (h0 : cas s 0 ≠ 0) :
    (MaxEntropy s2Z ∧ ¬ Function.Surjective newtonGen)
    ∧ (MaxEntropy (cas s) ∧ ¬ Function.Surjective newtonGen) :=
  ⟨⟨thueMorse_maxEntropy, maxEntropy_not_surjective s2Z thueMorse_maxEntropy⟩,
   ⟨golden_cassini_maxEntropy s hrec h0,
    maxEntropy_not_surjective (cas s) (golden_cassini_maxEntropy s hrec h0)⟩⟩

end E213.Lib.Math.Probability.MaxEntropy
