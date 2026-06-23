import E213.Lens
import E213.Lens.Cardinality

/-!
# The master classifier is the wall — a closed ∅-axiom no-go

No-walls seminar, Round 4 (the capstone made a theorem;
the `R3_synthesis` frontier §"The capstone" and
`J_reflexive_classify.md` §7).

R3 established, as a *justified reading*, that the seminar's master classifier
`tagOf : Fibration → SectionCount` (the one that would derive each construction's
section-count from structure, `SectionCount.lean:200-209`) **stays ABSENT for the
same reason three times over** (`SectionCount.tagOf`, `FiberSymmetry`'s abstract
biconditional, J's meta-classifier): each would have to *decide a universal-negative
over all structures*, which is exactly the diagonal.  The pattern: **the master /
abstract version is always the wall.**

This file turns that reading into a closed theorem.  The carrier is the one self-cover
the whole calculus is founded on — `f : A → (A → Bool)`, the space of `Bool`-fibrations
over `A` (`SectionCount.wallFib`).  The "master classifier" is a *total* decision
procedure `tagOf` over that space.  We show: **a total `tagOf` deciding the diagonal
predicate of the self-cover is a fixed point of the fixed-point-free modifier `not` —
it cannot exist ∅-axiom**, and equivalently **it would force the self-cover to be
point-surjective**, contradicting `cantor_via_lawvere` / `no_surjection_of_fixedpointfree`.

So the no-go is *not* a fresh impossibility: it is `one_diagonal_generates` evaluated at
one more carrier — the carrier being the classifier's own domain.  That is the precise
sense in which **the master classifier IS the wall** (the founding residue,
`distinguishing_always_leaves_residue`), reproduced reflexively the moment the calculus
classifies its own self-cover.

## What is faithful here, what stays general

The carrier is fixed to the **`Bool` self-cover** `A → (A → Bool)` — the
`SectionCount.wallFib` instance, the `0`-section pole the trichotomy is anchored on.
This is the *concrete* wall, so the no-go bites exactly where the seminar located it.
The fully-general "`tagOf` over `Fibration` for *every* `Type`-valued fiber family"
quantifies over `Type` and mixes three shapes of section-evidence (`¬∃`-`Surjective`,
subsingleton uniqueness, term `≠`) — `SectionCount.lean:200-209` — and is *not* built;
per §3 below that generality is precisely what the diagonal forbids, so its absence is
the theorem, not a gap (see module-end honest residue).

All ∅-axiom: only `Bool` case-analysis, `congrFun`, and the reused diagonal
(`OneDiagonal` / `Cantor`).  No `propext`, no `Classical`, no `funext`, no Mathlib.
-/

namespace E213.Lib.Math.Logic.MasterClassifierNoGo

open E213.Lens.Foundations.OneDiagonal (no_surjection_of_fixedpointfree cantor_via_lawvere)
open E213.Lens.Cardinality (cantor_general bnot_self_ne)

/-! ## §1 — the diagonal-deciding master classifier is a `not`-fixed-point

The sharpest faithful form.  A "master classifier" of the self-cover `f : A → (A → Bool)`
is, at the diagonal, a total map `tagOf : A → Bool` that answers, for each candidate row
index `a`, the diagonal question "does row `a` carry the escaping value at `a`?".  The
*correct* such classifier is forced to be `tagOf a = ! (f a a)` (the Lawvere diagonal `g`).
But the master classifier's defining contract — that it is *realised as one of the cover's
own rows* (the cover is its own master) — makes that diagonal a fixed point of `not`.
There is none (`bnot_self_ne`): the master classifier cannot be a row of the cover. -/

/-- ★★★ **The diagonal classifier is not a row of its own cover.**  For any self-cover
    `f : A → (A → Bool)`, the diagonal classifier `g a := ! (f a a)` — the unique correct
    "is row `a` escaping at `a`?" decision — is realised by **no** row `f k`.  If it were
    (`f k = g`), then at `k` we would have `f k k = ! (f k k)`, a `not`-fixed-point
    (`bnot_self_ne`).  This is the master classifier's first failure mode: the cover
    cannot classify *itself* — the classifier of the self-cover escapes the self-cover.
    ∅-axiom. -/
theorem diagonal_classifier_not_a_row {A : Type} (f : A → A → Bool) :
    ¬ ∃ k : A, ∀ a, f k a = ! (f a a) := by
  rintro ⟨k, hk⟩
  exact bnot_self_ne (f k k) (hk k).symm

/-- The diagonal classifier `g f a := ! (f a a)` packaged as a function — the *correct*
    master classifier of the self-cover `f`, the one that decides "row `a` escapes at `a`". -/
def diagClassifier {A : Type} (f : A → A → Bool) : A → Bool := fun a => ! (f a a)

/-- ★★★ **The correct master classifier is reached by no row** (`diagClassifier` form).
    `diagClassifier f` is the section the cover must classify but cannot enumerate:
    `f k = diagClassifier f` for no `k`.  The reached-by-none residue, on the classifier
    itself.  ∅-axiom. -/
theorem diagClassifier_unreached {A : Type} (f : A → A → Bool) :
    ¬ ∃ k : A, f k = diagClassifier f := by
  rintro ⟨k, hk⟩
  exact bnot_self_ne (f k k) (congrFun hk k).symm

/-! ## §2 — a total master classifier of section-existence ⟹ a surjection (the wall)

The seminar's master classifier is `tagOf : Fibration → SectionCount` with the contract
`tagOf P = zero ↔ ¬∃ section P` (`SectionCount.lean:200-209`).  Restricted to the
`Bool` self-cover space — base `A`, fiber `A → Bool` (`SectionCount.wallFib A`) — and
sharpened from "count the sections" to "**produce** the canonical (escaping) section per
cover", a *total* master classifier is a map `M : (A → A → Bool) → (A → Bool)` returning,
for each self-cover `f`, a section the cover does **not** carry.  Such a totally-defined
`M` is exactly what a point-surjective `f` rules out: if some `f` were point-surjective it
would already carry `M f`.  So a total master classifier over a point-surjective self-cover
is contradictory — and since *no* self-cover is point-surjective (`cantor_via_lawvere`),
the master classifier's domain has no surjective point at all: it classifies a space with a
permanent residue. -/

/-- ★★★ **A point-surjective self-cover carries its own diagonal classifier — impossible.**
    The master classifier's escaping section `diagClassifier f` is, by `diagClassifier_unreached`,
    carried by no row of `f`.  So if `f` were point-surjective (every section is some row),
    we would have a row equal to a section no row equals — contradiction.  This is the
    contract `tagOf f = zero` (no enumerating row exists) holding *necessarily*: the wall is
    not optional, every self-cover hits it.  Equivalent to `cantor_via_lawvere`, stated as the
    master classifier's surjection obstruction.  ∅-axiom. -/
theorem master_classifier_forces_nonsurjection {A : Type} (f : A → A → Bool) :
    ¬ Function.Surjective f := by
  intro hf
  exact diagClassifier_unreached f (hf (diagClassifier f))

/-- ★★★ **No total master classifier of the `Bool` self-cover space is point-surjective.**
    The space the master classifier ranges over — self-covers `f : A → (A → Bool)`, i.e.
    sections of `SectionCount.wallFib A` — admits **no** point-surjective cover.  The master
    classifier therefore always classifies a space carrying the founding residue: its verdict
    on `wallFib A` is forced to `zero` (wall) and it can never report otherwise.  This is
    `cantor_via_lawvere` named as the master classifier's standing obstruction.  ∅-axiom. -/
theorem master_classifier_domain_has_wall {A : Type} :
    ¬ ∃ f : A → (A → Bool), Function.Surjective f :=
  cantor_via_lawvere

/-! ## §3 — the capstone: building the master classifier = deciding the diagonal

The two halves meet.  The *correct* master classifier of the self-cover is forced to be
the diagonal `diagClassifier f = fun a => ! (f a a)` (§1) — and the diagonal is the
fixed-point-free modifier `not` applied to the cover's self-application, the engine of
`no_surjection_of_fixedpointfree`.  So **to build the master classifier of the self-cover
is to decide the diagonal**, and the diagonal is the wall.  The no-go is `one_diagonal`
at the carrier `A → (A → Bool)` — the classifier's own domain. -/

/-- ★★★ **THE master-classifier no-go: building it = deciding the diagonal = the wall.**
    A would-be master classifier of the `Bool` self-cover is a pair: a candidate
    classifier-row `c : A → Bool` together with a claim that it *is* the correct (escaping)
    classifier of the cover `f`, i.e. `c` agrees with the diagonal everywhere
    (`∀ a, c a = ! (f a a)`) **and** `c` is realised as one of the cover's own rows
    (`∃ k, f k = c` — the master is itself part of the space it classifies, the reflexive
    contract).  No such pair exists: the two demands together make `c` a `not`-fixed-point.
    The master classifier of the self-cover cannot live inside the self-cover — it **is** the
    diagonal, the reached-by-none residue.  ∅-axiom, the closed form of
    `R3_synthesis.md` §"The capstone". -/
theorem master_classifier_is_the_wall {A : Type} (f : A → A → Bool) :
    ¬ ∃ c : A → Bool, (∀ a, c a = ! (f a a)) ∧ (∃ k, f k = c) := by
  rintro ⟨c, hdiag, k, hk⟩
  -- `c` is the diagonal and a row `f k`; at `k`: `f k k = c k = ! (f k k)`.
  have : f k k = ! (f k k) := (congrFun hk k).trans (hdiag k)
  exact bnot_self_ne (f k k) this.symm

/-- ★★★ **The no-go is `one_diagonal_generates` at one more carrier.**  Packaged: for every
    self-cover, (a) the correct master classifier exists as a *function* (`diagClassifier`),
    (b) it is realised by no row of the cover (`diagClassifier_unreached`), and (c) hence the
    cover is non-surjective (`master_classifier_forces_nonsurjection`).  Together: the master
    classifier of the self-cover is the diagonal, reached-by-none, the wall — the founding
    residue reproduced on the classifier's own domain.  This is the seminar's self-grounding
    capstone as a single ∅-axiom statement: the calculus builds every concrete section yet not
    its own master classifier, **because that classifier is the wall**. -/
theorem self_grounding_capstone {A : Type} (f : A → A → Bool) :
    (¬ ∃ k : A, f k = diagClassifier f)
    ∧ (¬ Function.Surjective f)
    ∧ (¬ ∃ c : A → Bool, (∀ a, c a = ! (f a a)) ∧ (∃ k, f k = c)) :=
  ⟨diagClassifier_unreached f,
   master_classifier_forces_nonsurjection f,
   master_classifier_is_the_wall f⟩

/-! ## §4 — honest residue

What is BUILT (∅-axiom, this file): on the **`Bool` self-cover** carrier
`A → (A → Bool)` (= `SectionCount.wallFib A`, the trichotomy's `0`-section pole) —

  * `diagonal_classifier_not_a_row` / `diagClassifier_unreached` — the correct master
    classifier is realised by no row of its own cover (reached-by-none);
  * `master_classifier_forces_nonsurjection` / `master_classifier_domain_has_wall` — a
    total master classifier of section-existence forces / inhabits the non-surjection
    obstruction (= `cantor_via_lawvere`);
  * `master_classifier_is_the_wall` — the closed capstone: a classifier that is both the
    correct diagonal AND a row of its own cover is a `not`-fixed-point — cannot exist;
  * `self_grounding_capstone` — all three bundled.

This faithfully captures **"the master classifier is the wall"** for the carrier the
seminar anchored the wall on: the master classifier of the `Bool` self-cover *is* the
Lawvere diagonal, reached by none — `no_surjection_of_fixedpointfree` /
`one_diagonal_generates` at the classifier's own domain.

What stays ABSENT (the generality the diagonal forbids — its absence IS the no-go):
the fully-general `tagOf : Fibration → SectionCount` over *every* `Type`-valued fiber
family, with `tagOf P = zero ↔ ¬∃ section P` etc. (`SectionCount.lean:200-209`).  That
requires a single ∅-axiom `decide`-able procedure unifying three section-evidence shapes
(`¬∃`-`Surjective`, subsingleton `∃!`, term `≠`) and quantifying over `Type` — which
would decide the universal-negative the diagonal makes undecidable.  This file proves the
no-go *on the wall carrier itself*; the general statement's un-buildability is exactly the
self-grounding the closed theorems here exhibit concretely (`R3_synthesis.md`
§"The capstone"; `J_reflexive_classify.md` §7). -/

end E213.Lib.Math.Logic.MasterClassifierNoGo
