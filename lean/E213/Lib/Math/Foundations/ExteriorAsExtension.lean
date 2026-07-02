import E213.Lib.Math.Foundations.CeilingSchema
import E213.Lib.Math.Logic.MasterClassifierNoGo
import E213.Lens

/-!
# The exterior as extension — the capture theorem and the invariant core

The exterior-as-extension conjecture (frontier
`research-notes/frontiers/exterior_as_extension.md`, active scratch) reads
"no exterior" dynamically: **the exterior-role is always played by the residue-driven
extension** — what escapes stage `n` is inside stage `n+1`.  Its examination found the
conjecture true of one tower shape and provably false of another, forcing the amendment

> apparent exterior = (extension-capturable component) ⊕ (the invariant core).

This file pins both halves ∅-axiom (targets E2 + E3 of the frontier note, and the
decomposition capstone):

  * **E2, the progressing tower** (§1): the extension operator `extend` prepends the
    escapee `diag f` to the enumeration.  Yesterday's exterior is *literally* today's
    interior (`extend_captures`), every old level persists (`extend_preserves`), and the
    extended enumeration has a *fresh* escapee (`extend_still_escapes`).  Iterated
    (`tower`): at every stage the current diagonal escapes, is captured one stage up, and
    is replaced (`yesterday_exterior_today_interior`) — the Gödel/`Con(T)` ascent shape,
    ∅-axiom, in the framework's own diagonal vocabulary.
  * **E3, the invariant core** (§2): the undifferentiated predicate `fun _ => true` — the
    residue's cleanest member — is outside `Object1`'s image *entirely*
    (`undifferentiated_outside_every_image`), hence uncaptured by the re-entry composite
    at **every** depth `n` (`undifferentiated_uncaptured`): deepening the encoding
    extends the system and captures nothing of this witness.  Here the exterior-role is
    played by an invariant, not by the next stage.
  * **The decomposition capstone** (§3): both halves in one statement
    (`exterior_decomposition`) — the amendment as a theorem, not prose.

The two shapes are the two non-oscillating fates of `SelfReferenceThreeOutcomes` read at
the tower scale: the progressing tower is the converge-flavoured face (each gap is
absorbed one stage up), the fixed core is the escape face (the same witness re-appears at
every stage).  Neither is "the" exterior: the frozen reading (`object1_not_surjective`)
and this dynamic reading are co-present per `seed/AXIOM/05_no_exterior.md` §5.7.

All zero-axiom.
-/

namespace E213.Lib.Math.Foundations.ExteriorAsExtension

open E213.Theory (Raw)
open E213.Lens.Foundations.FlatOntology (Object1)
open E213.Lens.Foundations.PredicateSelfEncoding (predicateToRaw)
open E213.Lens.Foundations.ResidueReentry (multipoint_not_object1)
open E213.Lib.Math.Analysis.Cauchy.DepthCeilingResidue (diag diag_not_in_seq)
open E213.Lib.Math.Foundations.CeilingSchema (ReachedByNoStage)

/-! ## §1 — E2: the progressing tower (yesterday's exterior is today's interior)

The ceiling schema (`CeilingSchema`) states what a wall *is*: a target reached by no
stage of a finite-stage enumeration.  The extension move states what a wall *does*: the
named escapee, reified as a new stage, extends the enumeration — and the extension both
captures it and grows a fresh escapee.  `extend` is that move for the archetypal
enumeration `f : Nat → (Nat → Nat)` and its diagonal escapee `diag f`. -/

/-- **The extension operator.**  Prepend the escapee `diag f` to the enumeration: stage
    `0` of `extend f` is yesterday's exterior, stage `i+1` is yesterday's stage `i`.
    The residue-witness, reified as an operand — the extension move as an object. -/
def extend (f : Nat → Nat → Nat) : Nat → Nat → Nat
  | 0 => diag f
  | i + 1 => f i

/-- ★★ **Yesterday's exterior is today's interior.**  The diagonal escapee of `f` —
    reached by no stage of `f` (`diag_not_in_seq`) — is stage `0` of the extension.
    Capture is definitional: the extension *is* the reification of the escapee. -/
theorem extend_captures (f : Nat → Nat → Nat) : ∃ i, extend f i = diag f :=
  ⟨0, rfl⟩

/-- **Extension preserves the interior.**  Every old level persists, one index up:
    the extension loses nothing it had already reached. -/
theorem extend_preserves (f : Nat → Nat → Nat) (i : Nat) : extend f (i + 1) = f i :=
  rfl

/-- ★★ **The extension has a fresh exterior.**  The extended enumeration's own diagonal
    `diag (extend f)` is reached by no stage of `extend f`: capturing yesterday's
    escapee produces today's.  The cover never closes — one extension step at a time. -/
theorem extend_still_escapes (f : Nat → Nat → Nat) :
    ReachedByNoStage (extend f) (diag (extend f)) :=
  fun i h => diag_not_in_seq (extend f) i h.symm

/-- ★★★ **The extension step, bundled.**  One step of the residue-driven extension:
    the escapee of `f` is captured (`extend_captures`), the interior is preserved
    (`extend_preserves`), and a fresh escapee exists (`extend_still_escapes`).  This is
    the exterior-as-extension conjecture's positive half in its minimal form: the
    exterior-role of `diag f` is discharged by the extension and immediately re-occupied
    by `diag (extend f)`. -/
theorem extension_step (f : Nat → Nat → Nat) :
    (∃ i, extend f i = diag f)
    ∧ (∀ i, extend f (i + 1) = f i)
    ∧ ReachedByNoStage (extend f) (diag (extend f)) :=
  ⟨extend_captures f, extend_preserves f, extend_still_escapes f⟩

/-- **The extension tower.**  Iterate the extension move: stage `0` is the given
    enumeration, stage `k+1` reifies stage `k`'s escapee.  The Gödel/`Con(T)` ascent
    shape — each system extended by exactly what escaped it. -/
def tower (f : Nat → Nat → Nat) : Nat → Nat → Nat → Nat
  | 0 => f
  | k + 1 => extend (tower f k)

/-- ★★★ **The progressing tower: every stage's exterior is the next stage's interior,
    and every stage has one.**  Uniformly in the height `k`:

    1. the stage-`k` diagonal escapes stage `k` (today's exterior);
    2. it is stage `0` of stage `k+1` (captured — yesterday's exterior is today's
       interior, literally);
    3. stage `k+1` has a fresh diagonal escaping it (the exterior-role is re-occupied).

    The exterior-as-extension conjecture, exact on this tower shape: the exterior is
    never a place, always the next extension — and the ascent never terminates.
    ∅-axiom. -/
theorem yesterday_exterior_today_interior (f : Nat → Nat → Nat) (k : Nat) :
    ReachedByNoStage (tower f k) (diag (tower f k))
    ∧ (∃ i, tower f (k + 1) i = diag (tower f k))
    ∧ ReachedByNoStage (tower f (k + 1)) (diag (tower f (k + 1))) :=
  ⟨fun i h => diag_not_in_seq (tower f k) i h.symm,
   ⟨0, rfl⟩,
   fun i h => diag_not_in_seq (tower f (k + 1)) i h.symm⟩

/-! ## §2 — E3: the invariant core (the witness no extension captures)

The re-entry tower (`ResidueReentry`) is the other shape.  Its stage-`n` map is the
re-pointing composite `P ↦ Object1 (predicateToRaw n P)`; deepening `n` is that tower's
extension move.  But the image of every stage lies inside `Object1`'s image — the
single-Raw indicators — so a predicate true at two distinct Raws is captured at **no**
depth.  The undifferentiated predicate `fun _ => true` (the residue's cleanest member,
`FlatOntologyClosure.residue_witnessed`) is the named such witness: for it, the
exterior-role is played by an invariant, and the conjecture's "exterior = extension"
fails — provably. -/

/-- The two atoms differ — propext-free (`Tree.noConfusion`, not `decide`). -/
private theorem a_ne_b : Raw.a ≠ Raw.b :=
  fun h => E213.Term.Internal.Tree.noConfusion (congrArg Subtype.val h)

/-- ★★ **The undifferentiated predicate is outside the whole image.**  `fun _ => true`
    is true at both atoms `a ≠ b`, and every `Object1 r` is true at exactly one Raw —
    so no `r` whatsoever has `Object1 r = fun _ => true`.  Stronger than non-fixedness
    under re-entry: the witness is outside the cover's image *entirely*, before any
    question of encoding depth. -/
theorem undifferentiated_outside_every_image :
    ∀ r : Raw, Object1 r ≠ (fun _ : Raw => true) :=
  fun r => multipoint_not_object1 (fun _ => true) Raw.a Raw.b rfl rfl a_ne_b r

/-- ★★★ **E3 — the invariant core: no re-entry depth captures the witness.**  At every
    encoding depth `n`, the undifferentiated predicate is reached by no stage of the
    re-pointing composite `P ↦ Object1 (predicateToRaw n P)`.  Deepening `n` — this
    tower's extension move — captures nothing of it: unlike §1's escapee, this witness
    is not "yesterday's exterior awaiting capture" but an invariant the extension never
    touches.  The exterior-as-extension conjecture's counterexample half, pinned.
    ∅-axiom. -/
theorem undifferentiated_uncaptured (n : Nat) :
    ReachedByNoStage
      (fun P : Raw → Bool => Object1 (predicateToRaw n P)) (fun _ : Raw => true) :=
  fun P => undifferentiated_outside_every_image (predicateToRaw n P)

/-! ## §3 — the decomposition capstone (the amendment as one theorem) -/

/-- ★★★★ **The exterior decomposes: capturable extension ⊕ invariant core.**  In one
    statement, uniformly in the tower height `k` and the re-entry depth `n`:

    * **progressing half** — on the diagonal tower, the stage-`k` escapee is captured at
      stage `k+1`, which has a fresh escapee (`yesterday_exterior_today_interior`):
      there, "exterior" *is* the residue-driven extension, exactly as conjectured;
    * **invariant half** — on the re-entry tower, the undifferentiated predicate is
      captured at **no** depth (`undifferentiated_uncaptured`): there, the
      exterior-role is played by the one wall, and no extension of this cover-shape
      discharges it.

    So "the exterior of no-exterior is residue-driven system extension" holds exactly of
    the capturable component and fails exactly on the invariant core — the dynamic face
    of the tetrachotomy (`∅/0/1/many`): extension not-yet-built / the wall / forced /
    parametrized.  Frozen and dynamic readings co-present per §5.7; neither component is
    "the" exterior.  ∅-axiom. -/
theorem exterior_decomposition (f : Nat → Nat → Nat) (k n : Nat) :
    (ReachedByNoStage (tower f k) (diag (tower f k))
      ∧ (∃ i, tower f (k + 1) i = diag (tower f k))
      ∧ ReachedByNoStage (tower f (k + 1)) (diag (tower f (k + 1))))
    ∧ ReachedByNoStage
        (fun P : Raw → Bool => Object1 (predicateToRaw n P)) (fun _ : Raw => true) :=
  ⟨yesterday_exterior_today_interior f k, undifferentiated_uncaptured n⟩

/-! ## §4 — E4 (finite shadow): no stage carries its own diagonal; the next stage does

§1 ran the extension move on `Nat`-valued enumerations.  Here it runs on **`Bool`
self-covers** `f : Nat → (Nat → Bool)` — the wall carrier of the no-walls seminar
(`MasterClassifierNoGo`), where the escapee is the **diagonal classifier**
`diagClassifier f = fun a => ! (f a a)`, the cover's own canonical coker witness.

The result is the height-axis one-way statement (`no_walls_seminar` R7's open
question, in its finite-shadow form):

  * **no stage carries its own diagonal** — at every height `k`, the stage-`k` cover's
    diagonal classifier is realised by no row of stage `k`
    (`no_stage_carries_own_diagonal`, from `diagClassifier_unreached`);
  * **the next stage carries it** — the extension reifies it as row `0` of stage `k+1`
    (`next_stage_carries_diagonal`, definitional);
  * **the wall re-occurs at every stage** — stage `k+1` has its own uncarried diagonal,
    and the master-classifier no-go holds per stage (`master_classifier_is_the_wall`
    applied at height `k`).

So the ascent is **free** (the capture is always available one stage up — nothing
blocks the extension) while self-decision is **absent at every stage** (forced, not
chosen): the height axis is one-way.  The classical resonance — a system does not
carry its own consistency-witness, the extended system does, and the extension never
terminates — is a *Reading* of this shape; what is proven here is the cover-shape
statement on `Nat → (Nat → Bool)`, with no arithmetization and no claim beyond it.

Scope note vs "decides its own coker": the *full* coker-decider (a classifier of ALL
escaped sections) is the master classifier, impossible at every stage — that is the
invariant core again, not a per-stage increment.  What ascends is the **canonical
witness** (the diagonal); what never ascends is the wall.  The Bool tower thus carries
both halves of `exterior_decomposition` on one carrier. -/

open E213.Lib.Math.Logic.MasterClassifierNoGo
  (diagClassifier diagClassifier_unreached master_classifier_is_the_wall)

/-- **The extension operator for `Bool` self-covers.**  Prepend the stage's own
    diagonal classifier — the canonical coker witness — as row `0`; every old row
    persists one index up.  The §1 `extend`, on the wall carrier. -/
def extendCover (f : Nat → Nat → Bool) : Nat → Nat → Bool
  | 0 => diagClassifier f
  | i + 1 => f i

/-- **The cover tower.**  Iterate: stage `k+1` reifies stage `k`'s diagonal
    classifier.  The §1 `tower`, on the wall carrier. -/
def coverTower (f : Nat → Nat → Bool) : Nat → Nat → Nat → Bool
  | 0 => f
  | k + 1 => extendCover (coverTower f k)

/-- ★★ **No stage carries its own diagonal.**  At every height `k`, the stage-`k`
    cover's diagonal classifier is realised by no row of stage `k` — self-decision of
    the canonical coker witness is absent at every stage, uniformly
    (`diagClassifier_unreached` at height `k`). -/
theorem no_stage_carries_own_diagonal (f : Nat → Nat → Bool) (k : Nat) :
    ¬ ∃ i, coverTower f k i = diagClassifier (coverTower f k) :=
  diagClassifier_unreached (coverTower f k)

/-- ★★ **The next stage carries it.**  Stage `k`'s diagonal classifier — uncarried by
    stage `k` — is row `0` of stage `k+1`.  The capture is definitional: the ascent is
    free; nothing blocks reifying the witness one stage up. -/
theorem next_stage_carries_diagonal (f : Nat → Nat → Bool) (k : Nat) :
    ∃ i, coverTower f (k + 1) i = diagClassifier (coverTower f k) :=
  ⟨0, rfl⟩

/-- ★★★★ **E4, finite shadow: the height axis is one-way.**  Uniformly in the height
    `k`, on the wall carrier:

    1. stage `k` does **not** carry its own diagonal classifier (self-decision forced
       absent — `no_stage_carries_own_diagonal`);
    2. stage `k+1` **does** carry it (ascent free — `next_stage_carries_diagonal`);
    3. the wall holds **at** stage `k`: no classifier is both the correct diagonal and
       a row of the stage's own cover (`master_classifier_is_the_wall`).

    Ascent free, self-decision forced absent, the wall re-occurring at every height —
    the one-way height axis (`no_walls_seminar` R7), proven in its cover-shape finite
    shadow.  The two §3 components on one carrier: the diagonal is the *capturable*
    exterior (discharged one stage up, re-occupied), the master classifier is the
    *invariant* one (impossible at every stage).  ∅-axiom. -/
theorem height_axis_one_way (f : Nat → Nat → Bool) (k : Nat) :
    (¬ ∃ i, coverTower f k i = diagClassifier (coverTower f k))
    ∧ (∃ i, coverTower f (k + 1) i = diagClassifier (coverTower f k))
    ∧ (¬ ∃ c : Nat → Bool,
        (∀ a, c a = ! (coverTower f k a a)) ∧ (∃ i, coverTower f k i = c)) :=
  ⟨no_stage_carries_own_diagonal f k,
   next_stage_carries_diagonal f k,
   master_classifier_is_the_wall (coverTower f k)⟩

end E213.Lib.Math.Foundations.ExteriorAsExtension
