import E213.Lens.Foundations.FlatOntology
import E213.Lib.Math.NumberSystems.Real213.Core.AsLensOutput

/-!
# Real213.ObjectIsReadingScaleInvariant — object = reading, at both scales

A standing dual collapses to one shape under the pointing view: **an object is a
reading** (a `· → Bool` predicate / Lens output), with no separate sort for "the
thing" vs "the reading of it".  This file records that the *same* collapse
appears at two scales that classically look unrelated:

  * **atom scale** — a single `Raw` is its own indicator predicate
    `Object1 r : Raw → Bool` (`Lens/Foundations/FlatOntology`).  The object IS a
    `Raw → Bool` reading.
  * **limit scale** — a real number is `RealAsLensOutput = Nat → Nat → Bool`,
    a Lens output assigning a Bool to each rational target
    (`Real213/Core/AsLensOutput`).  The object IS a `Nat → Nat → Bool` reading.

Both are instances of one shape: `Object = (Index → Bool)` = a reading.
Classically "a point" and "a real" are different kinds of thing (a vertex vs a
Dedekind/Cauchy completion); here both are the same move — *the object is the
reading*, only the index differs (`Raw` vs `Nat`).  The collapse "object =
reading" is **scale-invariant**: not a fact about atoms that happens to recur,
but one shape read at two indices.

Formal companion of the informal "transition = state / line = point"
non-separation: at the atom it is `a/b` being both edge and vertex; at the limit
it is ℝ being both a rule (the cut predicate) and a totality (the number).

(Lives in `Lib/Math/` because it cites both `Lens` and `Lib`; the ring order is
`Term → Theory → Lens → Lib`, per `ARCHITECTURE.md`.)
-/

namespace E213.Lib.Math.NumberSystems.Real213.ObjectIsReadingScaleInvariant

open E213.Theory (Raw)
open E213.Lens.Foundations.FlatOntology (Object1 Object1_self)
open E213.Lib.Math.NumberSystems.Real213.Core.AsLensOutput (RealAsLensOutput)

/-- The shared shape: an **object at index `ι`** is a reading `ι → Bool`. -/
abbrev ObjectAsReading (ι : Type) : Type := ι → Bool

/-! ## Atom scale — a Raw is a `Raw → Bool` reading -/

/-- At the atom scale the index is `Raw` itself: an object-as-reading is a
    `Raw → Bool`, and `Object1` exhibits every Raw as one. -/
theorem atom_object_is_reading (r : Raw) :
    (Object1 r : ObjectAsReading Raw) = Object1 r := rfl

/-- The atom-scale reading is *faithful at its own point*: `Object1 r` reads
    `true` exactly at `r` (so the object is recovered from the reading — object
    and reading are the same datum, not two). -/
theorem atom_reading_pins_object (r : Raw) :
    (Object1 r : ObjectAsReading Raw) r = true :=
  Object1_self r

/-! ## Limit scale — a real is a `Nat → Nat → Bool` reading -/

/-- At the limit scale the index is `Nat` (rational targets, curried): a real
    object-as-reading is `Nat → (Nat → Bool)` = `RealAsLensOutput`.  The real
    number IS this reading, definitionally. -/
theorem real_object_is_reading :
    RealAsLensOutput = (Nat → ObjectAsReading Nat) := rfl

/-! ## Scale invariance — one shape, two indices -/

/-- ★★ **Object = reading, scale-invariant.**  At both scales the object is a
    reading `Index → Bool`; only the index differs (`Raw` at the atom scale,
    `Nat` at the limit scale).  The non-separation "object = reading" is not a
    coincidence repeating — it is one shape `ObjectAsReading ι` read at two
    indices.  (The atom reading is additionally pinned at its own point by
    `Object1_self`; the real reading is the index-curried form definitionally.) -/
theorem object_is_reading_scale_invariant :
    -- atom scale: object lives in `Raw → Bool`, pinned at its point
    (∀ r : Raw, (Object1 r : ObjectAsReading Raw) r = true)
    ∧ -- limit scale: a real IS a `Nat → (Nat → Bool)` reading
    (RealAsLensOutput = (Nat → ObjectAsReading Nat)) :=
  ⟨atom_reading_pins_object, real_object_is_reading⟩

end E213.Lib.Math.NumberSystems.Real213.ObjectIsReadingScaleInvariant
