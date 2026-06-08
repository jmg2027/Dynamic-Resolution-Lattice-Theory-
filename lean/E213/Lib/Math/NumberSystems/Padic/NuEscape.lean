import E213.Lib.Math.NumberSystems.Padic.Foundation
import E213.Theory.Raw.API

/-!
# A p-adic integer is a residue escape (the νF bridge, 2-adic case)

The companion to the König νF bridge (`Lib/Math/Combinatorics/KonigConditional.lean`)
and the read-through in `theory/math/numbersystems/padic_real213.md` /
`research-notes/frontiers/naming_abstract_concepts.md`: a p-adic integer is a **branch
of the p-ary tree** — an infinite digit stream reached by no finite prefix.  Here that is
made a *theorem* in the same νF carrier as a König binary-tree branch.

For `p = 2` the fit is exact and faithful: a 2-adic digit is a `Bool` (`Fin 2 ≃ Bool`),
so a `ZpSeq 2` *is* a `Nat → Bool` bit-stream, and `CoResidue.boolSpine_escapes` gives:
the 2-adic integer, as a νF inhabitant (`SlashNu`), is **reached by no finite Raw**.  So
`ℤ₂` sits inside the residue's escapes — a 2-adic integer is literally a branch of König's
binary tree, never a finite Raw, never a frozen value.

Scope (honest, per `seed/AXIOM/05_no_exterior.md` §5.4): general `p` needs a `Fin p`→bits
encoding (or a p-ary spine in `CoResidue`) — open.  ℝ's dyadic escape is already on record
(`theory/essays/foundations/reached_by_none.md`; `Analysis/Cauchy/DepthCeilingResidue`).
This file closes the 2-adic instance and pins the shared shape with König.
-/

namespace E213.Lib.Math.NumberSystems.Padic

open E213.Theory.Raw.CoResidue
open E213.Theory (Raw)

/-- A 2-adic integer's digit stream as a `Nat → Bool` bit-stream (`Fin 2 ≃ Bool`,
    faithful: digit `k` ↦ whether it is `1`). -/
def twoAdicBits (x : ZpSeq 2) : Nat → Bool := fun k => (x.digits k).val == 1

/-- ★ **A 2-adic integer IS a residue escape.**  Its bit-stream packages as a νF
    inhabitant (`SlashNu`) — the same carrier as a König binary-tree branch. -/
def twoAdicNu (x : ZpSeq 2) : SlashNu := boolSpineSlashNu (twoAdicBits x)

/-- The 2-adic integer is a genuine slash-νF co-tree: consistent and anti-reflexive. -/
theorem twoAdic_is_nu (x : ZpSeq 2) :
    Consistent (twoAdicNu x).val ∧ AntiRefl (twoAdicNu x).val :=
  (twoAdicNu x).property

/-- ★★ **A 2-adic integer is reached by no finite Raw.**  Its bit-stream escape differs
    (as a labelled co-tree) from every finite Raw's embedding (`rawToSlashNu`), by
    `boolSpine_escapes`.  So `ℤ₂` ⊂ the νF escapes: a 2-adic integer is a branch of
    König's binary tree, never a finite Raw — the same `boolSpine_escapes` shape as
    `KonigConditional.konig_infinity_no_finite_raw`. -/
theorem twoAdic_is_nu_escape (x : ZpSeq 2) (r : Raw) :
    (rawToSlashNu r).val ≠ (twoAdicNu x).val :=
  fun h => boolSpine_escapes (twoAdicBits x) r.val h.symm

end E213.Lib.Math.NumberSystems.Padic
