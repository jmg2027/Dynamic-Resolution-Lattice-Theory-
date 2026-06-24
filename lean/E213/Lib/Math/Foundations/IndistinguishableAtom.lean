/-!
# The third lattice bottom — indistinguishable atoms (`Unit`, the non-distinguishing)

`theory/meta/de_abstraction_calculus.md` reads the corpus onto a lattice by removal-fingerprint.
Two bottoms are named: cluster A (the **binary** distinguishing — `Bool`, kernel `xor b b =
false`, engine `XorInvolution.xorFold_involution`) and cluster B (the **iterated** distinguishing
— `ℕ = succ`, kernel `Nat.rec`, engine `MeasureInduction.measureInduction`).

This file names the **third**: the **undistinguished** atom — `Unit`, kernel `() = ()` (the
*non*-distinguishing).  When atoms carry no identity, structure collapses to **count alone**:
a list of indistinguishable atoms is determined by its length.  This is the exact dual of
cluster A — where `Bool` has `!b ≠ b` (the two atoms *are* distinguished), `Unit` has `() = ()`
(the atom is *not* distinguished).

So the lattice's three resolution-bottoms are the three readings of an atom:

| cluster | atom | kernel | reading |
|---|---|---|---|
| A | `Bool` | `xor b b = false` / `!b ≠ b` | atoms **distinguished** (parity, involution) |
| B | `ℕ` (`succ`) | `Nat.rec` | atoms **counted/ordered** (descent) |
| C | `Unit` | `() = ()` | atoms **undistinguished** (count is the complete invariant) |

These are exactly the count-Lens's facets (`seed/AXIOM/06_lens_readings.md`): the distinguishing
read binary, counted, and not-at-all.  The lattice's floor is the distinguishing at its three
atom-readings; there is nothing below to land on (`01_residue.md` §1.3).  The richer cluster-C
content — `(ℕ,+)` generated as `List Unit` append, `+`-commutativity from `append_comm` — lives
in the genesis seam (`Meta/Nat/UnitList`, `GenerationCapstone`); this file pins the kernel node.

∅-axiom.
-/

namespace E213.Lib.Math.Foundations.IndistinguishableAtom

/-- ★★★ **Indistinguishable atoms ⟹ count is the complete invariant.**  Two lists of `Unit`
    (an atom with no identity, `() = ()`) are equal as soon as they have the same length: with
    nothing to distinguish the atoms, only the count survives.  Cluster C's kernel node, dual to
    cluster A's `xor b b = false`.  Bottoms in `Unit` eta (`() = ()`), the non-distinguishing. -/
theorem list_unit_determined_by_length :
    ∀ (l₁ l₂ : List Unit), l₁.length = l₂.length → l₁ = l₂
  | [],      [],      _ => rfl
  | [],      _ :: _,  h => Nat.noConfusion h
  | _ :: _,  [],      h => Nat.noConfusion h
  | a :: as, b :: bs, h => by
    have hlen : as.length = bs.length := Nat.succ.inj h
    have htail : as = bs := list_unit_determined_by_length as bs hlen
    cases a; cases b
    exact congrArg (fun l => () :: l) htail

/-- The complete invariant of a `List Unit` is its length: equal-length ⟺ equal.  (The forward
    direction is `congrArg List.length`; the content is `list_unit_determined_by_length`.) -/
theorem list_unit_eq_iff_length (l₁ l₂ : List Unit) :
    (l₁.length = l₂.length → l₁ = l₂) ∧ (l₁ = l₂ → l₁.length = l₂.length) :=
  ⟨list_unit_determined_by_length l₁ l₂, congrArg List.length⟩

end E213.Lib.Math.Foundations.IndistinguishableAtom
