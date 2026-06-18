/-!
# AxisSeparation — the atom-forcing criterion as a checkable theorem (∅-axiom)

Across the corpus the same meta-pattern recurs: a counting/coordinate readout is
*faithful* (it separates, it is forced, it cannot be dropped) exactly when its
indexing **axis distinguishes**, and it *collapses* (carries no information, is
gauge/removable) exactly when the axis is **indistinguishable**.  Proven instances:

  * `Meta.Nat.VpSeparation.vp_separation` — the multiplicative atoms (primes) are
    distinguishable, so the prime-exponent vector is faithful (UFD).
  * `Lib/.../UnitList.append_comm` — the additive atoms (units) are indistinguishable,
    so the additive "vector" collapses to a bare count (order carries nothing).
  * the `c`-multiplicity removability audit (`research-notes/frontiers/
    atomic_c_multiplicity_forcing.md`) — the `c`-axis is not a distinguishing axis,
    so `c` is eliminable.

This file states the criterion abstractly, as a `#print axioms`-checkable theorem
(the open request in `theory/essays/synthesis/the_forcing_criterion_is_distinguishing.md`).
Per the multi-agent panel audit (2026-06-16): the *strong* reading — "one theorem
from which `vp_separation` and `c`-removal fall out as full corollaries" — is a
**forcible map** and is refused; `vp_separation` carries genuine UFD content and
`c`-removal carries a physics-inertness bridge that no free-monoid slogan subsumes.
What is true and worth pinning is the **kernel**: the one-hot (Kronecker) readout
collapses *iff* the atom type is a subsingleton.  The named instances cite this
kernel for their *cause* while keeping their own domain proofs local.

Note the panel also caught a bug in the first-draft statement: "the one-hot readout
is faithful ⟺ the atoms distinguish" is **false**, because faithfulness
(`∀ a a', a ≠ a' → ∃ axis, …`) is *vacuously true* for a subsingleton.  The correct,
non-vacuous kernel is the *collapse* form below.

All ∅-axiom.
-/

namespace E213.Meta.AxisSeparation

universe u

/-- An atom type is **distinguishing** when it carries two distinct atoms — the
    abstract precondition behind "primes are distinct", "`true ≠ false`", "`2 ≤ c`". -/
def Distinguishes (A : Type u) : Prop := ∃ a a' : A, a ≠ a'

/-- The **one-hot / Kronecker readout**: axis `i` reads `1` on atom `i`, else `0`.
    The minimal "occupation coordinate" — the abstract shadow of a valuation vector
    `vp p ·` or an occupation/multiplicity vector. -/
def onehot {A : Type u} [DecidableEq A] (i a : A) : Nat := if i = a then 1 else 0

/-- A readout **collapses** when no axis tells two atoms apart — it reads the same on
    every atom, carrying *no* atom-distinguishing information.  This is the genuine
    (non-vacuous) negation of faithfulness: a collapsed readout is droppable/gauge. -/
def Collapses {A : Type u} (r : A → A → Nat) : Prop := ∀ i a a' : A, r i a = r i a'

theorem onehot_diag {A : Type u} [DecidableEq A] (a : A) : onehot a a = 1 := if_pos rfl

theorem onehot_off {A : Type u} [DecidableEq A] {i a : A} (h : i ≠ a) :
    onehot i a = 0 := if_neg h

/-- ★★★ **The atom-forcing kernel.**  The one-hot readout on `A` **collapses iff `A`
    is a subsingleton** — i.e. the occupation coordinate carries no information exactly
    when the atom axis fails to distinguish.  This is the checkable form of "a readout
    is faithful ⟺ its indexing axis distinguishes".  ∅-axiom. -/
theorem subsingleton_iff_collapses {A : Type u} [DecidableEq A] :
    (∀ a a' : A, a = a') ↔ Collapses (onehot (A := A)) := by
  constructor
  · intro hsub i a a'; rw [hsub a a']
  · intro hcol a a'
    have h := hcol a a a'
    rw [onehot_diag] at h
    by_cases haa' : a = a'
    · exact haa'
    · rw [onehot_off haa'] at h; exact absurd h (by decide)

/-- ★ A distinguishing atom type has a **non-collapsing** one-hot readout: distinct
    atoms are separated by the axis indexed by either of them.  The faithful direction. -/
theorem distinguishes_not_collapses {A : Type u} [DecidableEq A]
    (h : Distinguishes A) : ¬ Collapses (onehot (A := A)) := by
  intro hcol
  obtain ⟨a, a', hne⟩ := h
  exact hne ((subsingleton_iff_collapses).mpr hcol a a')

/-! ## Instances — the three named patterns, each citing the kernel for its cause -/

/-- **Indistinguishable atom** (the `Unit`/units pattern, cause of `append_comm`):
    a singleton atom type collapses the readout — arrangement is no information. -/
theorem unit_collapses : Collapses (onehot (A := Unit)) :=
  (subsingleton_iff_collapses).mp (fun a a' => by cases a; cases a'; rfl)

/-- **Distinguishable atom** (the prime/`vp_separation` pattern, in miniature): two
    distinct atoms force a non-collapsing readout.  `Bool` is the order-2 witness. -/
theorem bool_distinguishes : Distinguishes Bool := ⟨true, false, by decide⟩

theorem bool_not_collapses : ¬ Collapses (onehot (A := Bool)) :=
  distinguishes_not_collapses bool_distinguishes

/-- **The `Fin`-axis pattern** (the `c`-multiplicity audit, in miniature): a `Fin c`
    axis distinguishes iff `2 ≤ c` — `Fin 1` collapses (the removable `c=1` layer),
    `Fin (c+2)` separates `0` from `1`.  The arithmetic face of "is the axis real?". -/
theorem fin_succ_succ_distinguishes (c : Nat) : Distinguishes (Fin (c + 2)) :=
  ⟨⟨0, Nat.succ_pos (c + 1)⟩, ⟨1, Nat.succ_lt_succ (Nat.succ_pos c)⟩,
    fun h => absurd (show (0 : Nat) = 1 from congrArg Fin.val h) (by decide)⟩

theorem fin_one_collapses : Collapses (onehot (A := Fin 1)) :=
  (subsingleton_iff_collapses).mp (fun a a' => Fin.ext (by
    have ha : a.val = 0 := Nat.le_zero.mp (Nat.le_of_lt_succ a.isLt)
    have hb : a'.val = 0 := Nat.le_zero.mp (Nat.le_of_lt_succ a'.isLt)
    rw [ha, hb]))

end E213.Meta.AxisSeparation
