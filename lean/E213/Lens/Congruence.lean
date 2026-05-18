import E213.Theory.Raw.API
import E213.Lens.LensCore
import E213.Lens.Number.Nat213.ChartGeneral


/-!
# Lens.Congruence — bridge between `Eqv` (internal) and `Lens.equiv` (external)

Per `research-notes/2026-05-18_lens_emergence_path.md` §2.6.  Each
lens `L : Lens α` induces an *external* equivalence
`L.equiv x y := L.view x = L.view y`.  Each generator set
`gens : Raw → Raw → Prop` induces an *internal* equivalence
`Eqv gens x y` via the equivalence closure
(`Theory.Raw.Congruence`).

The two are connected:

  1. **Internal → External**: if every generator pair preserves
     `L.view`, the whole `Eqv gens` closure preserves it.
  2. **External → Internal**: choosing `gens := L.equiv` makes the
     `Eqv` closure exactly `L.equiv` itself.

Result (2) — the biconditional `Eqv L.equiv ↔ L.equiv` — realises
§2.6's "external α-value agreement ⟺ internal `Eqv` equivalence"
for *any* lens.

**Caveat on §2.6's stronger conjectures.**  The research note also
proposes things like "ℕ₊ = Raw / (a ≡ b ∧ slash_assoc)" — Raw
quotiented by atomic identification + associativity.  That picture
is conceptually wrong (see `Theory.Raw.ParenthesizationDistinct`):
different parenthesisations are structurally distinct Raws, and
forcing associativity erases Raw-internal information.  ℕ₊ is the
*image* of `Lens.leaves.view`, not a quotient of `Raw`.  Option C
of the refactor realised this projection picture.  This file's
`Eqv` ↔ `L.equiv` biconditional is useful at the generic level
(any lens) but should not be used to "internalise" ℕ₊.

∅-axiom standard; the prohibited-tactic catalogue is
`STRICT_ZERO_AXIOM.md`.
-/

namespace E213.Lens

open E213.Theory

/-- If a lens's `view` is constant on every generator pair, it is
    constant on every `Eqv gens`-equivalent pair. -/
theorem view_eq_of_Eqv {α} {L : Lens α} {gens : Raw → Raw → Prop}
    (h_gens : ∀ {x y}, gens x y → L.view x = L.view y)
    {x y : Raw} (h : Eqv gens x y) : L.view x = L.view y :=
  Eqv.induction' (fun a b => L.view a = L.view b)
    (fun hgen => h_gens hgen)
    (fun _ => rfl)
    (fun ih => ih.symm)
    (fun ih₁ ih₂ => ih₁.trans ih₂) h

/-- Injecting `L.view`-equality into `Eqv L.equiv` is the `of`
    constructor. -/
theorem Eqv_of_view_eq {α} {L : Lens α} {x y : Raw}
    (h : L.view x = L.view y) :
    Eqv (fun a b => L.view a = L.view b) x y :=
  Eqv.of h

/-! ### The §2.6 biconditional — for any lens `L`

`Eqv L.equiv` is exactly `L.equiv`.  Direction (←) is the `of`
constructor; direction (→) follows from `view_eq_of_Eqv` since the
generator IS `L.equiv` (so the "respects view" hypothesis is
trivial). -/

/-- **Eqv ↔ view-equality** for the lens-induced generator.
    Realises §2.6's claim that *external* α-value agreement and
    *internal* `Eqv`-equivalence coincide when the generator set is
    chosen to be the lens equivalence itself. -/
theorem Eqv_equiv_iff {α} (L : Lens α) (x y : Raw) :
    Eqv (fun a b => L.view a = L.view b) x y
      ↔ L.view x = L.view y := by
  constructor
  · intro h
    exact view_eq_of_Eqv (fun hgen => hgen) h
  · intro h
    exact Eqv.of h

/-! ### Concrete instantiation — `Lens.leaves`

The natural-number lens `Lens.leaves : Lens Nat` (atom→1,
slash→sum) is the canonical chart projection for ℕ₊.  Two Raws are
`Eqv (fun a b => Lens.leaves.view a = Lens.leaves.view b)`-
equivalent iff they have the same leaves count. -/

/-- Specialisation of `Eqv_equiv_iff` to `Lens.leaves`.  Two Raws
    are leaves-`Eqv`-equivalent iff their leaves counts agree. -/
theorem Eqv_leaves_iff (x y : Raw) :
    Eqv (fun a b => Lens.leaves.view a = Lens.leaves.view b) x y
      ↔ Lens.leaves.view x = Lens.leaves.view y :=
  Eqv_equiv_iff Lens.leaves x y

/-! ### `Lens.leaves` image characterisation (added 2026-05-18)

`Lens.leaves : Lens Nat = ⟨1, 1, +⟩` has image exactly
`{n : Nat | 1 ≤ n} = ℕ₊`.  Containment in ℕ₊ is `leaves_view_pos`
(every Raw has at least one leaf).  Surjectivity onto ℕ₊ uses the
Method A numeral chain: `Lens.leaves.view (numeral n) = n + 1`
covers every `n ≥ 1` via `numeral (n - 1)`. -/

/-- `Lens.leaves.view r = Raw.value r` — both unfold to
    `Raw.fold 1 1 (·+·) r`.  Bridge between the Lens-side and the
    Nat213-Raw-side names. -/
theorem leaves_view_eq_value (r : Raw) :
    Lens.leaves.view r = E213.Lens.Number.Nat213.Raw.value r := rfl

/-- Every Raw has leaves-view ≥ 1. -/
theorem leaves_view_pos (r : Raw) : 1 ≤ Lens.leaves.view r := by
  rw [leaves_view_eq_value]
  exact E213.Lens.Number.Nat213.value_pos r

/-- **ℕ₊ ⊆ Range(Lens.leaves.view)**: every natural `n ≥ 1` is
    realised as the leaves count of some Raw — explicitly,
    `numeral (n - 1)`. -/
theorem leaves_view_surjective_on_ge_one (n : Nat) (hn : 1 ≤ n) :
    ∃ r : Raw, Lens.leaves.view r = n := by
  obtain ⟨r, hr⟩ :=
    E213.Lens.Number.Nat213.Raw.value_surjective_on_ge_one n hn
  exact ⟨r, by rw [leaves_view_eq_value]; exact hr⟩

end E213.Lens
