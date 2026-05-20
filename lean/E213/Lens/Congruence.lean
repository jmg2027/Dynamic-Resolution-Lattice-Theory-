import E213.Theory.Raw.API
import E213.Lens.LensCore
import E213.Lens.Number.Nat213.ChartGeneral


/-!
# Lens.Congruence — bridge between `Eqv` (generator closure) and `Lens.equiv` (view agreement)

Two readings of Raw equivalence connected here:

  - `Eqv gens` — equivalence closure of a generator set
    `gens : Raw → Raw → Prop` (structural reading).
  - `L.equiv x y := L.view x = L.view y` — α-view agreement
    (observational reading via Lens `L : Lens α`).

Both are residue-internal events (per
`seed/AXIOM/07_self_reference.md` §8.1, "internal/external" is
itself a Lens-imported framing; here the two names mark
*structural* vs *observational* readings of the same residue, not
a substrate/external split).

The two readings are connected:

  1. **Structural → Observational**: if every generator pair
     preserves `L.view`, the whole `Eqv gens` closure preserves it.
  2. **Observational → Structural**: choosing `gens := L.equiv`
     makes the `Eqv` closure exactly `L.equiv` itself.

Result (2) — the biconditional `Eqv L.equiv ↔ L.equiv` — realises
"view agreement ⟺ generator closure" for *any* lens.

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

/-! ### Strict-coarsening witness for `Lens.leaves` (added 2026-05-18)

`Lens.leaves.equiv` is *strictly coarser* than `=` on `Raw` —
the parenthesisations `(a/b)/z` and `a/(b/z)` from
`Theory.Raw.ParenthesizationDistinct` collapse under it.  This is
the Lens-side restatement of `lhs_rhs_leaves_eqv` (same fact, named
through `Lens.leaves.view`). -/

/-- **Strict coarsening at the Lens level**: there exist two
    distinct Raws that are `Eqv`-equivalent under
    `Lens.leaves.equiv`.  Concrete witnesses are the two
    parenthesisations of `Theory.Raw.ParenthesizationDistinct`. -/
theorem exists_distinct_leaves_view_eqv :
    ∃ x y : Raw, x ≠ y ∧
      Eqv (fun a b => Lens.leaves.view a = Lens.leaves.view b) x y := by
  obtain ⟨x, y, hxy, h⟩ :=
    E213.Theory.Raw.ParenthesizationDistinct.exists_distinct_leaves_eqv
  refine ⟨x, y, hxy, ?_⟩
  refine Eqv.weaken ?_ h
  intro a b (hab : Raw.leaves a = Raw.leaves b)
  show Lens.leaves.view a = Lens.leaves.view b
  show Raw.fold 1 1 (·+·) a = Raw.fold 1 1 (·+·) b
  rw [Raw.fold_eq_leaves, Raw.fold_eq_leaves]
  exact hab

/-! ### Eqv monotonicity in the Lens (added 2026-05-18)

If `M` refines `L` (every `M.view`-equality implies an `L.view`-
equality), then `Eqv M.equiv` ⊆ `Eqv L.equiv` — finer lens
generates coarser equivalence closure. -/

/-- Lens refinement induces weakening of the `Eqv`-closure: if
    `M.view`-equality implies `L.view`-equality, the `M`-generated
    `Eqv` is contained in the `L`-generated one. -/
theorem Eqv_monotone_in_lens {α β} (L : Lens α) (M : Lens β)
    (h_refines : ∀ x y, M.view x = M.view y → L.view x = L.view y)
    {x y : Raw}
    (h : Eqv (fun a b => M.view a = M.view b) x y) :
    Eqv (fun a b => L.view a = L.view b) x y :=
  Eqv.weaken (fun hgen => h_refines _ _ hgen) h

end E213.Lens
