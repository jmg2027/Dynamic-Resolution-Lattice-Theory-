# G83: Lens equality refactor strategy — convert ~50 funext-by-design DIRTY to ∅-axiom

## The problem

`Lens α` has a `combine : α → α → α` field.  When two Lens values
are compared for equality (`L = M : Prop`), Lean reduces this to
componentwise equality:
- `L.base_a = M.base_a` (∅-axiom for concrete α)
- `L.base_b = M.base_b` (∅-axiom)
- `L.combine = M.combine` (function eq → **funext = Quot.sound**)

Function equality is the SOLE source of Quot.sound in ~90 of the
144 remaining DIRTY items.  This is the "Lens funext-by-design"
category from `STRICT_ZERO_AXIOM.md`.

## Categorization of 144 DIRTY items

### Cat 1: Concrete-α Lens funext (~50 items, **REFACTORABLE**)

Lens with codomain `α ∈ {Bool, Nat, Int, Lipschitz, Sum α β, ...}`
(not Prop).  When proven `L = M : Prop`, Lean uses funext on
combine (= Quot.sound).  Pointwise `combine u v = combine' u v`
avoids funext.

**Strategy**: Define `LensEqPW` (pointwise eq), refactor theorems
to use it instead of `=`.

### Cat 2: Prop-codomain Lens (~25 items, **INHERENT**)

Lens (Raw → Prop) — combine is `(Raw → Prop) → (Raw → Prop) →
(Raw → Prop)`.  Even pointwise comparison requires propext for
Prop equality.  These include:
- QuotLens family
- joinLens, familyJoinLens
- Lens (Raw → Prop) any kind

**Strategy**: Cannot remove propext.  These are genuinely propext-
based by design (Prop = Prop is inherent).

### Cat 3: SemanticAtom Prop = Prop (25 items, **INHERENT**)

`propXor_comm`, `iff_comm_eq`, `propAsDistinguishing`, etc.  These
are PROP equality theorems.  Cannot avoid propext.

### Cat 4: BoolProp morphisms (10 items, **INHERENT**)

`boolToProp_true` etc. — proves Prop equalities via propext.

### Cat 5: Heavy ring polynomials (~15 items, partial)

CayleyHeavy, ZOmegaDomain, SedenionHeavy.  Use `quad_norm` /
`hurwitz_ring` tactics that internally use simp/omega.  Could be
fixed by 213-native ring tactic, but heavy work.

### Cat 6: Lean.Elab plumbing (9 items, **INHERENT**)

NativeGuard, DeriveConjugationCodomain, VerifyConjugation —
inherit Classical.choice from Lean.Elab.Command monad.  Cannot
be avoided without rewriting tactic infrastructure.

### Cat 7: Misc Int-related (5-10 items, partial)

Int.add_comm, Int.le_refl, Int.add_nonneg — Lean-core Int
operations bring propext.  Replace with `Int213.*` (∅-axiom)
where they exist.

## Refactor target: Cat 1 (~50 items)

The Cat 1 items are LENS funext-by-design but with concrete α.
We can extract these by defining pointwise lens equality.

### Step 1: Define `LensEqPW`

```lean
namespace Lens

/-- Pointwise Lens equality (avoids funext on combine). -/
def eqPW {α : Type} (L M : Lens α) : Prop :=
  L.base_a = M.base_a ∧
  L.base_b = M.base_b ∧
  ∀ u v, L.combine u v = M.combine u v

theorem eqPW_refl {α} (L : Lens α) : eqPW L L :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

theorem eqPW_symm {α} {L M : Lens α} (h : eqPW L M) : eqPW M L :=
  ⟨h.1.symm, h.2.1.symm, fun u v => (h.2.2 u v).symm⟩

theorem eqPW_trans {α} {L M N : Lens α}
    (h1 : eqPW L M) (h2 : eqPW M N) : eqPW L N :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1,
   fun u v => (h1.2.2 u v).trans (h2.2.2 u v)⟩

/-- View equality follows from pointwise lens equality. -/
theorem eqPW_view {α} {L M : Lens α} (h : eqPW L M) (r : Raw) :
    L.view r = M.view r := by
  show Raw.fold L.base_a L.base_b L.combine r
     = Raw.fold M.base_a M.base_b M.combine r
  -- Induct on r, use h to show base/combine match componentwise
  induction r using Raw.rec with
  | a => rw [Raw.fold_a, Raw.fold_a, h.1]
  | b => rw [Raw.fold_b, Raw.fold_b, h.2.1]
  | slash x y _ ihx ihy => sorry  -- requires symmetric combine
```

### Step 2: Strict equality from eqPW + funext

```lean
/-- If we accept funext, eqPW implies = (closes the gap). -/
theorem eq_of_eqPW {α} {L M : Lens α} (h : eqPW L M) : L = M := by
  cases L; cases M
  obtain ⟨h1, h2, h3⟩ := h
  congr 1
  · exact h1
  · exact h2
  · funext u v; exact h3 u v  -- THIS IS THE ONLY funext call
```

This isolates funext to ONE place.  All Cat 1 theorems can be
refactored to use `eqPW` directly, and the funext-using
`eq_of_eqPW` lemma is invoked only when strict `=` is required.

### Step 3: Refactor Cat 1 theorems

For each Cat 1 theorem `theorem foo : L = M := ...`:
1. Restate as `theorem foo_eqPW : LensEqPW L M := ...`
2. Optionally provide `theorem foo : L = M := eq_of_eqPW foo_eqPW`
   (DIRTY, but localized)
3. Migrate consumers to use `foo_eqPW`

This way:
- The PURE work happens via `eqPW`
- Strict `=` needed at only specific call sites
- Consumers can choose ∅-axiom or use the strict version

## Estimated impact

| Cat | Items | Refactorability |
|---|---|---|
| 1 (Concrete-α Lens funext) | ~50 | YES — pointwise eqPW |
| 2 (Prop-codomain Lens) | ~25 | NO — inherent propext |
| 3 (SemanticAtom Prop=Prop) | 25 | NO — inherent propext |
| 4 (BoolProp morphisms) | 10 | NO — inherent propext |
| 5 (Heavy rings) | ~15 | partial — 213 ring tactic |
| 6 (Lean.Elab) | 9 | NO — sealed Lean.Elab |
| 7 (Int.* core) | 5-10 | YES — Int213 helpers |

**Refactor target**: Cat 1 + 7 = **~55-60 items**.  After refactor,
remaining ~85 items are inherent (categories 2/3/4/5/6).

## Migration plan

### Phase 1: Infrastructure (1 commit)
- Add `Lens.eqPW` + reflexivity, symmetry, transitivity, view
- Add `eq_of_eqPW` (the funext bridge)

### Phase 2: Concrete-α Cat 1 fixes (10-20 commits)
- Identify each Cat 1 file
- Refactor `L = M` proofs to use eqPW
- Migrate consumers
- Each file: 1 commit

### Phase 3: Int.* replacements (3-5 commits)
- Replace Int.add_comm with Int213.add_comm
- Replace Int.le_refl with Int213 equivalent
- Add missing Int213 helpers

### Phase 4: Heavy ring tactic (5-10 commits, optional)
- Develop 213-native ring normalization
- Replace `quad_norm` / `hurwitz_ring`

### Phase 5: Document inherent items
- Update STRICT_ZERO_AXIOM.md with category breakdown
- Acknowledge Cat 2/3/4/6 as INHERENT (not seal — different status)

## Realistic outcome

After all 5 phases (multi-session work):
- **Real DIRTY: ~85 items** (down from 144)
- **Inherent DIRTY: ~85 items** (acknowledged as Lean-core boundary)
- **Real PURE**: 2542 + 60 = ~2600 (up from 2542)

The ~85 inherent items represent the BOUNDARY of where Lean's
classical core meets 213's constructive standard.  Below that is
"Lens-funext-by-design + Prop=Prop + Lean.Elab plumbing" — three
distinct boundary categories that need explicit acknowledgment.

## See also

- `lean/E213/Lens/LensCore.lean` — current Lens structure
- `lean/E213/Lens/Universal/QuotLens.lean` — Cat 2 example
- `lean/E213/Lens/SemanticAtom.lean` — Cat 3 example
- `lean/E213/Lens/Morphism/BoolProp.lean` — Cat 4 example
- `STRICT_ZERO_AXIOM.md` — current axiom status
