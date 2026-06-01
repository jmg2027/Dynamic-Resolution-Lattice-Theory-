# G161 — Skeptical review of the "sealed-DIRTY-by-design" seals (213-native view)

**Tier-1.**  Asked to re-examine the sealed-DIRTY justifications *not* from the
mechanical ∅-axiom view but from **213-native theory development**: is each seal
a genuine Lean-core boundary, or is it the residue of importing **classical
extensional equality** (`=` at `Prop` / at function-of-`Prop`) where 213's own
notion is the **Reading-equivalence** (pointwise `↔` / `Lens.equiv`)?

Conclusion: the two equality-seals are **largely artifacts of the `=` choice**,
demonstrably purifiable in their standalone form; only one residual is a genuine
*framework* (not Lean-core) commitment; and the `CommandElab` `Classical.choice`
seal is the only honestly-inherent one.

## The seals, restated

  - **(a) Prop-as-distinguishing** (`SemanticAtom`, `BoolProp`): `combine P Q =
    combine Q P` at `Prop` ⟹ `propext`.
  - **(b) Lens funext-by-design** (`QuotLens`, `IndexedJoin`, `Instances.Cauchy`,
    `DepthJoin`, `Compose.OnLens`, `Lattice.Join`, …): `combine f g = combine g f`
    at a function type `(Raw → Prop) → …` ⟹ `funext` (= `Quot.sound` in the
    kernel) + `propext`.
  - **(a-elab)** three `CommandElab` defs ⟹ `Classical.choice` via the
    `Lean.Elab.Command` monad.

## Skeptical finding 1 — the axioms come from `=`, not from 213 structure

`Raw` is **not a quotient**: `def Raw := { t : Tree // t.canonical = true }` (a
subtype).  So `Quot.sound` is **not** inherent to Raw-equality.  In the sealed
`combine_sym` proofs the `Quot.sound` enters through **`funext`** (Lean proves
function extensionality via `Quot`), and `propext` through `apply propext` — both
used only to lift a per-point statement to an `=` at function-of-`Prop`.
`Raw.slash_comm` (slash commutativity) is itself **PURE**.

## Skeptical finding 2 — the 213-native form is PURE (demonstrated)

State combine-symmetry the way 213 actually means it — as a **Reading-equivalence**,
i.e. the two combined readings distinguish the same things, pointwise `↔`:

```lean
theorem combine_sym_pointwise (E) (f g : Raw → Prop) (r' : Raw) :
    (universalLens E).combine f g r' ↔ (universalLens E).combine g f r' := by
  constructor <;> (rintro ⟨X, Y, h, hX, hY, hs⟩;
    exact ⟨Y, X, Ne.symm h, hY, hX, by rwa [Raw.slash_comm Y X (Ne.symm h)]⟩)
```

`#print axioms combine_sym_pointwise` → **"does not depend on any axioms"** —
fully PURE, using the very same `Raw.slash_comm`.  The sealed `=`-form
`combine f g = combine g f` is the *identical mathematical content* with two
extra lines (`funext r'; apply propext`) that import `Quot.sound` + `propext`.

So the seal does not protect a 213 fact that *needs* those axioms; it protects a
**statement shape** (`=` at function-of-`Prop`) that 213 has no native reason to
prefer over `↔`.  Per `seed/AXIOM/01_residue.md` and the meta-principle, `=` at
`Prop` imports a residual meaning (Prop-identity) beyond the Lens-defined
distinguishing relation; the native object is the `↔`.

## Skeptical finding 3 — the one genuine residual is *framework*, not Lean-core

`universalLens_view_eq` consumes the `=`-form: `Raw.fold_slash` is wired to take
`combine u v = combine v u` (function `=`) so the universal fold is well-defined
over the **commutative** `Raw.slash`.  So the `=`-form is *needed by `Raw.fold`'s
current interface* — but that is a **framework design choice**, not a Lean-core
necessity: a 213-native `Raw.fold` could require the combine to respect slash
commutativity **up to Reading-equivalence** (pointwise `↔`) instead of `=`, and
then nothing in the chain would touch `funext`/`propext`.  The seal comment
"refactoring would redefine what Lens equality means" is exactly the point — and
213-natively that redefinition is the *correct* one: **Lens/​combine sameness is
the Reading-equivalence, not function-`=`.**

## Skeptical finding 4 — only the elaborators are honestly sealed

The three `CommandElab` defs (`Tactic.QuadExtension`,
`Meta.Tactic.{DeriveConjugationCodomain,VerifyConjugation}`) carry
`Classical.choice` via the `Lean.Elab.Command` monad.  This is *not* a 213-math
equality choice — it is metaprogramming plumbing with no `↔`-form alternative.
This seal is genuinely inherent; keep it.

## Verdict + recommendation

| Seal | 213-native verdict |
|---|---|
| (a) Prop `combine_sym` `propext` | **artifact of `=`-at-`Prop`** — the `↔` (distinguishing-equivalence) form is PURE; `=`-form needed only as a typeclass *field* shape |
| (b) Lens `combine_sym` funext/`Quot.sound` | **artifact of `=`-at-(Raw→Prop)** — pointwise `↔` form PURE (demonstrated); `=`-form needed only by `Raw.fold`'s current interface |
| (a-elab) `Classical.choice` | **genuinely inherent** (Elab monad) — keep sealed |

So "57 sealed-by-design" splits into **3 honestly-inherent** (elaborators) and
**~54 framework-`=`-artifacts** that a Reading-equivalence refactor of the Lens
`combine` coherence (carry symmetry as pointwise `↔`, have `Raw.fold` respect
slash-commutativity up to `Lens.equiv`) would make PURE.  Not a falsifiability
issue (propext/Quot.sound are core-allowed), but the seals should be relabeled:
**not "Lens equality is inherently funext" but "the framework states combine
coherence as `=`; the 213-native pointwise form is PURE."**  The refactor is a
real, scoped piece of theory work (touches `Lens.combine`'s coherence field +
`Raw.fold`'s slash hypothesis), not a one-liner — flagged here for a dedicated arc.

## Refinement — applying the skepticism to *this note* (second pass)

The first pass said the (b) seals are "artifacts of the `=` choice".  Tested
harder, that is **too strong**.  Ground truth:

  - `Raw.slash_comm : Raw.slash x y h = Raw.slash y x (Ne.symm h)` is a genuine
    Raw `=` (canonical Trees sort children by `Tree.cmp`), proved
    constructively (`Tree.cmp_swap` + `split`/`rfl`) — **PURE**.
  - `Raw.fold_slash` genuinely takes **`hsym : ∀ u v : α, c u v = c v u`**
    (`Theory/Raw/Fold.lean:39`).  Because `slash x y = slash y x` *as Raw*,
    a function `fold : Raw → α` must return the same α on both, so the
    homomorphism law in arbitrary (unsorted) order genuinely needs combine
    `=`-symmetry **at α**.  For `α = Nat` that is plain `Nat` `=` (PURE, cf.
    `Levels.lean` leaf-count fold); for `α = Prop` / `Raw → Prop` it is
    `propext` / `funext` — and that is **forced, not gratuitous**.

So the honest verdict is between the two extremes:

  - The **standalone** "combine is symmetric" *is* PURE in its 213-native
    pointwise-`↔` form (demonstrated) — that part of the first pass stands.
  - But the sealed `=`-form is **genuinely required by `Raw.fold_slash`** over a
    genuinely (and purely) commutative slash.  It is not a lazy restatement
    artifact; it is the price of a **propositional-`=`-valued fold into a
    `Prop`/function-of-`Prop` codomain**.
  - The 213-native escape is therefore a real, scoped **foundational refactor**,
    not a relabel: a **Reading-equivalence-valued `fold_slash`** —
    `hsym : ∀ u v, c u v ≈ c v u` (pointwise `↔`) with conclusion
    `fold (slash x y) ≈ c (fold x) (fold y)` — which is PURE and is the correct
    213 reading ("the fold respects slash-commutativity *up to distinguishing*,
    not up to Lean `=`").  Consumers (`*_view_eq`, the `HasDistinguishing`
    `combine_sym` field) would move to `≈`.  This touches a foundational
    primitive (`Raw.fold`) and its whole consumer set — **a dedicated arc**, to
    be done carefully, not in passing.

**Net**: the equality-seals are *honest under the current `=`-valued fold
semantics* (so do not just delete them), **and** they are *not the 213-native
end state* (the `≈`-valued fold is).  Both are true; the seal comment should say
"`=`-valued fold over the commutative slash forces this; the `≈`-valued
(Reading) fold is the native target" rather than either "inherently funext" or
"trivially purifiable".

## Pointers
  - Demonstrated PURE pointwise form: `Lens/Universal/QuotLens.lean`
    `universalLens_combine_sym` (the `=`-form) vs the `combine_sym_pointwise`
    probe above.
  - `Raw` subtype: `Theory/Raw/Core.lean`; `Raw.slash_comm` (PURE):
    `Theory/Raw/Slash.lean`.
  - Sealed catalog: `STRICT_ZERO_AXIOM.md`; `tools/scan_all_axioms.py`
    `SEALED_DIRTY_PREFIXES`.
  - Equivalence-is-one-arrow: `theory/lens/unified_equivalence.md`.
