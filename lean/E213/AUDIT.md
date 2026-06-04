# lean/E213/AUDIT.md — Implementation × axiom cross-check

(formerly `seed/AXIOM/{08_implementation,09_audit}.md`, moved here
2026-05-12 — these are Lean-implementation analysis, NOT axiom
content.  AXIOM corpus stays focused on the axiom itself.)

This file contains:
- **Part I** (§I.*) — Implementation device classification
  (α/β/γ/δ): which Lean device is axiom re-expression vs. encoding
  artifact vs. derivation.  Demonstrates the Lean implementation is
  a **faithful emulator** with no (δ) additional commitment.
- **Part II** (§9.*) — Lean ↔ axiom 4-clause cross-check + corner
  cases + 5 silent-leak paths.

For the axiom itself: `seed/AXIOM/02_axiom.md`.
For the encoding-costs framing: `seed/AXIOM/10_encoding_costs.md`.


(formerly seed/IMPLEMENTATION.md)

## Abstract

This document structurally demonstrates that the Raw framework
implemented in `lean/E213/Theory/` is a **faithful emulator** of
the axiom in `02_axiom.md`.  Specifically:

1. Each implementation device in Lean 4 core (inductive type,
   subtype, canonical form, smart constructor, custom eliminator)
   is classified as either axiom addition, encoding artifact, or
   derivation.

2. Each safeguard (type gate, theorem precondition, doc warning,
   namespace convention) is analyzed for whether it **adds
   mathematical commitment**.  **Conclusion: no additional
   commitment.**  Safeguards fall into one of:
   - (i) type-level re-expression of an axiom clause,
   - (ii) conditional precondition of a theorem (the theorem itself
     is conditional),
   - (iii) meta-syntactic hygiene (preventing human misuse).

3. Analysis of API surfaces (Raw.fold, Raw.rec) where encoding
   artifacts can leak into Lens output, and the current mitigation
   state.

Related document: `seed/AXIOM/02_axiom.md`.

---

## §I.1 Problem statement

The axiom (`02_axiom.md` §3.2) consists of 4 clauses.  Since
Lean 4 core has no primitive quotient, several implementation
devices are introduced in the process of putting this axiom on a
machine:

- `inductive Tree | a | b | slash (x y : Tree)` — ordered free magma.
- `Tree.cmp : Tree → Tree → Ordering` — total order, canonical
  form selector.
- `Tree.canonical : Tree → Bool` — normal-form predicate.
- `Raw : Type := { t : Tree // t.canonical = true }` — subtype.
- `Raw.slash (x y : Raw) (h : x ≠ y) : Raw` — smart constructor
  (auto-canonicalize).

For each device, the following must be determined:

(α) **Type-level re-expression of the axiom** — mechanical
    translation of the axiom itself.
(β) **Encoding artifact** — technique to work around Lean 4 core's
    absence of primitive quotient.  Different choices are possible;
    the internal representation changes with choice but the
    mathematical meaning of Raw is invariant.
(γ) **Derivation** — a fact that automatically follows from the
    axiom.
(δ) **Additional axiom / constraint** — a new commitment not in
    the axiom.

If (δ) is found, it constitutes an axiom violation.

---

## §I.2 Classification of implementation devices

### §I.2.1 `inductive Tree | a | b | slash`

Lean inductive type.  Two nullary constructors + one binary
constructor.

- Two base constructors a, b: type-level re-expression of Axiom 1
  (distinguishing-yields-residue; the count-Lens reads this as
  "two"). → **(α) re-expression of the axiom**.
- Binary constructor slash: re-expression of Axiom 2 (pairing of
  distinguished items is itself a residue).  However at the Tree
  level, order exists (x, y argument positions distinguished) —
  resolved at the next stage by the quotient.  → **(α) +
  (β) temporary artifact (order)**.
- `deriving DecidableEq`: ensures executability of Axiom 4 ("x ≠ y"
  requirement).  Natural consequence of Axiom 4. →
  **(γ) derivation**.
- `deriving Repr`: pretty-print for debugging.  Mathematically
  irrelevant.  → hygiene.
- No-confusion principle (a ≠ b automatic): natural consequence of
  Axiom 1 ("primitive distinction"). → **(γ) derivation**.

**Verdict**: no (δ).

### §I.2.2 `Tree.cmp : Tree → Tree → Ordering`

Total-order comparison function.  a < b < slash_anything, slash
nodes compared recursively.

- The specific order choice (`a.cmp b = .lt`, etc.) is arbitrary.
  Other choices possible (e.g., b < a < slash).
- This choice has no mathematical meaning — it serves only as a
  selection function picking a **unique representative** from each
  equivalence class.
- Meta-theorem: if any two total orders cmp₁, cmp₂ induce the same
  equivalence (commutative-anti-reflexive), the resulting Raw types
  are isomorphic and all axiomatic theorems transport.

**Verdict**: **(β) Encoding artifact**.  Not (δ).

### §I.2.3 `Tree.canonical : Tree → Bool`

Predicate: are the two children of slash sorted in cmp order?

- `Tree.slash x y` is canonical ⟺ `cmp x y = .lt` and x, y are
  each canonical.
- A predicate dependent on the cmp choice; shares the fate of the
  cmp artifact.

**Verdict**: **(β) Encoding artifact** (derived from §I.2.2).

### §I.2.4 `Raw : Type := { t : Tree // t.canonical = true }`

Subtype: picks only canonical trees to emulate the quotient.

- Mathematically, Raw is the "symmetric quotient" of Tree — the
  set selecting the canonical representative from each
  equivalence class.
- Depends on the cmp choice, but the **global isomorphism class**
  is choice-independent.
- If a primitive quotient existed, a quotient could be used
  instead.  The limitation of Lean 4 core forces this workaround.

**Verdict**: **(β) Encoding artifact**.  Axiom-independent.

### §I.2.5 `Raw.slash (x y : Raw) (h : x ≠ y) : Raw`

Smart constructor.  Takes two Raw, canonicalizes, produces a new
Raw.

- Mandatory `h : x ≠ y` argument: type-level re-expression of
  Axiom 4 ("x/x is undefined").  **This is the axiom itself, not
  a choice.** → **(α)**.
- Internal canonicalize (rearranging children according to cmp):
  uses §I.2.2 artifact. → **(β)**.
- Result is of type Raw: re-expression of Axiom 2 (pairing result
  is also Raw). → **(α)**.

**Verdict**: (α) + (β).  No (δ).

### §I.2.6 `Raw.slash_comm` theorem

`Raw.slash x y h = Raw.slash y x (Ne.symm h)`.

- Proof of Axiom 3 ("pairing is symmetric") as a theorem.
- The proof shows that the canonicalize logic produces the same
  canonical form in both directions.  Depends on the swap property
  of cmp symmetry.

**Verdict**: **(γ) Derivation** — re-proves Axiom 3 atop canonical
form emulation.

### §I.2.7 `Raw.swap` (automorphism)

Exchange a ↔ b.  slash handled by structural recursion.

- Axiom 1 states "a, b have no relation other than not being
  equal."  This symmetry forces the automorphism.
- Therefore the **existence** of Raw.swap is a derivation of
  Axiom 1.
- The concrete implementation (swap children then re-canonicalize)
  is sub-artifact.

**Verdict**: **(γ) Derivation**.

### §I.2.8 `Raw.fold` (catamorphism)

`Raw.fold ba bb c r` = reduces r by structural recursion with
base_a→ba, base_b→bb, slash→c.

- A wrapper around the standard recursor of an inductive type.
  The elimination principle Lean automatically grants to inductive
  types.
- Mathematically "the unique morphism from the initial algebra to
  an arbitrary algebra" — not the axiom itself but **the means
  derived by the axiom**.
- Axiom conformance of fold's result ≠ axiom violation by fold
  itself.  (See §I.3.1.)

**Verdict**: **(γ) Derivation** (tool).

### §I.2.9 `Raw.rec` (custom eliminator)

Decorated with `@[elab_as_elim]`.  Forces Raw-layer pattern
matching via `induction r using Raw.rec`.

- Device to prevent Tree-layer exposure.  Using plain
  `induction r` falls back to the default `Subtype.mk` eliminator,
  exposing Tree.
- When using `Raw.rec`, cases are `a | b | slash x y h ihx ihy`.
- Mathematically: standard structural induction + subtype
  gymnastics.

**Verdict**: **(γ) Derivation** (tool).

---

## §I.3 Safeguard analysis

First, distinguish the **kinds** of safeguards:

- (i) **Type-level gate**: part of the signature.  To create a
  value, the gate must be satisfied.
- (ii) **Conditional precondition of a theorem**: theorem has the
  form `hyp → concl`.  If hyp fails, the theorem cannot be used,
  but the type system does not block it.
- (iii) **Doc warning**: a comment.  Not mechanically verified.
  Human hint.
- (iv) **Namespace / convention**: project convention using open,
  private, etc. in the module system.

Each kind is checked for whether it is (δ) additional commitment.

### §I.3.1 Type-level gates

Example: `Raw.slash (x y : Raw) (h : x ≠ y)`.

Without this gate, compilation fails.  Therefore it mechanically
enforces the axiom.  It is **a re-expression of the axiom itself
(§I.2.5)**, not an **addition**.

General principle:

> If a type-level gate has a 1:1 correspondence with an axiom
> clause, it is not (δ).  Adding a gate unrelated to any axiom
> clause would make it (δ) and it should fail the audit.

The only type-level gate in the current Theory is `h : x ≠ y`.
This is a literal translation of Axiom 4.  → **no (δ)**.

### §I.3.2 Conditional preconditions of theorems

Example: `hsym : ∀ u v, c u v = c v u` in `fold_slash`.

This precondition:

- **Makes the theorem selectively usable** — without hsym,
  fold_slash cannot be applied.
- **Does not add a condition to the axiom** — the axiom is still
  independent of fold.
- The theorem claims `IF hsym THEN conclusion`.  Without hsym, the
  conclusion does not hold — this is **the exact content of the
  theorem**, not the state of the axiom.

General principle:

> A theorem's precondition is part of the theorem's structure.
> It is not an additional constraint on the axiom.  When the
> theorem is not true without the precondition, the user simply
> must supply the precondition to use the theorem.

If a user writes a fold they cannot supply the precondition for →
fold itself executes, but its result **loses** axiomatic
properties (slash_comm preservation).  This is **not an axiom
violation — the user's Lens loses axiomatic meaning**.  A warning
about the user's Lens, not about the axiom.

→ **no (δ)**.

### §I.3.3 Doc warnings

Example: WARNING in `Fold.lean` — "using asymmetric combine causes
encoding artifact leak."

- Not mechanically verified.
- Referenced by human interpreters when making decisions.
- `lake build` result is identical whether or not the comment is
  removed.

→ **(iii) hygiene, no (δ)**.

### §I.3.4 Namespace / convention

Example: `E213.Theory.Internal` namespace, `private` modifier,
"Internal open forbidden" convention in CLAUDE.md.

- Lean 4 core is not a strict module system like Java / Haskell.
  `private` is a weak restriction (visible within the same file).
- `open Internal` is an explicit user import action.  Forbidden by
  convention only.
- Not mechanically verified.

→ **(iv) hygiene, no (δ)**.

### §I.3.5 Summary — safeguards do not add to the axiom

| Safeguard kind | Mathematical status | Adds commitment? |
|----------------|---------------------|------------------|
| Type-level gate (axiom-equivalent) | Re-expression of axiom | No |
| Conditional precondition of theorem | Part of theorem structure | No |
| Doc warning | Meta-syntactic hint | No |
| Namespace / convention | Meta-syntactic hint | No |

**Key observation**: **Removing** all safeguards still results in
Lean codebase compiling identically and proving identical
theorems.  What changes is only "the room for a user to
accidentally drag artifacts into a Lens."  Mathematical content is
invariant.

That is, **safeguards are usage hygiene, not mathematical
commitment**.

---

## §I.4 Corner cases: leak paths

The actual corner cases **to be concerned about** from an
axiom-compliance perspective are the 5 items below.  These are
**absences of safeguards**, not states of the axiom.  Summary:

| # | Path | Current state | Action |
|---|------|---------------|--------|
| A | `Raw.fold` asymmetric combine | Doc WARNING added | Introduce ValidLens predicate (future) |
| B | `Raw.rec` asymmetric slash handling | Doc WARNING added | Introduce ValidLens predicate (future) |
| C | Tree exposed via `.val` access | NOTATION.md convention done | none |
| D | `Internal` open convention | CLAUDE.md DO-NOT done | More aggressive use of private (future) |
| E | Absence of ValidLens predicate | Absent | Extend Lens/LensCore.lean (future) |

**Important**: Even if all 5 items are unaddressed, **the axiom is
not violated**.  It is merely that **a user's Lens may silently
import artifacts**.  If a user's Lens depends on artifacts, that
Lens is not a correct observation of Raw, but this is **the user's
Lens-choice problem, not a Raw axiom problem**.

---

## §I.5 Meta-theorem: cmp-independence (formalized)

To complete the argument, the following meta-theorem is needed:

> **Claim**: if any two total orders
> `cmp₁, cmp₂ : Tree → Tree → Ordering` induce the same
> "commutative-anti-reflexive equivalence" (i.e.,
> `Tree.slash x y ~ Tree.slash y x`, reflexive slash forbidden),
> then the two implementations `Raw_{cmp₁}`, `Raw_{cmp₂}` have a
> type-level isomorphism, and all public theorems of Theory
> transport through this isomorphism.

If this meta-theorem is formalized:

- It is mechanically verified that the specific cmp choice in
  Theory **has no effect on any axiomatic conclusion**.
- cmp being a choice external to the axiom is automatically
  proven.
- ValidLens predicate / symmetric combine requirement is revealed
  as the exact characterization of "Lenses invariant under cmp
  choice."

**Current status**: **Formalization complete**
(`Theory/Raw/CmpIndependence.lean`).

- Phase 1: `CmpProps` (eq_iff + swap) abstraction, `canonicalBy` /
  `RawBy` defined for arbitrary cmp.
- Phase 2-2.5: polymorphic `RawBy.slash` + `RawBy.slash_comm`
  (swap-invariance at the Raw level via slashTree commutativity).
- Phase 3-3.5: `transportTree` (computable Tree-level fold) and
  `transportRawBy` defined bidirectionally, `RawBy_bijection`
  formally proves RawBy cmp₁ ≃ RawBy cmp₂.

`#print axioms RawBy_bijection`: [propext] only —
Classical.choice absent.  `04_falsifiability.md` §8.2
falsifiability maintained.

Therefore the cmp choice in Theory is mechanically verified to
have **no effect on mathematical results**, and classification
(β) — that cmp is an outside choice of encoding — is formally
proven.

---

## §I.6 Boundary cases: axiom addition vs. derivation

Some boundary cases are subtle and require separate analysis.

### §I.6.1 No-confusion principle of Lean inductive

Lean automatically produces from `inductive Tree` declarations:

- `Tree.a ≠ Tree.b` (different constructors),
- `Tree.a ≠ Tree.slash _ _`, etc.

Is this an axiom or a derivation?

- Axiom 1 states "a, b stand in a primitive distinction
  relation."  Lean's `a ≠ b` is a literal translation. →
  **(α) re-expression of the axiom**.
- Lean's rule "different constructors of an inductive type are
  distinct" is consistent with Axiom 1, but strictly speaking it
  is an **axiom of Lean's meta-theory** (a type-theory
  fundamental).
- Does this Lean meta-theory axiom have priority over the 213
  axiom?  No.  The 213 axiom is **pre-linguistic** and Lean
  meta-theory is the layer for running the machine.  When the
  213 axiom records distinguishing-yields-residue (which the
  count-Lens reads as "two somethings have primitive distinction"),
  Lean's no-confusion is the means to put this on the machine —
  a parallel track, not an additional commitment.

**Verdict**: (α).  Lean meta-theory is imported, but only as the
minimum means to re-express the 213 axiom.

### §I.6.2 `DecidableEq Raw`

Axiom 4 requires "x ≠ y," so whether x = y must be decidable.
However, the axiom itself does not state "all Raw pairs are
decidably distinguishable."

- To make Axiom 4 **usable**, decidability is needed.  I.e.,
  (γ) derivation.
- The axiom itself does not require decidability, but **to
  actually use the axiom it is needed**.
- Lean's DecidableEq derives from the structural identity of
  Tree.  Tree is a finite-depth induction, so DecidableEq is
  automatic.

**Verdict**: **(γ) Derivation** — the executable form of
Axiom 4.

### §I.6.3 `noncomputable def Raw.rec`

The `noncomputable` modifier at Rec.lean lines 28, 68.

- `noncomputable` states that the function is used only in
  proofs, without compile-time code generation.
- A result of computation becoming complex because Raw.rec
  depends on Tree structure but the subtype proof is
  proof-relevant.
- Mathematically irrelevant.  Implementation convenience.

**Verdict**: Hygiene (iv), not (δ).

### §I.6.4 "Order" of `Tree` constructors

In `inductive Tree`, constructors are declared in the order
a, b, slash.  Does this declaration order have mathematical
meaning?

- Lean uses declaration order in no-confusion / rec structure,
  but mathematically a, b are **interchangeable** by Axiom 1 —
  swapping them leaves the axiom identical.
- Declaration order is an artifact.  Raw.swap is exactly the
  automorphism showing this exchange.

**Verdict**: (β) artifact.

---

## §I.7 Conclusion

### §I.7.1 Axiom faithfulness

The Lean implementation of Raw + Theory is a **faithful
emulator** of the axiom.  Classifying implementation devices:

- (α) Type-level re-expression of the axiom: Tree's a, b, slash
  constructors, `Raw.slash`'s `h : x ≠ y`.
- (β) Encoding artifact: Tree.cmp, Tree.canonical, Raw's subtype
  structure, canonicalize logic.
- (γ) Derivation: DecidableEq, slash_comm, Raw.swap, Raw.fold,
  Raw.rec, no-confusion consequences (a ≠ b, etc.).
- (δ) Additional commitment: **none**.

### §I.7.2 Status of safeguards

Every safeguard is one of the following:

- Type-level re-expression of the axiom (gate like h : x ≠ y).
- Conditional precondition of a theorem (hyp like hsym of
  fold_slash).
- Doc warning or namespace convention (meta-syntactic hygiene).

**Safeguards add no mathematical commitment.**  Removing them
leaves the Lean codebase compiling identically and proving the
same theorems.  Only the possibility of user misuse changes.

### §I.7.3 Open problems

- ~~cmp-independence meta-theorem formalization (§I.5)~~ —
  **completed** (CmpIndependence.lean, 2026-04-25).
- (future) Introduce ValidLens predicate (§I.4 E).
- (short-term) Lens-layer bleed migration — move Raw.depth,
  Raw.leaves, etc. to Lens (§I.4 Recommendation 3).
- (extension, completed) p-adic ℤ_p sub-tower formalization
  (`Lib/Math/NumberSystems/Hyper/Padic.lean`): leavesModNat sub-family + factorial
  seq instance.  ZFC reduction scope extended to number-theoretic
  limit territory.

All of these tasks are **safeguard reinforcement**, not axiom
changes.

---


(formerly seed/AUDIT_Lean.md)

**Audit target**: `lean/E213/Theory/`
**Reference**: `02_axiom.md` (the 4-clause axiom)
**Audit date**: 2026-04-24
**Overall verdict**: **Faithful**.  No structural revision required.
Three minor sanding items recommended.

---

## §9.1 Four-axiom cross-check

### Axiom 1: "Something exists.  At least two.  a, b.  Primitive distinction."

Lean implementation (`Theory/Raw/Core.lean`):

- `Raw.a : Raw := ⟨.a, rfl⟩` (line 60)
- `Raw.b : Raw := ⟨.b, rfl⟩` (line 61)
- `DecidableEq Raw` instance provided → "not equal" judgment
  available.

**Verdict**: ✓ Match.

### Axiom 2: "Pairing of two somethings is yet another something."

Lean implementation (`Theory/Raw/Slash.lean`):

- `Raw.slash (x y : Raw) (h : x ≠ y) : Raw` (line 20)
- Result is again Raw — closed.

**Verdict**: ✓ Match.

### Axiom 3: "Pairing is symmetric."

Lean implementation (`Theory/Raw/Slash.lean`):

- `Raw.slash_comm : Raw.slash x y h = Raw.slash y x (Ne.symm h)`
  (line 31)

**Verdict**: ✓ Match.

### Axiom 4: "No pairing with oneself."

Lean implementation:

- `Raw.slash` signature requires `h : x ≠ y` as mandatory
  argument.  → Calling with x = y is impossible by construction.
- `x ≠ y` is statically enforced by the Lean type system.

**Verdict**: ✓ Match.

---

## §9.2 Check for items "not in the axiom"

### Size / Cardinality / Finiteness / Infinity

Theory itself has no notion of size.  `leaves` and `depth` are
defined but these are **observation results** via `Raw.fold`, not
axioms.  The `Infinity/` module is also a separate folder
(outside Theory).

**Verdict**: ✓ Compliant.

### Order / Hierarchy / Ranking

**Caution point (A)**.  The Internal namespace contains
`Tree.cmp` (`Theory/Raw/Core.lean:23–36`).  This is an
**encoding device** for selecting canonical forms, not a
property of Raw — the ordering is the encoding's selection
function, not a property of the axiom.

→ **Recommendation 1**: State in `06_formalization.md` §7.1 that
"the Lean encoding uses canonical forms due to absence of
primitive quotient, and the ordering used there is an encoding
artifact, not an axiom."

**Verdict**: △ Matches but reinforcement done in §7.1.

### Set / Element / Membership

Lean 4 core's `inductive Tree` is not a ZFC set (type theory).
The `List Raw` in `RawLevels.lean` is a Lens-level enumeration;
acceptable even at the outside-Theory level.

**Verdict**: ✓ Compliant.

### Observer / Space / Perception / Structure / Geometry

Not present in Theory itself.  The `Lens` in Lens layer is a
separate module.

**Verdict**: ✓ Compliant.

### Mode of existence

Lean `inductive` is by definition compatible with either
Platonic or stepwise interpretation.  Companion narrative:
`research-notes/archive/17_existence_mode_lens.md`.  Current Lean
coverage: `lean/E213/Lens/Cardinality/Tower.lean` and
`lean/E213/Lens/Cardinality/Chain.lean`.

**Verdict**: ✓ Compliant.

### Associativity / distributivity / identity / inverse

`Raw.slash` guarantees only symmetry (Axiom 3) and
anti-reflexivity (Axiom 4).  Associativity, distributivity, etc.
**absent**.  If present, they belong at the Lens level.

**Verdict**: ✓ Compliant.

---

## §9.3 Theory content **beyond** the axiom

Not forbidden by the axiom, but utility content beyond the axiom
present in Theory — review required.

### Raw.fold (catamorphism)

Location: `Theory/Raw/Fold.lean`.  This is a wrapper around the
standard eliminator of an inductive type, serving as **the tool
for constructing all Lenses**, not a specific Lens.  Classified
as consumer utility.

**Verdict**: ✓ Accepted.  Theory location OK.

### Raw.swap (automorphism)

Location: `Theory/Raw/Swap.lean`.  Swap is directly **derived**
from Axiom 1 ("a, b have no relation other than not being
equal") — exchanging a ↔ b automatically becomes an
automorphism.  This is the first derivation.

**Caution point (B)**.  The axiom itself does not state that this
is "automatically derived from Axiom 1."  It appears in Paper 1
§2 (Symmetry of Raw) but a cross-reference is needed.

→ **Recommendation 2**: State in `04_falsifiability.md` or
`06_formalization.md` §7.2 that "Raw.swap is the first derivation
from Axiom 1."

**Verdict**: △ Accepted but reinforcement noted.

### Raw.depth, Raw.leaves

Location: `Theory/Raw/Slash.lean:52`,
`Theory/Raw/Levels.lean`.

**Caution point (C)**.  `depth` and `leaves` are observables of
specific Lenses (Lens.depth, Lens.leaves).  Their exposure in
Theory as `Raw.depth`, `Raw.leaves` is **Lens-layer bleed**.

`02_axiom.md` §3.3 excludes "size / cardinality" from the
axiom.  `Raw.leaves r` is **the observation result of a specific
Lens on that Raw**, so it should not reside at the axiom level.
The current location is strictly speaking incorrect.

Practically however:

- Internal `Tree.depth`, `Tree.leaves` are used in
  canonicality-related invariant proofs — must be kept Internal.
- Public `Raw.depth`, `Raw.leaves` should be **moved** to
  the Lens layer.

→ **Recommendation 3**: Move public declarations of `Raw.depth`,
`Raw.leaves` to the Lens layer.  Internal declarations
must be retained for canonicality proofs.

**Verdict**: ✗ Lens-layer bleed.  Migration noted.

### Raw.fold_eq_depth / leaves / signed_swap / swap_hom

Location: `Theory/Raw/FoldSwap.lean` (merged 2026-05-18 from
`Signed.lean` + `Hom.lean`).

These are "bridge theorems for reconstituting a specific Lens
via Raw.fold."  They are **Lens-level theorems** belonging in
Lens or Meta.

→ Migrate together with Recommendation 3.

**Verdict**: ✗ Lens-layer bleed.  Migration noted.

---

## §9.4 Overall verdict

**The Lean framework is a faithful implementation of the
axiom.**  No structural rewrite is required.  The existing 78
modules, 457 theorems, 0 sorry, 0 axiom can be maintained without
axiom updates.

### Three recommendations

1. **Reinforce `06_formalization.md` §7.1** — State explicitly
   that canonical forms / Tree.cmp in the Lean encoding are
   encoding artifacts, not axioms.  (5-minute task; done.)

2. **Reinforce `04_falsifiability.md` or `06_formalization.md`** —
   State that Raw.swap is the first derivation from Axiom 1.
   (5-minute task; done in `06_formalization.md` §7.1.)

3. **Lens-layer bleed migration** — Move public declarations of
   `Raw.depth`, `Raw.leaves`, `Raw.fold_eq_*`,
   `Raw.fold_signed_swap`, `Raw.fold_swap_hom` to Lens or
   Meta.  Retain Internal `Tree.*`.  (1-session task; downgraded
   to "acknowledged leak" per `06_formalization.md` §7.1.)

### What **not** to do

- **Do not change the form of the axiom itself.**  The current
  `Raw.a`, `Raw.b`, `Raw.slash (h : x ≠ y)`, `Raw.slash_comm`
  are a 1:1 translation of `02_axiom.md` §3.2.  This form
  must not be "upgraded" to the 3-element·2-operation form from
  ch22 (ch22 is a separate fudge issue).

- **Do not discard 78 modules and 457 theorems.**  After the
  migration in Recommendation 3, most are retained as-is.  The
  proof content itself need not change.

---

## §9.5 Deep audit: corner cases / safeguards (2nd pass)

The 1st audit focused on axiom cross-checking.  The 2nd asks
**"Can encoding artifacts leak into Lens output?"**

Raw is an abstract object as a quotient, independent of the
`Tree.cmp` choice, but since the Lean implementation uses
canonical forms, if user code accidentally depends on cmp, that
Lens will **carry encoding artifacts**.

### §9.5.1 Existing safeguards (pass)

| Device | Location | Effect |
|--------|----------|--------|
| Mandatory `h : x ≠ y` argument | `Raw.slash` signature | Static enforcement of anti-reflexivity |
| `Raw.slash_comm` theorem | Slash.lean | Formal proof of symmetry |
| `hsym` hypothesis in `fold_slash` | Fold.lean | Axiom-conforming results only with symmetric combine |
| 4 hypotheses in `fold_swap_hom` | FoldSwap.lean | Top-down congruence conforming only with symmetric+distributive |
| `Internal` namespace separation | Core.lean | Tree not exposed by `open E213.Theory` |
| Mathlib-free + 0 sorry | Project convention | Blocks import of external axioms |
| `@[elab_as_elim] Raw.rec` | Rec.lean | `induction` tactic forces Raw-layer eliminator |

These work in practice.  Scenarios where the **existence** of
canonical form contaminates Lens output are largely blocked by
these devices.

### §9.5.2 Insufficient safeguards (issues)

**(A) `Raw.fold` does not require combine symmetry — HIGH**

`Raw.fold ba bb combine r` type-checks even if `combine` is
**asymmetric**.  Using `Raw.fold` with such a `combine` makes
the result depend on the canonical ordering of Tree (= the cmp
choice).  This is a **silent leak** — something not in the
axiom (encoding artifact) leaking into Lens output.

`fold_slash` requires symmetry as a precondition, but that is
just a theorem; it does not prevent calling `Raw.fold` itself.
If a user constructs a Lens with an asymmetric combine, it works
without any warning, and the result is overcommitted relative to
the axiom.

**Recommendation A**: Add a warning to `Raw.fold`'s doc-string.
Or long-term, introduce a `Lens.valid` predicate to enforce
combine symmetry at the type level.

**(B) Order of `slash x y h` in `Raw.rec` — HIGH**

The slash branch of `Raw.rec` hands the user the pair `(x, y)`
in order.  This order originates from the canonical form — i.e.,
`cmp x y = .lt`.

If the user **treats x and y asymmetrically** in the slash
branch (e.g., `f x + 2 * g y`), the result depends on the cmp
choice.  Again a silent leak.

**Recommendation B**: Add a warning to `Raw.rec` doc-string:
"the slash branch must treat x, y symmetrically; otherwise the
result depends on encoding artifacts."  Or create an alternative
`Raw.rec_sym` requiring the motive to be swap-invariant.

**(C) `Subtype.val` access — LOW**

Using `r.val` exposes the underlying Tree.  In practice, every
Raw is canonical, so `.val` is the "unique representative" and
the leak is small.  However, using `.val` in Lens semantics
(e.g., `r.val.depth` instead of `Lens.depth.view r`) should be
avoided.

**Recommendation C**: Add to `seed/NOTATION.md`: "`.val` access
is for internal Theory proofs only; do not use in Lens
semantics."

**(D) Convention-dependence of `open E213.Theory.Internal` —
MEDIUM**

Lean 4 core has no strict visibility control (not a module
system).  A user can `open E213.Theory.Internal` from any
module to access Tree directly.

**Recommendation D**: Add to `CLAUDE.md` DO-NOT: "`open` of
`E213.Theory.Internal` is forbidden outside Theory internal
modules."  Or add a grep rule to CI.

**(E) Absence of `ValidLens` predicate / structure — MEDIUM (future)**

The current `Lens` only requires `⟨base_a, base_b, combine⟩`.
Combine symmetry / base symmetry / R1-R5 satisfaction are not
verified at Lens definition time.

**Recommendation E**: Introduce a `ValidLens` predicate in
`Lens/LensCore.lean`.  At minimum, make combine symmetry a
field.  All Lens declarations should be accompanied by a
validity proof.

### §9.5.3 Items that are **not** corner cases (already guarded)

- **Disguising a non-canonical Tree as Raw**: the subtype
  requires proof of `canonical = true`.  Cannot pass without
  `decide`.  OK.
- **Reflexive forms like `Tree.slash x x`**: canonical is false,
  so they cannot enter Raw.  OK.
- **Different canonical proofs recognized as the same Raw**:
  Lean's Subtype.ext handles this via proof-irrelevance.  OK.
- **Infinitely deep Raw**: inductive type is well-founded —
  every concrete Raw has finite depth.  Consistent with the
  axiom.  OK.
- **`Tree.a ≠ Tree.b` not derived from the axiom**: automatic
  via Lean inductive type's no-confusion principle.  Natural
  machine representation of Axiom 1 (primitive distinction).  OK.

### §9.5.4 Action priority

| # | Recommendation | Difficulty | Impact |
|---|----------------|------------|--------|
| A | Add symmetry-requirement warning to Raw.fold doc | 5 min | HIGH |
| B | Add symmetry-requirement warning to Raw.rec doc | 5 min | HIGH |
| D | Add Internal open prohibition to CLAUDE.md | 5 min | MEDIUM |
| C | Add `.val` prohibition to NOTATION.md | 5 min | LOW |
| 3 (§9.3) | Lens-layer bleed migration | 1 session | MEDIUM |
| E | Introduce ValidLens predicate | 1 session | MEDIUM (future) |

A, B, C, D can be applied immediately as doc additions.  3 and E
require code changes and need separate sessions.

---

## §9.6 Overall re-verdict (incorporating deep audit)

**Still Faithful, but 2 silent leak paths exist**.

The conclusion of the 1st audit (faithful to 4-clause axiom,
compliant with "absent items" list) is maintained.  The 2nd
audit additionally identifies **2 API surfaces** where Lens
output can silently depend on encoding artifacts (Raw.fold,
Raw.rec).  Mitigable by doc-level warnings.  Long-term,
type-level enforcement via a ValidLens predicate is recommended.

The structural consistency of 78 modules and 457 theorems is
unaffected.  Existing Lenses (Lens.depth, Lens.leaves,
signedLens, etc.) all use **symmetric combine** and are already
leak-free — verified (the `fold_slash` proof in Fold.lean uses
their symmetry).

**The vulnerability manifests only when a future user constructs
an asymmetric Lens.**  Doc warnings are sufficient to prevent
this.
