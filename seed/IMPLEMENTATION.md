# IMPLEMENTATION.md — Raw + Firmware implementation audit study

## Abstract

This document structurally demonstrates that the Raw framework implemented
in `lean/E213/Firmware/` is a **faithful emulator** of the `AXIOM.md`
axiom.  Specifically:

1. Each implementation device in Lean 4 core (inductive type, subtype,
   canonical form, smart constructor, custom eliminator) is classified as
   either axiom addition, encoding artifact, or derivation.

2. Each safeguard (type gate, theorem precondition, doc warning, namespace
   convention) is analyzed for whether it **adds mathematical commitment**.

   **Conclusion: no additional commitment.**  Safeguards fall into one of:
   - (i) type-level re-expression of an axiom clause,
   - (ii) conditional precondition of a theorem (the theorem itself is
     conditional),
   - (iii) meta-syntactic hygiene (preventing human misuse).

3. Analysis of the API surfaces (Raw.fold, Raw.rec) where encoding artifacts
   can leak into Lens output, and the current mitigation state.

Related documents: `AXIOM.md`, `AUDIT_Lean.md`.

---

## §1. Problem statement

The `AXIOM.md` axiom consists of 4 clauses (§3.2).  Since Lean 4 core has
no primitive quotient, several implementation devices are introduced in the
process of putting this axiom on a machine:

- `inductive Tree | a | b | slash (x y : Tree)` — ordered free magma.
- `Tree.cmp : Tree → Tree → Ordering` — total order, canonical form selector.
- `Tree.canonical : Tree → Bool` — normal-form predicate.
- `Raw : Type := { t : Tree // t.canonical = true }` — subtype.
- `Raw.slash (x y : Raw) (h : x ≠ y) : Raw` — smart constructor
  (auto-canonicalize).

For each device, the following must be determined:

(α) **Type-level re-expression of the axiom** — mechanical translation of
    the axiom itself.
(β) **Encoding artifact** — technique to work around the limitation of
    Lean 4 core (absence of primitive quotient).  Different choices are
    possible; the internal representation changes with choice but the
    mathematical meaning of Raw is invariant.
(γ) **Derivation** — a fact that automatically follows from the axiom.
(δ) **Additional axiom / constraint** — a new commitment not in the axiom.

If (δ) is found, it constitutes an axiom violation.

---

## §2. Classification of implementation devices

### §2.1 `inductive Tree | a | b | slash`

Lean inductive type.  Two nullary constructors + one binary constructor.

- Two base constructors a, b: type-level re-expression of Axiom 1
  ("two somethings"). → **(α) re-expression of the axiom**.
- Binary constructor slash: re-expression of Axiom 2 ("pairing of two
  somethings is yet another something").  However at the Tree level, order
  exists (x, y argument positions distinguished) — resolved at the next
  stage by the quotient.
  → **(α) re-expression + (β) temporary artifact (order)**.
- `deriving DecidableEq`: ensures executability of Axiom 4 ("x ≠ y"
  requirement).  Natural consequence of Axiom 4. → **(γ) derivation**.
- `deriving Repr`: pretty-print for debugging.  Mathematically irrelevant.
  → hygiene.
- No-confusion principle (a ≠ b automatic): natural consequence of
  Axiom 1 ("primitive distinction"). → **(γ) derivation**.

**Verdict**: no (δ).

### §2.2 `Tree.cmp : Tree → Tree → Ordering`

Total-order comparison function.  a < b < slash_anything, slash nodes
compared recursively.

- The specific order choice (`a.cmp b = .lt`, etc.) is arbitrary.
  Other choices are possible (e.g., b < a < slash).
- This choice has no mathematical meaning — it serves only as a
  selection function picking a **unique representative** from each
  equivalence class.
- Meta-theorem (not yet formalized): if any two total orders cmp₁, cmp₂
  induce the same equivalence (commutative-anti-reflexive), the resulting
  Raw types are isomorphic and all axiomatic theorems transport.

**Verdict**: **(β) Encoding artifact**.  Not (δ).

### §2.3 `Tree.canonical : Tree → Bool`

Predicate: are the two children of slash sorted in cmp order?

- `Tree.slash x y` is canonical ⟺ `cmp x y = .lt` and x, y are each
  canonical.
- A predicate dependent on the cmp choice; shares the fate of the cmp
  artifact.

**Verdict**: **(β) Encoding artifact** (derived from §2.2).

### §2.4 `Raw : Type := { t : Tree // t.canonical = true }`

Subtype: picks only canonical trees to emulate the quotient.

- Mathematically, Raw is the "symmetric quotient" of Tree — the set
  selecting the canonical representative from each equivalence class.
- Depends on the cmp choice, but the **global isomorphism class** (Raw
  types under different cmp choices are isomorphic) is choice-independent.
- If a primitive quotient existed, a quotient could be used instead.
  The limitation of Lean 4 core forces this workaround.

**Verdict**: **(β) Encoding artifact**.  Axiom-independent.

### §2.5 `Raw.slash (x y : Raw) (h : x ≠ y) : Raw`

Smart constructor.  Takes two Raw, canonicalizes, produces a new Raw.

- Mandatory `h : x ≠ y` argument: type-level re-expression of Axiom 4
  ("x/x is undefined").  **This is the axiom itself, not a choice.**
  → **(α)**.
- Internal canonicalize (rearranging children according to cmp):
  uses §2.2 artifact. → **(β)**.
- Result is of type Raw: re-expression of Axiom 2 (pairing result is
  also Raw). → **(α)**.

**Verdict**: (α) + (β).  No (δ).

### §2.6 `Raw.slash_comm` theorem

`Raw.slash x y h = Raw.slash y x (Ne.symm h)`.

- Proof of Axiom 3 ("pairing is symmetric") as a theorem.
- The proof shows that the canonicalize logic produces the same canonical
  form in both directions.  Depends on the swap property of cmp symmetry.

**Verdict**: **(γ) Derivation** — re-proves Axiom 3 atop canonical
form emulation.

### §2.7 `Raw.swap` (automorphism)

Exchange a ↔ b.  slash handled by structural recursion.

- Axiom 1 states "a, b have no relation other than not being equal."
  This symmetry forces the automorphism.
- Therefore the **existence** of Raw.swap is a derivation of Axiom 1.
- The concrete implementation (swap children then re-canonicalize) is
  sub-artifact.

**Verdict**: **(γ) Derivation**.

### §2.8 `Raw.fold` (catamorphism)

`Raw.fold ba bb c r` = reduces r by structural recursion with
base_a→ba, base_b→bb, slash→c.

- A wrapper around the standard recursor of an inductive type.  The
  elimination principle Lean automatically grants to inductive types.
- Mathematically "the unique morphism from the initial algebra to an
  arbitrary algebra" — not the axiom itself but **the means derived by
  the axiom**.
- Axiom conformance of fold's result ≠ axiom violation by fold itself.
  (See §3.1.)

**Verdict**: **(γ) Derivation** (tool).

### §2.9 `Raw.rec` (custom eliminator)

Decorated with `@[elab_as_elim]`.  Forces Raw-layer pattern matching
via `induction r using Raw.rec`.

- Device to prevent Tree-layer exposure.  Using plain `induction r`
  falls back to the default `Subtype.mk` eliminator, exposing Tree.
- When using `Raw.rec`, cases are `a | b | slash x y h ihx ihy`.
- Mathematically: standard structural induction + subtype gymnastics.

**Verdict**: **(γ) Derivation** (tool).

---

## §3. Safeguard analysis

First, distinguish the **kinds** of safeguards:

- (i) **Type-level gate**: part of the signature.  To create a value,
  the gate must be satisfied.
- (ii) **Conditional precondition of a theorem**: theorem has the form
  `hyp → concl`.  If hyp fails, the theorem cannot be used, but the type
  system does not block it.
- (iii) **Doc warning**: a comment.  Not mechanically verified.  Human hint.
- (iv) **Namespace / convention**: project convention using open, private,
  etc. in the module system.

Each kind is checked for whether it is (δ) additional commitment.

### §3.1 Type-level gates

Example: `Raw.slash (x y : Raw) (h : x ≠ y)`.

Without this gate, compilation fails.  Therefore it mechanically enforces
the axiom.  It is **a re-expression of the axiom itself (§2.5)**, not an
**addition**.

General principle:

> If a type-level gate has a 1:1 correspondence with an axiom clause,
> it is not (δ).  Adding a gate unrelated to any axiom clause would make
> it (δ) and it should fail the audit.

The only type-level gate in the current Firmware is `h : x ≠ y`.
This is a literal translation of Axiom 4.  → **no (δ)**.

### §3.2 Conditional preconditions of theorems

Example: `hsym : ∀ u v, c u v = c v u` in `fold_slash`.

This precondition:
- **Makes the theorem selectively usable** — without hsym,
  fold_slash cannot be applied.
- **Does not add a condition to the axiom** — the axiom is still
  independent of fold.
- The theorem claims `IF hsym THEN conclusion`.  Without hsym, the
  conclusion does not hold — this is **the exact content of the theorem**,
  not the state of the axiom.

General principle:

> A theorem's precondition is part of the theorem's structure.
> It is not an additional constraint on the axiom.  When the theorem
> is not true without the precondition, the user simply must supply
> the precondition to use the theorem.

If a user writes a fold they cannot supply the precondition for → fold
itself executes, but its result **loses** axiomatic properties
(slash_comm preservation).  This is **not an axiom violation — the
user's Lens loses axiomatic meaning**.  A warning about the user's
Lens, not about the axiom.

→ **no (δ)**.

### §3.3 Doc warnings

Example: WARNING in `Fold.lean` — "using asymmetric combine causes
encoding artifact leak."

- Not mechanically verified.
- Referenced by human interpreters when making decisions.
- `lake build` result is identical whether or not the comment is removed.

→ **(iii) hygiene, no (δ)**.

### §3.4 Namespace / convention

Example: `E213.Firmware.Internal` namespace, `private` modifier,
"Internal open forbidden" convention in CLAUDE.md.

- Lean 4 core is not a strict module system like Java / Haskell.
  `private` is a weak restriction (visible within the same file).
- `open Internal` is an explicit user import action.
  Forbidden by convention only.
- Not mechanically verified.

→ **(iv) hygiene, no (δ)**.

### §3.5 Summary — safeguards do not add to the axiom

| Safeguard kind | Mathematical status | Adds commitment? |
|----------------|---------------------|------------------|
| Type-level gate (axiom-equivalent) | Re-expression of axiom | No |
| Conditional precondition of theorem | Part of theorem structure | No |
| Doc warning | Meta-syntactic hint | No |
| Namespace / convention | Meta-syntactic hint | No |

**Key observation**: **Removing** all safeguards still results in
Lean codebase compiling identically and proving identical theorems.
What changes is only "the room for a user to accidentally drag artifacts
into a Lens."  Mathematical content is invariant.

That is, **safeguards are usage hygiene, not mathematical commitment**.

---

## §4. Corner cases: leak paths

The actual corner cases **to be concerned about** from an axiom-compliance
perspective are the 5 items in `AUDIT_Lean.md` §5.2.  These are **absences
of safeguards**, not states of the axiom.  Summary:

| # | Path | Current state | Action |
|---|------|---------------|--------|
| A | `Raw.fold` asymmetric combine | Doc WARNING added | Introduce ValidLens predicate (future) |
| B | `Raw.rec` asymmetric slash handling | Doc WARNING added | Introduce ValidLens predicate (future) |
| C | Tree exposed via `.val` access | NOTATION.md convention done | none |
| D | `Internal` open convention | CLAUDE.md DO-NOT done | More aggressive use of private (future) |
| E | Absence of ValidLens predicate | Absent | Extend Hypervisor/Lens.lean (future) |

**Important**: Even if all 5 items are unaddressed, **the axiom is not
violated**.  It is merely that **a user's Lens may silently import artifacts**.
If a user's Lens depends on artifacts, that Lens is not a correct observation
of Raw, but this is **the user's Lens-choice problem, not a Raw axiom problem**.

---

## §5. Meta-theorem: cmp-independence (future formalization)

To complete the argument, the following meta-theorem is needed:

> **Claim**: if any two total orders `cmp₁, cmp₂ : Tree → Tree → Ordering`
> induce the same "commutative-anti-reflexive equivalence" (i.e.,
> `Tree.slash x y ~ Tree.slash y x`, reflexive slash forbidden), then
> the two implementations `Raw_{cmp₁}`, `Raw_{cmp₂}` have a type-level
> isomorphism, and all public theorems of Firmware transport through this
> isomorphism.

If this meta-theorem is formalized:

- It is mechanically verified that the specific cmp choice in Firmware
  **has no effect on any axiomatic conclusion**.
- cmp being a choice external to the axiom is automatically proven.
- ValidLens predicate / symmetric combine requirement is revealed as the
  exact characterization of "Lenses invariant under cmp choice."

**Current status**: **Formalization complete** (`Research/CmpIndependence.lean`).

- Phase 1: `CmpProps` (eq_iff + swap) abstraction, `canonicalBy` /
  `RawBy` defined for arbitrary cmp.
- Phase 2-2.5: polymorphic `RawBy.slash` + `RawBy.slash_comm`
  (swap-invariance at the Raw level via slashTree commutativity).
- Phase 3-3.5: `transportTree` (computable Tree-level fold) and
  `transportRawBy` defined bidirectionally, `RawBy_bijection` formally
  proves RawBy cmp₁ ≃ RawBy cmp₂.

`#print axioms RawBy_bijection`: [propext] only — Classical.choice
absent.  AXIOM §5.2.1 falsifiability maintained.

Therefore the cmp choice in Firmware is mechanically verified to have
**no effect on mathematical results**, and classification (β) — that cmp
is an outside choice of encoding — is formally proven.

---

## §6. Boundary cases: axiom addition vs. derivation (subtle points)

Some boundary cases are subtle and require separate analysis.

### §6.1 No-confusion principle of Lean inductive

Lean automatically produces from `inductive Tree` declarations:
- `Tree.a ≠ Tree.b` (different constructors),
- `Tree.a ≠ Tree.slash _ _`, etc.

Is this an axiom or a derivation?

Analysis:
- Axiom 1 states "a, b stand in a primitive distinction relation."
  Lean's `a ≠ b` is a literal translation. → **(α) re-expression of the axiom**.
- Lean's rule "different constructors of an inductive type are distinct"
  is consistent with Axiom 1, but strictly speaking it is an **axiom of
  Lean's meta-theory** (a type-theory fundamental).
- Does this Lean meta-theory axiom have priority over the 213 axiom?
  No.  The 213 axiom is **pre-linguistic** and Lean meta-theory is the
  layer for running the machine.  When the 213 axiom says "two somethings
  have primitive distinction," Lean's no-confusion is the means to put
  this idea on the machine — a parallel track, not an additional commitment.

**Verdict**: (α).  Lean meta-theory is imported, but only as the minimum
means to re-express the 213 axiom.

### §6.2 `DecidableEq Raw`

Axiom 4 requires "x ≠ y," so whether x = y must be decidable.
However, the axiom itself does not state "all Raw pairs are decidably
distinguishable."

Analysis:
- To make Axiom 4 **usable**, decidability is needed.  I.e., (γ) derivation.
- The axiom itself does not require decidability, but **to actually use
  the axiom it is needed**.
- Lean's DecidableEq derives from the structural identity of Tree.
  Tree is a finite-depth induction, so DecidableEq is automatic.

**Verdict**: **(γ) Derivation** — the executable form of Axiom 4.

### §6.3 `noncomputable def Raw.rec`

The `noncomputable` modifier at Rec.lean lines 28, 68.

Analysis:
- `noncomputable` states that the function is used only in proofs,
  without compile-time code generation.
- A result of computation becoming complex because Raw.rec depends on
  Tree structure but the subtype proof is proof-relevant.
- Mathematically irrelevant.  Implementation convenience.

**Verdict**: Hygiene (iv), not (δ).

### §6.4 "Order" of `Tree` constructors

In `inductive Tree`, constructors are declared in the order a, b, slash.
Does this declaration order have mathematical meaning?

Analysis:
- Lean uses declaration order in no-confusion / rec structure, but
  mathematically a, b are **interchangeable** by Axiom 1 — swapping
  them leaves the axiom identical.
- Declaration order is an artifact.  Raw.swap is exactly the
  automorphism showing this exchange.

**Verdict**: (β) artifact.

---

## §7. Conclusion

### §7.1 Axiom faithfulness

The Lean implementation of Raw + Firmware is a **faithful
emulator** of the `AXIOM.md` axiom.  Classifying implementation devices:

- (α) Type-level re-expression of the axiom: Tree's a, b, slash constructors,
  `Raw.slash`'s `h : x ≠ y`.
- (β) Encoding artifact: Tree.cmp, Tree.canonical, Raw's
  subtype structure, canonicalize logic.
- (γ) Derivation: DecidableEq, slash_comm, Raw.swap, Raw.fold,
  Raw.rec, no-confusion consequences (a ≠ b, etc.).
- (δ) Additional commitment: **none**.

### §7.2 Status of safeguards

Every safeguard is one of the following:

- Type-level re-expression of the axiom (gate like h : x ≠ y).
- Conditional precondition of a theorem (hyp like hsym of fold_slash).
- Doc warning or namespace convention (meta-syntactic hygiene).

**Safeguards add no mathematical commitment.**
Removing them leaves the Lean codebase compiling identically and
proving the same theorems.  Only the possibility of user misuse changes.

### §7.3 Open problems

- ~~cmp-independence meta-theorem formalization (§5)~~ — **completed**
  (CmpIndependence.lean, 2026-04-25).
- (future) Introduce ValidLens predicate (§4 E).
- (short-term) Lens-layer bleed migration — move Raw.depth,
  Raw.leaves, etc. to Hypervisor (§4, AUDIT_Lean §3 Recommendation 3).
- (extension, completed) p-adic ℤ_p sub-tower formalization
  (`Research/Hyper/Padic.lean`): leavesModNat sub-family
  + factorial seq instance.  ZFC reduction scope extended to
  number-theoretic limit territory.

All of these tasks are **safeguard reinforcement**, not axiom changes.

---

## Change history

- 2026-04-24: Initial draft.  Session
  `claude/lean-infinity-explanation-QqnSp`.
- 2026-05-XX: §7.3 path correction (`Research/Padic.lean` →
  `Research/Hyper/Padic.lean` after the Research/Hyper/ sub-cluster
  split).  No content changes — implementation classification (α/β/γ/δ)
  is unaffected by sub-cluster reorganization.

  Companion theoretical context now in `lean/E213/ARCHITECTURE.md`:
  - Firmware layer scope (Raw + Atomicity sub-cluster);
  - Hypervisor layer scope (Lens framework + sub-clusters Instances,
    Characterisation);
  - Recommendation 3 (Lens-layer bleed migration) is **deprioritized**
    — see `AXIOM.md §7.1` for current status.

## Author

- Author: **Mingu Jeong only**.  Claude in Acknowledgments.
- Implementation study.  Not a research paper; an audit document.
