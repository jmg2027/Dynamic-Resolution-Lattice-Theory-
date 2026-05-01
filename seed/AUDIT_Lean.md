# AUDIT_Lean.md — Lean framework × AXIOM.md cross-check

**Audit target**: `lean/E213/Firmware/`
**Reference document**: `AXIOM.md` (2026-04-24)
**Audit date**: 2026-04-24
**Overall verdict**: **Faithful**.  No structural revision required.
Three minor sanding items recommended.

---

## §1. Four-axiom cross-check

### Axiom 1: "Something exists.  At least two.  a, b.  Primitive distinction."

Lean implementation (`Firmware/Raw/Core.lean`):
- `Raw.a : Raw := ⟨.a, rfl⟩` (line 60)
- `Raw.b : Raw := ⟨.b, rfl⟩` (line 61)
- `DecidableEq Raw` instance provided → "not equal" judgment available.

**Verdict**: ✓ Match.

### Axiom 2: "Pairing of two somethings is yet another something."

Lean implementation (`Firmware/Raw/Slash.lean`):
- `Raw.slash (x y : Raw) (h : x ≠ y) : Raw` (line 20)
- Result is again Raw — closed.

**Verdict**: ✓ Match.

### Axiom 3: "Pairing is symmetric."

Lean implementation (`Firmware/Raw/Slash.lean`):
- `Raw.slash_comm : Raw.slash x y h = Raw.slash y x (Ne.symm h)`
  (line 31)

**Verdict**: ✓ Match.

### Axiom 4: "No pairing with oneself."

Lean implementation:
- `Raw.slash` signature requires `h : x ≠ y` as mandatory argument.
  → Calling with x = y is impossible by construction.
- `x ≠ y` is statically enforced by the Lean type system.

**Verdict**: ✓ Match.

---

## §2. Check for items "not in the axiom"

### Size / Cardinality / Finiteness / Infinity

Firmware itself has no notion of size.  `leaves` and `depth` are defined
but these are **observation results** via `Raw.fold`, not axioms.  The `Infinity/`
module is also a separate folder (outside Firmware).

**Verdict**: ✓ Compliant.

### Order / Hierarchy / Ranking

**Caution point (A)**.  The Internal namespace contains `Tree.cmp`
(`Firmware/Raw/Core.lean:23–36`).  This is an **encoding device** for
selecting canonical forms, not a property of Raw.  PAPER1.md
(archival) §1.2 already states *"the ordering is the encoding's selection
function, not a property of the axiom"*.

However, this point is not stated in AXIOM.md.
→ **Recommendation 1**: Add to AXIOM.md §7.1 that "the Lean encoding uses canonical
forms due to absence of primitive quotient, and the ordering used there is an
encoding artifact, not an axiom."

**Verdict**: △ Matches but AXIOM.md update needed.

### Set / Element / Membership

Lean 4 core's `inductive Tree` is not a ZFC set (type
theory).  The `List Raw` in `RawLevels.lean` is a Lens-level
enumeration; acceptable even at the outside-Firmware level.

**Verdict**: ✓ Compliant.

### Observer / Space / Perception / Structure / Geometry

Not present in Firmware itself.  The `Lens` in Hypervisor is a separate module.

**Verdict**: ✓ Compliant.

### Mode of existence

Lean `inductive` is by definition compatible with either Platonic or stepwise
interpretation.  Companion narrative: `research-notes/17_existence_mode_lens.md`.
Current Lean coverage: `lean/E213/Infinity/Tower.lean`,
`lean/E213/Infinity/Chain.lean`, and `lean/E213/Physics/Foundations/FiniteUniverse.lean`.

**Verdict**: ✓ Compliant.

### Associativity / distributivity / identity / inverse of operations

`Raw.slash` guarantees only symmetry (Axiom 3) and anti-reflexivity (Axiom 4).
Associativity, distributivity, etc. **absent**.  If present, they belong at the
Lens level (e.g., Research/LipschitzLens).

**Verdict**: ✓ Compliant.

---

## §3. Firmware content **beyond** the axiom

Not forbidden by AXIOM.md, but utility content beyond the axiom present in
Firmware — review required.

### Raw.fold (catamorphism)

Location: `Firmware/Raw/Fold.lean`.  This is a wrapper around the standard
eliminator of an inductive type, serving as **the tool for constructing all
Lenses**, not a specific Lens.  Classified as consumer utility.

**Verdict**: ✓ Accepted.  Firmware location OK.

### Raw.swap (automorphism)

Location: `Firmware/Raw/Swap.lean`.  Swap is directly **derived** from
Axiom 1 ("a, b have no relation other than not being equal") — exchanging
a ↔ b automatically becomes an automorphism.  This is the first derivation.

**Caution point (B)**.  AXIOM.md does not state that this is "automatically
derived from Axiom 1."  It appears in Paper 1 §2 (Symmetry of Raw) but
a cross-reference in AXIOM.md is needed.
→ **Recommendation 2**: Add to AXIOM.md §5 or §7.2 that "Raw.swap is the
first derivation from Axiom 1."

**Verdict**: △ Accepted but AXIOM.md reinforcement needed.

### Raw.depth, Raw.leaves

Location: `Firmware/Raw/Slash.lean:52`, `Firmware/Raw/Levels.lean`.

**Caution point (C)**.  `depth` and `leaves` are observables of specific Lenses
(Lens.depth, Lens.leaves).  Their exposure in Firmware as `Raw.depth`,
`Raw.leaves` is **Lens-layer bleed**.

AXIOM.md §3.3 excludes "size / cardinality" from the axiom.
`Raw.leaves r` is **the observation result of a specific Lens on that Raw**,
so it should not reside at the axiom level.  The current location is strictly
speaking incorrect.

Practically however:
- Internal `Tree.depth`, `Tree.leaves` are used in canonicality-related
  invariant proofs — must be kept Internal.
- Public `Raw.depth`, `Raw.leaves` should be **moved** to Hypervisor.

→ **Recommendation 3**: Move public declarations of `Raw.depth`, `Raw.leaves`
to the Hypervisor layer.  Internal declarations must be retained for
canonicality proofs.

**Verdict**: ✗ Lens-layer bleed.  Migration needed.

### Raw.fold_eq_depth / fold_eq_leaves / fold_signed_swap / fold_swap_hom

Location: `Firmware/Raw/Signed.lean`, `Firmware/Raw/Hom.lean`.

These are "bridge theorems for reconstituting a specific Lens via Raw.fold."
They are **Lens-level theorems** belonging in Hypervisor or Meta.

→ Migrate together with Recommendation 3.

**Verdict**: ✗ Lens-layer bleed.  Migration needed.

---

## §4. Overall verdict

**The Lean framework is a faithful implementation of the AXIOM.md axiom.**
No structural rewrite is required.  The first two weeks of work (78 modules,
457 theorems, 0 sorry, 0 axiom) can be maintained without axiom updates.

### Three recommendations (in priority order)

1. **Reinforce AXIOM.md §7.1** — State explicitly that canonical
   forms / Tree.cmp in the Lean encoding are encoding artifacts, not axioms.
   (5-minute task.)

2. **Reinforce AXIOM.md §5 or §7** — State that Raw.swap is
   the first derivation from Axiom 1.  (5-minute task.)

3. **Lens-layer bleed migration** — Move public declarations of `Raw.depth`,
   `Raw.leaves`, `Raw.fold_eq_*`, `Raw.fold_signed_swap`, `Raw.fold_swap_hom`
   to Hypervisor or Meta.  Retain Internal `Tree.*`.
   (1-session task.  Cascading `import` changes required.)

Recommendations 1 and 2 are AXIOM.md document updates.  Recommendation 3 is
a Lean refactor requiring `lake build` to be re-run.

### What **not** to do

- **Do not change the form of the axiom itself.**  The current `Raw.a`, `Raw.b`,
  `Raw.slash (h : x ≠ y)`, `Raw.slash_comm` are a 1:1 translation of AXIOM.md §3.2.
  This form must not be "upgraded" to the 3-element·2-operation form from ch22
  (ch22 is a separate fudge issue).

- **Do not discard 78 modules and 457 theorems.**  After the migration in
  Recommendation 3, most are retained as-is.  The proof content itself need
  not change.

### Next steps (status as of 2026-05-XX)

- ~~Step 3: Replace PAPER.md §1 with AXIOM.md.  Split §2-§4 (R1-R5 + ℂ)
  into a separate paper.~~ — **superseded**: PAPER.md / PAPER2.md deleted
  (see `AXIOM.md §7.2`); AXIOM.md is now the sole axiom document, and the
  R1-R5 → ℂ derivation chain has not been re-built (see `AXIOM.md §9.4`).
- ~~Step 4: `book/AUDIT.md` — Audit ch01-ch21.~~ — **superseded**:
  `book/` no longer contains chapter sources (only README.md retained);
  audit role transferred to `guide/` (deductively-ordered narrative)
  and `lean/E213/ARCHITECTURE.md` (canonical theory architecture).

---

## Change history

- 2026-04-24: Initial audit.  Session
  `claude/lean-infinity-explanation-QqnSp`.
- 2026-05-XX: Stale-reference cleanup.  PAPER.md → PAPER1.md (archival);
  `Infinity/notes/17_existence_mode_lens.md` → `research-notes/17_existence_mode_lens.md`
  (renamed/relocated, not deleted); §3 Steps 3/4 deprecated (book/,
  papers/ deleted; superseded by AXIOM.md + guide/ + ARCHITECTURE.md).
  Audit verdict (faithful, no structural revision) is unchanged.

## Author

- Audit by: Claude (Anthropic), under Mingu Jeong's direction.

---

## §5. Deep audit: Corner cases / safeguards (2nd pass, 2026-04-24)

The 1st audit focused on axiom cross-checking.  The 2nd asks
**"Can encoding artifacts leak into Lens output?"**

Raw is an abstract object as a quotient, independent of the `Tree.cmp` choice,
but since the Lean implementation uses canonical forms, if user code accidentally
depends on cmp, that Lens will **carry encoding artifacts**.

### §5.1 Existing safeguards (pass)

| Device | Location | Effect |
|--------|----------|--------|
| Mandatory `h : x ≠ y` argument | `Raw.slash` signature | Static enforcement of anti-reflexivity |
| `Raw.slash_comm` theorem | Slash.lean | Formal proof of symmetry |
| `hsym` hypothesis in `fold_slash` | Fold.lean | Axiom-conforming results only with symmetric combine |
| 4 hypotheses in `fold_swap_hom` | Hom.lean | Top-down congruence conforming only with symmetric+distributive |
| `Internal` namespace separation | Core.lean | Tree not exposed by `open E213.Firmware` |
| Mathlib-free + 0 sorry | Project convention | Blocks import of external axioms |
| `@[elab_as_elim] Raw.rec` | Rec.lean | `induction` tactic forces Raw-layer eliminator |

These work in practice.  Scenarios where the **existence** of canonical form
contaminates Lens output are largely blocked by these devices.

### §5.2 Insufficient safeguards (issues)

#### (A) **`Raw.fold` does not require combine symmetry** — HIGH

`Raw.fold ba bb combine r` type-checks even if `combine` is **asymmetric**.
Using `Raw.fold` with such a `combine` makes the result depend on the
canonical ordering of Tree (= the cmp choice).
This is a **silent leak** — something not in the axiom (encoding artifact)
leaking into Lens output.

`fold_slash` requires symmetry as a precondition, but that is just a theorem;
it does not prevent calling `Raw.fold` itself.  If a user constructs a Lens
with an asymmetric combine, it works without any warning, and the result is
overcommitted relative to the axiom.

**Recommendation A**: Add a warning to `Raw.fold`'s doc-string.  Or
long-term, introduce a `Lens.valid` predicate to enforce combine symmetry
at the type level.

#### (B) **Order of `slash x y h` in `Raw.rec`** — HIGH

The slash branch of `Raw.rec` hands the user the pair `(x, y)` in order.
This order originates from the canonical form — i.e., `cmp x y = .lt`.

If the user **treats x and y asymmetrically** in the slash branch
(e.g., `f x + 2 * g y`), the result depends on the cmp choice.
Again a silent leak.

**Recommendation B**: Add a warning to `Raw.rec` doc-string: "the slash
branch must treat x, y symmetrically; otherwise the result depends on
encoding artifacts."  Or create an alternative `Raw.rec_sym` requiring
the motive to be swap-invariant.

#### (C) **`Subtype.val` access** — LOW

Using `r.val` exposes the underlying Tree.  In practice,
every Raw is canonical, so `.val` is the "unique representative"
and the leak is small.  However, using `.val` in Lens semantics
(e.g., `r.val.depth` instead of `Lens.depth.view r`) should be avoided.

**Recommendation C**: Add to `NOTATION.md`: "`.val` access is for internal
Firmware proofs only; do not use in Lens semantics."

#### (D) **Convention-dependence of `open E213.Firmware.Internal`** — MEDIUM

Lean 4 core has no strict visibility control (not a module system).
A user can `open E213.Firmware.Internal` from any module to access
Tree directly.

**Recommendation D**: Add to `CLAUDE.md` DO-NOT: "`open` of
`E213.Firmware.Internal` is forbidden outside Firmware internal modules."
Or add a grep rule to CI.

#### (E) **Absence of `ValidLens` predicate / structure** — MEDIUM (future)

The current `Lens` only requires `⟨base_a, base_b, combine⟩`.  Combine
symmetry / base symmetry / R1-R5 satisfaction are not verified at Lens
definition time.

**Recommendation E**: Introduce a `ValidLens` predicate in
`Hypervisor/Lens.lean`.  At minimum, make combine symmetry a field.
All Lens declarations should be accompanied by a validity proof.
(One separate session's worth of work.)

### §5.3 Items that are **not** corner cases (already guarded)

- **Disguising a non-canonical Tree as Raw**: the subtype requires proof of
  `canonical = true`.  Cannot pass without `decide`.  OK.
- **Reflexive forms like `Tree.slash x x`**: canonical is false, so they
  cannot enter Raw.  OK.
- **Different canonical proofs recognized as the same Raw**: Lean's
  Subtype.ext handles this via proof-irrelevance.  OK.
- **Infinitely deep Raw**: inductive type is well-founded — every concrete
  Raw has finite depth.  Consistent with the axiom.  OK.
- **`Tree.a ≠ Tree.b` not derived from the axiom**: automatic via Lean
  inductive type's no-confusion principle.  Natural machine representation
  of axiom 1 (primitive distinction).  OK.

### §5.4 Action priority

| # | Recommendation | Difficulty | Impact |
|---|----------------|------------|--------|
| A | Add symmetry-requirement warning to Raw.fold doc | 5 min | HIGH |
| B | Add symmetry-requirement warning to Raw.rec doc | 5 min | HIGH |
| D | Add Internal open prohibition to CLAUDE.md | 5 min | MEDIUM |
| C | Add `.val` prohibition to NOTATION.md | 5 min | LOW |
| 3 (§3) | Lens-layer bleed migration | 1 session | MEDIUM |
| E | Introduce ValidLens predicate | 1 session | MEDIUM (future) |

A, B, C, D can be applied immediately as doc additions.  3 and E require
code changes and need separate sessions.

---

## §6. Overall re-verdict (incorporating deep audit)

**Still Faithful, but 2 silent leak paths exist**.

The conclusion of the 1st audit (faithful to 4-clause axiom, compliant with
"absent items" list) is maintained.  The 2nd audit additionally identifies
**2 API surfaces** where Lens output can silently depend on encoding artifacts
(Raw.fold, Raw.rec).  Mitigable by doc-level warnings.  Long-term, type-level
enforcement via a ValidLens predicate is recommended.

The structural consistency of 78 modules and 457 theorems is unaffected.
Existing Lenses (Lens.depth, Lens.leaves, signedLens, etc.) all use
**symmetric combine** and are already leak-free — verified (the `fold_slash`
proof in Fold.lean uses their symmetry).

**The vulnerability manifests only when a future user constructs an asymmetric Lens.**
Doc warnings are sufficient to prevent this.
