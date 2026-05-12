# NOTATION.md — ZFC-artifact-free conventions for 213

## Why this file exists

The Raw axiom is **pre-foundational** in the sense that it
does not assume any prior mathematical framework — no set
theory, no category theory, no type theory beyond what Lean
needs to mechanically check proofs.  Standard mathematical
notation, however, carries quiet ZFC baggage that can
silently reimport the frameworks Raw is supposed to sit
below.

This file records the notation convention used inside 213.
It is not about aesthetics.  Each disallowed form has caused
at least one past session to re-derive the wrong thing.

## The principle

> **All notation is a Lens.  Some Lenses import unwanted
> structure; prefer the Lens that imports the least.**

Raw itself cannot be written down — any symbol is already a
choice.  We therefore record the *least committing* notation
available and mark the places where additional commitments
are unavoidable.

## Core conventions

### Axiom statement

When stating or re-stating the Raw axiom, use one of:

**(A) Pure prose (safest).**
> Two primitive distinctions and a binary pairing rule
> closing under itself.

**(B) BNF-style (still minimal).**
```
Raw ::= a | b | (Raw ⋄ Raw)      -- with a⋄a, b⋄b, a⋄b = b⋄a
```

**(C) Lean `inductive` (the mechanical realisation).**
```
inductive Tree | a | b | slash (x y : Tree)
def Raw : Type := { t : Tree // t.canonical = true }
```
Lean's comma in `slash (x y : Tree)` is Lean's parameter
syntax, not a Raw-level constituent.  Cite this explicitly
when the form appears.

### Raw-level terms — disallowed forms

| Disallowed                    | Why it fails                               |
|-------------------------------|--------------------------------------------|
| `{a, b}`                      | `{⋯}` is ZFC set literal; imports ∈-membership. |
| `{a, b, a/b}`                 | Same.                                      |
| `a ∈ Raw`                     | ZFC membership relation.                   |
| `Raw = {a, b, /}`             | Triple mistake: set literal, comma as constituent, `/` as element. |
| `the set of all Raw terms`    | Treats Raw as completed collection; forces existence-mode. |
| `element of Raw`              | Same implication.                          |

### Raw-level terms — preferred forms

| Preferred                     | Reading                                     |
|-------------------------------|---------------------------------------------|
| `a`, `b`                      | the two primitive distinctions              |
| `x ⋄ y` or `x / y`            | binary pairing of `x` and `y`               |
| `x : Raw`                     | `x` is a Raw term (Lean typing, not ∈)     |
| "the Raw term `a ⋄ (b ⋄ a)`" | explicit construction; no collection claim  |

### Enumeration ("level-k terms")

When enumerating finite collections of Raw terms (e.g.
level-1 or level-2 closures), the enumeration is *already a
Lens output* — a specific ordering + finiteness statement.
Enumeration is allowed, but marked as Lens-output:

```
Level-1 witnesses (under enumeration Lens):
  a, b, a⋄b           -- three Raw terms of depth ≤ 1
```

Avoid `{a, b, a⋄b}`.  Prefer a comma-separated list with an
explicit "witnesses" qualifier, or a `List Raw` in Lean.

### Lens-level notation — set theory is fine

Once a Lens has been chosen (Gödel-numbering Lens, finite-
enumeration Lens, graph-fold Lens, etc.), the Lens *image*
lives inside whatever framework that Lens targets.  Set
notation, morphisms, functors on Lens *images* are fine:

```
boolAndLens.image = {true}    -- OK: {true} is a set of Bools
signedLens.image ⊆ ℤ          -- OK: ℤ is the Lens codomain
```

The rule is: **ZFC-flavoured notation lives strictly to the
right of the Lens arrow, never to the left**.

## On the comma

The comma is itself a distinction operator: it says "this
and also this, separately".  Mingu's observation (session
2026-04-24): *"The comma itself is one of the distinction objects"*.

There is no way to fully escape the comma inside a textual
medium.  The convention records this as an acknowledged
residual cost, not a hidden assumption.  Where possible:
- Prefer line breaks over commas for Raw-level enumerations.
- When a comma is unavoidable (Lean parameter syntax,
  natural-language lists), treat it as a Lens-syntax
  artifact and do not attribute it to Raw itself.

## On existence language

The words "exist", "there are", "is an element" when
applied to Raw smuggle existence-mode (see
`research-notes/archive/17_existence_mode_lens.md`).  Prefer neutral
forms:

| Avoid                        | Prefer                                |
|------------------------------|---------------------------------------|
| "there exists a Raw term x"  | "the Raw term x (witness: …)"         |
| "Raw contains a⋄b"           | "a⋄b is a Raw term"                   |
| "Raw is infinite"            | "Raw's Lens-image under L has … size" |
| "all Raw terms"              | "every Raw term" (universal, not collective) |

Universal quantification ("every Raw term has property P")
is fine; collective language ("the set of all Raw terms")
is not.

## On the `∈` symbol

Reserve `∈` for Lens-image side only.  For Raw-level
membership use Lean's typing judgement `x : Raw`.

## On `.val` accessor (Lean encoding)

Since Raw is a subtype, `r.val : Tree` access is available.
`.val` exposes the encoding layer (the underlying Tree of the
canonical form).  Principle:

- `.val` is used **only in Firmware internal proofs**.
- **Forbidden in Lens semantics.**  Lens observations always
  go through `Lens.view` / `Raw.fold`.
- If `r.val.depth`, `r.val.cmp`, etc. appear in user code,
  it is an encoding artifact leaking into the Lens layer.  Requires correction.

This reflects the recommendation of `lean/E213/AUDIT.md` §9.5.2(C).

## Enforcement

- PR review: any occurrence of `{a`, `{b`, `∈ Raw`, or
  "Lens is a functor" triggers a required revision.
- Grep sanity check (should return no hits outside this
  file and `research-notes/archive/19_lens_not_functor.md`):
  ```
  grep -n 'Lens.*functor\|functor.*Lens' lean/E213/
  grep -nE '\{\s*(a|b)\s*[,}]' lean/E213/
  ```
