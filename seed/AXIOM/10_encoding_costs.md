# §10. Encoding costs of the Lean implementation

*Appendix.  Catalogues the Lean-4 codomain costs incurred when
emulating the axiom.  Independent of the no-exterior material in
§5 — placed here because it documents the implementation
boundary.*

The 213 axiom (§2.2) is the closure of "something exists" under
primitive distinction.  No order, no operator, no inductive
structure, no self-residue concept.  Putting this on Lean 4
imports several encoding devices.  Each is **a cost** of the
codomain choice — not a commitment of the axiom.  This
appendix catalogues the costs and their justifications.

For device-by-device classification (α / β / γ / δ) and the
audit cross-check, see `lean/E213/AUDIT.md`.

## §10.1 The four encoding costs

| Encoding device | What it imports | Why it's a cost |
|---|---|---|
| `inductive Tree | a | b | slash` | ℕ induction principle | Inductive types presuppose ℕ; ℕ is a Lens result of Raw, so importing it priorly is an **order-of-construction** cost. |
| `Tree.cmp : Tree → Tree → Ordering` | Total order on `Tree` | Order is absent from the axiom (§2.5); `cmp` is the **canonical-form selector** for the quotient. |
| `Tree.canonical = true` subtype | Single representative per equivalence class | Lean 4 core has no primitive quotient; emulated as subtype. |
| `Raw.slash (x y) (h : x ≠ y)` | `≠` from Lean metatheory + smart constructor | "Self-residue" not in the axiom; the precondition blocks `slash x x` at the Lean type level. |

Removing any of these breaks the *Lean* implementation, not the
axiom.  The axiom is the same; only the machine emulation needs
them.

## §10.2 Why these costs are unavoidable in Lean 4

The Lean 4 type-theory codomain dictates the shape of any
representation:

  - Types must have an **inductive presentation** (or
    coinductive / quotient).  Raw as "closure of distinguishing"
    maps onto inductive when we choose Lean — alternative
    codomains (Cubical type theory, a Rust enum, a hardware bit
    pattern) make different choices.
  - **No primitive quotient** in Lean 4 core.  `Quot` exists but
    brings the `Quot.sound` axiom, banned by ∅-axiom (§8.2).
    Subtype of canonical forms is the workaround.
  - **Decidable equality** is needed to enforce `≠`.  Tree's
    structural inductive type provides this automatically.

The encoding costs are **the price of running 213 on Lean**,
nothing more.

## §10.3 Faithful-emulator claim

Despite the costs, the Lean implementation is a faithful emulator
of the axiom — no (δ) additional commitment.  Classification of
every implementation device:

  - **(α) Re-expression of the axiom**: `a`, `b` constructors;
    `Raw.slash`'s `h : x ≠ y` precondition (encoding-level
    re-expression of axiom clauses 1, 2).
  - **(β) Encoding artefact (cost)**: `Tree.cmp`,
    `Tree.canonical`, `Raw` subtype, smart constructor's
    canonicalise logic.
  - **(γ) Derivation (automatic from α + β)**: `Raw.slash_comm`,
    `Raw.swap`, `Raw.fold`, `Raw.rec`, `DecidableEq` instance,
    no-confusion consequences (`a ≠ b`).
  - **(δ) Additional commitment**: **none**.

The full device-by-device analysis lives at
`lean/E213/AUDIT.md` Part I.

## §10.4 Meta-theorem: cmp-independence

The specific choice of `Tree.cmp` (which total order to use as
the canonical-form selector) has **no mathematical effect**.
The formal statement:

> Any two total orders `cmp₁, cmp₂` inducing the same
> commutative-anti-reflexive equivalence yield isomorphic
> `RawBy cmp₁ ≃ RawBy cmp₂`.  All Theory theorems transport.

Proof: `lean/E213/Theory/RawCmpIndependence.lean`.

This **mechanically verifies** that `Tree.cmp` is a (β) cost,
not axiom material.  The same meta-pattern would apply to the
inductive-structure cost (Lean inductive vs. some other codomain
presentation) if a 213-codomain-independence proof were
attempted — not currently formalised.

## §10.5 Term machinery split

Per `lean/E213/ARCHITECTURE.md` (the 4 ring + Meta layout), Tree
machinery itself — inductive `Tree`, `Tree.cmp`,
`Tree.canonical`, cmp lemmas — lives in the **Term ring** at
`lean/E213/Term/Internal/Tree*`.  The Theory ring (Raw axiom +
structure) imports Tree via the public API `E213.Term.Tree`.

This split reflects the appendix's framing:

  - **Term** = the encoding mechanism.
  - **Theory** = the axiom commitment over the Term API.
  - **Lens** = catamorphism (Lens-derived observables).

The split itself is a codomain artefact; the axiom is the same.
It is enforced by `.claude/hooks/layer-import-guard.sh`: Theory
cannot reach into `Term/Internal/` directly.
