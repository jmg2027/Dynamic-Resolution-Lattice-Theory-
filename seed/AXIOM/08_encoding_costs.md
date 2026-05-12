# §8a. Encoding costs of the Lean implementation

The 213 axiom (§3.2) is **closure of "something exists" under primitive
distinction**.  No order, no operator, no inductive structure, no
self-residue concept.

Putting this on Lean 4 imports several encoding devices, each of
which is **a cost** of the codomain choice — not a commitment of the
axiom.  This file catalogs the costs and their justifications.

For device-by-device classification (α/β/γ/δ) and audit cross-check,
see `lean/E213/AUDIT.md`.

## §8a.1 The four encoding costs

| Encoding device | What it imports | Why it's a cost |
|---|---|---|
| `inductive Tree | a | b | slash` | ℕ induction principle | Inductive types presuppose ℕ; ℕ is a Lens result of Raw, so importing it priorly is an **order-of-construction** cost. |
| `Tree.cmp : Tree → Tree → Ordering` | Total order on Tree | Order is absent from the axiom (§3.3); cmp is the **canonical-form selector** for the quotient. |
| `Tree.canonical = true` subtype | Single representative per equivalence class | Lean 4 core has no primitive quotient; emulated as subtype. |
| `Raw.slash (x y) (h : x ≠ y)` | `≠` from Lean metatheory + smart constructor | "Self-residue" not in the axiom; the precondition blocks `slash x x` at the Lean type level. |

**Important**: removing any of these breaks the *Lean* implementation,
not the axiom.  The axiom is the same; only the machine emulation
needs them.

## §8a.2 Why these costs are unavoidable in Lean 4

Lean 4's type-theory codomain dictates:

- Types must have **inductive presentation** (or coinductive / quotient).
  Raw as "closure of distinguishing" maps onto inductive when we
  choose Lean — alternative codomains (Cubical type theory, Rust
  enum, hardware bit pattern) make different choices.
- **No primitive quotient** in Lean 4 core.  `Quot` exists but
  brings `Quot.sound` axiom, banned by ∅-axiom (`04_falsifiability.md`
  §5.2.1).  Subtype of canonical forms is the workaround.
- **Decidable equality** needed to enforce `≠`.  Tree's structural
  inductive type provides this automatically.

The encoding costs are **the price of running 213 on Lean**, nothing
more.

## §8a.3 Faithful emulator claim

Despite the costs, the Lean implementation is a faithful emulator of
the axiom — no (δ) additional commitment.  Classification of every
implementation device:

- (α) **Re-expression of the axiom**: `a, b` constructors,
  `Raw.slash`'s `h : x ≠ y` precondition (encoding-level
  re-expression of axiom clauses 1, 2).
- (β) **Encoding artifact** (cost): `Tree.cmp`, `Tree.canonical`,
  `Raw` subtype, smart constructor's canonicalize logic.
- (γ) **Derivation** (automatic from α + β): `Raw.slash_comm`,
  `Raw.swap`, `Raw.fold`, `Raw.rec`, `DecidableEq` instance,
  no-confusion consequences (a ≠ b).
- (δ) **Additional commitment**: **none**.

Full device-by-device analysis: `lean/E213/AUDIT.md` Part I (§I.*).

## §8a.4 Meta-theorem: cmp-independence (formalized)

The specific choice of `Tree.cmp` (which total order to use as the
canonical-form selector) has **no mathematical effect**.  Proven:

> Any two total orders `cmp₁, cmp₂` inducing the same
> commutative-anti-reflexive equivalence yield isomorphic
> `RawBy cmp₁ ≃ RawBy cmp₂`.  All Theory theorems transport.

Formal proof: `lean/E213/Theory/Internal/RawCmpIndependence.lean`.

This **mechanically verifies** that `Tree.cmp` is a (β) cost, not
axiom material.  The same meta-pattern would apply to the
inductive-structure cost (Lean inductive vs. some other codomain
presentation) if a 213-codomain-independence proof were attempted —
not currently formalized.

## §8a.5 Tree machinery split (2026-05-12)

Per ARCHITECTURE.md (4 ring + Meta), Tree machinery itself (inductive
`Tree`, `Tree.cmp`, `Tree.canonical`, cmp lemmas) lives in **Term
ring** at `lean/E213/Term/Internal/Tree*`.  Theory ring (Raw axiom +
structure) imports Tree via the public API `E213.Term.Tree`.

This split reflects §8a's framing:

- **Term** = encoding mechanism (Raw 의 구현체 — Mingu Jeong 2026-05-12).
- **Theory** = axiom commitment over Term API.
- **Lens** = catamorphism (Lens-derived observables).

The split itself is a *codomain artifact*; the axiom is the same.
Enforced by `.claude/hooks/layer-import-guard.sh` (Theory cannot
reach into Term/Internal directly).
