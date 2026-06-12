# Order-embedding ↔ infinite subset of ℕ — reverse direction

**Status**: open (forward direction closed in Lean).

## What is closed

`lean/E213/Lens/Number/Nat213/SignatureMaps.lean` proves the **image
side** of the correspondence:

  - `strictMono_injective` — an order-embedding `f : ℕ → ℕ` is injective
    (a faithful enumeration).
  - `strictMono_unbounded` — its image meets every threshold (`N ≤ f N`),
    hence is infinite.

Injective + unbounded ⟹ the image of an order-embedding is an infinite
subset of ℕ.

## What is open (the reverse / bijection)

The reverse direction would make it a genuine bijection (↔):

> every infinite subset of ℕ arises as the image of a **unique** strictly
> increasing enumeration.

To formalize ∅-axiom:

  1. Represent a subset as `p : Nat → Bool`; "infinite" = unbounded:
     `∀ N, ∃ n, N ≤ n ∧ p n = true`.
  2. Build the enumerator `enum p : Nat → Nat` by **bounded search** —
     `enum p 0 = least n with p n`, `enum p (k+1) = least n > enum p k
     with p n`.  The "least `n ≥ k` with `p n`" helper needs a fuel /
     well-founded termination argument fed by the unboundedness witness.
  3. Prove `enum p` strictly monotone, `p (enum p k) = true` (lands in the
     subset), and surjective onto `{n | p n = true}` (hits every member).
  4. Round-trip: `enum (image-predicate of f) = f` for an order-embedding
     `f`, closing the bijection.

The friction is step 2 — a constructive least-witness search with
termination from unboundedness, kept axiom-clean (no `Classical`,
no `Nat.find` if it carries `propext`).  Mirrors the fuel-bounded parser
pattern in `Lens/SyntacticInternalization.lean` (`parseHelper` fuel).

Not claimed as proven until this closes.
