# Why the linear-algebra (dimension) method works — it is COUNT in a linear codomain

**Reproduced result.** The dimension bound: *more than `n` vectors in an
`n`-dimensional space over `𝔽₂` are linearly dependent.*  This is the engine of
the **linear-algebra method** — Oddtown, Fisher's inequality, Frankl–Wilson and
through it the **disproof of Borsuk's conjecture** (Kahn–Kalai 1993, open 60
years), and the polynomial-method cap-set bound (Ellenberg–Gijswijt).

**Why we picked it.** Its primitive — "independent vectors are bounded by the
dimension" — looks like a *ninth* move, nowhere among the eight instructions.
Reproducing it answers whether it is new.  It is **not**: over `𝔽₂` it is
**COUNT** (the quantitative `GAP` sub-mode from the probabilistic-method
essay) read through one extra Lens.

## The "why" in one line

A dependency among `m` vectors is two distinct sub-selections with the **same**
subset-sum.  The `2^m` subset-sums live in `𝔽₂^n`, a space of `2^n` values.  If
`m > n` then `2^m > 2^n`, so by **pigeonhole** two sub-selections collide — and a
linear dependency is exactly the residue of that collision.

That pigeonhole *is* COUNT: the deficit `|image| ≤ 2^n < 2^m = |domain|` forces a
coincidence.  The reproduction reuses the **identical** ∅-axiom witness the
probabilistic method used — `List213.nodup_length_le_of_subset` — now applied to
the subset-sum map instead of to colourings.

## The ∅-axiom witness

```
dimension_bound_is_count
  : (∀ v ∈ vs, v.length = n) → n < vs.length
  → ¬ ((allBoolLists vs.length).map (vsum n vs)).Nodup
```

(`Lib/Math/Combinatorics/LinearDependence.lean`, ∅-axiom.)  `vsum n vs` is the
subset-sum (XOR of the selected vectors); the `2^{|vs|}` sub-selections
(`allBoolLists vs.length`) map into the `2^n` length-`n` vectors; `n < |vs|`
gives `2^n < 2^{|vs|}`, so the image cannot be `Nodup` — two distinct
selections collide.  The proof is the pigeonhole step and nothing else: the
linear structure contributes only the *codomain*, the collision is COUNT.

`#print axioms → "does not depend on any axioms"`.

## Reading at the residue level

The dimension method is therefore not a new instruction; it is **COUNT through
the subset-sum Lens**.  Three things compile to the same residue fact:

  - the colouring space (probabilistic method) — COUNT through the
    colouring-restriction Lens;
  - the value space `𝔽₂^n` (here) — COUNT through the subset-sum Lens;
  - `pigeonhole` (`N+1 → N`) — COUNT bare.

"Dimension" is the count-Lens reading of the value space (`|𝔽₂^n| = 2^n`), and
"a space cannot hold more independent things than its dimension" is the deficit
`2^m > 2^n` forcing a collision.  The *dependency itself* — the nontrivial
`0`-combination — is the **residue** of the collision (the symmetric difference
of the two coinciding selections).  Linear independence carries no extra
primitive; it only changes which Lens reads the residue's size.

## Compiled form

```
dimension bound (m > n ⟹ dependent)
  = COUNT             (deficit 2^m > 2^n ⟹ collision ; nodup_length_le_of_subset)
  ∘ subset-sum READ   (selection ↦ XOR of selected vectors ; vsum)
  ∘ DISTINGUISH       (the value space 𝔽₂^n = a fold of n bit-distinguishings)
```

— the same shape as the probabilistic method, with the subset-sum Lens in place
of the colouring-restriction Lens.

## Open rung (bookkeeping, no new "why")

`dimension_bound_is_count` gives "a collision exists".  Turning a collision into
the *explicit* nontrivial `0`-combination is `vsum`-linearity over
selection-XOR (`vsum (s₁ ⊕ s₂) = vsum s₁ ⊕ vsum s₂`) plus "`s₁ ≠ s₂ ⟹
s₁ ⊕ s₂ ≠ 0`" — the symmetric difference is the dependency.  No new "why" (the
same XOR-multiplicativity already exhibited).  From there the named results
(Oddtown: `m` sets with `|Aᵢ|` odd, `|Aᵢ ∩ Aⱼ|` even ⟹ `m ≤ n`; Borsuk via
Frankl–Wilson) are the application layer.

## Witnesses

  - `lean/E213/Lib/Math/Combinatorics/LinearDependence.lean` —
    `vsum`, `vsum_len`, `dimension_bound_is_count`.
  - the reused COUNT core: `E213.Tactic.List213.nodup_length_le_of_subset`.
  - the COUNT instruction it instantiates: `theory/essays/proof_isa/probabilistic_method.md`,
    `seed/PROOF_ISA.md` (GAP sub-mode), `ProofISALifts` Archetype 4.
