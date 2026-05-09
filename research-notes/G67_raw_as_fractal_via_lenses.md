# G67: Raw as fractal — infinite Nat213-lenses imply self-similarity

## User insight (2026-05-09)

> "Nat213의 렌즈들이 무한히 많다면, 그 렌즈들의 해상도로 보았을
> 때에는 Raw가 프랙탈이어야 한다는 뜻이기도 할텐데"

> "atomCount, depthCount, parenCount 등 다 다른 lens인데, 걔들을
> 통해 보면 Nat213이 보여야 하는거고, atomCount랑 똑같이 생겨있는
> 거인거지.  (애초에 Raw 타입 자체도 렌즈의 한 형태이니)"

## The fractal claim

**Statement**: Raw is fractal in the sense that:
- It admits infinitely many distinct Nat213-lenses (proved in
  `Lenses.lean`: `infinite_family_of_lenses`)
- Each lens is a "different resolution" of Raw
- Yet ALL projections produce Nat213 — the **same type, same shape**
- "Same shape at every resolution" = **fractal self-similarity**

## Formal structure

Let `L₁, L₂, ...` be the (infinitely many) Nat213-lenses.  For a
fixed Raw `r`:
- `L₁(r), L₂(r), ... ∈ Nat213`  (all share Nat213 structure)
- Specific values differ (in general)
- Each value has form `succ^n one` for some `n ≥ 0`

The **fractal aspect** comes from Raw's recursive structure:

```
Raw r  is either:                      |  Each Nat213-lens L gives:
  Raw.a  (atom)                        |    L(r) = base_a       ∈ Nat213
  Raw.b  (atom)                        |    L(r) = base_b       ∈ Nat213
  slash x y  (compound)                |    L(r) = combine (L x) (L y) ∈ Nat213
```

The catamorphism property propagates Nat213-shape from leaves to
root.  At EVERY sub-Raw (= every "scale" or "depth"), the lens
produces a Nat213.  This is exactly the fractal self-similarity:
**the same shape (Nat213) at every recursion level**.

## "Same shape, different value"

Different lenses give different specific Nat213 values, but **all
values have the same structural shape**:

```
Lens 1: L₁(r) = succ^{n₁} one    (= n₁ + 1 in toNat)
Lens 2: L₂(r) = succ^{n₂} one    (= n₂ + 1 in toNat)
...
Lens k: L_k(r) = succ^{n_k} one
```

Each `succ^n one` element is structurally identical (just the
unary successor tower).  Different `n`'s but same shape.

This is the **fractal-resolution duality**:
- **Resolution** = lens choice (which structural feature to count)
- **Shape** = Nat213's recursive `succ` structure (preserved at
  every resolution)

## Three concrete lens-resolutions

User's examples translated:

| Lens name | (ba, bb, combine) | Captures |
|---|---|---|
| `atomCount` | (1, 1, +) | total atoms |
| `aDominantCount` | (2, 1, +) | a-weighted atoms |
| `depthCount` | (1, 1, λx y. succ (max x y)) | nesting depth |
| `slashCount` | depth-related | # of slashes |
| `parenCount` | nested-pair related | # of parentheses |

Each gives a **distinct view** of the same Raw.  All produce Nat213.

## Why this matters

The fractal observation says something important about Raw:
- Raw is **structurally rich** — it admits infinitely many
  Nat213-projections
- Each projection captures a **different aspect**
- Yet they all converge to the same codomain (Nat213)
- This convergence happens **at every recursion level** (catamorphism)

So Raw is a "Nat213-multiplicity": infinitely many ways to count,
all yielding Nat213-shape.

This is the **dual** of: ℕ is a "Raw-multiplicity": infinitely
many Raw's project to the same ℕ-element via various lenses.

## Connection to fractal mathematics

Standard fractals (Cantor, Mandelbrot, Sierpiński) have the
property: **same shape at every scale**.  Raw via Nat213-lenses
exhibits this:

- **Scale** = depth in Raw recursion (= sub-Raw level)
- **Shape** = Nat213 (preserved at every sub-Raw)

The recursive structure `slash : Raw → Raw → _ → Raw` IS the
self-similarity generator.  Each lens "samples" at a particular
weighted resolution.

## Lean formalization candidates

1. **Lens output is always Nat213-shape**: trivially from typing
   (`L.apply : Raw → Nat213`).  Already implicit.
2. **Catamorphism preserves Nat213 at every sub-Raw**: every sub-Raw
   gets a Nat213-value via the same lens.  Recursive evaluation.
3. **Multi-lens view**: a single Raw r produces a "Nat213-spectrum"
   via different lenses.  Concrete multi-witness.
4. **Self-similarity**: `L (slash x y) = combine (L x) (L y)` —
   already proved (catamorphism property).
5. **Fractal-resolution duality** witness: a single Raw, three
   lenses, three distinct Nat213 values, all with same `succ`-shape.

## Lean theorems (added in this update)

In `Theory/Nat213/Lenses.lean`:
- `raw_lens_recursive_structure`: explicit recursive form
- `multi_lens_spectrum`: same Raw, different lenses, distinct
  Nat213 values, all of `succ^n one` form

## See also

- `lean/E213/Theory/Raw.lean` — Raw recursive structure
- `lean/E213/Theory/Nat213/Lenses.lean` — lens infrastructure
- `research-notes/G66_lenses_to_Nat213.md` — lens characterization
- Fractal foundations: `seed/AXIOM/01_atomicity.md` (if exists),
  CLAUDE.md "fractal lens cardinality" reference
