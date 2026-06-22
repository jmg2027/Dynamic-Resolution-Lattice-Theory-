# Decomposition: the determinant

*213-decomposition of `det`, per `../README.md`.*

## The decomposition

- **Construction `C`** — a **matrix** = a `2×2` (here) bundle of directed counts, built by
  *composition* `mul M N`: distinguishing iterated as the ×-construction on transformations. `C`
  carries two of the README's read-off sub-structures: a **direction / orientation** bit (the swap
  that flips `M.a·M.d` against `M.b·M.c`) and a **fold-height** (the order/dimension — here `2`).
- **Reading** — the **character reading** `det`: the construction-preserving projection
  `M ↦ M.a·M.d − M.b·M.c` that takes the ×-construction `mul` to ordinary `·`. It is the README's
  **`L` character / logarithmic mode** — a reading whose readout *respects the operation*, here
  keeping multiplication as multiplication: `det(MN) = det M · det N`. Its readout splits into
  **magnitude** (`|det|`, an `ℕ`-style count of area-scaling) and a **direction bit** — the *sign*
  of `det` is the orientation sub-structure of `C` surfacing, exactly as `−`'s sign was the swap-bit
  of the directed count-pair in `integers.md`.
- **Residue** — `det` is massively many-to-one (every `M` with the same `a·d − b·c` reads the same;
  all of `SL₂(ℤ)` collapses to the single value `1`). The residue is everything the scalar forgets:
  the entire matrix interior the one number cannot recover — shear, the individual entries, the path
  through the tree. The unimodular tree (`SternBrocotMarkov`) lives *entirely inside* one residue
  fiber `det = 1`.

## Re-seeing

```
   det           =  ⟨ matrix (×-construction `mul`) | character reading (mul ↦ ·) ⟩
   "det(MN)=detM·detN"  =  the reading is ×-construction-preserving  (det2_mul)
   "det = ±1"    =  the character lands in the orientation sub-readout {+1,−1} = L₂ of integers.md
   "the sign"    =  the orientation bit of C, read out by det — not a Raw primitive
```

`det = ±1` is *verbatim* `parity.md`'s `L₂`: a construction-preserving reading into the two-element
orientation readout. For the unimodular family the character collapses to the **parity character**
`{+1, −1}` — the same finite-cyclic readout that is even/odd, the Legendre symbol, and the
permutation sign. The *general* `det` is that same character with the finite readout opened up to a
full multiplicative scalar.

## Revelation (collapse + forcing)

The load-bearing collapse: **`det` is one reading carried by every superficially-different
unimodular construction**, and Lean certifies it is the *same* reading, not four. The backbone is a
single pure `ℤ`-polynomial homomorphism

- `SternBrocotMarkov.det2_mul` — `det₂(MN) = det₂ M · det₂ N` (★★★★★, ∅-axiom, one `ring_intZ`);

and from that one law alone, **four independent constructions carry one invariant**
(`UnimodularSynthesis.unimodular_four_readings`): the Stern-Brocot mediant node, the continuant
node, and the two Minkowski `?`-cocycle bounds are all `det₂ = 1` — *readings of a single character*,
not four theorems. The *same* multiplicativity reappears proven independently three more times —
`HolonomyLattice.det_mul`, `FiniteOrderSpectrum.det_mul`, `ModArith` via Zolotarev — confirming it is
a reading-shape, not a local trick.

**Direction meets character — the dichotomy is the orientation bit.** In the recurrence form
(`CassiniUnimodular.det_step`) one composition step multiplies the determinant by the shift's own
`q`: `det s (n+1) = q · det s n`, closing to `det s n = qⁿ · det s 0` (`det_closed`). The
unimodular case is precisely `q = ±1`, and `cassini_law_one_at_two_multipliers` enacts the payoff:
"conserved Cassini (`q=1`)" and "period-2 alternating (`q=−1`)" are **not two phenomena** — they are
the *one* parametric `det_step` at the two values of the orientation bit. That `±1` is the swap-bit
of `C` (orientation) read through the character — direction (C) and character (L) meeting in a single
scalar. So `det = ±1` (parity), the `±` of `qⁿ` (Cassini dichotomy), and the sign of `integers.md`
are one structure: **the orientation sub-readout of a character reading**.

**Forcing**: multiplicativity is not chosen — it is *forced* by `det` being the read-out of the
×-construction `mul`. A reading that respects how `C` was built must take `mul` to `·`; `det2_mul`
is a bare `ring_intZ` identity precisely because there is nothing to choose. The character is the
build reporting itself.

## Note for the technique

This decomposition **confirms** both refined sub-structures of the README map meeting at one object:

- It confirms **`L`'s character mode**: `det` extends `parity.md`'s finite-cyclic "character"
  (`L₂` into `{+1,−1}`) to a **full multiplicative scalar** readout `det(MN) = detM·detN`. The
  unimodular case literally *is* `L₂` (`det = ±1`); the general case opens the same character's
  finite readout to all of `ℤ`. So "character" is not finite-only — it is *any* operation-preserving
  reading, finite-cyclic at one resolution, scalar at another.
- It confirms **`C`'s direction axis**: the *sign* of `det` is the orientation/swap-bit, the very
  same direction sub-structure `integers.md` surfaced under `L₋`. Here it surfaces as the `q = ±1`
  branch of `det_step` — one dichotomy, two values of the orientation bit.

So the deepest collapse again sits **where two map-axes meet** (README's emerging map): `det` is
where **direction (C) meets character (L)**, the magnitude/sign split of its scalar readout being
exactly the height/orientation split of `C`. Candidate sharpening: a **character** is a reading whose
readout is itself a (number) construction carrying the *same* direction + height sub-structure as
`C` — magnitude = the height/count it scales, sign = the orientation it preserves-or-flips.

**Verified Lean anchors** (all ∅-axiom-style pure `ℤ` identities):
- `Lib/Math/NumberSystems/Real213/Markov/SternBrocotMarkov.lean:det2_mul` (multiplicativity, the backbone)
- `Lib/Math/NumberSystems/Real213/Markov/UnimodularSynthesis.lean:unimodular_four_readings`,
  `unimodular_drives_tree_and_markov` (one invariant, four constructions / two domains)
- `Lib/Math/Algebra/CassiniUnimodular.lean:det_step`, `det_closed`, `cassini_law_one_at_two_multipliers`
  (the `q = ±1` orientation dichotomy)
- `Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean:det_mul`, `det_holonomy_eq_one`
  (multiplicativity again; `det = 1` the conserved transport invariant)
- `Lib/Math/NumberSystems/Real213/ModularGeometry/FiniteOrderSpectrum.lean:det_mul`
- cross-frame to `parity.md`: `Lib/Math/NumberTheory/ModArith/Zolotarev.lean:psign_mulPerm_hom`
  (the same `±1` character on the permutation construction)
