# Decomposition: equivalence / equivalence-class / isomorphism / homomorphism

*213-decomposition of the "sameness" family (동치 / 동치류 / 동형 / 준동형), per `../README.md`.*

## The decomposition

- **Construction `C`** — any two constructions `x, y` (Raws), plus a chosen **reading `L`**.
- **Reading `L`** — the Lens you are comparing *under*. "Same" never means "same construction"; it
  means **"reads the same under `L`"**:
  ```
     x ≈_L y   :=   L.view x = L.view y           (Lean: Lens.equiv)
  ```
- **Residue** — what `L` forgets is exactly what the equivalence *allows to differ*; the
  equivalence-class is the fibre of `L`, and the residue is everything inside one fibre.

## Re-seeing — the four "sameness" notions are one arrow

The whole family is facets of comparing constructions under a reading, i.e. of the single Lens-arrow
`Lens.refines` (`Lens/LensCore.lean`; one Lens's kernel sits inside another's):

```
   동치   (equivalence)        =  ⟨ x, y | L ⟩  with  x ≈_L y                 (equal under L)
   동치류 (equivalence-class)  =  the fibre  { z | z ≈_L x }                   (a residue-class of L)
   동형   (isomorphism)        =  two readings with the SAME kernel            (mutual refinement)
   준동형 (homomorphism)       =  a reading that RESPECTS a construction op     (kernel ⊇ the op's)
```

`isomorphism` is `Lens.refines L M ∧ Lens.refines M L` — equal kernels — characterized exactly by
`Unified.lensIso_iff_kernel_eq`. `homomorphism` is the same arrow with the construction's operation
required to pass through (the parity decomposition's `L₂(a+b)=L₂a+L₂b` is the instance).

## Revelation (collapse)

Four notions taught as four definitions — equivalence, equivalence-class, isomorphism, homomorphism —
are **one Lens-arrow read four ways**: comparison under `L`, the fibre of `L`, equality of two `L`s'
kernels, and an `L` that respects a construction. This is the CLAUDE.md failure-mode
**"Equivalence-pluralism"** stated positively (the miss: listing `cutEq, ZpSeqEquiv, signedEq, …` as
parallel objects; the truth: decompositions of one arrow). The collapse is **Lean-certified** by the
kernel-equality characterization `lensIso_iff_kernel_eq` — isomorphism *is* kernel coincidence, not a
separate primitive.

## Note for the technique

This decomposition shows the calculus's **comparison layer**: "sameness" is never a property of
constructions, always **a reading laid over a pair**. It also fixes the *altitude* of the technique:
its equivalence is `Lens.refines` — a 1-categorical / setoid-level kernel preorder (no
identity-types/univalence; the repo forbids `funext`/`Quot.sound`). So the calculus describes "same
under a reading", not higher coherence — a deliberate, honest ceiling, not an omission.
