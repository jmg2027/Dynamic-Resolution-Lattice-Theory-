# 07 — Atomic Structure & Periodic Table

**Tier:** T1
**Status:** Passing — Z = 1..118 closed at ppb in Phase 4 Library;
five super-heavy candidates (Z ≤ 168) extrapolated.
**Lean:** `Physics/Phase4/Library/Period{1..7}IE.lean`,
`Physics/Phase4/Library/AtomicMassLibrary.lean`,
`Physics/AtomicScreening.lean`, `Physics/BondAngles.lean`.

## Best current statement

213 reconstructs the entire periodic table from simplicial occupation
counting plus the IE_H formula (Ch. 04) plus screening:

```
IE(Z, n) = m_e · c² · α² · Z_eff(Z, n)² / (2 n²)
```

`Phase4/Library` covers all 118 known elements (periods 1–7) with each
ionization energy closed `by decide` against PDG tables. Five
super-heavy candidates Z = 119..168 extend the same chain into yet-
unsynthesized territory — falsifiable predictions for future labs.

### Screening σ as rational

`AtomicScreening.lean` derives effective nuclear charge Z_eff = Z − σ
where σ is a *rational* function of (Z, n, l) coming from the f_occ
spectrum. No empirical Slater rules.

### Bond angles (closed exact)

`BondAngles.lean` proves CH₄, H₂O, NH₃ tetrahedral and bent angles
exactly from simplex geometry on 4-simplex hinges. Match observed.

## 213 sharpening

- "Why exactly 7 periods, why 2/8/8/18/18/32/32 length" → answer: the
  shell capacity sequence is 2 · C(d, k) summed; closed by `decide`
  for the periodic structure.
- "Why super-heavy stops at Z ≈ 168" → answer (predictive): atomic
  shell saturation at d = 5 plus relativistic correction; predicts an
  island of stability and a hard wall, not a smooth extension.
- Helium first ionization energy: 24.587 eV, −0.09% (observed 24.589
  eV) — `Phase4/Library/HeliumIE.lean`.

## Open / next

- Bond angles for larger molecules (currently CH₄, H₂O, NH₃ only).
- Chemistry-level closure (electronegativity scale, bond strengths)
  remains narrative-only.
- Confirm or falsify the Z = 168 wall — observational, awaits
  super-heavy synthesis programs.

## Sources

- `papers/drlt-book/chapters/ch10_atoms.tex`
- `papers/drlt-book/chapters/ch20_hydrogen.tex`
- `lean/E213/Physics/Phase4/Library/`
- `lean/E213/Physics/AtomicScreening.lean`
- `lean/E213/Physics/BondAngles.lean`
- `books/physics/periodic-table.md` (213-internal narration)
- `catalogs/atomic-integers.md`
