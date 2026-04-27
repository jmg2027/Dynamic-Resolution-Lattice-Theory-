# E213.Physics ROADMAP

## Phase 1: Methodology Accumulation ✓ COMPLETE (2026-04-27)

**Goal:** Formal derivation of known precision quantities from atomic
primitives, pattern catalogue.

**Result:** 68 files, 0 axioms, 15+ precision quantities + 3 new
falsifiable physics.
See: `STATS.md`, `DISCOVERIES.md`.

---

## Phase 2: SM-frame Artifact Identification (recommended next axis)

**Goal:** Explicitly separate the *SM-frame dependent* parts of existing
physics.

### Artifacts to identify

1. **"M_Z scale" coordinate system** — DRLT uses N_eff lattice depth
2. **QED running** — DRLT uses simplicial cohomology decomposition
3. **"Y normalization 5/3"** — actually d/NS Fibonacci ratio (partially
   in FibonacciAtomic)
4. **"Renormalization"** — DRLT has P(x) closed propagator automatically
5. **Continuum assumption** — DRLT uses finite lattice

### Formalization candidates

- `DRLTNativeFrame.lean` — N_eff scale definition
- `SMArtifactCatalog.lean` — each artifact explicit + DRLT correspondence
- `RunningAsCohomology.lean` — running = cohomology decomposition

### Expected results

The identity of current 0.6-0.8% errors (sin²θ_W, α_em@M_Z):
*SM-frame friction → may disappear in DRLT-pure*.

---

## Phase 3: DRLT-Native Coordinate

**Goal:** Express all precision quantities directly in the
*DRLT-native frame*.

### Estimated work

- Recompute precision quantities on N_eff lattice depth
- Express all formulas *without* the M_Z concept
- Direct comparison with measurements (no SM intermediary)

### Difficulties

- Must specify "at which N_eff is each quantity measured"
- Separating frame dependence of measurement technique

---

## Phase 4: Rebuild from scratch

**Goal:** Use *no* existing physics frame — 213 axioms only.

### Work

- Feynman diagrams → lattice path counting
- Lagrangian → simplex weighting
- Renormalization → resolution depth (partially done)
- All quantity ↔ measurement (no SM intermediary)

### Expected results

- SM-frame artifact errors (0.6-0.8%) disappear
- Residual is only measurement precision + finite-N bracket limit
- True meaning of "0-parameter" — *direct* match with measurements

---

## Other axes (independent)

### Yang-Mills mass gap full proof

Current `YangMillsGap.lean` is structural ("mass gap = N_eff < ∞").
Strict Lean proof requires lattice Hamiltonian + spectral analysis.
Clay $1M problem.

### Gravity G_N derivation

Current `GravityShadow.lean` is W = |G|²/d separation only.
Strict G_N 9-digit derivation requires integration with quantum-gravity
sub-project.

### Atomic IE extension

Currently H, He, screening σ only. Li-Og (Z=3-118) all
atomicity-derived. Concrete ATM_022 numerical → Lean theorem series
possible.

### PAPER2 writing

Phase 1 results in paper form:
"DRLT Physics Formally Derived"
arXiv submission ready.

### Sub-directorization

68 files in flat dir. CLAUDE.md recommends "50+ → consider sub-dir".
**Currently deferred** — README/DISCOVERIES provides logical organization.
Actual sub-dir would require bulk import path update (risky).

---

## Critical path

```
Phase 1 ✓ → Phase 2 (DRLT-Native) → Phase 3 → Phase 4
              ↓
          PAPER2 possible
```

Or:
```
Phase 1 ✓ → Yang-Mills deeper → Clay $1M
            Gravity deeper → quantum gravity
            Atomic extension → periodic table 100% formal
```

---

## Decision Criteria

- Precision formal (criterion 1): achieve "0 error" through Phase 2-3
- New physics (criterion 2): Yang-Mills, Gravity formal proof
- When both accumulate, PAPER2 emerges naturally

This cycle (Phase 1) complete — awaiting user's next directive.
