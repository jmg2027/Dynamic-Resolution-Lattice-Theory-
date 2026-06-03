# Session Handoff — 2026-06-03 (C-finite orbit-dimension + number-tower founding, merged)

## Branch
`claude/goal-g183-CxU4X` — `origin/main` (the number-tower founding thread) merged in this
session, so the branch now carries **both** the C-finite/orbit-dimension work and the
founding chain.  Full `cd lean && lake build` clean; every new theorem ∅-axiom
(`tools/scan_axioms.py` → `N pure / 0 dirty`, run from repo root).

---

## Two threads now on this branch

### A. C-finite / orbit-dimension (this branch's work) — promoted to `theory/math/analysis/cfinite_orbit_dimension.md`
- **`Cauchy/OrbitDimension` (30 PURE)** — strict inclusion `polynomial ⊊ C-finite`; `CFiniteZ`
  (monic Δ-orbit recurrence); witnesses `2ⁿ`, general geometric `cⁿ` (orbit dim 1), Fibonacci
  (orbit dim 2); abelian group (`cfiniteZ_zero`/`neg`/`smul`/`congr`).
- **`Cauchy/CFiniteRing` (82 PURE)** — the difference-operator algebra (`applyOp`/`conv`/
  `applyOp_comm`); the `+`-ring (`conv_annih_add`, `cfiniteZ_add`/`sub`); C-finite ⟺ monic
  annihilator (`cfiniteZ_to_annih` / `annih_snoc_to_cfiniteZ`); **C-D both directions** —
  `cfiniteZ_iff_shiftRec` (orbit dimension = recurrence order, via the dual shift algebra
  `applyShift`, `Δ=applyShift[-1,1]`, `ePow`/`dPow`); **Hadamard corners** `cfiniteZ_geomScale`
  (`cⁿ·s`) and `cfiniteZ_geomCombo_mul` (`(Σaᵢcᵢⁿ)·t`).
- **`Linalg213/DetN` (6 PURE)** — `n×n` determinant over ℤ (cofactor expansion), Phase A toward
  the general Hadamard.

### B. Number-tower founding (merged from main) — `Lens/Number/`, promoted to `book/`
- `DifferenceLensFounding` (ℤ = count-Lens, swap=negation), `RatioLensFounding`
  (ℚ lowest-terms = `det P = NS−NT = 1`), `CauchyLensFounding` (ℝ = Cauchy fixpoint),
  `TowerFounding` (capstone), `PairCompletion` ("invert is one move": one mechanism at `+`/`·`),
  `NatPairToQPos` (reciprocal involution), `Nat213/Order`.  `book/` + `book/foundations/` quasi-book.

## The connecting insight (`research-notes/G185`)
The two threads are the **same Lens-bundling pattern**: C-finite = the *ratio rung* of a
sequence-tower parallel to `ℕ→ℤ→ℚ→ℝ`; the `+`-closure (roots union) and Hadamard `⊙`-closure
(roots product) are the **ℤ/ℚ sibling duality** ("invert is one move" on two operations); the
monic obstruction = the **shared unit `det P = 1`** (= Fibonacci Cassini = `det Qⁿ`).

## Open Problems (priority)

### 1. General Hadamard product `s·t` (both factors non-split, e.g. `fib·fib`)
The corners are closed (geometric, explicit-spectrum).  The general case needs the monic
resultant `det(zI−M)` — the determinant-free routes (linear dependence; the power-sum/Newton
`mconv`) give only non-monic relations (`research-notes/G188`: the power-sum `÷k` is "the
determinant in disguise").  Program (`research-notes/G185`): `DetN` (Phase A done) → alternating
property → integer Cayley–Hamilton → Kronecker `M` ⟹ `cfiniteZ_mul`.  ~1000+ lines, multi-session.
Also unlocks C-B.

### 2. C-B — Casoratian/Hankel rank = orbit dimension (same `det` foundation).
### 3. Reframing integration TODO — now that founding is merged: wire `PnFibonacciUniversal.det_pn_universal`/`ns_minus_nt_is_one` into a "monic = shared unit" theorem; extend `book`/the chapter with the C-finite ratio-rung as a parallel bundling chain.
### 4. DRLT Validation Standard (untouched) — the repo's stated real target.

## Precision Results
No physics constants changed (pure math).  Tables unchanged — `catalogs/`.

## Three-tier state
- **Promoted**: `theory/math/analysis/cfinite_orbit_dimension.md` (C-finite, mirrors
  `OrbitDimension`+`CFiniteRing`); the number-tower founding (`book/`, `Lens/Number/Founding`).
- **Active Tier-1 scratch**: `research-notes/G185_hadamard_linalg_program.md` (the determinant
  program + the number-tower reframing) and `research-notes/G188_multiplicative_conv_design.md`
  (the mconv verdict).

## Next
Either push the `DetN` determinant program (Phase B alternating → CH; unlocks general Hadamard +
C-B), or do the reframing integration (#3, now unblocked by the merge), or wrap up.
