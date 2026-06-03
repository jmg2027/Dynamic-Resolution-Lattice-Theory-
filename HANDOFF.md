# Session Handoff — 2026-06-02 (G183: above the polynomials — the C-finite rung + operator ring)

## Branch
`claude/goal-g183-CxU4X` — pushed.  Full `lake build` clean.  Every theorem below is
∅-axiom (`tools/scan_axioms.py` → `N pure / 0 dirty`).

---

## What Was Done This Session

The G183 thread — the **orbit-dimension ladder** *above* `DepthCharacterization.finite_depthZ_iff`
(finite divergence depth ⟺ polynomial).  The divergence-depth axis is coarse above the polynomials
(it bins `2ⁿ`, `e`, Fibonacci, Liouville all at `∞`); the **orbit dimension** of `⟨s, Δs, Δ²s, …⟩`
separates them.  Built **Conjecture C-A** (strict inclusion `polynomial ⊊ C-finite`) and the
**C-finite operator ring**.

### 1. `Cauchy/OrbitDimension` (30 PURE) — the strict inclusion + concrete witnesses + group
- ★ `twoPow_is_diffZ_fixed`: `Δ(2ⁿ)=2ⁿ` (geometric eigen-identity, `ring_intZ` over core-free
  `powInt`); `liftKZ_twoPow_fixed` (every iterate fixes it — orbit = single line).
- `CFiniteZ s := ∃ k c, ∀n, Δᵏs n = Σ_{i<k} cᵢ·Δⁱs n` (monic `Δ`-orbit recurrence) with `linComb`.
- ★ `polyDepthZ_cfiniteZ` (polynomial ⟹ C-finite, annihilator `Δ^{d+1}`); ★ `cfiniteZ_twoPow`
  (`2ⁿ` C-finite, annihilator `Δ−1`); ★★★ `twoPow_not_polyDepthZ` (`2ⁿ` not polynomial — strict).
- `cfiniteZ_smul` / `cfiniteZ_shift` / `cfiniteZ_add_sameRec` (module + shift + shared-annihilator-sum).
- **§5 general geometric family** `geomZ c = cⁿ`: `geom_diffZ` (`Δ(cⁿ)=(c−1)cⁿ`), `liftKZ_geomZ`,
  `cfiniteZ_geom` (orbit dim 1), `powInt_eq_zero`, `geom_not_polyDepthZ` (`c≠1` ⟹ not poly).
  `cfiniteZ_congr` (C-finite respects pointwise eq); `cfiniteZ_geom_mul` (`cⁿ·dⁿ=(cd)ⁿ` —
  geometric Hadamard instance, orbit dims multiply `1·1=1`).
- **§6 Fibonacci** `fibZ`: `cfiniteZ_fib` — orbit dimension 2 (`Δ²f=f−Δf`), a non-geometric witness.
- **Abelian group**: `cfiniteZ_zero`/`cfiniteZ_neg` (here) + `CFiniteRing.cfiniteZ_sub` — C-finite is
  an abelian group under `±` (commutative ring under `+`).

### 2. `Cauchy/CFiniteRing` (53 PURE) — operator algebra + ring + `cfiniteZ_sub` + §8 shift=Δ-op + §9 C-D reverse
- `applyOp p s = Σ_i pᵢ·Δⁱs` (coeff list low-to-high `Δ`-power); `applyOp_add`/`smul`/`zero`/`congr`,
  `applyOp_diffZ` (`Δ`-commutation), ★ `applyOp_comm` (`p(Δ)q(Δ)s=q(Δ)p(Δ)s` — operators commute,
  proven directly, **no `conv_comm` needed**).
- `conv` (coefficient convolution = operator product) + `applyOp_conv` (`(p·q)(Δ)=p(Δ)∘q(Δ)`),
  with `addL`/`smulL` + `applyOp_addL`/`applyOp_smulL`/`applyOp_cons0`.
- ★★★ **the ring law** `conv_annih_add`: `Annih p s → Annih q t → Annih (conv p q) (s+t)` — the
  constant-coefficient annihilators *multiply* (orbit dimensions add).  This IS "C-finite closed
  under `+`" at the operator level.  (`conv_annih_left`/`right` via `applyOp_comm`.)
- **Bridge both ways** → **C-finite ⟺ has a monic constant-coefficient annihilator**:
  `cfiniteZ_to_annih` (forward; `opOf c k=[−c₀,…,−c_{k-1},1]`, `applyOp_opOf`, `opOf_getLastD`) +
  `annih_snoc_to_cfiniteZ` (reverse; `applyOp_snoc_one` + `applyOp_eq_linComb` + `linComb_neg`).
- ★★★ **the ring closure** `cfiniteZ_add`: `CFiniteZ s → CFiniteZ t → CFiniteZ (s+t)` — monic
  annihilators multiply (`conv_snoc`: leading `1·1=1`, existential-value form absorbs `+0`/`*1`
  noise; `Nat.max`-free toolkit `length_snoc`/`smulL_snoc`/`addL_snoc_right`/`length_addL_right_ge`/
  `opOf_snoc`).  Witness `cfiniteZ_one_add_twoPow` (`1+2ⁿ`).  `polynomial ⊊ C-finite` is a **ring**.

### 3. Repo hygiene (latent bug fixed)
The whole divergence-depth thread was **orphaned from the `Cauchy.lean` aggregator** — `PolynomialDepth`,
`DepthCharacterization`, `CassiniDepthFloor`, `DepthAperyCubic`, `Casoratian{Step,Signed}`,
`CassiniSigned`, `Depth{Quadratic,Cubic}Generic`, `DepthResidueFloor`, `DepthSelfReference`,
`PhiResidueGlue` — so the default `lake build` / CI never checked them.  Wired all in (+ the two new
files).  **Default build now reaches every Cauchy module (0 orphans).**

## Open Problems (Priority Order)

### 1. Hadamard (pointwise) product closure `s·t` — the other ring operation [top open]
`cfiniteZ_add` (sum closure) is **done**; the geometric instance `cfiniteZ_geom_mul` (`cⁿ·dⁿ=(cd)ⁿ`)
is done.  The *general* product closure `CFiniteZ s → CFiniteZ t → CFiniteZ (s·t)` is genuinely
harder: characteristic roots multiply pairwise (tensor of recurrences, degree `k·m`).
`FiniteDepthAlgebra.polyDepthZ_mul` is the finite-*depth* analogue (discrete Leibniz); the C-finite
version needs the Hadamard/resultant construction.  C-B-adjacent.

### 2. C-B — Casoratian/Hankel rank = orbit dimension (`research-notes/G183` conj C-B)
The C-finite ⟺ Hankel determinants eventually vanish; orbit dimension = Casoratian rank.  Connects to
`CasoratianStep`/`CasoratianSigned`.  Needs a rank/determinant argument.

### 3. C-D — orbit dimension = recurrence order (`research-notes/G183` conj C-D) [reverse DONE]
**Reverse direction done** (`CFiniteRing` §8–§9): `applyOp_shift` (`E = applyOp [1,1] = I+Δ`),
`applyOp_ePow` (`Eᵏ` as a `Δ`-operator, no binomial sums), and `cfiniteZ_of_shiftRec` — a monic
order-`k` shift recurrence (`ShiftRecZ`) ⟹ `CFiniteZ` (orbit dim ≤ k), via `eCombo`/`ePow_eq_snoc`/
`eCombo_length_le`/`addL_snoc_right`.  Validated end-to-end by `cfiniteZ_fib_via_shift`.  **Remaining
— forward direction** (CFiniteZ ⟹ ∃ monic shift rec): heavier — assemble `newton_gregory` (`s(n+m)=
Σ binom·Δʲs(n)`) + `newton_gregory_inverse` (both in `NewtonGregory`) into a double sum reducing the
top `Δᵏ` via the orbit recurrence.  That would close the full equivalence (standard C-finite ⟺ CFiniteZ).

### 4. DRLT Validation Standard (unchanged, untouched this thread)
The repo's stated real target — strict ∅-axiom precision theorem AND falsifier for one observable.
This session was pure math (C-finite ladder).  See prior handoffs / `CLAUDE.md`.

## Precision Results
**No physics constants changed** (pure math: the C-finite rung above the divergence-depth polynomials).
Tables unchanged — `catalogs/physics-constants.md`, `catalogs/falsifiers.md`.

## File Map
```
NEW Lean (∅-axiom):
  lean/E213/Lib/Math/Cauchy/OrbitDimension.lean   ← poly ⊊ C-finite + geometric/Fibonacci/Hadamard/group (30 PURE)
  lean/E213/Lib/Math/Cauchy/CFiniteRing.lean      ← operator algebra + ring + §8 shift=Δ-op + §9 C-D reverse (53 PURE)
MODIFIED:
  lean/E213/Lib/Math/Cauchy.lean   ← wired in OrbitDimension, CFiniteRing + the orphaned depth thread
  lean/E213/Lib/Math/Cauchy/INDEX.md
  STRICT_ZERO_AXIOM.md
  research-notes/G183_above_the_polynomials.md
```

## Three-tier state
- **Active scratchpad**: `research-notes/G183_above_the_polynomials.md` (this thread; C-A *done* —
  strict inclusion + ring closure under `+` + both bridges + concrete witnesses; C-B/C-D + general
  Hadamard product open).
- **Promotion candidate**: the `OrbitDimension`+`CFiniteRing` pair is a clean, mostly-closed sub-tree
  (sum closure done; only the Hadamard product is open) → eligible for
  `theory/math/analysis/cfinite_orbit_dimension.md` per `PROMOTION_CRITERIA` (consider once the
  product closure lands, or promote the `+`-ring now and extend later).

## Next
C-D **reverse** is now done + validated.  Remaining, in rough difficulty order: **C-D forward**
(CFiniteZ ⟹ shift rec — double-binom assembly of `newton_gregory`(+inverse); closes the full
equivalence), **Open #1** general Hadamard product (tensor/resultant), **Open #2** C-B (Casoratian
rank).  Lower-risk alternative: promote the `+`-ring sub-tree to `theory/`.
