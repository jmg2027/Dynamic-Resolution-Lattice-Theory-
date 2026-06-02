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

### 1. `Cauchy/OrbitDimension` (15 PURE) — the strict inclusion
- ★ `twoPow_is_diffZ_fixed`: `Δ(2ⁿ)=2ⁿ` (geometric eigen-identity, `ring_intZ` over core-free
  `powInt`); `liftKZ_twoPow_fixed` (every iterate fixes it — orbit = single line).
- `CFiniteZ s := ∃ k c, ∀n, Δᵏs n = Σ_{i<k} cᵢ·Δⁱs n` (monic `Δ`-orbit recurrence) with `linComb`.
- ★ `polyDepthZ_cfiniteZ` (polynomial ⟹ C-finite, annihilator `Δ^{d+1}`); ★ `cfiniteZ_twoPow`
  (`2ⁿ` C-finite, annihilator `Δ−1`); ★★★ `twoPow_not_polyDepthZ` (`2ⁿ` not polynomial — strict).
- `cfiniteZ_smul` / `cfiniteZ_shift` / `cfiniteZ_add_sameRec` (module + shift + shared-annihilator-sum).

### 2. `Cauchy/CFiniteRing` (28 PURE) — the difference-operator algebra + ring law
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

### 3. Repo hygiene (latent bug fixed)
The whole divergence-depth thread was **orphaned from the `Cauchy.lean` aggregator** — `PolynomialDepth`,
`DepthCharacterization`, `CassiniDepthFloor`, `DepthAperyCubic`, `Casoratian{Step,Signed}`,
`CassiniSigned`, `Depth{Quadratic,Cubic}Generic`, `DepthResidueFloor`, `DepthSelfReference`,
`PhiResidueGlue` — so the default `lake build` / CI never checked them.  Wired all in (+ the two new
files).  **Default build now reaches every Cauchy module (0 orphans).**

## Open Problems (Priority Order)

### 1. Finish the predicate-level `cfiniteZ_add` (`CFiniteZ s → CFiniteZ t → CFiniteZ (s+t)`)
The math is **done** (`conv_annih_add` + both bridges).  One list lemma remains: **`conv` of two
monic operators is monic** (leading `1·1=1`).  Friction is purely syntactic — `addL` injects `+0`/`*1`
into the leading term (`conv [1] [1] = [1+0]`, not literal `[1]`).  Needed: a `v=1`-hypothesis form of
`applyOp_snoc_one`, plus `smulL_snoc` (`smulL c (q++[b]) = smulL c q ++ [c*b]`), `addL_snoc_right`
(`x.length ≤ y.length → addL x (y++[b]) = addL x y ++ [b]`, needs `Nat.le_of_succ_le_succ`/
`Nat.not_succ_le_zero` — verify pure), and `opOf_snoc` (`opOf c k = lower ++ [1]`, length `k`).
~50–70 lines.  Best done fresh.

### 2. C-B — Casoratian/Hankel rank = orbit dimension (`research-notes/G183` conj C-B)
The C-finite ⟺ Hankel determinants eventually vanish; orbit dimension = Casoratian rank.  Connects to
`CasoratianStep`/`CasoratianSigned`.  Needs a rank/determinant argument.

### 3. C-D — orbit dimension = recurrence order (`research-notes/G183` conj C-D)
A monic order-`k` `Δ`-recurrence ⟺ monic order-`k` shift(`E`)-recurrence (`E=I+Δ`, `Δ=E−I`; the
operator algebras coincide).  `BinomialTransform.lean` has the `Eᵏ=Σbinom·Δʲ` machinery.

### 4. Hadamard (pointwise) product closure `s·t` — the other ring operation
Characteristic roots multiply pairwise (tensor of recurrences, degree `k·m`).  Harder; C-B-adjacent.
`FiniteDepthAlgebra.polyDepthZ_mul` is the finite-*depth* analogue (discrete Leibniz); the C-finite
version needs the Hadamard/resultant construction.

### 5. DRLT Validation Standard (unchanged, untouched this session)
The repo's stated real target — strict ∅-axiom precision theorem AND falsifier for one observable.
This session was pure math (C-finite ladder).  See prior handoffs / `CLAUDE.md`.

## Precision Results
**No physics constants changed** (pure math: the C-finite rung above the divergence-depth polynomials).
Tables unchanged — `catalogs/physics-constants.md`, `catalogs/falsifiers.md`.

## File Map
```
NEW Lean (∅-axiom):
  lean/E213/Lib/Math/Cauchy/OrbitDimension.lean   ← poly ⊊ C-finite (15 PURE)
  lean/E213/Lib/Math/Cauchy/CFiniteRing.lean      ← operator algebra + ring law + bridges (28 PURE)
MODIFIED:
  lean/E213/Lib/Math/Cauchy.lean   ← wired in OrbitDimension, CFiniteRing + the orphaned depth thread
  lean/E213/Lib/Math/Cauchy/INDEX.md
  STRICT_ZERO_AXIOM.md
  research-notes/G183_above_the_polynomials.md
```

## Three-tier state
- **Active scratchpad**: `research-notes/G183_above_the_polynomials.md` (this thread; conjectures C-A
  done at the operator level, C-B/C-C/C-D + Hadamard open).
- **Promotion candidate**: once `cfiniteZ_add` closes, the `OrbitDimension`+`CFiniteRing` pair is a
  clean closed sub-tree → `theory/math/analysis/cfinite_orbit_dimension.md` per `PROMOTION_CRITERIA`.

## Next
Recommend **Open #1** (finish `cfiniteZ_add` — the headline ring closure, one list lemma away) or
**Open #3** (C-D via `BinomialTransform`, conceptually crisp).
