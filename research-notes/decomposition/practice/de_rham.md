# Decomposition: differential forms / de Rham cohomology (d, d²=0, Stokes, H*_dR, ∧)

*213-decomposition per `../README.md` (model v7.1). The consolidating hypothesis to **test**, not
re-skin: de Rham cohomology is **the cochain side of `homology.md`'s chains** — the *same* fold-height
reading run **upward** in degree. Concretely: (i) the **exterior derivative `d`** = `homology.md`'s
boundary `∂` read as the COBOUNDARY (`δ`, the height-axis raised one rung); (ii) **`d²=0`** = the SAME
`q=±1` orientation-cancellation as `∂²=0` (one theorem: `dsq_zero_universal_delta4`); (iii)
**Stokes `∫_M dω = ∫_∂M ω`** = the calculus's telescoping/adjunction — the SAME `Σ⊣Δ`/`∫⊣d` boundary-
collapse ALREADY BUILT as `gauss_conservation_telescope`; (iv) **`H*_dR = ker d / im d`** = the
`q=±1` RESIDUE of the coboundary reading, the SAME residue as `homology.md` tied to `curvature.md`'s
Gauss–Bonnet; (v) the **wedge `∧`** = the `q=−1` antisymmetric multiplication and `d(α∧β)=dα∧β±α∧dβ`
= the graded-Leibniz / graded-relation slot (`leibniz_universal_delta4`). This note tests whether de
Rham *consolidates* homology + integration + curvature + two_cells under ONE reading.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the **same simplex/nesting** `homology.md` reads: an `n`-cell is `n+1`
  distinguished vertices, the build-tree of iterated distinguishing, carrying `C`'s two read-off axes
  — a **fold-height** (cell dimension `k`) and a **direction/orientation bit** (vertex ordering /
  removal sign). A `k`-form is the `k`-cochain `Cochain n k` — the indicator on `k`-subsets
  (`Cochain/Core.lean`). On the integration side `C` is the dyadic bracket-chain of `integration.md`
  (points = refinement residues, a value hung at each); the two `C`'s meet *at the boundary pairing*
  (Stokes). Nothing smooth-manifold enters: there is **no `Ω^k` bundle, no alternating tensor, no
  smooth chart** — the construction is the combinatorial cochain complex and the dyadic bracket.

- **Reading `L↑` (the coboundary / exterior-derivative reading)** — the EXACT mirror of `homology.md`'s
  `L↓`. Where `∂` *peels* a face (drops cell-dimension by one, the height-axis run **down**), `d` is
  the **same alternating face-reading run UP in degree** — `δ : Cochain n k → Cochain n (k+1)`
  (`Delta/Core.lean : delta`, `deltaAt`), the alternating XOR-fold over the `k+1` faces `τ.eraseIdx i`,
  with the orientation sign `(−1)^i`. `homology.md` already names `delta` "the boundary/coboundary
  reading `Cᵏ → Cᵏ⁺¹`": **`d` and `∂` are literally one Lean operator** (`delta`), read in the two
  directions of the bidirectional height axis. So `d` is not a new reading — it is `L↓` with the
  degree-arrow reversed (cochains rise where chains fall; the orientation bit is identical).

- **Residue** — `q=±1` (the README's residue tag), with TWO faces that are one:
  1. *Cohomology face*: `L↑` has a kernel/image gap, and that gap IS de Rham cohomology:
     `H*_dR = ker d / im d` = closed-not-exact forms = "what `L↑` forces (closed, `dω=0`) but cannot
     fill from one degree down (exact, `ω=dη`)". This is `homology.md`'s residue verbatim, at the
     cochain level — de Rham cohomology *is* singular cohomology, the two are the **`q=±1` poles of
     one fold-height reading** (chains down / cochains up). Lean shadow: `BettiKernel.kerSizeDelta`,
     `reduced_betti_d4_contractible` (`ker δ = im δ` on the contractible Δ⁴ ⇒ residue empty).
  2. *Stokes/integration face*: pairing a form against a chain (`∫`) makes `d` and `∂` **adjoint**;
     the residue of the telescoped sum is exactly the surviving boundary (`integration.md`'s "+C" /
     boundary-collapse). The `q=+1` converging pole of `integration.md`.

## Re-seeing — ⟨C | L⟩

```
   d (exterior derivative)  =  ⟨ simplex (nesting) | L↑ = alternating face-reading, run UP in degree ⟩
                               = homology.md's ∂ with the height-arrow REVERSED (one Lean op: delta)
   "d²ω = 0"                 =  each codim-2 face removed by TWO orders → opposite signs cancel
                               = the SAME theorem as ∂²=0  (dsq_zero_universal_delta4)
   wedge  α ∧ β              =  ⟨ index-sets | the q=−1 ANTISYMMETRIC merge ⟩  (SignedCup.cup1, mergeSign)
   "d(α∧β)=dα∧β ± α∧dβ"      =  the graded-Leibniz / two_cells.md graded-relation slot (leibniz_universal_delta4)
   Stokes  ∫_M dω = ∫_∂M ω   =  telescoping at residue resolution: interior walls cancel, boundary survives
                               = gauss_conservation_telescope  (the SAME Σ⊣Δ / ∫⊣d adjoint, ALREADY BUILT)
   H*_dR = ker d / im d      =  Residue(L↑, C), q=±1  =  homology.md's residue read UP (de Rham = singular)
   Betti b₁                  =  curvature.md's Gauss–Bonnet  Σκ = 2(1−b₁)   (one residue, two readings)
```

The whole of de Rham is **one reading (`L↑` = `homology.md`'s `L↓` reversed) plus the integration
pairing** — no new primitive. Set against the three notes it consolidates:

| classical de Rham object | = the 213 reading | already in note | Lean anchor |
|---|---|---|---|
| exterior derivative `d` | `L↑` = `∂`'s height-axis run UP (one op `delta`) | `homology.md` (`∂` = `L↓`) | `Delta/Core.delta`, `deltaAt` |
| `d²=0` | `q=±1` sign-cancellation, codim-2 face twice | `homology.md` (`∂²=0`) | `dsq_zero_universal_delta4` |
| Stokes `∫dω=∫_∂ω` | telescoping = `Σ⊣Δ`/`∫⊣d` adjoint, boundary-collapse | `integration.md` (FTC = telescope) | `gauss_conservation_telescope`, `integral_eq_flux` |
| `H*_dR = ker d/im d` | `Residue(L↑,C)`, `q=±1`; de Rham = singular | `homology.md` (homology = `Residue(L↓,C)`) | `BettiKernel.reduced_betti_d4_contractible` |
| wedge `∧`, graded Leibniz | `q=−1` antisym product + graded-relation slot | `two_cells.md` (graded-relation), `parity.md` (det sign) | `SignedCup.cup1_antisymmetric`, `leibniz_universal_delta4` |
| Betti ⇄ curvature | one `q=±1` residue, two readings | `curvature.md` (`Σκ=2(1−b₁)`) | `gauss_bonnet_Kmn`, `totalCurv_eq` |

de Rham consumes BOTH of `C`'s axes (height to move degree, direction to sign faces) — exactly as
`homology.md` found `∂` does, because de Rham *is* `homology.md` read upward.

## LEVERAGE — does de Rham consolidate homology + integration + curvature under one reading?

**Verdict: PREDICTION — and the strongest *consolidation* in the notebook so far, because four legs are
already ∅-axiom theorems and three of them are SHARED VERBATIM with prior notes.** de Rham is not a new
edifice; it is the cochain reading of `homology.md` welded to `integration.md`'s telescoping pairing,
with `curvature.md`'s Gauss–Bonnet supplying the residue↔geometry tie. Leg by leg, honest.

**(1) `d` = `∂` read upward — ONE Lean operator, not an analogy.** `homology.md`'s anchor is literally
named "the boundary/**coboundary** reading `Cᵏ → Cᵏ⁺¹`": `delta`/`deltaAt` (`Delta/Core.lean`). The
exterior derivative and the boundary are the *same* `delta` op; cochains rise in degree where chains
fall. This is the bidirectional fold-height axis (model v4) read in its two directions — no new
primitive, the cleanest confirmation that "fold-height is bidirectional" was load-bearing.

**(2) `d²=0` = `∂²=0` — literally the SAME theorem (`dsq_zero_universal_delta4`), PURE.** Applying `L↑`
twice collects each codim-2 face *exactly twice* (remove `i` then `j`, vs `j` then `i`) with **opposite
orientation signs** that annihilate — the `q=−1` direction-bit cancelling pairwise, `homology.md`'s
exact mechanism. Verified universal on Δ⁴ at every interior stratum:
`V4Capstone.dsq_zero_universal_delta4` (`∀ σ, ∀ i, δ(δσ) i = false` at (5,1),(5,2),(5,3)), confirmed
**5 pure / 0 dirty** by `scan_axioms.py`. The `Multivariable/Stokes.ddOmega_zero_skeleton` (`n−n=0`) is
a *trivial placeholder*, NOT the content — the real `d²=0` is the simplicial cochain theorem.

**(3) ★ Stokes IS already a ∅-axiom theorem — `gauss_conservation_telescope` — the strongest find.**
The task's strongest leverage, confirmed: discrete Stokes `∫_M dω = ∫_∂M ω` is the SAME boundary-collapse
of a telescoped sum that `integration.md` cashed as the FTC.
`FluxMVT/TelescopingConservation.gauss_conservation_telescope` (`:152`, **8 pure / 0 dirty**) proves
along a bracket-chain that every **interior wall cancels** (`(fluxAlong f db_i).forward =
(fluxAlong f db_{i+1}).backward`) and only the **outer boundary cuts survive** (`= f db₀.leftCut`,
`= f db₂.rightCut`). Its own docstring names this "the **divergence theorem** `∫_Ω ∇·F = ∮_∂Ω F` … no
integral / measure machinery needed; the cancellation IS the conservation." That is Stokes/Green/
divergence as ONE edge-matching identity. And `IntegralViaAnti.integral_eq_flux` (`:47`, `rfl`) makes the
adjunction literal: the integral IS the flux of the antiderivative along the bracket — `∫ = F(b)−F(a)`
by definition-unfolding. So **Stokes = "`d` and `∂` are adjoint under the integration pairing"** = the
resolution-invariant telescoping (`integration.md`'s "FTC = telescoping is resolution-invariant"), at
the form level. This is the `∫⊣d` / `Σ⊣Δ` adjoint pair (`adjunction.md`/`galois.md`), `q=+1` converging
residue. **The repo already has Stokes as a proved theorem; we cite it, we do not build it.**

**(4) `H*_dR = ker d/im d` = `Residue(L↑,C)` = `homology.md`'s residue, `q=±1`.** Closed-not-exact forms
are exactly "forced (`dω=0`) but not captured (not `dη`)" — the README's residue, now at the cochain
level. `BettiKernel.reduced_betti_d4_contractible` (**11 pure / 0 dirty**: `kerSize 5 0 = 1`,
`kerSize 5 1 = 2`) makes it concrete — on the contractible Δ⁴, `ker δ = im δ`, residue empty (`b̃=0`):
no de Rham class because no un-fillable closed cochain. de Rham cohomology = singular cohomology = the
**`q=±1` poles of one fold-height reading**; the de Rham theorem (the iso) is the statement that the two
*directions* of `L` measure one residue. Tied to geometry by `curvature.md`'s Gauss–Bonnet
`gauss_bonnet_Kmn` / `totalCurv_eq` (`Σκ = 2χ = 2(1−b₁)`, ∅-axiom): the *same* `q=±1` residue read as
curvature (loop) on one side and Betti `b₁` (cohomology) on the other.

**(5) Wedge `∧` = the `q=−1` antisymmetric product; graded Leibniz = the graded-relation slot.** The
genuine signed exterior product is built: `SignedCup.cup1`/`mergeSign = (−1)^{inv}` with
`cup1_antisymmetric` (`e_i∧e_j = −(e_j∧e_i)`, `e_i∧e_i = 0`; **14 pure / 0 dirty**) — the alternating
sign IS `parity.md`/`determinant.md`'s `q=−1` determinant character (the orientation bit the Bool cup
collapses, `SignedCup.lean:10` "the genuine exterior/wedge product"). The graded Leibniz
`d(α∧β)=dα∧β ± α∧dβ` is `two_cells.md`'s **graded-relation slot**, grounded as
`V4Capstone.leibniz_universal_delta4` (`:62`, PURE in the 5-theorem capstone): `δ(α⌣β) = δα⌣β ⊕ α⌣δβ`
— the same three-term graded law. The wedge ring structure (associativity/unit) is in `Cup/Ring.lean`
(`⌣`).

**Honest boundary — Lean-built vs conceptual.**
- *Lean-built (∅-axiom, scanned PURE):* (a) `d`/`∂` = one `delta` op (`Delta/Core`); (b) `d²=0` =
  `dsq_zero_universal_delta4` (5/0); (c) discrete Stokes = `gauss_conservation_telescope` (8/0) +
  `integral_eq_flux` (`rfl`, in a 1/0 module); (d) `H* = ker/im` residue = `reduced_betti_d4_contractible`
  (11/0); (e) wedge antisymmetry `cup1_antisymmetric` + graded Leibniz `leibniz_universal_delta4`
  (SignedCup 14/0; V4Capstone 5/0); (f) Gauss–Bonnet `b₁` tie (`gauss_bonnet_Kmn`, `totalCurv_eq`).
- *Conceptual-only / the precise missing leg (the `knots.md`-style gap):* **the smooth-manifold de Rham
  complex is ABSENT.** There is no `Ω^k(M)` of smooth differential forms, no alternating cotangent tensor
  bundle, no smooth chart/atlas, and **no de Rham comparison ISOMORPHISM `H*_dR(M) ≅ H*_sing(M;ℝ)`** as a
  proved theorem (grep for `deRham`/`smooth form`/`Ω^k`/alternating-tensor returns only the *combinatorial*
  cochain complex and a *conformal-curvature* file, not a form complex). What IS built is the
  **discrete/combinatorial cochain version** — `Cochain n k` + `delta` on Δ⁴ and surfaces (T²,
  `T2nBetti`), which is the cellular/simplicial de Rham analogue. The `Multivariable/Stokes.lean`
  per-dimension "masters" (`greens_master`, `divergence_master`, `stokes_4d_master`) are
  **constant-field witnesses** (`c·1 − c·1 = 0`) and `stokes_n_existence`/`ddOmega_zero_skeleton` are
  *trivial skeletons* (`∃k,k=n−1`; `n−n=0`) — the load-bearing Stokes is `gauss_conservation_telescope`,
  NOT these. So the gap is exactly: a smooth 1-parameter form bundle over a manifold and the de Rham iso
  — the same `Real213`-cut/`h→0` residue and smooth-tensor absence that `curvature.md` (no smooth
  Riemann tensor), `derivative.md` (general `Δ↔d/dx`), and `lie_theory.md` (no tangent `ε²=0`) hit.

So: **PREDICTION, cashed on the combinatorial/telescoping spine (four shared ∅-axiom legs); the
smooth-manifold form complex + the de Rham iso is the named open leg, not a hand-wave.**

## Revelation (consolidation: de Rham = homology + integration + curvature under one reading)

**Collapse — de Rham, homology, FTC/Stokes, and curvature are ONE reading at the `q=±1` poles, not
four theories.** The single fold-height reading on the simplex `C`, run in its two directions and
paired against a chain, *generates all four*:
- run **down** in degree (`∂`, `L↓`) → chains, homology = `Residue(L↓,C)` (`homology.md`);
- run **up** in degree (`d`, `L↑`) → cochains/forms, de Rham = `Residue(L↑,C)` (here) — *the same `delta`
  op, the same `q=−1` two-step cancellation `dsq_zero = ∂sq_zero`*;
- **paired against the chain** (`∫`, the `Σ⊣Δ`/`∫⊣d` adjoint) → Stokes = the telescoping boundary-collapse
  ALREADY proved as `gauss_conservation_telescope` (`integration.md`);
- the **residue read as a loop** → curvature, `Σκ=2(1−b₁)` ties the de Rham/homology residue `b₁`
  directly to curvature (`curvature.md`).

This is the capstone of the README's "one character read four ways" (det = scalar / `Aut`-invariant /
loop-holonomy / `∂`-down): de Rham adds the **`∂`-UP** reading and the **integration pairing** that
binds it to the other three, making the de Rham theorem (de Rham ≅ singular) the literal statement
"`L↑` and `L↓` measure one residue", and Stokes the literal statement "`d ⊣ ∂` under `∫`". The four
classical theories collapse to **one reading + one adjoint + one residue tag** — exactly the model's two
load-bearing invariants (the character/adjoint and the `q=±1` residue), now spanning differential
topology in full. **EXTEND by consolidation; no new axis; the interior model v7.1 holds.** The one
genuine absence — the smooth form bundle — is located precisely, the differential-topology twin of
`curvature.md`'s missing smooth Riemann tensor.

## Note for the technique

- **de Rham confirms the bidirectional fold-height axis is the deepest structural lever.** `homology.md`
  established `∂` = height-DOWN; de Rham is height-UP on the SAME `delta` op. That `d²=0` and `∂²=0` are
  *one Lean theorem* (`dsq_zero_universal_delta4`) is the sharpest possible confirmation that the calculus
  was right to make height bidirectional rather than positing `d` and `∂` as two primitives.
- **The integration pairing is what turns two readings into an ADJOINT pair (Stokes).** de Rham's deepest
  lesson for the model: the `∫⊣d` adjunction (`integration.md`) is not auxiliary — it is *the de Rham
  theorem's engine*. Stokes = the boundary-collapse of the telescoped pairing = `gauss_conservation_telescope`.
  This ties the **resolution axis** (Σ/∫ dial) to the **adjoint-pair structure** (galois/adjunction)
  AT THE FORM LEVEL, the strongest cross-tie the resolution parameter has earned.
- **The graded-relation slot (`two_cells.md`) is vindicated.** The wedge's graded Leibniz
  `d(α∧β)=dα∧β±α∧dβ` is a genuine three-term graded relation, grounded as `leibniz_universal_delta4` —
  the same slot the skein relation and Jacobi (`lie_theory.md`) occupy. de Rham gives the slot its
  cleanest, fully-PURE instance.
- **The break is the same one, located again.** No new break: the smooth form bundle / de Rham iso is
  the `Real213`-cut/`h→0` + smooth-tensor absence shared with `curvature.md`/`derivative.md`/`lie_theory.md`
  — the *continuous* completion, not a structural gap in the discrete reading.

---

### Verified Lean anchors (file : theorem — all grep-verified on `lean/E213`; purity via `tools/scan_axioms.py`)

| Leg | Theorem (file : name) | Status |
|---|---|---|
| ★ `d` = `∂` read UP (one `delta` op, the coboundary `Cᵏ→Cᵏ⁺¹`) | `Lib/Math/Cohomology/Delta/Core.lean : delta`, `deltaAt`, `subsetIdx` | ∅-axiom ✓ (named "boundary/**coboundary** reading" in `homology.md`) |
| ★ `d²=0` = `∂²=0` (same theorem, `q=±1` sign-cancel) | `Lib/Math/Cohomology/Delta/V4Capstone.lean:41 : dsq_zero_universal_delta4` | **PURE, scanned 5/0** ✓ |
| ★★ Stokes = telescoping boundary-collapse (= `Σ⊣Δ`/`∫⊣d`) | `Lib/Math/Analysis/FluxMVT/TelescopingConservation.lean:152 : gauss_conservation_telescope` | **PURE, scanned 8/0** ✓ (docstring: divergence theorem, "cancellation IS conservation") |
| ★ integral = flux of antiderivative (`∫=F(b)−F(a)`, the adjunction) | `Lib/Math/Analysis/Integration/IntegralViaAnti.lean:47 : IsAntiderivative.integral_eq_flux` (`rfl`) | ∅-axiom ✓ (module scanned 1/0; `rfl` proof) |
| ★ `H*_dR = ker d/im d` = `Residue(L↑,C)` (Δ⁴ contractible ⇒ empty) | `Lib/Math/Cohomology/Examples/BettiKernel.lean:63 : reduced_betti_d4_contractible`, `kerSizeDelta`, `kerSize_5_0/1` | **PURE, scanned 11/0** ✓ |
| ★ wedge `∧` = `q=−1` antisymmetric product (the orientation/det sign) | `Lib/Math/Cohomology/Cup/SignedCup.lean:62 : cup1_antisymmetric`, `mergeSign` (`(−1)^inv`), `signed_cup_capstone` | **PURE, scanned 14/0** ✓ |
| ★ graded Leibniz `d(α∧β)=dα∧β±α∧dβ` (the graded-relation slot) | `Lib/Math/Cohomology/Delta/V4Capstone.lean:62 : leibniz_universal_delta4` (← `CupAW/Leibniz.leibniz_universal_5_1_1`) | **PURE, scanned 5/0** ✓ |
| Betti `b₁` ⇄ curvature (one `q=±1` residue, two readings) | `Lib/Math/Geometry/DiscreteCurvature/DiscreteGaussBonnet.lean:42,53 : gauss_bonnet_Kmn`, `totalCurv_eq` (`Σκ=2(1−b₁)`) | ∅-axiom ✓ (via `curvature.md`) |
| Hodge `⋆⋆=id` (the dual involution, `q=−1` once) | `Lib/Math/Cohomology/Delta/V4Capstone.lean:53 : hodge_involution_universal_delta4`; `Hodge/InvolutionLifts.lean` | **PURE, scanned 5/0** ✓ |
| wedge ring (`⌣` assoc/unit) | `Lib/Math/Cohomology/Cup/Ring.lean : ⌣` ring laws; `Cup/Core.lean : cup` | ∅-axiom ✓ |
| de Rham of T²/T²ⁿ (real cochain cohomology dims) | `Lib/Math/Cohomology/Surfaces/T2nBetti.lean : T2n_betti = binom (2n) k`, `T2n_betti_kunneth_recursion` | ∅-axiom ✓ |
| cross-frame | `homology.md` (`∂=L↓`, `∂²=0`, `Residue(L↓,C)`), `integration.md` (FTC=telescope, `∫⊣d`), `curvature.md` (`Σκ=2(1−b₁)`), `two_cells.md` (graded-relation slot), `parity.md`/`determinant.md` (`q=−1` det sign) | prior, ∅-axiom ✓ |

### Dropped / unverified citations (honest)

- **No smooth-manifold de Rham complex in `lean/E213`** — no `Ω^k(M)` smooth form bundle, no
  alternating cotangent tensor, no smooth chart/atlas, and **no de Rham comparison isomorphism
  `H*_dR ≅ H*_sing(·;ℝ)`** as a proved theorem (grep for `deRham`/`smooth form`/`Ω^k`/alternating-tensor
  returns only the combinatorial cochain complex + a conformal-curvature file). The discrete/cellular
  cochain version (`Cochain n k` + `delta`) IS built; the smooth completion + de Rham iso is the named
  open leg — the differential-topology twin of `curvature.md`'s missing smooth Riemann tensor and
  `derivative.md`'s general `Δ↔d/dx`.
- **`Multivariable/Stokes.lean` cited only as scope-honest scaffolding, NOT as the content.**
  `stokes_n_existence` (`∃k,k=n−1`) and `ddOmega_zero_skeleton` (`n−n=0`) are trivial skeletons;
  `greens_master`/`divergence_master`/`stokes_4d_master` are constant-field witnesses (`c·1−c·1=0`).
  The load-bearing discrete Stokes is `gauss_conservation_telescope`, cited above.
- **Purity note**: `dsq_zero_universal_delta4`, `leibniz_universal_delta4`, `hodge_involution_universal_delta4`
  (V4Capstone, 5/0), `cup1_antisymmetric`/`signed_cup_capstone` (SignedCup, 14/0),
  `gauss_conservation_telescope` (TelescopingConservation, 8/0), `reduced_betti_d4_contractible`
  (BettiKernel, 11/0) all freshly re-scanned PURE via `tools/scan_axioms.py` in this session.
  `integral_eq_flux` is `rfl` (cannot import an axiom; module scans 1/0).
