# Decomposition: free probability (free independence, ⊞, the R-transform, the free CLT, free cumulants, non-crossing partitions)

*A FRESH decomposition of "free independence / freeness, the free convolution `⊞`, the R-transform
`R_{μ⊞ν}=R_μ+R_ν`, the free CLT → the semicircle law, free cumulants, non-crossing partitions, the
Cauchy/Stieltjes transform" per `../README.md` (model v7.1). LEVERAGE phase. This note is the
**character-arrow companion** to `random_matrix.md` — that note read free probability through the
SPECTRAL side (the semicircle as the limiting eigenvalue density, a weight pushed through
`spectral.md`'s `q=+1` symmetric corner). The NEW datum here is the **`×↦+` character side**: the
**R-transform is the free analogue of `log` — the additive linearizer of `⊞`**, exactly the
`×↦+` arrow `gaussian_clt.md`/`entropy.md`/`exponential.md` carry for ordinary convolution, and
**free cumulants = non-crossing partitions = Catalan** is the free analogue of the classical
cumulants = all-partitions, with the moment↔cumulant relation grounded as a PURE
self-convolution (`CatalanSegner.catSeg_succ`). To avoid re-skinning the two neighbors: the
spectral fixed-point picture is theirs; this note's load-bearing claim is the **character arrow for
FREE convolution**, and its sharpest grounding is that the non-crossing-partition moment-cumulant
relation is literally `conv catSeg catSeg` in ∅-axiom Lean.*

The thesis under test (from the task): **free probability is the calculus's `×↦+` character for
FREE convolution** — the R-transform is the free `log` (the additive linearizer of `⊞`), the
semicircle is the free-CLT `q=+1` fixed point (the free Gaussian), and free cumulants = non-crossing
partitions = Catalan are the free analogue of classical cumulants = all-partitions. So free
probability = gaussian_clt's CLT structure with `⊞` replacing `*`, the R-transform replacing `log`,
the semicircle replacing the Gaussian — **NO new primitive**.

> **Honest split up front.** ABSENT (grep on `lean/E213` for `freeConvolution`/`free_convolution`,
> `RTransform`/`R_transform`, `freeCumulant`/`free_cumulant`/`cumulant`, `nonCrossing`/`non_crossing`/
> `noncrossing`, `semicircle`/`wigner`, `Stieltjes`/`cauchyTransform`/`resolvent`, `freeness`/
> `freeIndependence` returns **nothing**). BUILT and PURE: the classical convolution + its moment
> homomorphisms (`ConvolveProfile.mass_conv`/`momentNum_conv`, 20/0), the `q=+1` convolve-rescale
> contraction (`ConvolveRescaleContraction.Φ_contraction`, 20/0), the `×↦+` character
> (`vp_mul` 10/0, `entropy_additive`/`surprise_additive` 14/0), the `q=±1` tag
> (`ResidueTag` 55/0), and — the sharpest grounding — **the non-crossing-partition Catalan sequence as
> a convolution self-square** (`CatalanSegner.catSeg_succ : catSeg (n+1) = conv catSeg catSeg n`, 7/0;
> `Catalan.catalan` 17/0; `MotzkinNumbers.motzkin_catalan_table` 9/0). So this is a **PREDICTION with
> every engine built and the moment-cumulant non-crossing recursion PURE, the named free objects
> (`⊞`/R-transform/semicircle/free cumulant/non-crossing/Stieltjes) absent** — the
> `random_matrix.md`/`gaussian_clt.md` shape.

## The decomposition (C / Reading / Residue)

- **Construction `C` — NO new construction; the same weight-reading as `probability.md`/`gaussian_clt.md`.**
  A free random variable (a non-commutative random variable, an element of a tracial \*-algebra read
  through its moment sequence) is *not* a primitive. Its only handle in the calculus is `probability.md`'s
  **weight** read as a **moment sequence** — the `k`-th moment is the value-weighted count
  (`Expectation.discreteNum`), exactly `gaussian_clt.md`'s `Profile = List Nat` weight-profile. "Free"
  adds nothing constructive: it is a *different rule for composing two weights* (the free product of the
  underlying algebras vs the tensor product), not a new object. So a free variable is
  `⟨ family ∣ weight read as moments ⟩` — the same `C` as classical probability, differing only in the
  composition law `L` applies.

- **Reading `L_free = (free-weight-composition `⊞`) ∘ (rescale) at residue resolution`** — a **composite,
  iterated reading**, structurally identical to `gaussian_clt.md`'s `L`, with ONE slot swapped:
  1. **free-weight-composition (`⊞`)** — the free analogue of `gaussian_clt.md`'s classical convolution
     `⋆` (`ConvolveProfile.conv`). Classical: adding *independent* variables convolves their weights
     (`f ⋆ g`), and the moment relation is governed by *all* set partitions (the classical
     moment-cumulant formula). Free: adding *free* variables free-convolves their distributions (`μ ⊞ ν`),
     and the moment relation is governed by the **non-crossing** set partitions only. This is the single
     structural difference between this note and `gaussian_clt.md`: **all partitions → non-crossing
     partitions**, i.e. **the lattice the moment↔cumulant sum runs over is restricted to the planar
     (non-crossing) sub-lattice** — and that sub-lattice is *counted by Catalan*.
  2. **the R-transform = the `×↦+` linearizer of `⊞`** — the load-bearing claim. Just as classical
     cumulants (the `log` of the characteristic/moment-generating function) are **additive under `⋆`**
     (`κ_{μ⋆ν} = κ_μ + κ_ν`, the `×↦+` arrow `vp_mul`/`surprise_additive` carries), the **R-transform is
     additive under `⊞`** (`R_{μ⊞ν} = R_μ + R_ν`). So the R-transform is the **free `log`** — the
     construction-preserving reading whose readout turns the (free-)convolution PRODUCT into a SUM. It is
     `exponential.md`'s `×↦+` character arrow read for FREE independence: the same arrow that is
     `log`/`vp_mul`/`surprise_additive`/the cumulant-generating-function, now linearizing `⊞` instead of
     `⋆`. (The Cauchy/Stieltjes transform `G_μ(z)=∫(z−x)⁻¹dμ` is the moment-generating side; the
     R-transform is `R_μ(z)=G_μ⁻¹(z)−1/z` — the functional-inverse *is* the `+↦×`/`×↦+` direction toggle
     `exponential.md` names, the free analogue of `log = exp⁻¹`.)
  3. **rescale + residue resolution** — identical to `gaussian_clt.md`: standardize (center, shrink by
     `1/√n`) and read the iterate in the residue via a modulus `N(ε)`, the limit never the operand.

  So `L_free` = README's three slots meeting (**weight × character (`+`-mode) × resolution**) — exactly
  `gaussian_clt.md`'s `L`, with the convolution `⋆` replaced by `⊞` and the linearizer `log` replaced by
  the R-transform. **The only swapped piece is "all partitions → non-crossing partitions".**

- **Residue — the semicircle, tagged `q = +1` (converging) — the free-CLT fixed point.** The standardized
  free-sums climb toward one fixed profile and never land on it at any finite `n`: the **semicircle
  density** `ρ(x)=(1/2π)√(4−x²)` on `[−2,2]`, the fixed point of `Φ_free = rescale(μ ⊞ μ)`, named by its
  finite generator — its even moments are the **Catalan numbers** (counting non-crossing pair-partitions
  of `2k` points, the free analogue of the Gaussian's *all* pairings via Wick/Isserlis). It is
  `gaussian_clt.md`'s residue at the *same* `q=+1` converging pole as the Gaussian and φ, with `⊞` and the
  R-transform in the roles of `⋆` and `log`. The √-cut band edge `±2` is the `Real213` √-cut residue
  (exactly `random_matrix.md`/`spectral.md`'s eigenvalue-value residue).

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   a free random variable     =  ⟨ family ∣ weight read as a moment sequence ⟩   (C — NO new construction; probability.md's weight)
   free independence (freeness)=  the rule "compose weights by ⊞ (free product), not ⋆ (tensor)"   = a composition law on L, not a new object
   adding free variables       =  μ ⊞ ν  (free convolution)   = the FREE analogue of gaussian_clt's ⋆ (ConvolveProfile.conv)
   the R-transform             =  the ×↦+ linearizer of ⊞:  R_{μ⊞ν} = R_μ + R_ν   = the FREE log  (exponential.md's arrow, free)
   the Cauchy/Stieltjes G_μ    =  the moment-generating side;  R_μ = G_μ⁻¹ − 1/z   = the +↦× direction-toggle (exp⁻¹ = log)
   free cumulants κ_n          =  the additive coordinates (R-transform's coefficients)   = the free analogue of classical cumulants
   moment ↔ cumulant relation  =  the sum over NON-CROSSING partitions   (classical: sum over ALL partitions)   ← the ONLY swapped slot
   |non-crossing partitions(n)|=  the CATALAN number   (Catalan.catalan, non-crossing chord diagrams, PURE)
   the moment self-recursion   =  catSeg (n+1) = conv catSeg catSeg n   (CatalanSegner.catSeg_succ, PURE)  ← the convolution self-square
   centering / rescale         =  the resolution dial on L  (subtract mean, shrink spread)
   the semicircle              =  Residue(L_free, C),  q=+1   = the free-CLT (Φ_free) FIXED POINT  ("the free Gaussian")
   "free-sum → semicircle"     =  reached-by-none, narrowed by the moment/modulus (Catalan)   (limit never operand)
   universality                =  the q=+1 attractor's robustness (banach_unique's uniqueness)   = same as CLT universality
```

The proportion: **R-transform : `⊞` :: log/cumulant : `⋆` :: semicircle : Gaussian**. Free probability is
`gaussian_clt.md`'s entire CLT structure with three substitutions, ALL in `L` (none in `C`):

| | classical (`gaussian_clt.md`/`entropy.md`) | free (this note) |
|---|---|---|
| convolution (the iterated op) | `⋆` (`ConvolveProfile.conv`, PURE) | `⊞` (free convolution — ABSENT) |
| the `×↦+` linearizer | `log` / cumulants additive under `⋆` (`vp_mul`, `surprise_additive`, PURE) | the **R-transform** additive under `⊞` (ABSENT) |
| moment↔cumulant lattice | **ALL** set partitions (classical cumulants) | **NON-CROSSING** partitions only (free cumulants) |
| partition count | Bell numbers (all partitions) | **Catalan** numbers (`Catalan.catalan`, PURE) |
| CLT fixed point | the Gaussian (Wick: all pairings) | the **semicircle** (non-crossing pairings) |
| `q` tag | `+1` (converges) | `+1` (converges) |
| fixed-point engine | `Φ_contraction` / `banach_unique` (PURE) | same `q=+1` engine — `⊞`/R-transform ABSENT |

## LEVERAGE — does the calculus PREDICT free probability as "the CLT structure with `⊞`/R-transform/semicircle for `⋆`/log/Gaussian"?

**Honest verdict: PREDICTION — the strongest character-arrow extension since `entropy.md`, with the
moment-cumulant NON-CROSSING recursion grounded PURE; the named free objects absent.** The calculus,
*before looking for a free-probability object*, emits a specific non-trivial claim from its parts: a free
variable is `probability.md`'s weight read as moments; "free" is a *composition law* on `L` (the free
product), not a new `C`; the R-transform is `exponential.md`'s `×↦+` arrow (the additive linearizer of the
free convolution); and a `q=+1` residue is a **fixed point of a self-applying map** (`gaussian_clt.md`).
Composing these *forces*: **free probability = the CLT structure with `⊞`/R-transform/semicircle replacing
`⋆`/log/Gaussian, the moment↔cumulant lattice restricted from all partitions to non-crossing partitions
(= Catalan), the semicircle the `q=+1` free-CLT fixed point.** That is a derivation of free probability's
*shape* and *why it converges* from the model's slots, not a relabeling. Four legs, honestly graded:

### Leg 1 — the R-transform = the `×↦+` character arrow for FREE convolution (the free `log`). **PREDICTION — the NEW datum; the classical arrow BUILT PURE.**
This is the note's load-bearing claim and the part `random_matrix.md` did NOT develop (it named the
R-transform as "the `×↦+` arrow for free independence" but spent its weight on the spectral fixed point).
The calculus predicts the R-transform is to `⊞` exactly what `log`/cumulants are to `⋆`: the
construction-preserving reading whose readout turns a (free-)convolution PRODUCT into a SUM —
`R_{μ⊞ν} = R_μ + R_ν` is the SAME shape as `κ_{μ⋆ν} = κ_μ + κ_ν` is the SAME shape as `vp(mn)=vp m+vp n`
is the SAME shape as `surprise(jk) = surprise j + surprise k`. The classical instance is **built PURE**:
`vp_mul` (`Meta/Nat/VpMul.lean`, 10/0 — the `×↦+` valuation character), `entropy_additive`/
`surprise_additive` (`Entropy.lean`, 14/0 — `−log` turns the independence-product into a sum, the cumulant
linearizer). The character arrow now provably runs through parity, valuation, det, entropy, Noether,
Fourier, rep-theory characters (`representation.md`'s seven), and **free independence is the predicted
eighth** — with the genuine new content over `random_matrix.md` being that the **functional inversion**
`R_μ = G_μ⁻¹ − 1/z` IS `exponential.md`'s `+↦×` direction-toggle (`log = exp⁻¹`): the R-transform is the
free `log` not by analogy but by the *same arrow structure* (a character is bidirectional; its inverse
direction is the generating-function inverse). **Honest:** `⊞`, the R-transform, free cumulants, and the
Cauchy/Stieltjes transform are ABSENT (grep: nothing). The arrow is predicted, its classical instance
(`vp_mul`, `surprise_additive`) built PURE, the free instance the located gap.

### Leg 2 — free cumulants = non-crossing partitions = Catalan; the moment↔cumulant relation is a convolution self-square. **PREDICTION — grounded PURE at the sharpest point in the cluster.**
This is the note's *sharpest honest grounding* and a genuine datum beyond `random_matrix.md` (which cited
Catalan only as "the semicircle's moments"). The free moment-cumulant relation (Speicher) says the `n`-th
moment is the sum over **non-crossing partitions** of products of free cumulants — the planar restriction
of the classical (Bell-number) all-partitions sum. The number of non-crossing partitions / non-crossing
chord diagrams on `2n`/`n` points is the **Catalan number**, and `Catalan.lean`'s own docstring names
exactly this reading: *"non-crossing chord diagrams on 2n points"* (`Catalan.lean:19`, PURE 17/0). The
load-bearing find: **the moment↔cumulant relation, in its recursive form, is literally a convolution
self-square in ∅-axiom Lean** — `CatalanSegner.catSeg_succ : catSeg (n+1) = conv catSeg catSeg n`
(`CatalanSegner.lean:81`, 7/0 PURE). Segner's Catalan recursion `C_{n+1} = Σ_k C_k C_{n−k}` IS the
self-convolution `conv catSeg catSeg`, and the file's docstring states it verbatim: *"Catalan is the conv
self-square fixed point."* That is precisely the structure of the free moment-cumulant relation for the
semicircle (where all free cumulants vanish except `κ₂`, so the moment recursion reduces to the
self-convolution counting non-crossing pairings). So the calculus's prediction — *free cumulants live on
the non-crossing sub-lattice, counted by Catalan, related to moments by a convolution* — is grounded by a
PURE theorem stating the non-crossing-Catalan sequence IS a convolution self-square. The
**Motzkin–Catalan relation** `M(n) = Σ_k C(n,2k)·catalan(k)` (`MotzkinNumbers.motzkin_catalan_table`,
9/0 PURE) is a further grounding: Motzkin counts non-crossing diagrams *with isolated points* — the free
moment expansion of a general distribution (semicircle pairings + point-mass singletons), the
`⊞`-decomposition of an arbitrary free convolution, in PURE table form. **Honest:** the *named* free
cumulant / non-crossing-partition objects are ABSENT; what is PURE is the combinatorial skeleton (Catalan
= non-crossing, as a convolution self-square; Motzkin–Catalan as the point-decorated expansion).

### Leg 3 — the semicircle = the `q=+1` free-CLT fixed point. **PREDICTION — same engine as `gaussian_clt.md`, deferred to `random_matrix.md`.**
The semicircle as the `Φ_free = rescale(μ ⊞ μ)` `q=+1` fixed point is developed in `random_matrix.md`
(the spectral side); this note does not re-derive it, only ties it to leg 1/2: the semicircle is the free
CLT's fixed point precisely because all free cumulants beyond `κ₂` vanish under rescaling — the free
analogue of "the Gaussian is the unique distribution with all cumulants beyond `κ₂` zero". The engine is
the SAME `q=+1` convolve-rescale contraction (`ConvolveRescaleContraction.Φ_contraction`, 20/0;
`center_fixed`/`orbit_to_center`), one level up on `⊞`, and the same `ResidueTag` converge pole
(`converge_residue_fixed`, `golden_is_converge`, 55/0). **Honest:** the engine is PURE; the `⊞`/semicircle
instantiation is the located gap (the density is the reached-by-none `Real213`-cut limit; the Catalan
moments are the finite generator).

### Leg 4 — freeness = a composition law on `L`, not a new `C`. **PREDICTION / consolidation.**
The calculus predicts "free independence" is not a new construction but the choice of *how `L` composes two
weights* — classical independence composes by the tensor product (the `×↦·` character `Independence.joint`,
`probability.md`), free independence by the free product. Both are *the same weight-reading `C`* under
*different composition rules in `L`*; freeness is the "maximally non-commutative" composition (the free
product has no relations between the two algebras), classical independence the commutative one. This is
`groups.md`/`probability.md`'s lesson — readings compose, and the composition rule is a parameter — applied
to the convolution slot. The classical composition is built (`joint`, `mass_conv`, `momentNum_conv`); the
free composition `⊞` is the located gap. **Consolidation, not a new axis.**

## The located break (honest, in the `random_matrix.md`/`gaussian_clt.md` spirit)
**The free-probability objects are ABSENT.** Grep on `lean/E213` for `freeConvolution`/`free_convolution`,
`RTransform`/`R_transform`, `freeCumulant`/`free_cumulant`/`cumulant`, `nonCrossing`/`non_crossing`/
`noncrossing`, `semicircle`/`wigner`, `Stieltjes`/`cauchyTransform`/`resolvent`, `freeness`/
`freeIndependence` returns **nothing**. What is built is every *engine* the prediction rides on:
- the **`×↦+` character** (`vp_mul` 10/0, `entropy_additive`/`surprise_additive` 14/0) — the R-transform's
  classical kin (cumulants additive under `⋆`);
- the **classical convolution** `⋆` + moment homomorphisms (`ConvolveProfile.conv`, `mass_conv`,
  `momentNum_conv`, 20/0) — the scalar analogue of `⊞`;
- the **`q=+1` convolve-rescale fixed point** (`ConvolveRescaleContraction.Φ_contraction`,
  `center_fixed`, 20/0) — the semicircle's engine, one level up;
- the **non-crossing-partition combinatorics** as a convolution self-square (`Catalan.catalan` 17/0,
  `CatalanSegner.catSeg_succ` 7/0, `MotzkinNumbers.motzkin_catalan_table` 9/0) — the moment↔cumulant
  skeleton, the finite generator;
- the **`q=±1` tag** (`ResidueTag`, 55/0) — semicircle/Gaussian/φ one converge pole.

The genuinely missing primitives (a clean promotion target, not a failure):
1. **Free convolution `⊞`** on moment sequences + the **R-transform** as its `×↦+` linearizer (free
   cumulants additive) — the free analogue of `ConvolveProfile`'s `conv` + moment homomorphisms. The
   buildable witness named below is the start.
2. **The moment↔free-cumulant relation over non-crossing partitions** as a named object — the skeleton is
   PURE (`catSeg_succ` = the convolution self-square), the *named* `nonCrossingPartition`/`freeCumulant`
   bundle absent.
3. **The Cauchy/Stieltjes transform `G_μ`** + its functional inverse (the R-transform) — needs the
   `Real213` value-cut (the `z`-resolvent is a real/complex-valued object the repo's discrete moment
   skeleton does not host).
4. **The semicircle measure** + "semicircle = `Φ_free`'s fixed point" — same residual as
   `random_matrix.md`/`gaussian_clt.md` (the density is the reached-by-none limit; the Catalan moments are
   the finite generator).

This is the `random_matrix.md` residual read through the character side: there the missing object was the
spectral measure / `⊞`; here it is the R-transform / free-cumulant linearizer. Not a break of the model
(no new axis) — a located prediction with all engines present.

## Revelation

**The collapse + the forcing: free probability is `gaussian_clt.md`'s CLT structure with THREE
substitutions, ALL inside `L` (none in `C`) — `⊞` for `⋆`, the R-transform (the free `log`) for `log`,
the semicircle for the Gaussian — driven by ONE swapped slot: the moment↔cumulant lattice restricted from
ALL partitions to NON-CROSSING partitions (= Catalan).** The Revelation is *collapse + forcing*:

- **collapse** — the R-transform is not a new analytic gadget; it is the calculus's single `×↦+` character
  arrow (`vp_mul`/`surprise_additive`/`log`) read for the FREE convolution. `R_{μ⊞ν}=R_μ+R_ν`,
  `κ_{μ⋆ν}=κ_μ+κ_ν`, `vp(mn)=vp m+vp n`, `surprise(jk)=surprise j+surprise k` are **one arrow** — the
  eighth field it runs through. The functional inversion `R_μ=G_μ⁻¹−1/z` is `exponential.md`'s `+↦×`
  direction-toggle (`log=exp⁻¹`), so the R-transform is the free `log` by the *same arrow structure*, not
  by analogy.
- **forcing** — the difference between classical and free probability is **forced** to be a single thing:
  the moment↔cumulant sum runs over ALL partitions (classical) vs the NON-CROSSING sub-lattice (free).
  Everything else (the weight-reading `C`, the rescale dial, the `q=+1` fixed-point engine, the universality
  = `banach_unique`) is identical. The non-crossing lattice is **counted by Catalan**, and the
  moment↔cumulant recursion is **a convolution self-square** — grounded PURE: `Catalan.catalan` (docstring:
  "non-crossing chord diagrams on 2n points"), `CatalanSegner.catSeg_succ : catSeg(n+1)=conv catSeg catSeg n`
  ("the conv self-square fixed point"), `MotzkinNumbers.motzkin_catalan_table` (the point-decorated free
  expansion). So the semicircle is the free Gaussian *because* its only non-vanishing free cumulant is `κ₂`
  — the free analogue of the Gaussian having only `κ₂` — and the moments it then has are the non-crossing
  pairings = Catalan.

So the two load-bearing invariants — the **character arrow** (`×↦+`, now the R-transform for `⊞`) and the
**`q=+1` residue** (the semicircle, the free-CLT fixed point) — absorb free probability with nothing added:
free independence is a composition rule on `L`, the R-transform is the `×↦+` arrow for `⊞`, free cumulants
= non-crossing partitions = Catalan (PURE), and the semicircle is the `q=+1` convolve-rescale fixed point
one level up (`random_matrix.md`). The honest residue is precisely the *named field object*: `⊞`, the
R-transform, free cumulants, non-crossing partitions, the Cauchy/Stieltjes transform, and the semicircle
measure are absent — every *engine* (the `×↦+` character, the classical convolution, the `q=+1`
contraction, the Catalan/non-crossing self-convolution skeleton) is a PURE theorem.

## VALIDATE verdict

**EXTEND (by consolidation) + PREDICTION.** No new primitive; no break. Free probability EXTENDS the model
v7.1 by *fusing* four existing entries onto one swapped slot:
- `gaussian_clt.md` supplies the convolve-rescale `q=+1` fixed-point structure (`⊞` for `⋆`, the semicircle
  for the Gaussian);
- `entropy.md`/`exponential.md`/`vp_mul` supply the `×↦+` character (the R-transform = the free `log`);
- the Catalan / non-crossing combinatorics (`Catalan`, `CatalanSegner`, `Motzkin`) supply the moment↔cumulant
  skeleton (non-crossing partitions = the planar sub-lattice, a convolution self-square);
- `random_matrix.md` supplies the spectral realization (the semicircle = the limiting eigenvalue density).

The genuine NEW datum (not in either neighbor): **the R-transform is the `×↦+` character arrow for FREE
convolution — the free `log` — and free cumulants = non-crossing partitions = Catalan is the free analogue
of classical cumulants = all-partitions, with the moment↔cumulant relation grounded as a PURE convolution
self-square `catSeg_succ`.** The PREDICTION (the located gap, a promotion target): the named `⊞`/
R-transform/free-cumulant/non-crossing/Stieltjes/semicircle objects, of which the `⊞`-as-conv-on-moments
+ R-transform-as-`×↦+`-linearizer is within reach (the buildable witness below).

## Verified Lean anchors (file:line:theorem — all grep-confirmed this session; `tools/scan_axioms.py` from repo root)

| Leg | Theorem / def (file:line : name) | Purity (scanned this session) |
|---|---|---|
| ★★★★★ free cumulants = non-crossing partitions = Catalan; the moment↔cumulant relation IS a convolution self-square (Segner's recurrence through the abstract `conv`) | `Lib/Math/Combinatorics/CatalanSegner.lean:81 catSeg_succ` (`catSeg (n+1) = conv catSeg catSeg n`); `:67 catSeg_succ_sumTo`; `:37 catSeg` | **PURE 7/0** ✓ |
| ★★★★ the non-crossing-partition count = Catalan (docstring `:19` "non-crossing chord diagrams on 2n points"); the semicircle's even moments | `Lib/Math/Combinatorics/Catalan.lean:26 catalan`; `:53 catalan_5` (=42); `:63 catalan_recursion_3`..`:88 catalan_recursion_7` | **PURE 17/0** ✓ |
| ★★★ the point-decorated free expansion (non-crossing diagrams with isolated points = Motzkin); Motzkin–Catalan relation `M(n)=Σ_k C(n,2k)·catalan(k)` | `Lib/Math/Combinatorics/MotzkinNumbers.lean:114 motzkin_catalan_table`; `:106 motzkin_table`; `:130 motzkin_three_term_recurrence` | **PURE 9/0** ✓ |
| ★★★★★ the `×↦+` character arrow (the R-transform's classical kin — cumulants/log additive under convolution) | `Lib/Math/Probability/Information/Entropy.lean:83 entropy_additive`; `:90 surprise_additive`; `Meta/Nat/VpMul.lean:165 vp_mul` | **PURE 14/0 (Entropy), 10/0 (VpMul)** ✓ |
| ★★★★ the classical convolution `⋆` (the scalar analogue of `⊞`) + moment homomorphisms | `Lib/Math/Probability/Limit/ConvolveProfile.lean:149 conv`; `:190 mass_conv` (×↦·); `:239 momentNum_conv` (×↦+, mean of a sum = sum of means); `:268 profileMean_conv`; `:279 Φ_profile` (self-conv doubling) | **PURE 20/0** ✓ |
| ★★★★ the `q=+1` convolve-rescale fixed point (the semicircle's engine, one level up via `⊞`) | `Lib/Math/Probability/Limit/ConvolveRescaleContraction.lean:345 Φ_contraction`; `:419 center_fixed`; `:471 orbit_to_center`; `:399 Φ_picard_cauchy` | **PURE 20/0** ✓ |
| ★★★ the `q=±1` residue tag (the converge pole — semicircle/Gaussian/φ one tag) | `Lib/Math/Foundations/ResidueTag.lean:160 converge_residue_fixed`; `:180 golden_is_converge`; `:86 multiplier_unimodular`; `:228 residue_tag_two_poles` | **PURE 55/0** ✓ |

**Fresh purity scan (this session, `python3 tools/scan_axioms.py <module>` from repo root):**
`Combinatorics.Catalan` 17/0, `Combinatorics.CatalanSegner` 7/0, `Combinatorics.MotzkinNumbers` 9/0,
`Probability.Limit.ConvolveProfile` 20/0, `Probability.Limit.ConvolveRescaleContraction` 20/0,
`Probability.Information.Entropy` 14/0, `Meta.Nat.VpMul` 10/0, `Foundations.ResidueTag` 55/0. All pure / 0
dirty.

## Dropped / flagged (honest — the located break, NOT cited as anchors)

- **Free convolution `⊞`** — ABSENT (grep: no `freeConvolution`/`free_convolution`). The classical `⋆` is
  built PURE (`ConvolveProfile.conv`); `⊞` is predicted with the same moment-additivity shape but on
  *free cumulants* (non-crossing) rather than classical cumulants (all partitions).
- **The R-transform** (`R_{μ⊞ν}=R_μ+R_ν`, the `×↦+` linearizer of `⊞`, the free `log`) — ABSENT (grep: no
  `RTransform`/`R_transform`). Predicted as `exponential.md`'s character arrow for free independence; the
  classical instance (`vp_mul`, `surprise_additive`, cumulants additive under `⋆`) is the kin.
- **Free cumulants** / **non-crossing partitions** as named objects — ABSENT (grep: no `freeCumulant`/
  `cumulant`/`nonCrossing`/`non_crossing`/`noncrossing`). The combinatorial skeleton is PURE (Catalan =
  non-crossing count, `catSeg_succ` = the convolution self-square, Motzkin = the point-decorated expansion);
  the named bundle is the gap.
- **The Cauchy/Stieltjes transform `G_μ`** + its functional inverse — ABSENT (grep: no `Stieltjes`/
  `cauchyTransform`/`resolvent`). Needs the `Real213` value-cut (the `z`-resolvent is a real/complex-valued
  object the discrete moment skeleton does not host).
- **The semicircle measure** + "semicircle = `Φ_free`'s fixed point" — ABSENT (grep: no `semicircle`/
  `wigner`). The `q=+1` contraction engine + the Catalan moments are PURE; the density is the
  reached-by-none `Real213`-cut limit (same residual as `random_matrix.md`/`gaussian_clt.md`).
- **Freeness / free independence** as a named composition law — ABSENT (grep: no `freeness`/
  `freeIndependence`). Predicted as the free-product composition on `L` (vs classical independence's
  tensor-product composition `Independence.joint`); a composition rule, not a new object.

### Verified buildable witness (a clean promotion target, the first step toward `⊞`)
**The free moment-cumulant relation for the semicircle is ALREADY a PURE convolution self-square** —
`CatalanSegner.catSeg_succ : catSeg (n+1) = conv catSeg catSeg n` (7/0). This is the load-bearing
combinatorial half of "`⊞` on the semicircle". A concrete buildable promotion (not asserted as proved here,
flagged as a target): define `freeConvMoments` on a moment-sequence type as the analogue of
`ConvolveProfile.conv` but summing over the non-crossing sub-lattice, and prove the semicircle's moment
sequence is its self-convolution fixed point — `catSeg_succ` already supplies the recursion
`C_{n+1}=Σ_k C_k C_{n−k}` (= the non-crossing pair-partition count) as `conv catSeg catSeg`. This is within
reach of the existing `Convolution213.conv` + `Catalan`/`CatalanSegner` infrastructure, exactly as
`random_matrix.md`'s 2×2 GOE toy is within reach of `Mat2SymmetricSpectrum`. **No false witness is
proposed**: the only NEW numeric claim made (the buildable target) reuses `catSeg_succ`'s already-PURE
recursion; every cited equation above is a grep-confirmed existing theorem, scanned PURE this session.
