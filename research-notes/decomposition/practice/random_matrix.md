# Decomposition: random matrix theory (Wigner semicircle, GUE/GOE, free convolution, universality)

*A FRESH decomposition of "a random symmetric matrix, the eigenvalue distribution, the Wigner
semicircle law, the GUE/GOE ensembles, the spectral measure, eigenvalue rigidity / universality, free
probability's free convolution `⊞` and the R-transform" per `../README.md` (model v7.1). LEVERAGE
phase — the bar is PREDICTION/REVELATION, consolidating `spectral.md` (eigenvalue = `q=+1`
scale-residue; symmetric ⟹ real spectrum, the `q=+1` corner) + `gaussian_clt.md` (the Gaussian = the
`q=+1` convolve-rescale fixed point) + `probability.md` (the weight-reading) + the convolution
(`ConvolveProfile.conv`). The thesis: random matrix theory has **no construction of its own** — it is
`spectral.md`'s symmetric-spectral reading composed with `probability.md`'s weight; and the **Wigner
semicircle is the `q=+1` fixed point of free convolve-rescale**, the matrix/spectral analogue of
`gaussian_clt.md`'s Gaussian — "the Gaussian of free probability".*

The hypotheses under test (from the task):
1. A **random matrix** = `⟨ a symmetric Mat-reading | random entries (a weight on entry-space) ⟩` —
   `spectral.md`'s symmetric real-spectrum reading (`disc_symmetric_nonneg`, the `q=+1` corner)
   composed with `probability.md`'s weight. The eigenvalue **distribution** = the spectral measure =
   the weight pushed through the spectrum-reading.
2. The **Wigner semicircle law** = a `q=+1` FIXED POINT — the matrix/spectral analogue of
   `gaussian_clt.md`'s Gaussian: as the CLT is the fixed point of convolve-rescale on *scalar*
   weights, the semicircle is the fixed point of the analogous operation on *spectral measures* (free
   convolution `⊞`). The tie under test: **semicircle : free convolution :: Gaussian : classical
   convolution — both the `q=+1` fixed point of a convolve-rescale**.
3. **Free convolution `⊞`** = the non-commutative/spectral analogue of `ConvolveProfile.conv`; the
   **R-transform** linearizes `⊞` (the free analogue of `log`/the character — the `×↦+` arrow for
   free independence), tying `exponential.md`/the character arrow.
4. **Eigenvalue rigidity / universality** = the `q=+1` attractor's robustness — the spectral fixed
   point is reached regardless of the entry distribution, the same universality as the CLT.

> **Honest split up front.** `spectral.md`'s symmetric real spectrum (`disc_symmetric_nonneg`, PURE),
> `gaussian_clt.md`'s `q=+1` convolve-rescale fixed point (`Φ_contraction`, `gaussian_center_fixed_via_engine`,
> PURE), the convolution operator (`ConvolveProfile.conv` + `mass_conv`/`momentNum_conv`, PURE),
> `probability.md`'s weight (`discreteNum`), and even the **semicircle's moment sequence** (the Catalan
> numbers, `Combinatorics/Catalan.catalan`, PURE) are all **built and ∅-axiom**. What is **absent** —
> grep on `lean/E213` for `semicircle`/`wigner`/`freeConvolution`/`RTransform`/`randomMatrix`/`GUE`/
> `GOE`/`ensemble`/`spectralMeasure`/`cumulant`/`Stieltjes`/`resolvent` returns **nothing** — is an
> *actual random-matrix object, the semicircle measure, free convolution `⊞`, and the R-transform*.
> So this is a **PREDICTION with the engines built but the field object missing** — exactly the
> `knots.md`/`information_geometry.md` shape: the consolidating picture is right and every load-bearing
> *engine* is a PURE theorem from a sister decomposition, but the specifically-random-matrix legs
> (`⊞`, the semicircle measure, the R-transform) are the located missing leg. The verdict states this
> precisely.

## The decomposition (C / Reading / Residue)

- **Construction `C` — NO new construction; a symmetric `Mat`-reading + a weight on entry-space.**
  A random matrix is *not* a primitive. The matrix is `spectral.md`/`determinant.md`'s `C` exactly —
  a `2×2` (`Mat2`) or `d×d` bundle of directed counts built by `mul`, carrying the orientation bit
  and fold-height. **Random** adds nothing constructive: it is `probability.md`'s **weight-reading**
  placed on the *entry space* (each entry is a distinguishable read as a `ProbabilityCut`/weight). A
  random *symmetric* matrix constrains the entries to `b = c` (`Mat2SymmetricSpectrum.IsSymmetric`) —
  the *only* structural input, exactly as `graph_theory.md`'s adjacency reading is symmetric. So a
  random matrix is `⟨ symmetric Mat-reading | weight on entries ⟩` — `spectral.md` composed with
  `probability.md`, no new `C`.

- **Reading `L_RM = (symmetric-spectral reading) ∘ (push-forward of the entry-weight)`.** This is a
  **composite of two readings already in the calculus** (`probability.md`'s composite-reading slot):
  1. the **entry-weight** (`probability.md`): the entries carry a weight `w` (a `ProbabilityCut` /
     `discreteNum` value per entry);
  2. the **symmetric-spectral reading** (`spectral.md`): `M ↦ spectrum(M)`, which for a *symmetric*
     `M` lands in the `q=+1` real corner (`disc_symmetric_nonneg` — the discriminant is a sum of
     squares, so the spectrum is REAL; a symmetric operator never rotates). The eigenvalue is the
     `q=+1` scale-residue of the linear reading (`spectral.md`'s thesis).
  The **eigenvalue distribution** is the entry-weight *pushed through* the spectrum-reading — the
  composite `spectrum ∘ weight`. This is the **spectral measure** (the empirical eigenvalue density):
  a weight on the *spectrum* induced by the weight on the *entries*. So a random matrix's spectral
  measure = `probability.md`'s weight, read through `spectral.md`'s `q=+1` symmetric corner. **No new
  reading** — the two compose.

- **Residue — the limiting spectral density (the Wigner semicircle), tagged `q = +1` (converging).**
  As the matrix size `N → ∞`, the spectral measure (rescaled by `1/√N`) climbs toward one fixed
  profile and *never lands on it* at any finite `N` — the **semicircle density** `ρ(x) = (1/2π)√(4−x²)`
  on `[−2,2]`. This is the **fixed point of the free convolve-and-rescale map** on spectral measures,
  named by a finite generator (its moments — the *Catalan numbers*, `Combinatorics/Catalan.catalan`),
  never grasped as an analytic object. It is `gaussian_clt.md`'s residue at the *same* `q=+1`
  converging pole as the Gaussian and φ — a self-applying map *with* a fixed point, asymptoting toward
  it — **one level up** (on spectra, via free convolution `⊞`, instead of on scalar weights via
  classical `⋆`). The reached-by-none value (`√(4−x²)`, the band edge `±2`) is the `Real213` √-cut
  residue, exactly `spectral.md`'s honest eigenvalue-value residue.

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   a random matrix          =  ⟨ symmetric Mat-reading | weight on entries ⟩   (C — NO new construction; spectral.md ∘ probability.md)
   the entry randomness      =  probability.md's weight on the entry space         (discreteNum / ProbabilityCut)
   symmetric ⟹ real spectrum =  the q=+1 corner (disc_symmetric_nonneg, sum of squares ≥ 0)  ← GUE/GOE Hermitian postulate
   the eigenvalue distribution=  spectrum ∘ weight = the SPECTRAL MEASURE (weight pushed through the spectrum reading)
   sum of independent matrices=  FREE convolution ⊞ of spectral measures   = the spectral analogue of conv (ConvolveProfile.conv)
   the R-transform            =  the ×↦+ linearizer of ⊞  (free analogue of log/the character arrow)   = exponential.md's arrow, free
   the Wigner semicircle      =  Residue(L_RM, C), q=+1  = the free convolve-rescale FIXED POINT  ("the Gaussian of free probability")
   "spectral measure → semicircle" = reached-by-none, narrowed by the moment/modulus (Catalan numbers)   (limit never operand)
   universality / rigidity    =  the q=+1 attractor's robustness (same fixed point regardless of entry weight) = CLT universality
   the band edge ±2, √(4−x²)   =  the Real213 √-cut residue (reached-by-none value)   = spectral.md's eigenvalue-value residue
```

The map to iterate is `Φ_free : μ ↦ rescale(μ ⊞ μ)` (free-convolve a spectral measure with itself,
then rescale by `1/√2`). The semicircle is `Φ_free`'s fixed point — the **exact analogue** of the
Gaussian as `gaussian_clt.md`'s `Φ = rescale(weight ⋆ weight)` fixed point, with `⊞` in the role of
`⋆`. The two stand in a clean proportion:

| | `gaussian_clt.md` (Gaussian) | `random_matrix.md` (Wigner semicircle) |
|---|---|---|
| what iterates | a **scalar weight** (`probability.md`) | a **spectral measure** (a weight on a spectrum) |
| self-applying map | `Φ = rescale(weight ⋆ weight)` (classical conv) | `Φ_free = rescale(μ ⊞ μ)` (FREE conv) |
| convolution | classical `⋆` (`ConvolveProfile.conv`, PURE) | free `⊞` (the non-commutative analogue — ABSENT) |
| linearizer (the `×↦+` arrow) | `log` / characteristic function (`exponential.md`) | the **R-transform** (ABSENT) |
| fixed point | the Gaussian | the semicircle |
| moments (finite generator) | factorial moments | the **Catalan numbers** (`catalan`, PURE) |
| `q` tag | `+1` (converges) | `+1` (converges) |
| reached-by-none | no finite `n` lands on the Gaussian | no finite `N` lands on the semicircle |
| universality | CLT: any finite-variance summand → Gaussian | Wigner: any finite-variance entry → semicircle |
| Lean engine | `Φ_contraction`/`gaussian_center_fixed_via_engine` (PURE) | same `q=+1` engine — but `⊞`/measure object ABSENT |

## LEVERAGE — does the calculus PREDICT the semicircle as the free convolve-rescale fixed point?

**Honest verdict: PREDICTION (the strongest tie in the spectral cluster), engines built, field object
missing — the `knots.md`/`information_geometry.md` shape.** The calculus, *before looking for a
random-matrix object*, emits a specific non-trivial claim from its parts: a random matrix is
`spectral.md`'s symmetric reading composed with `probability.md`'s weight; the eigenvalue distribution
is the weight pushed through the `q=+1` symmetric spectrum; summing independent matrices free-convolves
their spectral measures (`⊞`, the spectral analogue of `⋆`); and a `q=+1` residue is a **fixed point of
a self-applying map** (`gaussian_clt.md`/`golden_ratio.md`). Composing these *forces* the form: **the
limiting spectral density is the fixed point of free-convolve-and-rescale, computed via a moment/
modulus, never grasped — and it is the semicircle, the `q=+1` spectral twin of the Gaussian.** That is
a derivation of the semicircle law's *shape* and *why it converges* from the model's slots, not a
relabeling. Four legs, honestly graded:

### Leg 1 — random matrix = symmetric-spectral reading ∘ weight; the distribution = the pushed weight. **PREDICTION, both component engines BUILT PURE.**
The decomposition's first claim is a *composition of two existing readings*, and **both halves are
built ∅-axiom**:
- the **symmetric `q=+1` real spectrum** is `Mat2SymmetricSpectrum.disc_symmetric_nonneg` (PURE,
  29/0 incl. deps): a symmetric `Mat2` has `disc = (a−d)²+(2b)² ≥ 0`, so its spectrum is real — the
  elliptic `disc<0` escape is structurally unavailable. **This IS the GUE/GOE Hermitian postulate**:
  "the matrix is symmetric/Hermitian so the spectrum is real" is *exactly* `disc_symmetric_nonneg`,
  the `q=+1` corner. (Same theorem `graph_theory.md` used for the Laplacian's real spectrum — random
  matrices and graph Laplacians share the symmetric `q=+1` reading.)
- the **weight on entries** is `probability.md`'s `ProbabilityCut`/`discreteNum` — the value-weighted
  count, PURE.
The **eigenvalue distribution = spectrum ∘ weight** (the spectral measure) is then the *composite of
two built readings*; what is missing is only the *named random-matrix object* welding them (a
`d×d` symmetric matrix with `ProbabilityCut`-valued entries and its induced spectral measure — ABSENT,
grep confirms). So leg 1 is a PREDICTION whose **two component engines are each PURE**; the composite
object is the located gap.

### Leg 2 — the Wigner semicircle = the `q=+1` free convolve-rescale fixed point ("the Gaussian of free probability"). **PREDICTION — the leverage, the engine is the SAME `q=+1` contraction.**
This is the load-bearing tie. `gaussian_clt.md` proved the Gaussian is the `q=+1` fixed point of
`Φ = rescale(weight ⋆ weight)` — `Φ_contraction : Contraction (dyMet L) Φ` (PURE, 20/0),
`center_fixed`/`orbit_to_center` (the `q=+1` fixed point reached-by-none),
`gaussian_center_fixed_via_engine` (the center as the modulated-Banach limit, PURE). The calculus
predicts the semicircle is the **identical structure one level up**: the self-applying map is
`Φ_free = rescale(μ ⊞ μ)` acting on **spectral measures** (not scalar weights), and its fixed point
(the semicircle) is the `q=+1` converging residue by the *same signature* — reached-by-none, narrowed
by a moment/modulus. The proportion **semicircle : `⊞` :: Gaussian : `⋆`** is the prediction, and it
is non-trivial: it says (a) the semicircle is the *unique attractor* of a convolve-rescale, (b) it sits
at the same `q=+1` pole as the Gaussian/φ/ODE-flow (one `ResidueTag`), and (c) it converges *because*
the rescale is a contraction — the very property `Φ_contraction` proves for the classical case. The
engine the semicircle residue needs (`banach_fixed_point`/`Φ_contraction`/the modulated completion) is
**already built and PURE**; only its instantiation on a *free-convolution* operator is missing.

**★ The moments leg is grounded — the Catalan numbers are BUILT PURE.** The semicircle's even moments
are exactly the **Catalan numbers** (`∫ x^{2k} ρ_sc(x) dx = C_k`, counting the non-crossing
pair-partitions of `2k` points — the free analogue of the Gaussian's pairings via Wick/Isserlis). And
`Combinatorics/Catalan.catalan` is **built ∅-axiom** (17/0 PURE): `catalan 0..7 = 1,1,2,5,14,42,132,429`,
the segre/convolution recursion `catalan_recursion_3..7`. So the **finite generator the calculus names
for the semicircle residue — its moment sequence — is a PURE object in the repo**, exactly as the
Gaussian's preserved moments (`ConvolveProfile.momentNum_conv`) are. This is the sharpest honest
grounding: *the semicircle is named by its moments; those moments are the Catalan numbers; the Catalan
numbers are built and PURE.* The limit density is reached-by-none; its finite signature (Catalan
moments) is the computable operand — the calculus's standing "limit never the operand, the modulus is"
rule, instantiated.

### Leg 3 — free convolution `⊞` = the spectral analogue of `conv`; the R-transform = the `×↦+` linearizer. **PREDICTION, the classical analogue BUILT PURE, the free object ABSENT.**
The calculus predicts `⊞` is to spectral measures what `ConvolveProfile.conv` (the classical Cauchy
convolution `⋆`) is to scalar weights — the operation of "adding two free/independent variables". The
classical side is **built PURE**: `ConvolveProfile.conv` with `mass_conv` (mass multiplies, `×↦·`) and
`momentNum_conv` (mean of a sum = sum of means, `×↦+`) — the convolution operator and its moment
homomorphisms (20/0). The calculus predicts `⊞` carries the *same* moment-additivity but for **free
cumulants** (the R-transform is additive under `⊞`: `R_{μ⊞ν} = R_μ + R_ν`), the free analogue of the
classical fact that the *cumulants* (log-characteristic function) add under `⋆`. So **the R-transform
is `exponential.md`'s `×↦+` character arrow, read for free independence**: the same arrow that is
`log`/`vp_mul`/`surprise_additive`/the characteristic-function-logarithm — *linearize a convolution
into a sum*. The character arrow now provably runs through parity, valuation, det, entropy, Noether,
Fourier, rep-theory characters (`representation.md`'s seven), and the calculus predicts an **eighth
reading: free independence**, with `⊞ ↦ +` via the R-transform exactly as `⋆ ↦ +` via `log`/cumulants.
**Honest:** `⊞`, the R-transform, and free cumulants are **ABSENT** (grep: nothing). The arrow is
predicted, its classical instance built, the free instance the located gap.

### Leg 4 — universality / eigenvalue rigidity = the `q=+1` attractor's robustness. **PREDICTION — the same universality as the CLT.**
The calculus predicts Wigner universality (the limiting spectral density is the semicircle *regardless
of the entry distribution*, given finite variance) is the **`q=+1` attractor's robustness** — the same
phenomenon as CLT universality (the Gaussian is reached regardless of the summand distribution). Both
are the statement "the contraction `Φ`/`Φ_free` has a *unique* fixed point, reached from any seed in
the basin" — `banach_unique` (the Banach fixed point is unique) + `Φ_contraction` (the rescale is a
contraction, so the orbit from *any* seed converges to the one center). Universality is not a separate
miracle: it is `banach_fixed_point`'s **uniqueness** read on the spectral convolve-rescale. Eigenvalue
rigidity (the eigenvalues sit at predictable quantile positions with tiny fluctuation) is the *rate*
half — the geometric modulus `picard_cauchy`'s `N(m)` controlling how fast the orbit reaches the fixed
point. **Honest:** `banach_unique`/`Φ_contraction` are PURE (the *engine* of universality), but no
random-matrix universality theorem is stated (no `⊞`, no spectral measure object). PREDICTION, engine
built.

## The located break (honest, in the `knots.md`/`spectral.md`/`information_geometry.md` spirit)
**The random-matrix / semicircle / free-convolution objects are ABSENT.** Grep on `lean/E213` for
`semicircle`, `wigner`, `freeConvolution`/`free_convolution`, `RTransform`/`R_transform`,
`randomMatrix`/`random_matrix`, `GUE`/`GOE`, `ensemble`, `spectralMeasure`/`spectral_measure`,
`cumulant`, `Stieltjes`/`resolvent` returns **nothing**. What is built is every *engine* the
prediction rides on:
- the **symmetric `q=+1` real spectrum** (`Mat2SymmetricSpectrum.disc_symmetric_nonneg`, PURE) — the
  GUE/GOE Hermitian postulate;
- the **`q=+1` convolve-rescale fixed point** (`gaussian_clt.md`'s `Φ_contraction`,
  `gaussian_center_fixed_via_engine`, `banach_unique`, PURE) — the Gaussian's engine, the same one the
  semicircle needs;
- the **classical convolution** (`ConvolveProfile.conv`, `mass_conv`, `momentNum_conv`, PURE) — the
  scalar analogue of `⊞`;
- the **weight** (`probability.md`'s `discreteNum`, PURE);
- the **semicircle's moment sequence** (`Combinatorics/Catalan.catalan`, PURE) — the finite generator.

The genuinely missing primitives (a clean promotion target, not a failure):
1. **A random-matrix object** — a `d×d` symmetric matrix with `ProbabilityCut`-valued entries, and its
   induced **spectral measure** (the weight pushed through `spectrum`). At `d=2` this is *within reach*
   of the existing `Mat2`/`Mat2SymmetricSpectrum`/`probability` infrastructure (cf. `graph_theory.md`'s
   2-vertex Laplacian promotion): a `Mat2` with a weight on `(a,b,d)` and the induced distribution of
   `(tr ± √disc)/2` — a 2×2 GOE toy, `disc = (a−d)²+(2b)² ≥ 0` guaranteeing real eigenvalues PURE.
2. **Free convolution `⊞`** on spectral measures + the **R-transform** as its `×↦+` linearizer (the
   free cumulants additive) — the spectral analogue of `ConvolveProfile`'s moment homomorphisms.
3. **The semicircle as `Φ_free`'s fixed point** — instantiate `gaussian_clt.md`'s `q=+1` contraction
   engine on `⊞` (the same located-open shape as the Gaussian *density profile*: a measure space + an
   `L¹`/Cauchy modulus the repo lacks; the moments — Catalan — are the finite generator, the density is
   the reached-by-none limit).

This is the dual of `gaussian_clt.md`'s own residual (there the Gaussian *density profile* is the
reached-by-none limit, the discrete moments built; here the semicircle *density* is the reached-by-none
limit, the Catalan moments built) — *one level up*, on spectra. Not a break of the model (no new axis)
— a located prediction with all engines present.

## Revelation

**The residue surfaced and the collapse: random matrix theory has no construction of its own — a
random matrix is `spectral.md`'s symmetric reading composed with `probability.md`'s weight, and the
Wigner semicircle is `gaussian_clt.md`'s `q=+1` convolve-rescale fixed point read ONE LEVEL UP, on
spectral measures via free convolution `⊞` — "the Gaussian of free probability".** The collapse is
precise:

- **A random matrix = `⟨ symmetric Mat-reading | weight on entries ⟩`** — `spectral.md` ∘
  `probability.md`, no new `C`. The eigenvalue distribution = the spectral measure = the entry-weight
  pushed through the `q=+1` symmetric spectrum (`disc_symmetric_nonneg` — the GUE/GOE Hermitian
  postulate is the `q=+1` corner, the *same* theorem `graph_theory.md`'s Laplacian used).
- **The semicircle : free convolution :: Gaussian : classical convolution — both the `q=+1` fixed
  point of a convolve-rescale.** The proportion is the leverage: `Φ_free = rescale(μ ⊞ μ)` on spectral
  measures is the structural twin of `gaussian_clt.md`'s `Φ = rescale(weight ⋆ weight)` on scalar
  weights; the semicircle is `Φ_free`'s `q=+1` converging residue exactly as the Gaussian is `Φ`'s.
  The convolve-rescale **contraction engine is the same one, BUILT PURE** (`Φ_contraction`); only the
  free-convolution instantiation is missing.
- **The semicircle's finite generator is BUILT** — its moments are the Catalan numbers
  (`Combinatorics/Catalan.catalan`, PURE), the free analogue of the Gaussian's pairings. The limit
  density is reached-by-none; its Catalan-moment signature is the computable operand — the calculus's
  "limit never the operand" rule, instantiated on a spectral measure.
- **The R-transform = `exponential.md`'s `×↦+` character arrow, read for free independence** — the
  eighth field the character arrow runs through; **universality = `banach_unique`'s uniqueness** read
  on the spectral convolve-rescale (same robustness as the CLT).

So the two load-bearing invariants — the **character arrow** (`×↦+`/`×↦·`) and the **`q=+1` residue** —
absorb random matrix theory with nothing added: the eigenvalue is `spectral.md`'s `q=+1` scale-residue,
the spectral measure is `probability.md`'s weight pushed through it, the semicircle is
`gaussian_clt.md`'s `q=+1` convolve-rescale fixed point one level up, and the R-transform is the
character arrow for free independence. The honest residue is precisely the *field object*: the
random-matrix/semicircle/free-convolution/R-transform constructs are absent — the engines (symmetric
real spectrum, the `q=+1` contraction, the classical convolution, the weight, the Catalan moments) are
each a PURE theorem, the consolidating object that welds them is the located missing leg.

## Does the Wigner semicircle fall out as the `q=+1` free-convolve-rescale fixed point? — YES (as a prediction; engines built, the `⊞` object missing).

The chain is structurally complete and engine-grounded:
- a random symmetric matrix ⟹ real spectrum ⟹ `q=+1` corner (`disc_symmetric_nonneg`, PURE);
- the eigenvalue distribution = `probability.md`'s weight pushed through the spectrum (composite
  reading, both halves PURE);
- summing independent matrices = free-convolving their spectral measures (`⊞`, the spectral analogue
  of `ConvolveProfile.conv` — PREDICTED, classical `⋆` built PURE);
- the limiting density = `Φ_free = rescale(μ ⊞ μ)`'s `q=+1` fixed point = the semicircle (PREDICTED,
  the `q=+1` contraction engine `Φ_contraction`/`gaussian_center_fixed_via_engine` built PURE);
- the semicircle's moments = the Catalan numbers (`catalan`, BUILT PURE) — the finite generator.

So the semicircle falls out as the `q=+1` free-convolve-rescale fixed point *as a prediction with all
engines present and the moment generator built*, more completely grounded than a bare conceptual leg
(the Catalan moments + the symmetric corner + the contraction are all PURE), but short of a closed
derivation (no `⊞`/semicircle-measure object). PREDICTION, consolidating spectral + gaussian_clt +
probability + the convolution.

## Touches on model v7.1?

**No new primitive; a decisive consolidation onto the `q=+1` convolve-rescale fixed point, one level
up (on spectra).** Random matrix theory does not add to model v7.1 — it *fuses* four existing entries:
- the **symmetric `q=+1` spectrum** (`spectral.md`'s `Mat2SymmetricSpectrum`) supplies "the random
  symmetric matrix has a real spectrum, the `q=+1` corner" (= the GUE/GOE Hermitian postulate);
- the **weight-reading** (`probability.md`) supplies the entry randomness and the spectral measure
  (weight pushed through the spectrum);
- the **`q=+1` convolve-rescale fixed point** (`gaussian_clt.md`'s `Φ_contraction`/`banach_unique`)
  supplies the semicircle (the fixed point, one level up via `⊞`) AND universality (uniqueness);
- the **`×↦+` character arrow** (`exponential.md`) supplies the R-transform (the free linearizer).

Note for the README's batch log:

> **Random matrix theory = `spectral.md`'s symmetric reading ∘ `probability.md`'s weight; the Wigner
> semicircle = `gaussian_clt.md`'s `q=+1` convolve-rescale fixed point ONE LEVEL UP (on spectral
> measures, via free convolution `⊞`) — "the Gaussian of free probability".** A random matrix has no
> construction of its own (`⟨symmetric Mat | weight on entries⟩`); the eigenvalue distribution = the
> spectral measure = the weight pushed through the `q=+1` symmetric spectrum
> (`Mat2SymmetricSpectrum.disc_symmetric_nonneg`, PURE — the GUE/GOE Hermitian postulate IS the `q=+1`
> corner, same theorem as `graph_theory.md`'s Laplacian). **semicircle : `⊞` :: Gaussian : `⋆`, both
> the `q=+1` fixed point of a convolve-rescale** — the same contraction engine (`gaussian_clt.md`'s
> `Φ_contraction`/`gaussian_center_fixed_via_engine`, PURE), one level up. The semicircle's finite
> generator — its moments = the **Catalan numbers** — is BUILT PURE (`Combinatorics/Catalan.catalan`,
> 17/0). The R-transform = `exponential.md`'s `×↦+` arrow for free independence (the eighth field);
> universality = `banach_unique`'s uniqueness, the CLT's robustness. Located break (the
> `knots.md`/`information_geometry.md` shape): the random-matrix / semicircle-measure / free-convolution
> `⊞` / R-transform objects are ABSENT — every *engine* is PURE, the welding field object is the
> missing leg. Promotion target: a 2×2 GOE toy (a `Mat2` with a weight on `(a,b,d)`, induced spectrum
> distribution) inside the existing `Mat2SymmetricSpectrum`/`probability` infrastructure.

## Verified Lean anchors (grep + `tools/scan_axioms.py` this session — all PURE, build-confirmed)

| Leg | Theorem / def (file:line : name) | Purity |
|---|---|---|
| ★★★★★ symmetric ⟹ real spectrum (GUE/GOE Hermitian postulate = the `q=+1` corner) — `disc = (a−d)²+(2b)² ≥ 0` | `Lib/Math/NumberSystems/Real213/Mat2/Mat2SymmetricSpectrum.lean:83 disc_symmetric_nonneg`; `:67 disc_symmetric_sum_of_squares`; `:137 symmetric_spectrum_real` | **PURE** (29/0 scanned this session) ✓ |
| ★★★ symmetric `disc=0 ⟺ scalar` (cusp); non-scalar ⟹ distinct real eigenvalues | `…/Mat2SymmetricSpectrum.lean:93 disc_zero_iff_scalar`; `:111 disc_symmetric_pos_of_nonscalar` | **PURE** ✓ |
| ★★★★★ the `q=+1` convolve-rescale fixed point engine (the semicircle's engine, one level up) — convolve⋆rescale IS a `Contraction` | `Lib/Math/Probability/Limit/ConvolveRescaleContraction.lean:345 Φ_contraction`; `:419 center_fixed`; `:471 orbit_to_center`; `:399 Φ_picard_cauchy` | **PURE** (20/0 scanned) ✓ |
| ★★★★ the `q=+1` center as the modulated-Banach completion-limit | `Lib/Math/Probability/Limit/DyadicCompletion.lean:612 gaussian_center_fixed_via_engine`; `:366 orbit_to_center_completion` | **PURE** (per `gaussian_clt.md`) ✓ |
| ★★★ Banach fixed point + uniqueness (universality engine) + geometric modulus (rigidity rate) | `Lib/Math/Analysis/BanachFixedPoint.lean:202 banach_fixed_point`; `:250 banach_unique`; `:154 picard_cauchy` | ∅-axiom (per `gaussian_clt.md`) ✓ |
| ★★★★ the classical convolution `⋆` (the scalar analogue of `⊞`) + moment homomorphisms | `Lib/Math/Probability/Limit/ConvolveProfile.lean:149 conv`; `:190 mass_conv` (×↦·); `:239 momentNum_conv` (×↦+, mean of a sum = sum of means); `:279 Φ_profile` (self-conv doubling) | **PURE** (20/0 scanned) ✓ |
| ★★★ the entry-weight (`probability.md`'s weight on entry-space) | `Lib/Math/Probability/Foundation/Cut.lean:27 ProbabilityCut`; `Foundation/Expectation.lean:62 discreteNum` (value-weighted count) | ∅-axiom (per `probability.md`) ✓ |
| ★★★★ the semicircle's moment sequence = the **Catalan numbers** (the finite generator, free analogue of Gaussian pairings) | `Lib/Math/Combinatorics/Catalan.lean:26 catalan`; `:53 catalan_5` (=42); `:63 catalan_recursion_3`..`catalan_recursion_7` | **PURE** (17/0 scanned this session) ✓ |
| ★★★ eigenvalue = `q=+1` scale-residue; det/tr = e₂/e₁ of the spectrum (the spectral reading) | `Lib/Math/NumberSystems/Real213/Mat2/Mat2Spectrum.lean:103 det_eq_e2`; `:115 tr_eq_e1`; `:167 disc_eq_gap_squared`; `Mat2CayleyHamilton.lean:37 cayley_hamilton` | **PURE** (13/0 scanned) ✓ |
| ★★ the `×↦+` character arrow (the R-transform's classical kin — `log`/cumulants additive under convolution) | `Lib/Math/Probability/Information/Entropy.lean:83 entropy_additive`; `:90 surprise_additive`; `Meta/Nat/VpMul.lean:165 vp_mul` | ∅-axiom (per `exponential.md`/`entropy.md`) ✓ |
| `q=±1` residue tag (the converge pole — semicircle/Gaussian/φ/ODE one tag) | `Lib/Math/Foundations/ResidueTag.lean:73 ResidueTag`; `:160 converge_residue_fixed`; `:86 multiplier_unimodular`; `:228 residue_tag_two_poles` | **PURE** (per `gaussian_clt.md`/`spectral.md`) ✓ |
| det = `×↦·` multiplicative character (cross-ref `determinant.md`); symmetric reading shared with the graph Laplacian (`graph_theory.md`) | `…/Markov/SternBrocotMarkov.lean:104 det2_mul`; `Combinatorics/GraphConnectivity.lean:61 closed_const` | ∅-axiom (prior) ✓ |

**Fresh purity scan (this session):** `scan_axioms.py` — `Mat2SymmetricSpectrum` 29/0,
`ConvolveProfile` 20/0, `ConvolveRescaleContraction` 20/0, `Mat2CayleyHamilton`+`Mat2Spectrum` 13/0,
`Combinatorics.Catalan` 17/0. All pure / 0 dirty; build clean.

## Conceptual-only / ABSENT legs (honest — the located break, not cited as anchors)

- **A random-matrix object** — a symmetric matrix with `ProbabilityCut`-valued entries + its induced
  **spectral measure** — is **ABSENT** (grep: no `randomMatrix`/`GUE`/`GOE`/`ensemble`/`spectralMeasure`
  in `lean/E213`). The two halves (symmetric spectrum, weight) are each PURE; the composite object is
  the gap. Promotion target: a 2×2 GOE toy inside `Mat2SymmetricSpectrum`/`probability`.
- **Free convolution `⊞`** — the non-commutative/spectral analogue of `ConvolveProfile.conv` — is
  **ABSENT** (grep: no `freeConvolution`/`free_probability`). The classical `⋆` is built PURE; `⊞` is
  predicted with the same moment-additivity shape (additive *free cumulants*).
- **The R-transform** (the `×↦+` linearizer of `⊞`, the free analogue of `log`/cumulants) — **ABSENT**
  (grep: no `RTransform`/`cumulant`/`Stieltjes`/`resolvent`). Predicted as `exponential.md`'s character
  arrow for free independence; the classical instance (cumulants additive under `⋆`) is the kin.
- **The Wigner semicircle measure** + the theorem "semicircle = `Φ_free`'s fixed point" — **ABSENT**.
  The `q=+1` contraction engine is built PURE and the moments (Catalan) are built PURE; the *density*
  is the reached-by-none limit (same residual as `gaussian_clt.md`'s Gaussian density profile — needs a
  measure space + Cauchy/`L¹` modulus the repo lacks), one level up on spectra.
- **Universality / eigenvalue rigidity** as a stated random-matrix theorem — **ABSENT** as an object;
  its *engine* (`banach_unique` uniqueness + `picard_cauchy` rate) is PURE. PREDICTION.
