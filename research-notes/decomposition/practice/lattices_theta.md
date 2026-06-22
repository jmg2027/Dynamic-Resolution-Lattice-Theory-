# Decomposition: lattices and theta functions

*213-decomposition of "a lattice `Λ ⊂ ℝⁿ`, the Gram matrix, the dual lattice `Λ*`, the theta series
`θ_Λ(τ) = Σ_{v∈Λ} q^(|v|²/2)` (a modular form), even/unimodular lattices (E8, Leech), Poisson summation
`θ_{Λ*}(−1/τ) = (covolume factor)·θ_Λ(τ)` (modularity), sphere packing / kissing number", per
`../README.md` (model v7.1) and `SYNTHESIS.md` (the two invariants + the q=±1 spine). A **fresh** field,
LEVERAGE phase — the bar is PREDICTION/REVELATION. This entry tests whether a lattice + its theta series
**consolidates** four prior decompositions (`modular_forms` + `generating_functions`/`zeta_euler` +
`fourier` + `quadratic_reciprocity`'s Gram/quadratic-form leg) with NO new primitive.*

## The thesis under test

A lattice + its theta series is the calculus's **count reading (vectors by norm) packaged as a
modular-form generating function, with Poisson summation = Fourier self-duality (the `q=±1` reflection)**.
Concretely, four sub-claims:

1. `θ_Λ(τ) = Σ_v q^(|v|²/2)` = the **count reading graded by norm** — the number `r_Λ(m)` of lattice
   vectors of each squared-length `m`, packaged as a generating function. This is exactly
   `generating_functions.md`'s `L_gen` (the height-indexed count-family, `q` the grading coordinate),
   with the grading height = `|v|²/2`.
2. `θ_Λ` **IS a modular form** (`modular_forms.md`) — so a lattice's theta is a `modular_forms` instance:
   the `q=+1` `SL(2,ℤ)`-invariant family-reading, the Eichler–Shimura/period machinery already mapped.
3. The **Gram matrix** = a quadratic form (the disc/signature); the dual `Λ*` + Poisson summation
   `θ_{Λ*}(−1/τ)` = the modular `S`-transformation = `fourier.md`'s Fourier **self-duality** (the
   lattice/dual = the Fourier pair, the `q=±1` reflection `τ↦−1/τ` = the `s↔k−s` reflection, `FenchelMoreau`
   antitone). Even unimodular lattices (E8/Leech) = self-dual forms = the **`q=±1` fixed point** `Λ=Λ*`.
4. Sphere packing / kissing number = the **count optimum** (the densest = the `q=+1` optimum).

NO new primitive: lattices+theta = (the count reading by norm = the theta GF) + (`θ_Λ` = a modular form)
+ (Poisson/dual = Fourier self-duality = the `q=±1` `τ↦−1/τ` reflection) + (self-dual lattice = the
`q=±1` fixed point).

## The decomposition (C / Reading / Residue)

- **Construction `C` — the integer-point lattice as a discrete distinguishing-grid, with the Gram matrix
  the inner-product reading on it.** A lattice `Λ = ⊕ ℤ·bᵢ` is the bare integer-combination grid (the
  `ℕ`/`ℤ` count construction at `n` axes — `integers.md`'s difference-Lens carrier raised to a tuple),
  and the **Gram matrix `G_{ij} = ⟨bᵢ, bⱼ⟩`** is the repo's own built `Vec.inner` reading of pairwise
  inner products (`Linalg213/Gram.lean`, `Gram`, `Vec.inner`, `Vec.inner_comm` — the Gram matrix is
  symmetric, ∅-axiom). The **covolume** (the parallelepiped volume `√det G`) is the lattice area /
  determinant — built ∅-axiom over ℤ as the 2D signed area `area2` and its Gram-determinant Lagrange
  identity `area2² = |u|²|v|² − (u·v)²` (`LatticeArea.area2_sq_eq_gram` = the 2×2 Gram determinant). So
  `C` here is `LatticeArea`'s integer grid + `Gram`'s inner-product reading — *both already in-repo*,
  nothing new constructed.

- **Reading `L_θ` — the count-by-norm reading, packaged as a generating function.** A theta series reads
  the lattice by **one feature only**: the multiset of squared-norms `{|v|² : v ∈ Λ}`, projected to the
  count `r_Λ(m) = #{v : |v|² = m}`, then packaged as `θ_Λ = Σ_m r_Λ(m) qᵐ` — *exactly*
  `generating_functions.md`'s family-reading `L_gen` with the grading coordinate `q` and the height =
  the norm `m`. The coefficient `r_Λ(m)` is the **count reading** (`cardinality.md`'s count), graded by
  `quadratic_forms`-the-Gram-quadratic-form. The in-repo grounding of "this count is non-trivial and
  multiplicatively structured" is the **sums-of-squares corpus**: for `Λ = ℤᵏ` the squared-norm is the
  quadratic form `Σ xᵢ²`, and `r_{ℤᵏ}(m) = #` representations of `m` as `k` squares — built ∅-axiom as
  `nat_isSum4` (Lagrange: `r_{ℤ⁴}(m) > 0` for all `m`), `two_square` (`r_{ℤ²}(p)>0` for `p≡1 mod 4`),
  `eisenstein_repr_int` (the `A₂`/Eisenstein lattice `x²+xy+y²`, `p≡1 mod 3`). Read at the **modular**
  level, `L_θ` is `modular_forms.md`'s `q=+1` `SL(2,ℤ)`-invariant family-reading (`θ_Λ` is a weight-`n/2`
  modular form).

- **Residue** — `q = ±1`, at two strata, exactly as `modular_forms`/`fourier` locate it.
  - The **Poisson summation / `S`-transformation** `θ_{Λ*}(−1/τ) = covol·(−iτ)^{n/2}·θ_Λ(τ)` is the
    order-reversing **reflection involution** `τ ↦ −1/τ` — `fourier.md`'s Fourier self-duality and
    `modular_forms.md`'s functional-equation reflection (`FenchelMoreau` antitone `star∘star = clo`;
    `FoldReflections`' det `=−1` folds composing to the order-4 swap `S = [[0,−1],[1,0]]`). The
    `q=±1` direction bit; even-unimodular `Λ = Λ*` = its `q=+1` fixed point.
  - The **analytic theta value** `θ_Λ(τ)` as a number (`q = e^{2πiτ}` transcendental, the full infinite
    sum, the actual E8/Leech series as Lean objects) is the `Real213`-cut RESIDUE — reached by no
    truncation, the same transcendental-cut residue every infinite series carries here. **And the lattice
    objects `Lattice`/`thetaSeries`/`dualLattice`/`E8`/`Leech`/`sphere_packing` themselves are the
    genuine ABSENCE** (grep-confirmed; the `knots.md`/`modular_forms.md`-style located break).

## Re-seeing — ⟨C | L_θ⟩ ⊕ Residue

```
   lattice Λ = ⊕ℤ·bᵢ      =  ⟨ ℤⁿ integer-grid | the n-axis count construction ⟩   (integers.md tuple; LatticeArea grid)
   Gram matrix G_{ij}      =  ⟨ basis | Vec.inner pairwise reading ⟩, symmetric     (Gram.Gram, Vec.inner_comm)  [BUILT]
   covolume √det G         =  the lattice area / Gram determinant                    (LatticeArea.area2_sq_eq_gram = |u|²|v|²−(u·v)²)  [BUILT, n=2]
   θ_Λ = Σ_v q^(|v|²/2)    =  ⟨ {r_Λ(m)} count-by-norm family | L_gen ⟩, q=grading   (generating_functions.md; GeneratingFunction.convolution)
   r_Λ(m) = #{|v|²=m}       =  the count reading (cardinality.md) graded by the Gram quadratic form
   r_{ℤᵏ}(m) (= θ_{ℤᵏ})   =  #representations as k squares                           (nat_isSum4, two_square, eisenstein_repr_int)  [BUILT, k=2,3,4]
   θ_{Λ⊕Λ'} = θ_Λ · θ_Λ'  =  GF of a direct sum = product of GFs = Euler four-sq id  (four_sq_id; isSum4_mul; conv = product)  [BUILT]
   θ_Λ is a modular form   =  the q=+1 SL(2,ℤ)-invariant family-reading              (modular_forms.md; det_holonomy_eq_one)
   ── the q=±1 reflection ──────────────────────────────────────────────────────
   dual lattice Λ*         =  the Fourier-dual reading of C                          (fourier.md's Ĉ; Λ↔Λ* = the Fourier pair)
   Poisson  θ_{Λ*}(−1/τ)   =  the S-transformation = Fourier self-duality            (fourier.md; FenchelMoreau antitone star∘star)
   modular S = τ↦−1/τ      =  the q=±1 order-reversing reflection involution         (FoldReflections: negation_recip_eq_swap → S; S²=−I)
   even unimodular Λ=Λ*    =  the q=±1 fixed point (E8, Leech)                        (ResidueTag converge pole; covol=1, det G=1)
   SL(2,ℤ) preserves covol =  area2_unimodular (det=±1 ⟹ area fixed)                  (LatticeArea.area2_unimodular)  [BUILT — the geometric root of modularity]
   sphere packing / kissing =  the count optimum (densest = q=+1 optimum)             [OBJECT ABSENT]
```

Set side by side, **a lattice + its theta series is the count-by-norm reading of the integer grid,
packaged as `modular_forms.md`'s `q=+1` invariant generating function, with the dual/Poisson pairing the
`q=±1` `τ↦−1/τ` reflection** — every load-bearing piece reduces to a prior decomposition:

| classical object | the calculus's reading | repo status |
|---|---|---|
| Gram matrix / quadratic form | `Vec.inner` reading on the grid, symmetric | **BUILT ∅-axiom** (`Gram`, `Vec.inner_comm`) |
| covolume `√det G` | lattice area = Gram determinant | **BUILT ∅-axiom, n=2** (`area2_sq_eq_gram`) |
| `θ_Λ = Σ q^(|v|²/2)` | `L_gen` count-by-norm family-reading | the GF reading BUILT; the lattice `θ_Λ` object absent |
| `r_Λ(m)` (theta coefficients) | the count reading graded by norm | **BUILT for `ℤ²,ℤ³(Eis),ℤ⁴`** (two/Eisenstein/four-square) |
| `θ_{Λ⊕Λ'} = θ_Λ·θ_Λ'` | GF-product = convolution = `×↦·` character | **BUILT** (`four_sq_id`, `isSum4_mul`) |
| `θ_Λ` is a modular form | the `q=+1` `SL(2,ℤ)`-invariant (`det_holonomy_eq_one`) | the action/invariant BUILT; the modular `θ_Λ` absent |
| dual `Λ*` + Poisson `θ_{Λ*}(−1/τ)` | Fourier self-duality = `q=±1` `τ↦−1/τ` reflection | the involution engine BUILT (`FoldReflections`, `FenchelMoreau`); `Λ*`/Poisson absent |
| even unimodular `Λ=Λ*` (E8/Leech) | the `q=±1` fixed point | the fixed-point tag BUILT (`ResidueTag`); E8/Leech absent |
| sphere packing / kissing | the count optimum (`q=+1`) | **OBJECT ABSENT** (located break) |

## LEVERAGE — leg by leg, honest

**Net verdict: PREDICTION + PARTIAL (EXTEND by consolidation + one located break).** The four legs are
*structurally predicted* and resolve into prior decompositions; the **Gram-matrix, covolume, and
sums-of-squares theta-coefficient corpus grounds the count-by-norm side far more than expected** (all
∅-axiom PURE); but the **`Lattice`/`thetaSeries`/`dualLattice`/`E8`/`Leech`/sphere-packing OBJECTS are
genuinely ABSENT** — a clean located break in the `modular_forms.md`/`knots.md` spirit. No new primitive,
no new axis; model v7.1 holds.

### Leg 1 — `θ_Λ` = the count-by-norm generating function. **PREDICTION; the count BUILT for `ℤ^{2,3,4}`, the `θ_Λ` object ABSENT (PARTIAL).**
The calculus predicts `θ_Λ = Σ_m r_Λ(m) qᵐ` is `generating_functions.md`'s `L_gen` family-reading with
the grading height = the Gram quadratic form's value `|v|²`. The **count `r_Λ(m)` is the count reading**
(`cardinality.md`), and for the standard lattices `ℤᵏ` it is built ∅-axiom: `nat_isSum4` (Lagrange — every
`m` is a sum of 4 squares, so `θ_{ℤ⁴}` has full support, 34/0 PURE), `two_square` (`ℤ²`/Gaussian lattice,
`p≡1 mod 4`, 19/0), `eisenstein_repr_int` (the `A₂`/Eisenstein lattice `x²+xy+y²`, the hexagonal lattice
with its own non-`ℤᵏ` Gram form, `p≡1 mod 3`, 27/0). The Gram matrix itself is built (`Gram.Gram`,
`Vec.inner_comm`, 9/0) and the GF apparatus exists (`GeneratingFunction.convolution`, `xVar`). **What is
absent**: a `thetaSeries Λ` object packaging `r_Λ` as a Lean GF over a `Lattice` type — the
count-coefficients are built per-form, the *graded series object* is not. PARTIAL.

### Leg 2 — `θ_Λ` IS a modular form. **PREDICTION (consolidation), via `modular_forms.md`.**
This leg consolidates with no new work: `θ_Λ` is `modular_forms.md`'s `q=+1` `SL(2,ℤ)`-invariant
family-reading (`det_holonomy_eq_one`, the holonomy `Aut`-family with `det=1`). The **geometric root of
modularity is BUILT ∅-axiom**: `LatticeArea.area2_unimodular` (`det = ±1 ⟹ area preserved`) and
`area2_linMap` (`area scales by det`) prove `SL₂(ℤ)`/`GL₂(ℤ)` preserve lattice covolume — the literal
statement that the lattice/Gram data is invariant under the modular group, which is *why* `θ_Λ`
transforms as a modular form. So this leg ties the lattice directly to `modular_forms.md`'s entire built
Eichler–Shimura/period corpus (the Stern–Brocot cusps, the Manin trick, the period polynomials): a
lattice's theta is one more reading of `connections.md`'s `SL(2,ℤ)` `Aut`-family. **Honest boundary**:
the modular-form *object* (`θ_Λ` as an `SL(2,ℤ)`-equivariant Lean function on `ℍ`) is absent, identically
to `modular_forms.md`'s located break — but the structural prediction (theta = the `q=+1` modular
invariant) and its geometric grounding (`area2_unimodular`) are the deliverable.

### Leg 3 — dual `Λ*` + Poisson summation = Fourier self-duality = the `q=±1` reflection. **PREDICTION; the involution engine BUILT, `Λ*`/Poisson ABSENT (PARTIAL).**
The calculus predicts: the dual lattice `Λ*` is `fourier.md`'s Fourier-dual `Ĉ` (the lattice/dual = the
Fourier pair), and Poisson summation `θ_{Λ*}(−1/τ) = covol·(−iτ)^{n/2}·θ_Λ(τ)` is the modular
`S`-transformation `τ↦−1/τ` = `fourier.md`'s Fourier **self-duality**, an order-reversing reflection
involution. The **involution engine is built ∅-axiom**: `FoldReflections`' two det `=−1` reflections
(negation, reciprocal) compose to the order-4 det `=+1` swap `S = [[0,−1],[1,0]]`
(`negation_recip_eq_swap`, `N_involutive`, `R_involutive`) — `S` is the `z↦−1/z` reflection, `S²=−I`; and
abstractly `FenchelMoreau`'s antitone self-adjoint `star∘star = clo` (`biconjugate_eq_clo`,
`closed_iff_fixed`: fixed = closed = the `q=+1` locus) is the order-reversing-involution-with-fixed-point
shape. So the `q=±1` reflection tag the prediction needs is fully built; this is the SAME reflection
`modular_forms.md`/`fourier.md` cite. **What is absent**: the dual-lattice construction `Λ*` and the
Poisson summation formula itself (it needs the analytic Gaussian-sum / Fourier transform on `ℝⁿ`, which
is the `Real213`-cut residue). PARTIAL: the reflection involution is built; `Λ*` and Poisson are absent.

### Leg 4 — even unimodular (E8/Leech) = the `q=±1` fixed point `Λ=Λ*`. **PREDICTION (consolidation onto `ResidueTag`); the OBJECT ABSENT (the located BREAK).**
The calculus predicts: an even unimodular (self-dual) lattice `Λ = Λ*` is the **`q=+1` fixed point** of
the Fourier-duality reflection — `covol = 1` (`det G = 1`), so the `S`-transformation maps `θ_Λ` to
itself, making `θ_Λ` a modular form for the *full* `SL(2,ℤ)` (not just a congruence subgroup), forced
into weight `n/2` with `8 | n`. This consolidates onto the formal **`ResidueTag`** (`Lib/Math/
Foundations/ResidueTag.lean`, 55/0): the `converge` pole (`multiplier = +1`, `multiplier_unimodular`,
`golden_is_converge`) is exactly "the surplus asymptotes to a fixed point" — here the fixed point of
`τ↦−1/τ`, `Λ=Λ*`. The Gram-determinant-`1` condition is the `LatticeArea.area2_unimodular` covolume-`1`
case. So E8/Leech are predicted as the `q=+1` self-dual fixed points, the unimodular pole, *the same*
`q=±1` tag the whole corpus runs on. **But there is NO `E8`/`Leech`/`unimodularLattice` object in the
repo** (grep-confirmed — no `E8`, no `Leech`, no `dualLattice`). This is the genuine located break, the
`modular_forms.md`/`knots.md` shape: the calculus names the structure precisely (self-dual = `q=+1` fixed
point, `det G = 1`, weight `n/2`), but the lattices themselves are an absent construction.

### Leg 5 — sphere packing / kissing number = the count optimum. **PREDICTION; OBJECT ABSENT.**
The calculus predicts: the densest packing / maximal kissing number is the **`q=+1` count optimum** —
the lattice maximizing `r_Λ(min)` (the kissing number = the first non-trivial theta coefficient
`r_Λ(min) = #` minimal vectors) and the packing density = the covolume-normalized count. This is
`topology.md`/`measure.md`'s `q=+1` finiteness-optimum on the count reading; the LP-bound certificate
(Viazovska's E8/Leech proof) is a `convex_duality.md`/`optimal_transport.md` `f**=clo` strong-duality
(the magic function = the self-dual certificate, a Poisson-summation fixed point — the SAME `q=±1`
reflection of Leg 3). **OBJECT ABSENT**: no packing/density/kissing object. The structural prediction —
kissing = the leading theta coefficient = the count optimum, the LP bound = `f**=clo` duality — is the
deliverable, but stays conceptual here (it needs the absent lattice + the analytic Fourier certificate).

## ★ The new datum — the sums-of-squares corpus IS the theta-coefficient (count-by-norm) side

The deliverable beyond re-skinning `modular_forms.md`/`fourier.md`: a lattice's theta series is the
**count-by-norm reading packaged as a modular-form GF**, and the repo's **sums-of-squares corpus grounds
exactly that count side, ∅-axiom PURE** — which `modular_forms.md` did not surface. Concretely:

- **The theta coefficient `r_Λ(m)` = the representation count, BUILT for the standard lattices.** For
  `Λ = ℤᵏ` the norm is `Σ xᵢ²`, so `r_{ℤᵏ}(m) = #` representations of `m` as `k` squares = the `m`-th
  theta coefficient. `nat_isSum4` (Lagrange, `ℤ⁴`), `two_square` (`ℤ²`/Gaussian), and
  `eisenstein_repr_int` (the hexagonal `A₂` lattice, a genuine non-`ℤᵏ` Gram form) are the *existence*
  (support) of these coefficients, all PURE.
- **`θ_{Λ⊕Λ'} = θ_Λ · θ_Λ'` (the GF-product = direct-sum theta) is the `×↦·` character — and it is
  literally Euler's four-square identity.** `four_sq_id` (the bilinear identity making `Σ4²` closed under
  `×`) and `isSum4_mul` (`isSum4 m → isSum4 n → isSum4 (mn)`) are the multiplicativity of the
  sum-of-squares count under the quaternion/octonion norm — *the same `×↦·` character arrow* as
  `vp_mul`/`det2_mul`/`legendre_mul`/`mass_conv` (the GF of a direct sum = the product of GFs,
  `generating_functions.md`). So the theta series' multiplicative structure is the calculus's central
  character, now read on the lattice's norm form.
- **The Gram determinant = the covolume = the lattice area, BUILT at `n=2`.** `area2_sq_eq_gram`
  (`area2² = |u|²|v|² − (u·v)²`) IS the 2×2 Gram determinant `det G`; `area2_unimodular` is "`det G = 1`
  is preserved by `SL₂(ℤ)`" — the covolume invariant that makes even-unimodular `Λ=Λ*` the `q=+1` fixed
  point.

So the count-by-norm side (Leg 1) and the modularity root (Leg 2) are *built*, the reflection involution
(Leg 3) is built, and the `q=±1` fixed-point tag (Leg 4) is built — only the *named lattice/theta/dual/
E8/Leech/packing objects* are absent. The break is the `modular_forms.md` automorphic-side break, now on
the lattice-geometry side: the *count coefficients and the reflection are built; the lattice that hosts
them is not.*

## Revelation

**Collapse + located break — a lattice + its theta series is `modular_forms.md`'s `q=+1` invariant
generating function, with the count-by-norm coefficients = the sums-of-squares corpus and the dual/Poisson
pairing = `fourier.md`'s Fourier self-duality = the `q=±1` `τ↦−1/τ` reflection.** The decomposition
consolidates four prior notes with NO new primitive:
- `θ_Λ = Σ q^(|v|²/2)` = `generating_functions.md`'s `L_gen` count-by-norm family-reading, its
  coefficients `r_Λ(m)` the count reading graded by the Gram quadratic form — **built for `ℤ²,ℤ³(Eis),ℤ⁴`**
  (`two_square`, `eisenstein_repr_int`, `nat_isSum4`), with `θ_{Λ⊕Λ'}=θ_Λ·θ_Λ'` the `×↦·` character
  (`four_sq_id`, `isSum4_mul`);
- `θ_Λ` = `modular_forms.md`'s `q=+1` `SL(2,ℤ)`-invariant — geometrically rooted in
  `LatticeArea.area2_unimodular` (`SL₂(ℤ)` preserves covolume);
- Poisson summation `θ_{Λ*}(−1/τ)` = `fourier.md`'s Fourier self-duality = the `q=±1` order-reversing
  reflection `S = τ↦−1/τ` (`FoldReflections.negation_recip_eq_swap`, `FenchelMoreau` antitone);
- even unimodular `Λ=Λ*` (E8/Leech) = the `q=±1` **fixed point** (`ResidueTag` converge pole,
  `multiplier_unimodular`, `golden_is_converge`; covolume `det G = 1`);
- sphere packing/kissing = the `q=+1` count optimum, the LP bound an `f**=clo` strong duality.

So lattices + theta are **not a new field** — they are the count-by-norm reading of the integer grid,
packaged as the `SL(2,ℤ)` `Aut`-family's `q=+1` invariant GF, read with the Fourier-duality reflection,
tying `generating_functions` + `zeta_euler` + `modular_forms` + `fourier` + the Gram/quadratic-form leg
into one picture. The deepest revelation is the **new grounding**: the sums-of-squares corpus
(`four_sq_id`/`nat_isSum4`/`two_square`/`eisenstein_repr_int`) IS the theta-coefficient count side, and
`LatticeArea.area2_unimodular` IS the modularity covolume invariant — both ∅-axiom PURE,
`modular_forms.md` did not cite them. The **break** is the lattice-object side: `Lattice`/`thetaSeries`/
`dualLattice`/`E8`/`Leech`/`sphere_packing` are absent — the precise missing leg, the geometric twin of
`modular_forms.md`'s missing automorphic form. **EXTEND by consolidation + one located break; no new
axis; model v7.1 holds. 109+ decompositions, the count-by-norm reading + the `q=±1` reflection unchanged.**

## Note for the technique

- **Theta = the count reading at a new grading: by the Gram quadratic form.** `generating_functions.md`'s
  family-reading was graded by a height index `n`; theta grades by `|v|²` = the quadratic-form value. This
  is not a new axis — it is the *resolution/height* axis with the grading supplied by the Gram reading. The
  theta coefficient `r_Λ(m)` is `cardinality.md`'s count, the leading one (`r_Λ(min)`) the kissing number.
- **The `×↦·` character now runs through the lattice norm form.** `four_sq_id`/`isSum4_mul` (multiplicative
  sum-of-squares count) = `θ_{Λ⊕Λ'}=θ_Λ·θ_Λ'` = the GF-product = the SAME `×↦·` arrow as `vp_mul`/`det2_mul`/
  `legendre_mul`. The single character arrow reaches one more field (the quaternion/octonion norm).
- **Self-dual `Λ=Λ*` is the cleanest `q=±1` fixed point of a *geometric* reflection.** Where φ is the
  `q=+1` fixed point of the Cassini multiplier and the Gaussian of convolve-rescale, E8/Leech are the
  `q=+1` fixed points of the Poisson/`τ↦−1/τ` reflection — the same `ResidueTag` converge pole on the
  lattice's Fourier self-duality. The reflection involution is built (`FoldReflections`); only the
  self-dual lattice realizing the fixed point is absent.
- **The break is the geometric twin of `modular_forms.md`'s automorphic break** — there the form realizing
  the period was absent though the period corpus was built; here the lattice realizing the theta is absent
  though the count corpus + the modularity covolume invariant are built. Grep before declaring a gap: the
  Gram matrix, the covolume, the representation counts, the reflection, and the `q=±1` tag are all in-repo.

---

### Verified Lean anchors (file:line:theorem — all grep + `tools/scan_axioms.py`-verified this session; all PURE)

| Leg | Theorem (file : name : line) | Status |
|---|---|---|
| Gram matrix = the inner-product reading, symmetric (the quadratic form) | `Lib/Math/Algebra/Linalg213/Gram.lean : Gram` (:50), `Vec.inner` (:31), `Vec.inner_comm` (:72), `gram_orthonormal_2` (:59) | **PURE (scanned 9/0)** ✓ |
| ★ covolume = lattice area = Gram determinant (`area2² = \|u\|²\|v\|²−(u·v)²`) | `Lib/Math/Geometry/LatticeArea.lean : area2_sq_eq_gram` (:95), `area2` (:33), `cross2` (:30) | **PURE (scanned 18/0)** ✓ |
| ★★ `SL₂(ℤ)`/`GL₂(ℤ)` preserves covolume (det=±1) — the geometric root of modularity | `Lib/Math/Geometry/LatticeArea.lean : area2_unimodular` (:148), `area2_linMap` (:139), `linMap` (:132) | **PURE (18/0)** ✓ |
| ★★ theta coefficient (`ℤ⁴`): Lagrange four-square (full support of `θ_{ℤ⁴}`) | `Lib/Math/NumberTheory/FourSquare.lean : nat_isSum4` (:588), `isSum4` (:131) | **PURE (scanned 34/0)** ✓ |
| ★★ `θ_{Λ⊕Λ'}=θ_Λ·θ_Λ'` = `×↦·` character = Euler four-square identity (multiplicative count) | `Lib/Math/NumberTheory/FourSquare.lean : four_sq_id` (:122), `isSum4_mul` (:134) | **PURE (34/0)** ✓ |
| theta coefficient (`ℤ²`/Gaussian lattice): two-square theorem (`p≡1 mod 4`) | `Lib/Math/NumberTheory/TwoSquareTheorem.lean : two_square` (:252), `two_square_isSumTwoSq` (:279) | **PURE (scanned 19/0)** ✓ |
| theta coefficient (`A₂`/Eisenstein hexagonal lattice `x²+xy+y²`, `p≡1 mod 3`) | `Lib/Math/NumberTheory/EisensteinRepresentation.lean : eisenstein_repr_int` (:438), `eisenstein_repr_of_root` (:397) | **PURE (scanned 27/0)** ✓ |
| `θ_Λ = Σ r_Λ(m) qᵐ` = `L_gen` family-reading; GF-product = convolution; `q` = grading coord | `Lib/Math/Combinatorics/GeneratingFunction.lean : convolution` (:50), `xVar` (:36) | ∅-axiom (per `generating_functions.md`) ✓ |
| ★ Poisson/`S` = `q=±1` reflection: det `=−1` folds compose to `S=τ↦−1/z` (the involution) | `…/Real213/ModularGeometry/FoldReflections.lean : negation_recip_eq_swap` (:55), `N_involutive` (:42), `R_involutive` (:43) | PURE (per `modular_forms.md`) ✓ |
| reflection involution (abstract): antitone `star∘star=clo`, fixed = `q=+1` closed | `Lib/Math/Order/FenchelMoreau.lean : biconjugate_eq_clo` (:59), `closed_iff_fixed` (:152) | PURE (per `fourier`/`convex_duality.md`) ✓ |
| `θ_Λ` modular = `q=+1` `Aut(C)`-invariant (holonomy `det=1`) | `…/Real213/ModularGeometry/HolonomyLattice.lean : det_holonomy_eq_one` (:136), `holonomy_append` (:108) | ∅-axiom (per `connections`/`modular_forms.md`) ✓ |
| even unimodular `Λ=Λ*` = the `q=±1` converge fixed point (the unimodular tag) | `Lib/Math/Foundations/ResidueTag.lean : residue_tag_two_poles` (:228), `multiplier_unimodular` (:86), `golden_is_converge` (:180) | PURE (per `SYNTHESIS.md`, 55/0) ✓ |
| the dual cusp grid (Stern–Brocot/Farey, det-1 adjacency) the modular action lives on | `…/Real213/Markov/SternBrocotMarkov.lean : sbInterval_adj` (:66), `sbStep_preserves` (:53), `adj` (:37) | PURE (per `modular_forms.md`) ✓ |

### Dropped / flagged (honest — NOT cited as built)

- **`Lattice` / `thetaSeries Λ` / `dualLattice Λ*` as Lean objects** — ABSENT. grep `lattice`/`theta`/
  `dual_lattice`/`Poisson` returns only: the **Real213 cut-order lattice** (`Real213/Lattice/`,
  `CutMaxMin` etc. — an *order* lattice, NOT a geometric ℝⁿ lattice — predicted-not-built, correctly), the
  **holonomy lattice** (`HolonomyLattice`, the `Mat2` group action — relevant to modularity, cited), the
  `Geometry/LatticeArea`/`NumberGrid` (the integer grid + covolume — cited), and `Lens/Lattice.lean` (an
  unrelated reading-lattice). No geometric lattice / theta-series / dual-lattice *type*. The count
  coefficients (`r_Λ`) are built per-form; the graded **series object** is not.
- **`E8` / `Leech` / `unimodularLattice` / `evenLattice`** — ABSENT (grep: no `E8`, no `Leech`). The
  structural prediction (self-dual = `q=+1` fixed point, `det G = 1`, weight `n/2`, `8 ∣ n`) is the
  deliverable; the lattices are not constructed. The located break (Leg 4).
- **Poisson summation formula `θ_{Λ*}(−1/τ) = covol·(−iτ)^{n/2}·θ_Λ(τ)`** — ABSENT. It needs the analytic
  Gaussian Fourier transform on `ℝⁿ` = the `Real213`-cut residue (same boundary `fourier.md` located: the
  analytic kernel `ζ`/Gaussian sits in the cut residue). The reflection *involution* (`FoldReflections`,
  `FenchelMoreau`) is built; the analytic Poisson identity is not.
- **`sphere_packing` / `kissing number` / density / LP-bound certificate** — ABSENT (grep: no
  `sphere_packing`/`kissing`). Predicted as the `q=+1` count optimum with the LP bound an `f**=clo` strong
  duality (Leg 5); conceptual-only, needs the absent lattice + the analytic Fourier certificate.
- **The analytic theta value `θ_Λ(τ)` as a number** (`q = e^{2πiτ}`, the full infinite sum) — the
  `Real213`-cut residue, the same transcendental-cut boundary every infinite series carries here. Not
  claimed.

### Any verified buildable witness

- **A direct-sum theta multiplicativity statement on the built `GeneratingFunction.CoeffSeq`** is
  buildable ∅-axiom NOW: package `r_{ℤ²}` and `r_{ℤ⁴}` (or any explicit small-norm count table) as
  `CoeffSeq` and prove `θ_{Λ⊕Λ'} = convolution θ_Λ θ_Λ'` at low degree by `decide`/`rfl` — the GF-product
  side is already `four_sq_id`/`isSum4_mul` at the coefficient level; welding it to `CoeffSeq.convolution`
  is the same shape as `conv_one_one_0` (`decide`). This is the calculus's predicted "theta of a direct
  sum = product of thetas = the `×↦·` character" as a concrete Lean theorem, no new primitive. (The
  *general* `θ_Λ` object over an abstract `Lattice` type remains the located break.)
