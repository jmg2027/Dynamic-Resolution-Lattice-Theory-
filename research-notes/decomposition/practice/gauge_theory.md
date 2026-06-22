# Decomposition: gauge theory / Yang–Mills

*213-decomposition of "a connection `A` on a principal bundle, the curvature `F = dA + A∧A`, gauge
transformations, the Yang–Mills action `∫|F|²`, the YM equations `d⋆F = 0`, instantons (self-dual
`F = ⋆F`), the Bianchi identity `dF = 0`, holonomy, Wilson loops, and `∫tr(F∧F) = c₂`", per
`../README.md` (model v7.1) and `../SYNTHESIS.md` (the two invariants + the `q=±1` spine + the
det-character read four ways). LEVERAGE phase — the bar is PREDICTION/REVELATION. Sits directly atop
`curvature.md` (curvature = the loop-reading's `q=±1` residue, the holonomy det Noether-invariant),
`characteristic_classes.md` (`∫tr(F∧F) = c₂` = the det-character of the curvature, the `e_i` Vieta),
`noether.md` (gauge invariance = the `Aut`-invariant character, `det = 1`), and `de_rham.md` (`dF = 0`
= `d²=0`, the telescope). ★ The NEW datum: **instantons (`F = ±⋆F`) = the `q=±1` self-duality of the
Hodge star** — the `⋆` involution's `±1` eigenspaces ARE the symmetric/antisymmetric (`q=+1`/`q=−1`)
split, and the gauge field itself = the antisymmetric/`q=−1` half of
`SignedCup.gram_hermitian_gravity_gauge_split` (gravity = symmetric metric, gauge = the cup). And —
surprise — **the YM mass gap is already BUILT ∅-axiom** (`YangMills/Gap.lean`).*

The thesis under test: **Yang–Mills is `curvature.md`'s curvature reading with the holonomy/det
character, gauge invariance = noether's `q+1` Aut-invariance, Bianchi = de Rham's `d²=0`, instantons
= the `q=±1` self-duality of the Hodge star, and `∫tr(F∧F) = c₂` = characteristic_classes' Chern
character — no new primitive.**

## The decomposition (C / Reading / Residue)

- **Construction `C` — the holonomy/parallel-transport data, `curvature.md`'s `HolonomyLattice`;
  nothing new.** The connection `A` introduces no construction of its own: it IS the
  parallel-transport datum `curvature.md` already decomposed — a `List Mat2` of transitions, folded by
  `holonomy w = g₀·g₁·…·gₙ·I` (`HolonomyLattice.holonomy`). Transport composes functorially
  (`holonomy_append` = a monoid homomorphism `(List Mat2, ++) → (Mat2, ·)`), so the connection is the
  `Mat2` ×-construction read as state-transitions, with `C`'s direction bit (`q=±1`, the sign-fold
  `S`) and fold-height. On the abstract-index side `A` is the Christoffel/connection of
  `TensorCalculus.lean`, and the curvature is the Riemann tensor `riemUp`. The classical packaging —
  a principal `G`-bundle, a smooth `𝔤`-valued 1-form `A`, the curvature 2-form `F ∈ Ω²(M;𝔤)` — is the
  `Real213`-cut residue (see Residue).

- **Reading `L` — the curvature reading with the holonomy/det character (three faces of one arrow).**
  Yang–Mills reads `C` through exactly the readings the geometry cluster already carries:
  1. **The curvature `F = dA + A∧A` = `curvature.md`'s loop-residue.** Curvature is the deficit by
     which the holonomy fails to be flat: flat ⟺ the det character is conserved (`det_holonomy_eq_one`,
     `det = 1` around every loop), and `F` measures the deviation. The first non-trivial curvature is
     `holonomy [S,S] = −I ≠ I` (`first_loop_is_the_fold`), the `q=−1` deficit born exactly when the
     sign-fold enters; the ℕ⁺ (tree) sector is loop-free/flat (`positive_loop_trivial`). So `F` =
     `Residue(L_loop, C)`, tagged `q=±1` — verbatim `curvature.md`.
  2. **Gauge transformations = the `Aut`-family, the `q+1` invariance (noether).** A gauge
     transformation is a `C`-preserving relabel — an element of `Aut(C)` — and the YM action being
     gauge-invariant IS `noether.md`'s statement that the conserved readout is the `Aut`-invariant
     character: `det = 1` is fixed under the action (`det2_mul` evaluated where generators carry
     `det = 1`), and `noether_local` is `∂·j = 0 ⟺ Aut-invariant`. Gauge invariance = the `q+1`
     conserved-character pole, the same arrow.
  3. **`∫tr(F∧F) = c₂` = the det-character of the curvature (characteristic_classes).** The
     topological charge is the `×↦·` det-character read on the curvature, landing as the second Chern
     class `c₂ = e₂(spectrum F) = det F` (`Mat2Spectrum.det_eq_e2`); the Chern character `tr exp(F)`
     is its additive `×↦+` twin (`vp_mul`). Wilson loops = the holonomy trace = the `×↦·` character
     read around a loop.

- **Residue — `q=±1`, with the NEW instanton stratum: the Hodge star's self-duality split.**
  1. *The instanton self-duality (THE new datum)*: the YM action `∫|F|²` is the **curvature norm**;
     instantons minimize it at the self-dual / anti-self-dual locus `F = ±⋆F`. The Hodge star `⋆` is
     the `q=±1` involution — `⋆∘⋆ = (−1)^{k(n−k)}` (`SignedHodgeStar.star_star_eq_sign`, an
     operator identity on all 16 forms of `Λ(Δ⁴)`), and **at grade 2 — the seat of the curvature
     2-form `F` on a 4-manifold — `⋆²=+1`** (`star_sq_pos_one_grade2`), so the involution splits into
     `±1` eigenspaces `F = F⁺ ⊕ F⁻`: self-dual (`q=+1`, `F=⋆F`) and anti-self-dual (`q=−1`, `F=−⋆F`).
     This is the SAME `q=±1` split as symmetric/antisymmetric (the `det=±1` parity `L₂`), here the
     Hodge decomposition. The instanton = the `q+1` self-dual fixed point of the curvature norm. And
     the **gauge field = the antisymmetric/`q=−1` half** of
     `SignedCup.gram_hermitian_gravity_gauge_split`: the Hermitian Gram `G = GRe + 𝐢·GIm` splits with
     `GRe = hPair` symmetric (the gravity/metric half) and `GIm = cup1` antisymmetric (the
     symplectic/gauge half) — gauge is the cup/`q=−1` part, gravity the symmetric/`q=+1` part.
  2. *The cohomology landing*: `dF = 0` (Bianchi) = de_rham's `d²=0` (`dsq_zero_universal_delta4`,
     since `F = dA ⟹ dF = d²A = 0` in the abelian case), the `q=±1` orientation-cancellation; the
     topological charge lands in `H*` mod `im d`.
  3. *The smooth `Real213`-cut residue*: the smooth `G`-bundle, `A ∈ Ω¹(M;𝔤)`, `F ∈ Ω²(M;𝔤)`, the
     continuum YM action / `d⋆F=0` variational equation, the moduli space of instantons, and the
     **Wilson-loop area-law functional** are ABSENT (grep-confirmed) — the same boundary
     `curvature.md`/`de_rham.md` locate, plus the open `yang_mills_confinement.md` frontier.

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   the connection A              =  curvature.md's holonomy/transport data           (holonomy, holonomy_append)
   curvature F = dA + A∧A        =  the loop-reading's q=±1 residue (failure of flat) (det_holonomy_eq_one: flat⟺det=1; first_loop_is_the_fold)
   gauge transformations         =  the Aut(C)-family relabel                          (noether's Aut-action)
   "YM action is gauge-invariant" =  the q+1 conserved Aut-invariant character det=1   (noether_local, det_holonomy_eq_one)
   the Bianchi identity dF = 0    =  de Rham's d²=0 (F=dA ⟹ dF=d²A=0)                  (dsq_zero_universal_delta4)
   ★ instantons F = ±⋆F          =  the q=±1 eigenspaces of the Hodge ⋆ involution     (⋆²=+1 at grade 2: star_sq_pos_one_grade2)
   the YM action ∫|F|²           =  the curvature norm, minimized at the q+1 instanton (the self-dual fixed point)
   the gauge field (vs gravity)  =  the ANTISYMMETRIC/q=−1 cup half of the Gram        (gram_hermitian_gravity_gauge_split: GIm=cup1)
   ∫tr(F∧F) = c₂                 =  the ×↦· det-character of the curvature = e₂        (det_eq_e2; the Chern character, vp_mul twin)
   Wilson loop ⟨tr hol⟩          =  the ×↦· character read around a loop               (det2_mul; the trace readout)
   the YM mass gap (BUILT!)      =  the gauge-lattice Laplacian's first nonzero λ > 0   (mass_gap_master, gap = c·min(NS,NT)=4)
```

The single move: **Yang–Mills is not a new edifice** — it is `curvature.md`'s curvature +
`noether.md`'s `Aut`-invariance + `de_rham.md`'s `d²=0` + `characteristic_classes.md`'s Chern
character, with the **`q=±1` self-duality of the Hodge star supplying instantons** as the genuinely
new contribution.

## Re-seeing table (the unification)

| classical gauge-theory object | the calculus's reading | repo status |
|---|---|---|
| the connection `A` | `curvature.md`'s holonomy / parallel-transport data | **BUILT** (`holonomy`, `holonomy_append`) |
| curvature `F = dA + A∧A` | the loop-reading's `q=±1` residue (the flatness deficit) | **BUILT** (`det_holonomy_eq_one`, `first_loop_is_the_fold`, `riemUp`) |
| gauge transformations (the `Aut`-family) | `noether.md`'s `Aut(C)`-action | **BUILT** as the action (`det2_mul`, `noether_local`) |
| YM action gauge-invariant | the `q+1` conserved `Aut`-invariant character `det=1` | **BUILT** (`det_holonomy_eq_one`, `noether_local`) |
| Bianchi `dF = 0` | de Rham's `d²=0` (`F=dA ⟹ dF=d²A=0`) | **BUILT** (`dsq_zero_universal_delta4`) |
| ★ instanton self-duality `F = ±⋆F` | the `q=±1` eigenspaces of the Hodge `⋆` involution | **BUILT** (`star_star_eq_sign`, `star_sq_pos_one_grade2`) |
| the YM action `∫|F|²` (curvature norm) | the norm minimized at the `q+1` self-dual fixed point | structural (the norm; the variational minimum is the residue) |
| ★ gauge field = antisymmetric half | the `q=−1` cup/symplectic part of the Hermitian Gram | **BUILT** (`gram_hermitian_gravity_gauge_split`, `GIm=cup1`) |
| `∫tr(F∧F) = c₂` (topological charge) | the `×↦·` det-character of the curvature = `e₂` | **BUILT at matrix level** (`det_eq_e2`, `det_tr_split_is_e1_e2`) |
| Wilson loop `⟨tr hol⟩` | the `×↦·` character trace around a loop | holonomy **BUILT**; the named `WilsonLoop` functional ABSENT |
| ★ the YM mass gap `> 0` | the gauge-lattice Laplacian's first nonzero eigenvalue | **BUILT ∅-axiom** (`mass_gap_master`, gap `= 4`) |
| colored-mode confinement (spectral) | the SOS positivity of `Δ₀(Δ₀−massGap·I) ⪰ 0` | **BUILT ∅-axiom** (`colored_confinement_master`) |
| the smooth `G`-bundle / `A∈Ω¹(M;𝔤)` / continuum YM eqn `d⋆F=0` / instanton moduli / area law | the `Real213`-cut smooth residue | **ABSENT** (the located break) |

## Revelation (collapse + forcing + the q=±1 spine)

**Collapse — instantons (`F = ±⋆F`) ARE the `q=±1` eigenspaces of the Hodge involution; this is the
NEW datum.** `SignedHodgeStar.star_star_eq_sign` proves the Hodge star is a `q=±1` involution as a
genuine operator identity (`⋆∘⋆ = (−1)^{k(n−k)}` on all 16 forms), and at grade 2 — exactly the
degree of the curvature 2-form `F` on a 4-manifold — `⋆²=+1` (`star_sq_pos_one_grade2`). An
involution with `⋆²=+1` decomposes its space into `±1` eigenspaces, so `F = F⁺ ⊕ F⁻` with
`F⁺` self-dual (`⋆F⁺=+F⁺`, `q=+1`) and `F⁻` anti-self-dual (`⋆F⁻=−F⁻`, `q=−1`). **This is the SAME
`q=±1` split** the calculus runs everywhere: symmetric/antisymmetric (`det=±1`, `parity.md`'s `L₂`),
`∂²=0` vs `⋆⋆=id` (homology), Cassini `q=±1` (`multiplier_unimodular`). The instanton is the `q=+1`
self-dual fixed point where the YM action `∫|F|²` (the curvature norm) is minimized — exactly
`ResidueTag`'s converge pole. So `golden_ratio`'s φ, the Gaussian fixed point, AND the instanton are
the *same* `q=+1` converging residue read in three fields. This is the contribution beyond re-skinning
`curvature.md` (which gave curvature = the loop-residue) and `characteristic_classes.md` (which gave
`∫tr(F∧F)=c₂` = the det-character): the **self-dual/anti-self-dual decomposition is the Hodge star's
`q=±1` eigenspace split**, with the gauge field itself the antisymmetric/`q=−1` half of
`gram_hermitian_gravity_gauge_split` (gravity = symmetric metric `GRe`, gauge = the cup `GIm`).

**Forcing — gauge invariance, Bianchi, and Whitney/topological multiplicativity are FORCED, not
chosen.**
- *Gauge invariance of the action* is *forced* by the YM observable being the `Aut`-invariant
  character: the only reading fixed by every relabel is the character `det` (`det2_mul`,
  `noether.md`), read to the unit by gauge generators — `det_holonomy_eq_one` is that invariance
  around every loop.
- *Bianchi `dF=0`* is *forced* by `d²=0`: `F = dA` gives `dF = d²A = 0` by
  `dsq_zero_universal_delta4` (the `q=±1` orientation cancellation, the same as `∂²=0`), with the
  abstract-index Bianchi `riem_bianchi1` the curvature-tensor form.
- *`∫tr(F∧F⊕G∧G) = ∫tr(F∧F)+∫tr(G∧G)`* (additivity of the charge on `⊕`) is *forced* by
  `tr exp` / `det` being the character arrow on block-diagonal curvature (`det2_mul`,
  characteristic_classes' Whitney leg).
- *Wilson-loop multiplicativity around composed loops* is *forced* by `holonomy_append` (the monoid
  homomorphism) composed with the `det`/trace character.

**The `q=±1` spine (`SYNTHESIS.md` §3) on the gauge field.**
- *Flat connection* (`F=0`, `q=+1` conserved `det_holonomy_eq_one`) vs *curved* (`q=−1` deficit
  `first_loop_is_the_fold`) — the curvature detects exactly the `q=−1` holonomy deficit.
- *Self-dual instanton* (`q=+1`, `F=⋆F`, action-minimizer = the converge fixed point,
  `converge_residue_fixed`) vs *anti-self-dual* (`q=−1`, `F=−⋆F`) — the SAME `±1` involution bit
  (`multiplier_unimodular`).
- *Gauge = antisymmetric/`q=−1`* (the cup `GIm`) vs *gravity = symmetric/`q=+1`* (the metric `GRe`)
  in `gram_hermitian_gravity_gauge_split`.
- ★ *The YM mass gap*: the gauge-lattice Laplacian `Δ₀` of `K_{3,2}^{(c=2)}` has a **one-dimensional
  `λ=0` kernel** (the connected lattice = unique vacuum, the `q+1` constant-kernel pole, the same
  `GraphConnectivity` mechanism ergodicity uses) and a strictly positive first nonzero eigenvalue
  `massGap = c·min(NS,NT) = 4` (`mass_gap_master`) — the colored excitations are the gapped `q=−1`
  modes (`colored_confinement_master`).

So gauge theory = (curvature = `curvature.md`'s loop-residue) + (gauge invariance = noether's `q+1`
`Aut`-character) + (Bianchi = de Rham's `d²=0`) + (instantons = the Hodge star's `q=±1` self-duality)
+ (`∫tr(F∧F)=c₂` = characteristic_classes' Chern character) — **no new primitive**.

## VALIDATE verdict — **EXTEND** (a decisive consolidation + one genuinely-new instanton datum; with a BUILT YM mass gap; two located breaks)

No new primitive, no break in the interior. Yang–Mills slots entirely into the v7.1 model: `C` = the
holonomy/transport data (`curvature.md`, carrying direction `q=±1` + fold-height), `L` = the curvature
reading + the `Aut`-invariant `det`/`tr` character (noether/characteristic_classes), `Residue` = the
`q=±1` Hodge-self-duality split (instantons) + the smooth `Real213`-cut bundle. It is a decisive
consolidation tying `curvature.md`, `noether.md`, `de_rham.md`, and `characteristic_classes.md`
into one field, and it carries the **genuinely new datum** that the self-dual/anti-self-dual instanton
decomposition is the `q=±1` eigenspace split of the Hodge star.

- **The surprise — the YM mass gap is already BUILT ∅-axiom (not predicted-not-built).**
  `YangMills/Gap.lean` (24/0 PURE) proves `mass_gap_master`: the gauge-lattice Hodge Laplacian of
  `K_{3,2}^{(c=2)}` has exact spectrum `{0,4,4,6,10}` (complete eigenbasis, `det = −30 ≠ 0`), a
  unique vacuum (1-dim kernel = connectivity), and a strictly positive gap `= c·min(NS,NT) = 4`. The
  spectral face of **confinement** is also built — `ColoredGap.lean` (4/0 PURE)
  `colored_confinement_master`: the SOS certificate `⟨Δ₀f,Δ₀f⟩ − 4⟨Δ₀f,f⟩ = 2(2(f₀+f₁+f₂)−3(f₃+f₄))²
  + 6(f₃−f₄)²` forces `Δ₀(Δ₀−massGap·I) ⪰ 0` for *every* configuration. This is one half of the 213
  Yang–Mills conjecture, machine-checked — far stronger than a prediction.

- **PREDICTION leg (honest):** the calculus *predicts* the form of the continuum YM machine — the
  action `∫|F|²` as the curvature norm minimized at the `q+1` self-dual locus, the equations `d⋆F=0`
  as the variational extremum, `c₂ = e₂(spectrum F)` (forced by Vieta, matrix-level `e₂` closed; `d>2`
  by analogy), additivity (forced by the character arrow), Bianchi (forced by `d²=0`). The grade-2
  `⋆²=+1` self-duality split is **closed** as an operator identity; the curvature-norm minimum and the
  instanton moduli are structural.

- **Located break 1 (the Wilson-loop area law / the smooth bundle).** The smooth `G`-bundle, `A∈Ω¹`,
  `F∈Ω²(M;𝔤)`, the continuum action / `d⋆F=0`, the instanton moduli space, and — sharpest — the
  **Wilson-loop area-law functional** are ABSENT. "Wilson" in the repo is *Wilson's theorem*
  (number theory, `WilsonExistence.lean`), not the Wilson loop. The open `yang_mills_confinement.md`
  frontier records the honest wall: on the abstract bipartite `K_{3,2}` there is no embedding, hence no
  enclosed "area" and no string tension to even *state* `⟨W⟩ ∼ exp(−σ·Area)` (§5.1, no exterior); the
  holonomy machinery shows the ℕ⁺ sector is loop-free and the first loop is order-4 torsion, so an
  area-law decay is not hiding there. A 213-native combinatorial Wilson functional + cohomological
  perimeter/area readout would have to be *built*; no internal handle found. This is the same
  `Real213`-cut/no-exterior boundary `curvature.md`/`de_rham.md` locate, not a new one.

- **Located break 2 (the smooth instanton / `d⋆F=0`).** The `⋆²=±1` involution is built as an
  operator, and the `±` eigenspace split is the self-dual/anti-self-dual decomposition; but the
  *smooth* `⋆` on a varying metric and the YM equation `d⋆F=0` as a `Real213` variational extremum are
  the smooth-tensor residue (the same as `curvature.md`'s missing transported curvature field).

## Verified Lean anchors (file:line:theorem) — all grep-confirmed, scans from repo root

**★ Instantons = the `q=±1` self-duality of the Hodge star (the central NEW collapse):**
- `lean/E213/Lib/Physics/Mixing/SignedHodgeStar.lean:85` `star_star_eq_sign`
  (`⋆∘⋆ = (−1)^{k(4−k)}` on all 16 forms of `Λ(Δ⁴)`, the genuine `q=±1` operator involution);
  `:98` `star_sq_pos_one_grade2` (`⋆²=+1` at grade 2 — the curvature-2-form seat, where `F=±⋆F`
  splits into `±1` eigenspaces); `:94` `star_sq_neg_one_grade1`; `:106` `hodge_i_order_four`.
  **PURE (12/0).**
- `lean/E213/Lib/Math/Cohomology/Hodge/SignedStarC4.lean:69` `signed_star_sq_neg_I` (the `C₄` model,
  `⋆²=−I`); `signed_star_ring_is_gaussian`, `signed_hodge_is_cp_i`. **PURE (10/0).**

**★ The gauge field = the antisymmetric/`q=−1` cup half (the load-bearing gauge anchor):**
- `lean/E213/Lib/Math/Cohomology/Cup/SignedCup.lean:127` `gram_hermitian_gravity_gauge_split`
  (`G = GRe + 𝐢·GIm`: `GRe = hPair` symmetric/positive-definite = gravity metric; `GIm = cup1`
  antisymmetric = the symplectic/gauge half); `:62` `cup1_antisymmetric` (`e_i∧e_j = −e_j∧e_i`, the
  `q=−1` orientation sign). **PURE (14/0).**

**★ The YM mass gap + colored confinement — BUILT ∅-axiom (the surprise):**
- `lean/E213/Lib/Physics/YangMills/Gap.lean:168` `mass_gap_master` (exact spectrum `{0,4,4,6,10}`,
  unique vacuum, `massGap = c·min(NS,NT) = 4 > 0`); `:145` `eigenbasis_independent` (`det = −30`);
  `:156` `massGap_pos`; `:153` `massGap_eq_c_min`; `:196` `octet_is_harmonic_sector` (`b₁ = 8 = NS²−1`,
  the gluon octet the gap sits above). **PURE (24/0).**
- `lean/E213/Lib/Physics/YangMills/ColoredGap.lean:168` `colored_confinement_master`; `:65`
  `colored_form_identity` (the SOS certificate); `:114` `colored_rayleigh_ge`
  (`⟨Δ₀f,Δ₀f⟩ ≥ massGap·⟨Δ₀f,f⟩` for all `f`); `:132` `colored_gap`. **PURE (4/0).**

**The connection / curvature = `curvature.md`'s holonomy loop-residue:**
- `lean/E213/Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean:108`
  `holonomy_append` (the connection = functorial transport, monoid homomorphism); `:136`
  `det_holonomy_eq_one` (flat ⟺ `det=1` = the `q+1` conserved character); `:313`
  `first_loop_is_the_fold` (`holonomy[S,S]=−I≠I`, the `q=−1` curvature deficit); `:292`
  `positive_loop_trivial` (the tree sector is flat). **PURE (26/0, per `curvature.md`).**
- `lean/E213/Lib/Math/Geometry/TensorCalculus.lean` `riemUp` (the curvature as Riemann tensor),
  `riem_bianchi1` (the Bianchi cyclic `q=−1` cancellation). **PURE (23/0, per `curvature.md`).**

**Gauge invariance = noether's `Aut`-invariant character; `∫tr(F∧F)=c₂` = the det-character:**
- `lean/E213/Lib/Math/NumberSystems/Real213/ModularGeometry/NoetherCurrent.lean` `noether_local`
  (`∂·j=0 ⟺ Aut-invariant`), `continuity_eq`. (per `noether.md`, 15/0)
- `lean/E213/Lib/Math/NumberSystems/Real213/Mat2/Mat2Spectrum.lean:103` `det_eq_e2`
  (`det = e₂ = c₂`, the `×↦·` topological charge); `:115` `tr_eq_e1` (`= c₁`); `:204`
  `det_tr_split_is_e1_e2`. **PURE (9/0, per `characteristic_classes.md`).**
- `lean/E213/Lib/Math/NumberSystems/Real213/Markov/SternBrocotMarkov.lean:104` `det2_mul`
  (`det(MN)=det M·det N`, the `×↦·` character = Whitney/Wilson-loop multiplicativity).
- `lean/E213/Lib/Math/NumberTheory/PrimeValuation.lean:96` `vp_mul` (`×↦+`, the Chern character
  `tr exp(F)` additivity). **PURE (7/0).**

**The Bianchi identity `dF=0` = de Rham's `d²=0`:**
- `lean/E213/Lib/Math/Cohomology/Delta/V4Capstone.lean` `dsq_zero_universal_delta4` (`d²=0`, the
  `q=±1` orientation cancellation = Bianchi `F=dA ⟹ dF=d²A=0`). (per `de_rham.md`, 5/0)

**The `q=±1` residue tag (the spine):**
- `lean/E213/Lib/Math/Foundations/ResidueTag.lean:228` `residue_tag_two_poles`; `:86`
  `multiplier_unimodular` (the `±1` self-duality bit); `:160` `converge_residue_fixed` (the `q+1`
  instanton/action-minimizer pole); `:180` `golden_is_converge`. **PURE (55/0).**

**The gravity/Regge tie (`J = S`, scope-honest, per `curvature.md`/`noether.md`):**
- `lean/E213/Lib/Physics/Cosmology/MetricHolonomyBridge.lean:50` `metric_J_is_holonomy_S`
  (the metric `J` = the holonomy generator `S`, both `²=−I`; own CAVEAT: a generator identity, no
  curvature field).

**Scan tallies (`python3 tools/scan_axioms.py E213.<module>`, from repo root, this session):**
`SignedHodgeStar` 12/0 · `SignedStarC4` 10/0 · `SignedCup` 14/0 · `YangMills.Gap` 24/0 ·
`YangMills.ColoredGap` 4/0 · `Mat2Spectrum` 9/0 · `ResidueTag` 55/0 (HolonomyLattice 26/0,
TensorCalculus 23/0, NoetherCurrent 15/0, PrimeValuation 7/0 per neighbor notes). All PURE, 0 DIRTY.

## Dropped / flagged (honest)

- **The named connection / Yang–Mills / instanton / Wilson-loop objects — ABSENT, predicted-not-built
  (except the mass gap, which IS built).** grep over `lean/E213` (case-insensitive) for
  `connection`/`gaugeField`/`YangMills` (as a *field* object beyond the gap spectrum)/`instanton`/
  `selfDual`/`anti.self.dual`/`principalBundle`/`WilsonLoop`/`Wilson_loop`/`gaugeTransform`/
  `curvature.*form`/`fieldStrength` returns **no named Lean object**. The only `Wilson` hits are
  *Wilson's theorem* (`WilsonExistence.lean`, `WilsonTheorem`, number theory) — NOT the Wilson loop.
  The `YangMills/` namespace contains the *mass-gap spectrum* (`Gap`, `ColoredGap`) and GUT-side files
  (`SU5Roots`, `WeinbergAngle`, `WZBosons`), not a connection/curvature-form/instanton object. Confirmed
  absent — the located `Real213`-cut smooth-bundle break.
- **`∫tr(F∧F)=c₂` grounded for `e₂` only (the `Mat2` 2×2 ceiling), per `characteristic_classes.md`.**
  `det_eq_e2` closes `c₂=det=e₂`; general `c_i=e_i` for `d>2` is by analogy to the closed `Mat2` case.
- **The YM action `∫|F|²` as a curvature *norm* and its variational minimum are structural.** The
  Hodge pairing `hPair = I` (positive-definite, `SignedCup.hodge_pairing_is_identity`) gives the norm,
  and the `q+1` self-dual locus is the minimizer, but `∫|F|²` as a named functional and its
  Euler–Lagrange equation `d⋆F=0` are the smooth `Real213`-cut residue. Cited scope-honest.
- **The Wilson-loop area law is genuinely open** (`yang_mills_confinement.md` frontier): no embedding
  on the abstract `K_{3,2}` ⟹ no area / string tension to state `⟨W⟩ ∼ exp(−σ·Area)` (§5.1). The
  *spectral* face of confinement IS built (`colored_confinement_master`); the *area-law* face is the
  honest wall.
- **`MetricHolonomyBridge` cited with its CAVEAT** — a generator identity `J=S`, not a transported
  curvature/gauge field; flagged thin so the gravity/gauge tie is not overclaimed.
- **Verified buildable witness (no new claim asserted):** the load-bearing collapse is already a set of
  `decide`/`ring_intZ` theorems — `star_star_eq_sign` (the `q=±1` Hodge involution), `star_sq_pos_one_grade2`
  (the grade-2 `±1` eigenspace split = self-dual/anti-self-dual), `gram_hermitian_gravity_gauge_split`
  (gauge = the `q=−1` cup half), and `mass_gap_master` (the gap `>0`) — all scanned PURE this session.
  A clean additional witness would be a grade-2 self-dual/anti-self-dual *projector* `P± = ½(I±⋆)` with
  `P±²=P±` on `Λ²(Δ⁴)` (idempotent, since `⋆²=+1` there) — a `decide`-level corollary of
  `star_sq_pos_one_grade2`; no new count-inequality is proposed beyond the grep-confirmed, scanned-PURE
  anchors above.
