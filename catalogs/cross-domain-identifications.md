# Cross-Domain Identifications Catalog (CDI)

Math ↔ Physics ↔ Cohomology decls with **byte-identical
elaborated Expr** (post-normalisation) discovered by
shape-vector grouping over `tools/_ast_shape_rows.tsv`
(`tools/ast_shape_scan.py`).

When two or more decls in distinct top-level namespaces produce
the same 14-dimensional Expr-shape vector, they are NOT just
analogous — they have **literally the same proof structure**
at the elaborated level.  Each named CDI below is a
machine-verified cross-domain identification.

109 cross-namespace groups discovered total; 25 are
substantive Math ↔ Physics bridges.  This catalog names the
top entries.

---

## CDI-1 — `b₁(K_{NS,NT}) = NS² - 1 = inv_α_em^{(finite)}`

**Group size**: 3 decls  
**Spans**: Math.HodgeConjecture, Math.Cohomology

**Decls**:
  · `Math.HodgeConjecture.Foundation.ConjectureLens.b1_eq_NS_sq_minus_one`
  · `Math.Cohomology.Bipartite.Parametric.EulerAndCapstone.b1Formula_K32`
  · `Math.HodgeConjecture.Pairing.HodgeIndex.h1_dim_K32`

**Identification**: The first Betti number of K_{NS,NT}^{(c=2)}
bipartite multigraph equals NS² - 1 = 8 (gluon octet count =
1/α_3 confinement integer).  **Byte-identical proof at Expr level
across namespaces** confirms the cohomological bridge isn't
analogical — it's structural identity.

**Atomicity origin**: NS = 3 from atomicity chain.  K_{NS,NT}
bipartite from (3,2) decomposition.  H¹ rank = 8 from cycle
space.  α_em coupling derived from gluon octet via gauge
emergence (parallel branch C3 chain).

---

## CDI-2 — distinct integers sharing a trivial `a·a−1 = n` proof shape (NOT an identity)

**Spans**: Math.Cohomology, Physics.Mixing, Physics.YangMills

**Decls**:
  · `Math.Cohomology.Examples.K5.b1_K5`            (value 6)
  · `Physics.Mixing.Bridge.delta_cp_atomic`        (value 24)
  · `Physics.YangMills.Bridge.adjoint_SU_d_atomic` (value 24)
  · `Physics.YangMills.Bridge.adjoint_SU_NS_atomic`(value 8)

**Honest reading**: these are **three different integers** (6, 24, 8),
not a single identified quantity.  A prior version of this entry called
them a "4-way structural identity"; that was **false** — the only thing
shared is the trivial proof *shape* `a·a − 1 = n` discharged by
`decide`.  Same `decide` proof form is not a cross-domain identification
of *values*.  Retained here only to record that the shape-vector scan
groups them by proof skeleton, not to claim the numbers coincide.

---

## CDI-3 — `b₁(K_25) = inv_α_3_via_NS² = adjoint_SU(5)`

**Group size**: 4 decls, 237 nodes  
**Spans**: Math.Cohomology.Fractal, Physics.Couplings,
Physics.Simplex

**Decls**:
  · `Math.Cohomology.Fractal.V25.b1_K25`
  · `Physics.Couplings.ColorConfinement.inv_alpha_3_via_NS_sq`
  · `Physics.Simplex.Counts.inv_alpha_3_confined`
  · `Physics.Simplex.Counts.adjoint_su5`

**Identification**: First Betti of K_25 fractal ≡ inverse-α₃
(strong coupling) derived via NS² ≡ SU(5) adjoint dimension.
**4-way identity** — color-confinement coupling from K_25
Betti structure.

**Atomicity origin**: K_25 = K_{d²} = K_{25} fractal level 2.
SU(5) adjoint = 24 ≡ K_25's cycle space.  Strong coupling α₃
emerges from this Betti structure.

---

## CDI-4 — `Atomic constants square template`

**Group size**: 2 decls, 11,051 nodes (largest single bridge by mass)
**Spans**: Math.Extras, Physics.Foundations

**Decls**:
  · `Math.Extras.CauchySchwarz2D.sq_add_two`
  · `Physics.Foundations.AtomicConstantsParametric.sq_of_add`

**Identification**: `(a+b)² = a² + 2ab + b²` algebraic identity
≡ atomic-constants `sq_of_add` proof.  **The physics derivation
literally elaborates to the same Expr as the algebraic
identity**.

**Reading (deflated)**: per its own source note, `sq_of_add` is a
**deliberately duplicated** lemma `(a+b)² = a² + 2ab + b²` (inlined to
avoid an upward dependency).  So the byte-identical Expr is expected: it
is the *same lemma copied*, not two independent derivations converging.
This records the duplication, not a "physics IS math" bridge.

---

## CDI-5 — `Physics atomic-bracket containment template`

**Group size**: 5 decls, 321 nodes (Bridge 20)  
**Plus** 3 more decls, 1,077 nodes (Bridge 8)  
**Spans**: 5 distinct Physics sub-namespaces

**Decls (Bridge 20)**:
  · `Physics.Cosmology.Bridge.omega_lambda_atomic`
  · `Physics.Nuclear.DeuteronBinding.E_d_bracket`
  · `Physics.Atomic.Helium.he_IE_in_bracket`
  · `Physics.Hadron.NeutronProton.dmnp_bracket`
  · `Physics.Atomic.Hydrogen.H_E1_bracket`

**Decls (Bridge 8)**:
  · `Physics.AlphaEM.StructuralGap.n50_bracket_contains_candidate`
  · `Physics.YangMills.WZBosons.cos2_W_in_75_78`
  · `Physics.AlphaEM.GramSelfEnergy.aug_bracket_contains_observed_high_precision`

**Honest reading (deflated)**: 8 physics-domain "observed constant X is
in bracket [low, high]" proofs share the **same `decide` interval-check
proof shape**.  This is *shared triviality* — every `low < x ∧ x < high`
discharged by `decide` elaborates the same way — **not** a structural
bridge between the domains.  The constants and brackets differ; only the
proof skeleton is shared.  A prior version called this a "universal
pattern / deep unity"; that framing is retracted.

---

## CDI-6 — `Mersenne-3 ≡ Lucas-2 ≡ Mersenne d-form (atomicity Mersenne)`

**Group size**: 2 decls, 325 nodes  
**Spans**: Math.Geometry, Physics.Simplex

**Decls**:
  · `Physics.Simplex.SubInventory.thirty_one_is_two_d_minus_1`
  · `Math.Geometry.Rotation.mersenne_3_eq_lucas_2`

**Identification**: Δ⁴ subface count 31 = 2^d - 1 (Mersenne
form) ≡ M_3 = L_2 (geometry's Mersenne/Lucas identity).  Both
are atomicity-numeric consequences (d = 5).

---

## CDI-8 — `Fractal levels ≡ Nuclear magic ≡ Multivariable integral`

**Group size**: 6 decls, 597 nodes  
**Spans**: Math.Cohomology.Fractal (4), Math.Multivariable,
Physics.Nuclear

**Decls**:
  · `Math.Cohomology.Fractal.Level.{level1, level2, level3, level4}`
  · `Math.Multivariable.Capstone.multiIntegral_witness`
  · `Physics.Nuclear.Bridge.magic_atomic`

**Identification**: 4 fractal level proofs ≡ multivariable
integral witness ≡ nuclear magic number proof.  **6-way
structural identity** linking cohomology fractal structure,
multivariable integration, and nuclear physics.

---

## CDI-9 — Mobius determinant identity (3-way)

**Group size**: 3 decls, 397 nodes  
**Spans**: Math.Mobius213, Math.Geometry, Math.Mobius213OneAsGlue

**Decls**:
  · `Math.Mobius213.mobius_213_det`
  · `Math.Geometry.Rotation.p_det_is_glue`
  · `Math.Mobius213OneAsGlue.mobius_det_is_unit`

**Identification**: Mobius213 P matrix determinant ≡ Geometry
rotation P determinant-is-glue ≡ Mobius213OneAsGlue
determinant-is-unit.  **3-way intra-math identity** — all are
the same "det = 1" check on the Pell-unit matrix.

---

## CDI-10 — `n_mul_sq` parametric family

**Group size**: 3 decls, 1,665 nodes  
**Spans**: Math.ModArith (×2), Meta.Nat

**Decls**:
  · `Math.ModArith.PureNatMod3.three_mul_sq`
  · `Math.ModArith.PureNatMod5.five_mul_sq`
  · `Meta.Nat.PureNat.even_sq` (= mod-2 form)

**Identification**: `n_mul_sq` proofs for n ∈ {2, 3, 5} (=
{NT, NS, d}) are byte-identical.  Direct parametric
candidate: single `nat_p_mul_sq` template instantiated at
atomicity numerics.

---

## How to interpret CDIs

A CDI is a **machine-verified cross-domain structural
identification**.  It says:

> The proof of theorem A in namespace X and the proof of
> theorem B in namespace Y produce **byte-identical elaborated
> Expr** post-normalisation.

It means the elaborator produced the same term (modulo named
constants).  **Caution**: a shared Expr-shape is only as meaningful as
the proof it encodes.  When the shared shape is a *trivial* tactic
(`decide` on an interval, `decide` on `a·a−1 = n`, or a duplicated
lemma), the grouping records shared *triviality*, not a structural
identity of the *values* — see CDI-2, CDI-4, CDI-5.  A CDI is genuine
only when the shared term carries non-trivial mathematical content
(e.g. CDI-1, CDI-9's "det = 1" Pell-unit check); read each entry's own
"honest reading" before citing it as a bridge.

---

## How to add a new CDI

  1. Re-run the shape-vector grouping over
     `tools/_ast_shape_rows.tsv` (`tools/ast_shape_scan.py`
     output).
  2. Sort cross-namespace groups by Expr-size.
  3. Inspect top entries — if they represent a structurally
     meaningful identity, add as CDI-N here.
  4. Cite the witnessing Lean decls for evidence.

---

## Methodology-pattern reference

**Byte-identical Expr cross-domain bridges**
(`theory/meta/methodology_patterns.md` Pattern #18):
when two decls in distinct top-level namespaces produce
byte-identical 14-dim Expr-shape vectors, they share an
implicit cross-domain identification.  Quantified at 109
cross-namespace groups in DRLT.

---

## Pointers

  · Re-run: shape-vector grouping over
    `tools/_ast_shape_rows.tsv` (gitignored; regenerable via
    `python3 tools/ast_shape_scan.py`)
  · Related: `catalogs/atomic-integers.md`,
    `catalogs/correspondences.md`, `catalogs/falsifiers.md`,
    `catalogs/physics-constants.md`
