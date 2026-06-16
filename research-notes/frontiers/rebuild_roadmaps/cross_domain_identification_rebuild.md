# Genuine cross-domain structural-map rebuild (post-deletion of the CDI fakery)

Companion to `research-notes/frontiers/genuine_hodge_rebuild.md` — same
honesty contract.

## 1. What was deleted & why bogus

The Cross-Domain Identifications (CDI) catalog read **"byte-identical
`decide` proof shape"** as **"same object"**. The fake content:

  · `catalogs/cross-domain-identifications.md` grouped declarations in
    distinct namespaces by a 14-dimensional Expr-shape vector, then
    declared each group a "machine-verified cross-domain *identification*".
    Example (CDI-2): `b1_K5 = 6`, `delta_cp_atomic = 24`,
    `adjoint_SU_d_atomic = 24`, `adjoint_SU_NS_atomic = 8` were called a
    "4-way structural identity" — but those are **three different
    integers** (6, 24, 8). The only thing shared was the trivial proof
    *skeleton* `a·a − 1 = n` discharged by `decide`. The catalog's own
    later honesty pass already flags CDI-2 as "**NOT an identity**".
  · `Foundations/CrossDomainUnification.lean` records `binom 5 k = 0`
    (k ≥ 6) appearing in several files with "the SAME `decide` on the same
    Pascal recursion". This is a genuine *shared lemma reused*, but the
    framing "cleanest cross-domain witness" overclaims: re-deriving one
    truncation identity in two namespaces is **code reuse**, not a
    structure-preserving map between two domains' objects.

Equal integers, or an identical proof skeleton, is **not** a cross-domain
identification. Two objects are "the same" only via an actual
structure-preserving map (iso / functor) — `8 = 8` is not `H¹(K) ≅
𝔰𝔲(3)`.

## 2. The genuine content

A real cross-domain identity is a **morphism in a category**, with
preserved structure:
  · a group/algebra **isomorphism** `φ : A ≅ B` (preserves the operation),
    or a **module isomorphism** (preserves the action), or
  · a **functor** `F : 𝒞 → 𝒟` with a natural transformation witnessing
    that a construction in one domain maps to a construction in the other.

The canonical worked example the deleted catalog *pretended* to have:
"the gluon octet `b₁(K_{3,2}) = 8` equals the `SU(3)` adjoint dimension."
The genuine statement is **not** `8 = 8`; it is a **module isomorphism**
`H¹(K_{3,2}; 𝔽₂) ≅ 𝔰𝔲(3)-adjoint` as `Sym(3)`-representations
(`Sym(3)` = the `SU(3)` Weyl group) — preserving the group action, the
irrep decomposition, and the characters. Equal dimension is a *necessary*
shadow of such an iso, never sufficient.

## 3. The 213-native obstruction (honest)

  · The substrate has the two *objects* in several alleged pairs (a graph
    cohomology `H¹`, the octet module, etc.), but **almost no proven maps
    between them** that preserve structure. The CDI catalog substituted
    equal readouts for the missing maps.
  · Building a genuine bridge requires defining the map *and* proving it
    intertwines the structure (commutes with the group action / ring
    operation / differential) — which is real work, not a shape-vector
    grep. The shape-vector scan (`tools/ast_shape_scan.py`) is fine as a
    *lead generator* ("these proofs look alike, investigate") but its
    output is **not** a theorem.

## 4. Staged plan

**Stage 1 — the one genuine seam: the octet as a `Sym(3)`-representation.**
`OctetModule.lean` already does the *intra-domain* structural work that a
cross-domain bridge would need on the algebra side. It proves, ∅-axiom:
  · `Octet := Fin 8 → Bool` is a rank-8 𝔽₂-module, dimension sourced as
    `NS² − 1 = 8` (`rank_eq_NSsq_minus_1`);
  · two involution generators with the **Coxeter presentation**
    `s² = t² = (st)³ = e` (`M_S01_squared`, `M_S12_squared`, `M_ρ_cubed`)
    — a faithful `Sym(3) ⊂ GL(8, 𝔽₂)`;
  · the **irrep decomposition** `Octet = 2·trivial ⊕ 3·standard`
    (`composition_multiplicities`, `fixedSize_eq_4`), with explicit
    standard 2-rep pairs (`std1_*`, `std2_*`) satisfying the standard-rep
    matrices, and 𝔽₂-characters (`boolTrace_*`).
This is a **genuine `Sym(3)`-module with proven structure** — the
antithesis of `8 = 8`. Stage 1 = treat this as the *one endpoint* of a
future bridge, and state precisely what the *other* endpoint and the
*intertwiner* would have to be.

**Stage 2 — define a candidate map, not a coincidence.** Pick a second
genuine object carrying a `Sym(3)`-action (e.g. a graph-cohomology `H¹`
with an automorphism-induced action, or a slot-arithmetic structure).
Define an explicit `𝔽₂`-linear map `φ : H¹ → Octet` and prove it
**intertwines** the two `Sym(3)`-actions: `φ(g·x) = g·φ(x)` for the
generators. *Equal dimension is assumed only as a precondition; the
content is the intertwining.*

**Stage 3 — prove the iso (injectivity + surjectivity / character match).**
Upgrade Stage 2's intertwiner to an isomorphism: same irrep multiplicities
on both sides (Stage 1 gives `(2, 3)` for the octet), equal characters,
and a two-sided inverse. *This* would be a real cross-domain
identification: `H¹ ≅ 𝔰𝔲(3)-adjoint` as `Sym(3)`-modules — a proven map,
not a shared integer.

**Stage 4 — categorical / functorial bridges (research arc).** Generalize
from a single iso to a functor between the math (cohomology) and physics
(representation) categories, with naturality. This is the genuine
"cross-domain unification" the deleted catalog gestured at; it is open and
substantial.

**Catalog discipline (immediate).** Rewrite `cross-domain-identifications.md`
so every entry is *either* (a) a proven structure-preserving map, *or*
(b) explicitly labelled "shared proof shape only — NOT an identification"
(as CDI-2 already is). The shape-vector scan stays a lead generator, never
a verdict.

## 5. Honest scope

  · The octet `Sym(3)`-module structure (`OctetModule.*`,
    `Sym3OctetOrbits.*`) is **proven ∅-axiom** — genuine
    representation theory, but **intra-domain** (one object).
  · `CrossDomainUnification.shared_grade_truncation` is **proven** but is
    **code reuse of one identity**, not a cross-domain map — must be framed
    as such.
  · There is currently **no proven structure-preserving map** between two
    distinct-domain objects. All Stage-2/3/4 isos and functors are
    **open**.
  · "Equal integer" / "byte-identical Expr-shape" CDI claims are
    **withdrawn**: they are coincidences of value or proof skeleton, not
    identifications. The catalog records them only as scan leads.

## 6. Cross-references (genuine kept seams)

  · `lean/E213/Lib/Physics/Symmetry/OctetModule.lean` (Stage 1 — the one
    genuine `Sym(3)`-module: Coxeter presentation, `2·triv ⊕ 3·std`
    decomposition, standard-rep pairs, characters)
  · `lean/E213/Lib/Math/Combinatorics/Sym3OctetOrbits.lean` (the orbit
    structure of the same action — Burnside count, fixed sets)
  · `lean/E213/Lib/Math/Foundations/CrossDomainUnification.lean` (the
    shared-lemma reuse — to be reframed as reuse, not identification)
  · `catalogs/cross-domain-identifications.md` (CDI catalog — to be
    rewritten under the map-or-label discipline; CDI-2 already honest)
  · `theory/math/foundations/cross_domain_unification.md` (narrative)
  · `tools/ast_shape_scan.py` (the shape-vector scan — lead generator only)
