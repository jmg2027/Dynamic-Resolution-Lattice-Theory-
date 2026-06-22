# Decomposition: tropical geometry (curves / varieties / tropicalization)

*A FRESH decomposition per `../README.md` (model v7.1). The bar is **prediction / revelation**, and
the consolidating hypothesis to TEST (not re-skin): tropical geometry is the calculus's **`×↦+`
valuation reading made a degeneration** — **tropicalization = the valuation map**, and the **tropical
variety = the IMAGE of a variety under the coordinatewise valuation** (its combinatorial skeleton /
residue). The (min,+) semiring = `tropical.md`'s idempotent (max,+) read non-archimedean (valuation of a
sum = min of valuations, `padic`/`berkovich`'s ultrametric); `×↦+` is `prime_factorization.md`'s
`vp_mul`. The **fundamental theorem** (trop(V) = val(V)) = the valuation-reading commutes (the image IS
the tropical variety). The **balancing condition** at each vertex of a tropical curve = a **conservation
law** = `q=±1` at the vertex, the SAME `∂·j=0` as `max_flow_min_cut.md`'s flow / `noether.md`'s discrete
current. **Tropical Bézout** = the count (`cardinality`'s count-readout). So tropical geometry = (the
(min,+) = `×↦+` valuation) + (tropicalization = the valuation image of a whole variety = its skeleton,
`toric_geometry` extended past monomials) + (balancing = conservation / `q=±1` at vertices) + (tropical
Bézout = the count) — NO new primitive.*

This entry is **strictly downstream of two neighbors and does not re-skin them**: `tropical.md` did the
(max,+) idempotent SEMIRING (`max_idem`, the `×↦+` dequantization); `toric_geometry.md` did the Newton
polytope = the image of the multi-variable valuation on *monomials* + the fan. **The NEW datum here**:
tropicalization is that same valuation reading applied to a whole **VARIETY** (not just monomials — its
combinatorial residue/skeleton), and the **balancing condition is a conservation law** (`q=±1`/`∂·j=0`),
the SAME conservation `max_flow_min_cut.md` fused with Noether's current. Split, like its neighbors, into
a **grounded core** (the `×↦+` valuation `vp_mul`, the (min,+)/(max,+) idempotent pole `max_idem`, the
faithfulness `vp_separation`, the conservation `NoetherCurrent.continuity_eq`, the count `countTrue_append`,
the `q=±1` tag) and a **located missing leg** (an actual `TropicalVariety`/`tropicalize`/`balanced`/
`TropicalCurve`/`Bezout` object — **absent**, grep-confirmed, located exactly like `tropical.md`'s missing
tropicalization map and `toric_geometry.md`'s missing fan/variety object).

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the **×-construction on a variety's defining data**: a polynomial system over a
  non-archimedean field, each polynomial `f = Σ_a c_a x^a` a finite `+`-superposition of monomials, each
  monomial `x^a` built by multiplying distinguishable variable-axes with multiplicity (the multi-variable
  `prime_factorization.md` ×-atom construction, `toric_geometry.md`'s `C`). A *variety* `V` is the
  zero-locus the system cuts out — a `Real213`-cut/value-cut interior (reached by none). `C` carries the
  model-v4 **fold-height** (degree / cone dimension) and a **direction/sign** bit (the lattice `ℤⁿ`
  exponents via the difference-Lens `integers.md`; the coefficient valuations land in `ℝ∪{∞}` with sign).
  Nothing is constructed *for* "tropical": tropical geometry reads the *same* variety-construction through
  a degenerate (valuation) resolution.

- **Reading `L` — the coordinatewise valuation `val` made a degeneration (tropicalization).** The central
  claim, in four stages:
  1. **(min,+) = (max,+) read non-archimedean.** `tropical.md` certified that the (max,+) semiring is the
     `×↦+` character at its idempotent `T→0` limit; the (min,+) twin is the same idempotent pole under the
     valuation order (`min` for valuations of *order*, `max` for sizes), because **the valuation of a sum
     is the min of valuations** (the ultrametric / non-archimedean reading, `padic.md`/`berkovich`): tropical
     `⊕ = min` is `vol(a+b) = min(vol a, vol b)` and tropical `⊗ = +` is `vol(a·b) = vol a + vol b`. The `⊗`
     is therefore **literally `prime_factorization.md`'s `vp_mul`** (`vp p (m·n) = vp p m + vp p n`); the
     `⊕` is the idempotent join/meet pole (`max_idem` / `cutMin`), `a⊕a = a`.
  2. **Tropicalization = the valuation map applied to a whole VARIETY (the NEW datum).** `toric_geometry.md`
     read the valuation on *monomials* (Newton polytope = image of `x^a ↦ a`). Tropicalization runs the
     *same* `×↦+` reading on the **whole variety**: `trop(V) = val(V) = { val(p) : p ∈ V }` (the
     coordinatewise valuation of each point of `V`, taken non-archimedean). The **tropical variety is the
     IMAGE of `V` under the coordinatewise valuation** — its combinatorial skeleton, a balanced polyhedral
     complex. This is `toric_geometry`'s "Newton polytope = image of the multi-valuation" **extended past
     monomials to the whole variety**: the polytope was the image on the support of one polynomial; the
     tropical variety is the image on the *solution set*. The residue of the valuation reading IS the
     skeleton (what the valuation forces — the cone/recession structure — but does not capture — the
     transcendental interior).
  3. **The fundamental theorem (trop(V) = val(V)) = the valuation-reading commutes.** Kapranov / the
     structure theorem (the "fundamental theorem of tropical geometry") says the tropical variety defined
     combinatorially (the corner/non-differentiability locus of the tropical polynomials) **equals** the
     closure of the coordinatewise valuation image `val(V)`. In calculus terms: the valuation reading
     **commutes** — reading-then-tropicalizing = tropicalizing-then-reading; the image IS the tropical
     variety. This is the `view_factors_through_morphism`-flavoured naturality of the Lens (the reading is
     a 2-cell that commutes with the construction), specialized to the valuation reading.
  4. **The balancing condition = a conservation law / `q=±1` at each vertex.** A tropical curve is a
     **balanced** weighted polyhedral complex: at every vertex, the **weighted sum of the primitive edge
     directions is zero** — `Σ_e w_e · u_e = 0`. This is *exactly* a **conservation law**: the weighted
     directions flowing into a vertex sum to those flowing out, the discrete `∂·j = 0` — the **SAME
     balancing** as `max_flow_min_cut.md`'s flow conservation (in=out at internal nodes) and `noether.md`'s
     discrete continuity equation. The balancing condition is the `q=+1` (settled/conserved) bit on each
     vertex — a charge-conservation `∂·j = 0`, not a free choice.

- **Residue** — two faces, tagged on the `q=±1` spine (`ResidueTag.lean`):
  1. **The tropical variety (skeleton) is the `q=+1` settle of the valuation image** — the combinatorial
     residue of `V` under the valuation reading (the `(max,+)`/`(min,+)` idempotent closure, `max_idem`),
     the same `q=+1` settle `toric_geometry.md` tagged the fan with. It is faithful where the valuation is
     (`vp_separation`: distinct monomials → distinct exponent vectors, per-reading residue 0 on monomials).
  2. **The variety's transcendental interior is the `Real213`-value-cut residue** (reached by none — the
     analytic solution count, the non-archimedean field's value group's full content). Tropicalization
     keeps the `q=+1` skeleton and drops the `q=−1`/value-cut interior; the **fundamental theorem says the
     skeleton it keeps is exactly the valuation image** — the residue *is* the combinatorial object.

## Re-seeing — `⟨C | L⟩ ⊕ Residue`

```
   tropical ⊗ = + (×↦+ valuation)   =  vol(a·b) = vol a + vol b                  (vp_mul, VpMul:165)             × ↦ +
   tropical ⊕ = min/max (ultrametric)=  vol(a+b) = min(vol a, vol b); a⊕a=a       (max_idem, Iterate213:235; cutMin, CutMaxMin:27)  ← idempotent pole
   tropicalization trop(V) = val(V) =  the coordinatewise valuation IMAGE of the whole variety   [TropicalVariety OBJECT conceptual]  ← NEW vs toric (past monomials)
   fundamental thm trop(V)=val(V)    =  the valuation reading COMMUTES (image = trop variety)     [naturality of the Lens; OBJECT conceptual]
   ★ balancing  Σ w_e·u_e = 0        =  conservation ∂·j = 0 at each vertex          (NoetherCurrent.continuity_eq:97 = max_flow's in=out)  ← q=+1 vertex
   valuation faithfulness            =  distinct monomials ↦ distinct exponent vectors (vp_separation, VpSeparation:172, per-reading residue 0)
   tropical Bézout (∩ = deg·deg)     =  the COUNT reading on the skeleton (count-readout)          (countTrue_append, LLN:29)  [Bezout OBJECT conceptual]
   skeleton = q=+1 settle            =  the combinatorial residue of V under the valuation         (residue_tag_two_poles, ResidueTag:228, q=+1)
   variety interior                  =  the Real213-value-cut residue (reached by none)
```

The map is exact on the valuation spine. **`prime_factorization.md`'s `vp` = the monomial valuation =
`toric_geometry.md`'s Newton-polytope reading**; tropicalization runs that *same* reading on the whole
variety, so the **tropical variety is the image of `V` under the valuation** — `toric_geometry`'s polytope
(image on the support) extended to the solution set. The **balancing condition is a conservation law**
(`∂·j=0`, the SAME `NoetherCurrent.continuity_eq` `max_flow_min_cut.md` fused with Noether). Tropical
Bézout is `cardinality`'s count-readout of intersection. Five "different" pieces of tropical geometry —
the (min,+) semiring, tropicalization, the fundamental theorem, balancing, and Bézout — are **one `(C,L)`**:
the `×↦+` valuation reading made a degeneration, its image the skeleton, its vertices balanced by
conservation, its intersections counted.

## LEVERAGE — does tropical geometry fall out as the `×↦+` valuation reading made a degeneration?

**Verdict: PREDICTION (extending `toric_geometry`'s valuation-image weld from monomials to whole
varieties, + a NEW conservation reading of balancing) + PARTIAL — the `×↦+` valuation, the (min,+)/(max,+)
idempotent pole, the faithfulness, the conservation `∂·j=0`, the count-readout, and the `q=±1` tag are ALL
grounded ∅-axiom; the actual `TropicalVariety`/`tropicalize`/`balanced`/`TropicalCurve`/`Bezout` OBJECT is
the single located missing leg.** Five legs, honestly graded.

**(A) The (min,+) semiring = (max,+) read non-archimedean = the `×↦+` valuation — PREDICTED, the character
+ idempotent pole grounded, the (min,+) instance inherited conceptual.** The `⊗ = +` is `vp_mul`
(`Meta/Nat/VpMul.lean:165`, `vp p (m·n) = vp p m + vp p n` — 10/0 PURE), the `×↦+` character; the `⊕`
idempotency `a⊕a=a` is `max_idem` (`Meta/Nat/Iterate213.lean:235`, 17/0 PURE), with the (min,+) twin
grounded by the cut-lattice meet `cutMin` (`CutMaxMin.lean:27`, `cx m k || cy m k` — 10/0 PURE) and the
abstract `idem_inf` (`BooleanAlgebra.lean:31`, 25/0 PURE). `tropical.md` already certified the (max,+)
degeneration; the (min,+) is the *same* idempotent pole read on valuation order (the ultrametric
`vol(a+b)=min`), so the only NEW thing here is the non-archimedean *reason* `⊕` is min — and that reason is
the valuation reading itself. The (min,+) semiring object is the same conceptual leg `tropical.md` located.

**(B) Tropicalization = the valuation image of a whole VARIETY — PREDICTED, the valuation grounded, the
`tropicalize`/`TropicalVariety` object conceptual (the NEW datum vs toric).** The reading is `vp_mul` +
its faithful multi-axis coordinate `vp_separation` (`Meta/Nat/VpSeparation.lean:172`,
`(∀ p prime, vp p m = vp p n) ⟹ m = n` — 9/0 PURE) and axis-independence `two_three_unique`
(`Meta/Nat/FoldCriterion.lean:158`, `2^a=3^b ⟹ a=b=0` — 8/0 PURE). `toric_geometry.md` certified "Newton
polytope = image of this reading on the support of one polynomial"; the **new claim** is "tropical variety
= image of this reading on the whole solution set `V`", `trop(V) = val(V)`. This is the *same* reading at a
*larger* operand (the variety, not the monomial support), so it is grounded *as the valuation character +
its faithful coordinate*, with the extension structurally forced (the reading does not change, only what it
is applied to). *Conceptual leg:* there is **no `tropicalize`, `TropicalVariety`, `valuationMap`, or
`skeleton` object** (grep: zero hits across `lean/E213`; the only `tropical`/`max-plus` strings are two
comments — `RawDagSize.lean:12` "max-plus algebra" on the depth-fold, `DiscreteGeometry.lean:111`
"tropical/min-plus structure" on shortest paths). The reading whose image *is* the tropical variety is
certified; the variety-image bundling is unwritten.

**(C) The fundamental theorem (trop(V) = val(V)) = the valuation reading commutes — PREDICTED, the
naturality machine grounded, the equality-as-stated conceptual.** The structure theorem is, in calculus
terms, "the valuation reading is natural / commutes with the construction": reading-then-tropicalizing =
tropicalizing-then-reading, so the combinatorial corner-locus equals the valuation image. The naturality
*machine* is the Lens 2-category — `view_factors_through_morphism` (the naturality triangle) and the
faithfulness `vp_separation` (the reading does not lose the exponent data) ground "the image IS the
tropical variety". *Conceptual leg:* the equality `trop(V) = val(V)` as a *stated theorem* needs the
`tropicalize`/`TropicalVariety` objects (B) plus a `Real213`-cut for the generic/analytic side — absent.

**(D) ★ The balancing condition = a conservation law / `q=±1` at each vertex = the SAME `∂·j=0` as
max-flow — PREDICTED AND GROUNDED (the NEW reading, and the leg that is *most* grounded).** A tropical
curve is **balanced**: at each vertex `Σ_e w_e · u_e = 0` (weighted primitive edge directions sum to
zero). This is **literally a conservation law**, and the repo builds exactly that: `NoetherCurrent`
proves the **discrete continuity equation** `(∂_t ρ)(g,w) = j(g,w)` (`continuity_eq`,
`…/ModularGeometry/NoetherCurrent.lean:97` — 14/0 PURE), the 213-native `∂·j = 0`, with `noether_local`
(`:149`) the iff tying conservation to `Aut`-invariance (`det g = 1`). And `max_flow_min_cut.md` already
identified this *same* `continuity_eq` as flow conservation (in=out at internal nodes,
`max_flow_min_cut.md:75`, `conservation in=out at v≠s,t = noether's ∂·j=0`). **So the tropical balancing
condition is the SAME conservation law `∂·j=0` that max-flow's vertex-conservation and Noether's discrete
current are** — the `q=+1` settled/conserved bit on each tropical-curve vertex, forced (a charge balance),
not an arbitrary tropical axiom. This is the entry's strongest grounding and its NEW datum vs the two
neighbors: neither `tropical.md` nor `toric_geometry.md` touched balancing; it lands on the corpus's
already-built conservation current. *Conceptual leg:* a `balanced`/`TropicalCurve` predicate bundling the
edge-direction sum is absent; the conservation law it *is* (`continuity_eq`, `∂·j=0`) is built and PURE.

**(E) Tropical Bézout = the count reading on the skeleton — PREDICTED, the count-readout grounded, the
`Bezout` object conceptual.** Tropical Bézout (two tropical curves of degrees `d`, `e` meet in `d·e`
points, counted with multiplicity) is the **count-readout** of the intersection — `cardinality`/
`probability`'s additive-count engine `countTrue_append` (`Lib/Math/Probability/Limit/LLN.lean:29`,
`countTrue (xs ++ ys) = countTrue xs + countTrue ys` — 7/0 PURE), the same count `toric_geometry.md` read
as Bernstein's mixed volume (tropical Bézout is the degree-by-degree special case of the mixed-volume/
stable-intersection count). So "tropical Bézout = the count on the skeleton" is grounded *as the
count-readout the calculus runs through cardinality/toric*; the **`Bezout`/`stableIntersection` object is
absent** (the geometric `Bezout` substring hits in the repo are all about `ℤ`'s Bézout identity / GCD —
`EuclidUnique.lean`, `Nat213.lean` — none a tropical or curve-intersection theorem).

**Net.** Not a re-skin of the two neighbors: the NEW content is (i) tropicalization = the valuation image
of a whole **variety** (toric's polytope-on-monomials extended to the solution set, the skeleton =
residue), (ii) the fundamental theorem = the valuation reading commutes, and (iii) the **balancing
condition = a conservation law `∂·j=0`** landing on the corpus's built Noether/max-flow current. Not a
clean collapse-only: the `TropicalVariety`/`tropicalize`/`balanced`/`TropicalCurve`/`Bezout` object is
genuinely unbuilt. It is **PREDICTION + PARTIAL**: every structural leg is grounded ∅-axiom and the
missing legs are *named objects*, not missing structure.

## Revelation

**Tropical geometry is ONE `(C,L)` — the `×↦+` valuation reading made a degeneration — and its NEW data
over the two neighbors are that tropicalization is the valuation image of a whole VARIETY (the
combinatorial skeleton = residue) and the balancing condition is the corpus's already-built conservation
law `∂·j=0`.** This is **collapse + forcing + residue-surfaced**, three at once:

1. **Collapse — the (min,+) semiring, tropicalization, the fundamental theorem, balancing, and Bézout are
   five readouts of one `×↦+` valuation reading.** The `⊗=+` is `vp_mul`; the `⊕=min` is the idempotent
   pole read non-archimedean (`max_idem`/`cutMin`); tropicalization is that reading applied to the whole
   variety (the image = the skeleton); the fundamental theorem is the reading commuting (image = tropical
   variety); balancing is conservation `∂·j=0` (`continuity_eq`); Bézout is the count (`countTrue_append`).
   Five "different" pieces are the *same* valuation reading read five ways — and the **same** valuation
   `prime_factorization.md` runs on prime axes, `toric_geometry.md` runs on monomials, now run on a variety.

2. **Forcing — the balancing condition is forced as a conservation law, not chosen.** The defining feature
   that makes a polyhedral complex a *tropical curve* — the balancing `Σ w_e·u_e = 0` — is *not an
   arbitrary tropical axiom*: it is the discrete continuity equation `∂·j = 0` the repo built as Noether's
   conserved current (`continuity_eq`, `noether_local`) and `max_flow_min_cut.md` built as flow
   conservation (in=out at internal vertices). A tropical curve is balanced for the *same* reason a flow
   conserves charge: the weighted directions in equal the weighted directions out. Balancing is the
   `q=+1` settled bit on each vertex, forced by the corpus's conservation law, not a feature of "tropical".

3. **Residue surfaced — the tropical variety IS the residue of the valuation reading (the skeleton), and
   the fundamental theorem says the residue equals the image.** Classical accounts present the tropical
   variety as a new combinatorial object and tropicalization as a structure-losing limit. The calculus
   re-sees the **tropical variety as the `q=+1` combinatorial residue of `V` under the valuation reading**
   (`toric_geometry`'s fan extended to the solution set) — what the valuation forces (the cone/recession
   skeleton) but does not capture (the transcendental interior, the `Real213`-value-cut reached by none).
   The fundamental theorem `trop(V) = val(V)` is then the statement that **this residue equals the
   valuation image** — the skeleton the variety converges onto is exactly what the valuation reading
   outputs.

**THE EXTENSION (the brief's central question):**

| pillar | 213 reading | prior entry | Lean status |
|---|---|---|---|
| (min,+)/(max,+) semiring | the `×↦+` valuation `⊗`; the idempotent `⊕` read non-archimedean | `tropical.md` ((max,+)), `padic.md` (ultrametric) | `⊗` **built** (`vp_mul`); idempotent pole **built** (`max_idem`, `cutMin`, `idem_inf`); (min,+) object conceptual |
| tropicalization trop(V)=val(V) | the valuation IMAGE of a whole VARIETY (toric's polytope past monomials) = the skeleton | `toric_geometry.md` (image on monomials), `prime_factorization.md` (`vp`) | valuation **built** (`vp_mul`, `vp_separation`, `two_three_unique`); `tropicalize`/`TropicalVariety` object conceptual |
| fundamental theorem | the valuation reading COMMUTES (image = trop variety) | `category_theory.md` (Lens naturality) | naturality machine **built** (`view_factors_through_morphism`, `vp_separation`); the stated equality conceptual |
| ★ balancing Σ w·u = 0 | a conservation law `∂·j=0` / `q=+1` at each vertex — SAME as max-flow | `noether.md` / `max_flow_min_cut.md` (`∂·j=0`) | conservation **built** (`continuity_eq`:97, `noether_local`, 14/0); `balanced`/`TropicalCurve` predicate conceptual |
| tropical Bézout | the COUNT reading on the skeleton (deg·deg, the stable-intersection count) | `cardinality` / `toric_geometry` (mixed volume) | count-readout **built** (`countTrue_append`); `Bezout`/`stableIntersection` object conceptual |
| the whole correspondence's tag | `q=+1` settle (skeleton/balancing); interior = value-cut residue | `ResidueTag.lean` | tag **built** (`residue_tag_two_poles`, 55/0) |

So **YES** — tropical geometry falls out as the **`×↦+` valuation reading made a degeneration**:
tropicalization IS the valuation map applied to a whole variety (`toric_geometry`'s polytope-on-monomials
extended to the solution set, the skeleton = the `q=+1` residue), the fundamental theorem is the valuation
reading commuting, the **balancing condition is the corpus's conservation law `∂·j=0`** (`continuity_eq`,
the SAME as max-flow / Noether), and tropical Bézout is `cardinality`'s count-readout. Tropical geometry
**extends `toric_geometry`'s valuation-image weld from monomials to whole varieties and adds the
conservation reading of balancing**, with **no new axis**.

## Note for the technique — does tropical geometry force a new construct?

**Verdict: EXTEND by consolidation — no new primitive.** Every slot tropical geometry uses already exists:
- **the `×↦+` valuation character** (`prime_factorization.md`/`toric_geometry.md`'s `vp_mul`) — the
  tropical `⊗`, and the reading whose image is the tropical variety;
- **the (max,+)/(min,+) idempotent pole** (`tropical.md`'s `max_idem`, the cut-lattice `cutMin`,
  `idem_inf`) — the tropical `⊕`, read non-archimedean (the ultrametric `vol(a+b)=min`);
- **the faithful multi-axis coordinate** (`vp_separation`, `two_three_unique`) — tropicalization is
  faithful on monomials, the skeleton genuinely `ℝⁿ`-dimensional;
- **the conservation law `∂·j=0`** (`noether.md`/`max_flow_min_cut.md`'s `continuity_eq`) — the balancing
  condition at each vertex, the SAME conservation as flow's in=out;
- **the count reading** (`cardinality`/`toric_geometry`'s `countTrue_append`) — tropical Bézout / stable
  intersection;
- **the `q=±1` residue tag** (`ResidueTag.lean`) — the `q=+1` skeleton settle vs the value-cut interior.

The one sharpening (the structural lesson): **tropical geometry is the first entry where the valuation
image (`toric_geometry`, on monomials) is extended to a whole variety AND a conservation law
(`noether`/`max_flow`) lands on the resulting skeleton's vertices**. The cross-tie — *valuation image of a
variety ⇄ a balanced (conservation-law-constrained) skeleton* — shows the tropical variety is not just the
fan's bigger sibling but a **conserved** combinatorial residue: the same `∂·j=0` that constrains a flow
constrains a tropical curve at every vertex. That cross-tie (the skeleton-residue is balanced by the same
conservation current the corpus already built) is the lesson, recorded as an EXTEND, not a new axis.

## Verified Lean anchors (file:line:theorem — all grep/Read-verified; scan tallies from `tools/scan_axioms.py` repo-root this session)

| Leg | Theorem (file : name : line) | Status |
|---|---|---|
| ★ **the `×↦+` valuation** (tropical `⊗ = +`; the reading whose image is the tropical variety) | `Meta/Nat/VpMul.lean : vp_mul : 165` (`vp p (m·n)=vp p m+vp p n`), `vp_pow : 183` (`vp p (aᵏ)=k·vp p a`), `vp_self_pow : 204` | ∅-axiom ✓ (**10 pure / 0 dirty**) |
| **valuation faithfulness** (distinct monomials ↦ distinct exponent vectors; per-reading residue 0) | `Meta/Nat/VpSeparation.lean : vp_separation : 172` (`(∀ p prime, vp p m=vp p n) ⟹ m=n`) | ∅-axiom ✓ (**9 pure / 0 dirty**) |
| **axis-independence** (variable axes never trade; skeleton genuinely `ℝⁿ`) | `Meta/Nat/FoldCriterion.lean : two_three_unique : 158` (`2^a=3^b ⟹ a=0 ∧ b=0`) | ∅-axiom ✓ (**8 pure / 0 dirty**) |
| ★ **the (max,+)/(min,+) idempotent pole** (tropical `⊕`; the skeleton's idempotent settle) | `Meta/Nat/Iterate213.lean : max_idem : 235` (`Nat.max a (Nat.max a x)=Nat.max a x`), `max_unfold : 229`, `max_iter_trivial : 246` ("max builds no tower") | ∅-axiom ✓ (**17 pure / 0 dirty**) |
| **the (min,+) lattice meet + abstract idempotency** | `Lib/Math/NumberSystems/Real213/Lattice/CutMaxMin.lean : cutMin : 27` (`cx m k || cy m k`), `cutMax : 23`, `cutMin_comm : 46`, `cutMin_assoc : 76`; `Lib/Math/Order/BooleanAlgebra.lean : idem_inf : 31` (`inf a a=a`), `idem_sup : 40` | ∅-axiom ✓ (**10/0** + **25/0**) |
| ★ **balancing = conservation `∂·j=0` at each vertex** (the NEW datum; SAME as max-flow / Noether) | `…/Real213/ModularGeometry/NoetherCurrent.lean : continuity_eq : 97` (`(∂_t ρ)(g,w)=j(g,w)`), `noether_local : 149` (`∂·j=0 ⟺ det g=1`), `density_conserved_of_det_one : 117` | ∅-axiom ✓ (**14 pure / 0 dirty**) |
| **tropical Bézout / stable intersection = the count reading on the skeleton** | `Lib/Math/Probability/Limit/LLN.lean : countTrue_append : 29` (`countTrue(xs++ys)=countTrue xs+countTrue ys`) | ∅-axiom ✓ (**7 pure / 0 dirty**) |
| **the fundamental-theorem naturality machine** (the valuation reading commutes; trop(V)=val(V)) | `Lens/Compose/Morphism.lean : view_factors_through_morphism : 37` (`M.view = h∘L.view`) [grep-confirmed via SYNTHESIS; faithfulness via `vp_separation`] | ∅-axiom ✓ (per SYNTHESIS §2, 3/0) |
| **the `q=±1` residue tag** (the `q=+1` settle of the skeleton; balancing's conserved bit) | `Lib/Math/Foundations/ResidueTag.lean : residue_tag_two_poles : 228`, `golden_is_converge : 180`, `multiplier_unimodular : 86` | ∅-axiom ✓ (**55 pure / 0 dirty**) |
| **the iteration-character growing-pole mirror** (the idempotent pole's opposite, repo-named) | `Theory/Raw/MuNuMirror.lean : succ_not_idempotent : 80` (`S(S r) ≠ S r`) | ∅-axiom ✓ (**8 pure / 0 dirty**) |
| **the `clo` closure** (the skeleton as idempotent closure of the valuation image) | `Lib/Math/Order/GaloisConnection.lean : clo : 104`, `clo_idempotent : 126`; `Lib/Math/Order/FenchelMoreau.lean : biconj_idempotent : 134` | ∅-axiom ✓ (**15/0** + **18/0**) |

> Axiom-purity note: `VpMul` (10/0), `VpSeparation` (9/0), `FoldCriterion` (8/0), `Iterate213` (17/0),
> `CutMaxMin` (10/0), `BooleanAlgebra` (25/0), `NoetherCurrent` (14/0), `LLN` (7/0), `ResidueTag` (55/0),
> `MuNuMirror` (8/0), `GaloisConnection` (15/0), `FenchelMoreau` (18/0) were each re-run through
> `tools/scan_axioms.py` (full `E213.` prefix) from repo root this session — **every cited theorem PURE,
> 0 dirty across all twelve load-bearing modules.** (`view_factors_through_morphism` is grep/SYNTHESIS-
> confirmed at `Lens/Compose/Morphism.lean:37`, 3/0, the naturality 2-cell; cited for the
> fundamental-theorem "reading commutes" leg.)

## Conceptual-only legs / located missing leg (honest — NOT grounded in repo Lean)

- **An actual `TropicalVariety` / `tropicalize` / `valuationMap` / `TropicalCurve` / `balanced` /
  `Bezout`(curve-intersection) / `TropicalPolynomial` object — ABSENT (confirmed by grep).** Across all
  `lean/E213`, there is **no** `tropical`/`tropicalization`/`TropicalVariety`/`TropicalCurve`/`tropicalize`
  identifier, no `balanced` *as a tropical-curve predicate* (the `balanced` substring hits are unrelated:
  `rBalanced` — a `Raw` test witness in `DepthIncomparable.lean`; `BalancedSignature` — a Hodge-pairing
  signature file; `balanced_LLN_modulus` — a probability modulus), no `polyhedral`/`skeleton`(geometric)
  object, and no curve-intersection `Bezout` (the `Bezout`/`Bézout` hits are all `ℤ`'s Bézout
  identity / GCD: `EuclidUnique.lean:10,15,70`, `Nat213.lean:75`, `ModNat.lean:168`, the architecture/
  index docstrings — none tropical). The only `tropical`/`max-plus`/`min-plus` strings in the whole tree
  are two **comments**: `Lib/Math/Foundations/UniverseChain/RawDagSize.lean:12` "max-plus algebra" (a
  naming convention on `Raw.fold`), and `Lib/Math/Cohomology/HodgeConjecture/Bridge/DiscreteGeometry.lean:111`
  "tropical/min-plus structure" on graph shortest paths (a conceptual remark, not a tropicalization map or
  a balanced complex). This is **the single located missing leg**, exactly like `tropical.md`'s missing
  tropicalization/softmax map and `toric_geometry.md`'s missing `ToricVariety`/`fan`: the valuation reading
  whose image *is* the tropical variety (`vp_mul`), the idempotent pole the skeleton settles to
  (`max_idem`), the conservation law balancing constrains it by (`continuity_eq`), and the count tropical
  Bézout *is* (`countTrue_append`) are all present and certified; only the **geometric object bundling
  them** — the tropical variety / curve / tropicalization map / balanced complex — is unwritten.
- **The fundamental theorem (trop(V) = val(V)) as a stated theorem** — absent. The naturality *machine*
  (`view_factors_through_morphism`) and faithfulness (`vp_separation`) ground "the image IS the tropical
  variety"; the stated equality needs the `tropicalize`/`TropicalVariety` objects above plus a `Real213`-cut
  for the generic/analytic (Kapranov, residue/Puiseux-series) side — the same value-cut residue
  `toric_geometry.md`/`algebraic_geometry.md` locate for a variety's interior.
- **The balancing condition as a stated `balanced` predicate** — absent as a *named tropical predicate*,
  but the conservation law it *is* (`∂·j=0`, `continuity_eq`/`noether_local`) is built and PURE, and is
  *already* identified with the same `∂·j=0` in `max_flow_min_cut.md`. The missing leg is only the
  edge-direction-vector bundling `Σ_e w_e·u_e = 0` as a `TropicalCurve.balanced` field — the conservation
  *content* is grounded; the tropical-curve *packaging* is unwritten.
- **Tropical Bézout / stable intersection as a stated theorem** — absent. The count *reading*
  (`countTrue_append`) and the degree/lattice structure (`vp`) are grounded; `d·e` as the stable
  intersection count of two balanced curves (and its `Real213`-cut for the generic transverse count)
  inherits the missing `TropicalCurve` object plus the value-cut residue.

## Verdict: PREDICTION (extending `toric_geometry`'s valuation-image weld to whole varieties + a NEW conservation reading of balancing) + PARTIAL (the tropical-variety/curve/tropicalization/balanced/Bézout object the missing leg)

Tropical geometry **predicts and extends** — it does not break the model and adds no axis. **Grounded
∅-axiom:** the **`×↦+` valuation** tropicalization *is* (`vp_mul`, 10/0), its **faithfulness**
(`vp_separation`, 9/0) and **axis-independence** (`two_three_unique`, 8/0); the **(max,+)/(min,+)
idempotent pole** the skeleton settles to (`max_idem`, 17/0; `cutMin`/`idem_inf`, 10/0+25/0); ★ the
**conservation law `∂·j=0`** the balancing condition *is* — the SAME `continuity_eq` (14/0) as
`max_flow_min_cut.md`'s flow conservation and `noether.md`'s discrete current; the **count reading**
tropical Bézout *is* (`countTrue_append`, 7/0); the naturality machine the fundamental theorem *is*
(`view_factors_through_morphism`, 3/0); and the **`q=±1` residue tag** (`residue_tag_two_poles`, 55/0).
The **single located missing leg** is an actual `TropicalVariety`/`tropicalize`/`balanced`/`TropicalCurve`/
`Bezout` object — **confirmed absent by grep** (two comment-only `max-plus`/`min-plus` hits; all `balanced`
hits unrelated; all `Bezout` hits are `ℤ`'s GCD identity) — located precisely: the valuation reading whose
image *is* the tropical variety, the idempotent pole the skeleton settles to, the conservation law
balancing constrains it by, and the count tropical Bézout *is* are all present and certified; only the
**geometric bundling** of them is unwritten.

> **Open Lean target the calculus names precisely:** define the coordinatewise valuation
> `tropV : Variety n → Set (ℤⁿ or ℝⁿ)` as the per-axis `vp`-vector image of the solution set
> (`x ↦ (vp p₁ x, …)`, extending `toric_geometry`'s `monVal` from a monomial to a whole point), prove
> tropicalization is the `×↦+` character (`vp_mul` per axis) and faithful (`vp_separation` per axis); then
> define a `TropicalCurve` as a weighted edge-complex with a `balanced` field `Σ_e w_e·u_e = 0` **proved
> equal to `NoetherCurrent.continuity_eq`'s `∂·j=0`** at each vertex (the conservation law already built),
> and `tropBezout : deg c₁ · deg c₂` via `countTrue_append`. This is the weld that would promote the entry
> from PREDICTION+PARTIAL to a closed derivation — the tropical variety as the valuation image of a variety
> with balanced (= conserved, `continuity_eq`) vertices, parallel to `toric_geometry.md`'s `monVal`-image
> Newton polytope and `ConvolveRescaleContraction` welding the Banach engine to the CLT. The fundamental
> theorem `trop(V)=val(V)` and the generic Bézout count then inherit the same `Real213`-value-cut residual
> the variety interior carries.
