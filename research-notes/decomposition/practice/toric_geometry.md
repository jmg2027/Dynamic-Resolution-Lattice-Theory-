# Decomposition: toric geometry / Newton polytopes

*A FRESH decomposition per `../README.md` (model v7.1). The bar is **prediction / revelation**, and
the consolidating hypothesis to TEST (not re-skin): toric geometry is the calculus's **`×↦+` valuation
character made geometric** — the **Newton polytope IS the image of the multi-variable monomial
valuation reading** (`prime_factorization.md`'s `vp` generalized to the exponent-vector of a Laurent
monomial), and the **fan↔toric-variety correspondence is the tropical/(max,+) residue**
(`tropical.md`): tropicalization sends a variety to its fan = the valuation/(max,+) image, the fan
being the combinatorial residue of the variety under the valuation reading. **Bernstein's theorem**
(mixed volume = generic solution count) = the **count reading** on the polytope (`cardinality`'s
count-readout, `countTrue_append`), and the **moment map** = the **convex-duality** image of the torus
action (`convex_duality.md`'s `f**=clo`). So toric geometry = (the `×↦+` valuation character,
multi-variable) + (the polytope = its image) + (the fan = the tropical/(max,+) residue) — NO new
primitive, it welds `prime_factorization.md`'s `vp` and `tropical.md`'s (max,+) onto monomials.*

This entry is split, like `algebraic_geometry.md`/`tropical.md`/`convex_duality.md`, into a **grounded
core** (the `×↦+` valuation character `vp_mul`, its faithfulness `vp_separation`, the axis-independence
`two_three_unique`, the (max,+) idempotent pole `max_idem`, the count-readout `countTrue_append`, the
`clo` closure / Legendre dual) and a **located missing leg** (an actual `ToricVariety`/`NewtonPolytope`/
`fan`/`mixedVolume`/`momentMap` object — **absent**, confirmed by grep, located exactly like
`algebraic_geometry.md`'s missing `Spec` and `tropical.md`'s missing tropicalization map).

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the **×-construction on monomials**, the multi-variable generalization of
  `prime_factorization.md`'s `ℕ_{>0}` under `×`. A Laurent monomial `x^a = x₁^{a₁}···xₙ^{aₙ}` is built
  by multiplying generators, iterated; the distinguishing-history is **which axes (variables) were used,
  with multiplicity** — and the axes are **distinguishable** (the multi-variable form of
  `prime_factorization.md`'s ×-atom distinguishability: `two_three_unique`, the 2-axis and 3-axis never
  trade). `C` carries the model-v4 **fold-height** (the total degree / cone dimension) and a
  **direction/sign** bit (the lattice `ℤⁿ` vs `ℕⁿ` — the difference-Lens `integers.md` on each exponent
  axis, giving Laurent `x⁻¹`). A polynomial `f = Σ_a c_a x^a` is a *finite formal `+`-superposition* of
  these monomials.

- **Reading `L` — the multi-variable `×↦+` monomial valuation `x^a ↦ a ∈ ℤⁿ`** (the central claim).
  This is `prime_factorization.md`'s `vp` with the prime-axes replaced by variable-axes: the same
  construction-preserving **logarithmic/character reading** whose readout group changes the operation,
  monomial-multiply `↦` exponent-add: `x^a · x^b ↦ a + b`. The classical statements decompose:
  1. **The Newton polytope `Newt(f)` = the convex hull of `{a : c_a ≠ 0}`** = the **image of this `×↦+`
     reading**, i.e. the support of the character collected into a convex body. The polytope is *not a
     new object* — it is the geometric collection of the exponent vectors the valuation reading outputs.
  2. **The fan ↔ toric-variety correspondence = the tropical/(max,+) residue.** Tropicalization sends a
     variety `V` to its fan/recession structure by reading each monomial through its **valuation** and
     keeping the `min`/`max` (`tropical.md`'s (max,+) idempotent pole): the fan is the **combinatorial
     residue of the variety under the valuation reading** — what the valuation forces (the cone
     structure) but does not capture (the variety's `Real213`-cut interior). The toric variety `X_Σ` is
     reconstructed *from* the fan `Σ` = the variety is the `q=+1` settle of its own valuation image.
  3. **Bernstein's theorem (mixed volume = generic # of solutions) = the count reading on the polytope.**
     The number of solutions of a generic system is the **mixed volume** of the Newton polytopes — a
     **count-readout** (`cardinality`'s count-reading; the `countTrue_append`/additive-count engine) of
     the polytope's lattice points / normalized volume. It is the `×↦+` character's **volume readout**:
     the additive structure of the exponent lattice counted.
  4. **The moment map = the convex-duality image of the torus action.** The moment map
     `μ : X_Σ → Newt(f)` sends the torus orbit to the polytope by the **Legendre/`f**=clo` dual**
     (`convex_duality.md`): it is the gradient of the (log of the) torus-equivariant function, the
     order-reversing-closure image of the `(ℂ*)ⁿ`-action — the same `clo` the Legendre transform is.

- **Residue** — two faces, tagged on the `q=±1` spine (`ResidueTag.lean`):
  1. **The Newton polytope itself is the `q=+1` settle of the valuation image** (the convex hull is the
     `clo`-closure of the finite exponent set — `max_idem`/`idem_sup` make the lattice-sup idempotent,
     the convex hull is the idempotent closure of the support). It is faithful where the valuation is
     (`vp_separation`-analogue: distinct monomials have distinct exponent vectors), so the *per-reading*
     residue on monomials is **zero** — exactly `prime_factorization.md`'s faithful-coordinate datum.
  2. **The fan is the `q=+1` tropical residue of the variety** (the (max,+) image, `tropical.md`'s
     idempotent pole `max_idem`); the variety's transcendental interior (the actual solution `Real213`
     cuts, the analytic count) is the `Real213`-value-cut residue (reached by none — the same residue
     `algebraic_geometry.md`/`convex_duality.md` locate).

## Re-seeing — `⟨C | L⟩ ⊕ Residue`

```
   monomial valuation (×↦+)   =  x^a · x^b ↦ a + b                              (vp_mul, multi-axis: vₚ(mn)=vₚm+vₚn)   × ↦ +
   axis-distinguishability     =  2^a = 3^b ⟹ a=b=0                            (two_three_unique, axes never trade)
   valuation faithfulness      =  distinct monomials ↦ distinct exponent vectors (vp_separation, per-reading residue 0)
   Newton polytope Newt(f)     =  conv{ a : c_a ≠ 0 } = the IMAGE of the ×↦+ reading   [polytope OBJECT conceptual]
   hull = idempotent closure   =  the convex hull is clo of the support; sup idempotent (max_idem / idem_sup, q=+1)
   fan ↔ toric variety         =  tropicalize = the (max,+) valuation residue of V       [fan/ToricVariety OBJECT conceptual]
   tropical/(max,+) residue    =  max(a,a)=a, the idempotent pole                (max_idem, Iterate213:235)
   Bernstein: mixedVol = #sol  =  the COUNT reading on the polytope (volume readout)      (countTrue_append; count = ×↦+ volume)  [mixedVolume OBJECT conceptual]
   moment map μ: X_Σ → Newt(f) =  convex_duality.md's f**=clo image of the torus action   (clo_idempotent / biconj_idempotent)  [momentMap OBJECT conceptual]
   variety interior            =  the Real213-value-cut residue (reached by none, q=+1 settle)
```

The map is exact on the valuation spine. **`prime_factorization.md`'s `vp` (one prime axis per atom)
IS the monomial valuation (one exponent axis per variable)**; the Newton polytope is the image of that
reading collected into a convex body; the fan is `tropical.md`'s (max,+) residue of the variety; the
mixed volume is `cardinality`'s count-readout of the polytope; the moment map is `convex_duality.md`'s
`f**=clo` image of the torus action. Five "different" pieces of toric geometry are **one `(C,L)`** — the
multi-variable `×↦+` character — with its image (polytope), its tropical residue (fan), its count-readout
(Bernstein), and its closure-dual (moment map).

## LEVERAGE — does toric geometry fall out as the multi-variable `×↦+` valuation character?

**Verdict: PREDICTION (a weld of `prime_factorization.md`'s `vp` and `tropical.md`'s (max,+)) + PARTIAL
— the valuation character, its faithfulness, the axis-independence, the (max,+) idempotent pole, the
count-readout, and the `clo` closure are ALL grounded ∅-axiom; the actual `ToricVariety`/`NewtonPolytope`/
`fan`/`mixedVolume`/`momentMap` OBJECT is the single located missing leg.** Five legs, honestly graded.

**(A) The Newton polytope = the image of the multi-variable `×↦+` valuation — PREDICTED, the character
grounded, the polytope object conceptual.** The character `×↦+` is built and certified at one axis:
`vp_mul` (`Meta/Nat/VpMul.lean:165`, `vp p (m·n) = vp p m + vp p n` — 10/0 PURE), with `vp_pow`
(`:183`, `vp p (aᵏ) = k·vp p a`, exactly the monomial-power readout `x^{ka} ↦ k·a`). The multi-variable
monomial valuation `x^a ↦ a` is *literally this reading run one-axis-per-variable* (`prime_factorization.md`
already names the prime axes as exactly this vector readout). The **faithfulness** — distinct monomials
map to distinct exponent vectors, so the per-reading residue is zero — is `vp_separation`
(`Meta/Nat/VpSeparation.lean:172`, `(∀ p prime, vp p m = vp p n) ⟹ m = n` — 9/0 PURE), and the
**axis-independence** (axes never trade, the multi-variable lattice is genuinely `ℤⁿ` not collapsible)
is `two_three_unique` (`Meta/Nat/FoldCriterion.lean:158`, `2^a=3^b ⟹ a=b=0` — 8/0 PURE). So the claim
"the Newton polytope is the image (convex hull of the support) of this `×↦+` reading" is **grounded as
the valuation character + its faithful multi-axis coordinate**, not asserted. *Conceptual leg:* there
is **no `NewtonPolytope`, `convexHull`, or polytope object** in the repo (grep: zero hits; the only
`convexHull`/`hull` strings are unrelated Heine–Cantor/Fenchel/König lemmas). The reading whose image
*is* the polytope is certified; the convex-body bundling its image is unwritten.

**(B) The fan ↔ toric-variety correspondence = the tropical/(max,+) residue — PREDICTED, the (max,+)
idempotent pole grounded, the fan/variety object conceptual.** `tropical.md` established (max,+) =
the `×↦+` character at its idempotent `T→0` limit, with the idempotency `a⊕a=a` = the iteration-
character's idempotent pole: `max_idem` (`Meta/Nat/Iterate213.lean:235`, `Nat.max a (Nat.max a x) =
Nat.max a x` — 17/0 PURE), the repo's own docstring reading it as "max builds no tower" (`:241-245`).
The claim "tropicalization sends a variety to its fan = the valuation/(max,+) image; the fan is the
combinatorial residue of the variety under the valuation reading" is the *same* (max,+)-valuation
reading `tropical.md` certified, now applied to the variety's defining polynomial: each monomial read
through its valuation, the cone structure surviving as the `min`/`max` of valuations. The fan is the
`q=+1` settle (idempotent closure) of the valuation image — `idem_sup` / the lattice sup `cutMax`
(`tropical.md`'s anchors) ground the join. *Conceptual leg:* **no `fan`, `Fan`, `ToricVariety`, or
`tropicalize` object** (grep: zero — the only `tropical`/`max-plus` strings are two *comments*,
`RawDagSize.lean:12` "max-plus algebra" on the depth-fold, `DiscreteGeometry.lean:111` "tropical/min-plus
structure" on shortest paths, neither a fan or a variety). The (max,+) residue *machine* is present and
certified; the fan-as-tropicalization-of-a-variety *instance* is unwritten.

**(C) Bernstein's theorem (mixed volume = generic # of solutions) = the count reading on the polytope —
PREDICTED, the count-readout grounded, the mixed-volume object conceptual.** `cardinality`/`probability`'s
count reading is the additive-count engine `countTrue_append` (`Lib/Math/Probability/Limit/LLN.lean:29`,
`countTrue (xs ++ ys) = countTrue xs + countTrue ys` — 7/0 PURE) — the count distributes over `++`, the
`×↦+`/`+`-additive readout. Bernstein's count (the number of generic solutions = the mixed volume = the
normalized lattice-point/volume count of the Newton polytopes) is **the count reading applied to the
polytope** — the `×↦+` character's *volume* readout, the additive structure of the exponent lattice
counted. (The single-polytope case — Kushnirenko — is the volume; mixed volume is the polarized/multi-
linear count, the same count read multilinearly.) So "Bernstein = count on the polytope" is grounded *as
the count-readout the calculus runs through cardinality/probability/generating-functions*; the **mixed
volume / `mixedVolume` object is absent** (grep: zero hits) — the volume *count* is the certified
reading, the mixed-volume-of-polytopes *instance* is the named leg.

**(D) The moment map = the convex-duality image of the torus action — PREDICTED, the `clo` closure
grounded, the moment-map object conceptual.** `convex_duality.md` established the Legendre–Fenchel
`f**=clo` as the order-reversing-closure on functions (`GaloisConnection.clo_idempotent`,
`Lib/Math/Order/GaloisConnection.lean:126` — 15/0 PURE; `FenchelMoreau.biconj_idempotent`,
`Lib/Math/Order/FenchelMoreau.lean:134`, `closed_iff_fixed:152` — 18/0 PURE). The moment map
`μ : X_Σ → Newt(f)` is *exactly* the Legendre/`clo` image of the torus action: it is the gradient of
the log-equivariant function, sending the torus orbit onto the polytope by the same order-reversing
closure that maps a convex function to its Newton-polytope-of-gradients. So "moment map =
`convex_duality.md`'s `f**=clo` image of the torus action" is grounded *as the closure machine the
Legendre transform inhabits*; the **`momentMap` object is absent** (grep: zero hits). The closure
*structure* (`clo`, `biconj_idempotent`, `closed_iff_fixed`) is present and certified; the
torus-action-to-polytope *instance* is the named leg — inheriting exactly `convex_duality.md`'s missing
`convexConjugate`/`f*` object.

**(E) The whole correspondence is `q=±1`-tagged — PREDICTED, the tag grounded.** The fan, polytope, and
the variety's settle all live at the `q=+1` converging/closure pole (the convex hull = idempotent
closure of the support; the fan = the (max,+) idempotent settle; the moment map = `clo`); the variety's
transcendental interior (the analytic solution count, the `Real213`-cut metric) is the value-cut residue
reached by none. This is the formal `ResidueTag` (`Lib/Math/Foundations/ResidueTag.lean`,
`residue_tag_two_poles:228`, `golden_is_converge:180` — 55/0 PURE), the `q=+1` converge pole the whole
toric/closure spine sits on.

**Net.** Not a re-skin: it **predicts** the form of the four toric pillars (polytope = valuation image,
fan = tropical residue, Bernstein = count-readout, moment map = `clo` dual) and **derives why** — the
Newton polytope is the image of `prime_factorization.md`'s `vp` made multi-variable, the fan is
`tropical.md`'s (max,+) residue, the count is `cardinality`'s readout, the moment map is
`convex_duality.md`'s closure. Not a clean collapse-only: the `ToricVariety`/`NewtonPolytope`/`fan`/
`mixedVolume`/`momentMap` object is genuinely unbuilt. It is **PREDICTION + PARTIAL**: every structural
leg is grounded ∅-axiom and the missing legs are *named objects*, not missing structure.

## Revelation

**Toric geometry is ONE `(C,L)` — the multi-variable `×↦+` monomial valuation character — and it WELDS
two prior entries (`prime_factorization.md`'s `vp` and `tropical.md`'s (max,+)) into one geometric
object.** This is **collapse + forcing + residue-surfaced**, three at once:

1. **Collapse — the Newton polytope, the fan, the mixed volume, and the moment map are FOUR readouts of
   one `×↦+` valuation character.** The Newton polytope (the image of `x^a ↦ a`), the fan
   (tropicalization = the (max,+) residue of the variety), Bernstein's mixed volume (the count-readout
   of the polytope), and the moment map (the `clo` dual of the torus action) are **not four
   constructions** — they are the *same* multi-variable `×↦+` character (`vp_mul`, `vp_pow`) read four
   ways: as an *image* (polytope), as a *tropical residue* (fan, `max_idem`), as a *count* (Bernstein,
   `countTrue_append`), and as a *closure dual* (moment map, `clo_idempotent`). The character that
   `prime_factorization.md` runs on `ℕ_{>0}`'s prime axes is the character toric geometry runs on a
   polynomial's variable axes — the Newton polytope is literally the picture of its support.

2. **Forcing — the polytope's exponent axes are forced as distinguishable ×-atoms; the fan's idempotency
   is forced as the (max,+) pole.** The Newton polytope is genuinely `n`-dimensional (the axes do not
   collapse) for the *same* reason `vp` is a faithful vector coordinate: ×-atom distinguishability,
   `two_three_unique` (`FoldCriterion:158`) — the variable axes never trade, exactly the multi-variable
   form of `prime_factorization.md`'s "vector readout because atoms are distinguishable". And the fan's
   defining idempotency (tropicalization's `min`/`max` is idempotent: a cone is its own closure) is
   *forced* as `tropical.md`'s idempotent pole `max_idem` (`Iterate213:235`), not an arbitrary feature.

3. **Residue surfaced — the fan is the tropical residue of the variety, and the variety's interior is
   the value-cut residue.** Classical accounts present the fan↔variety correspondence as a structure
   theorem and the toric variety as a new geometric object; the calculus re-sees the **fan as the
   combinatorial residue of the variety under the (max,+) valuation reading** (`tropical.md`'s `q=+1`
   settle) — what the valuation forces (the cone structure) but does not capture (the transcendental
   interior, the analytic solution count = the `Real213`-cut residue reached by none). The toric variety
   is the `q=+1` settle of its own valuation image: the fan reconstructs `X_Σ` because the valuation's
   residue *is* the combinatorial skeleton the variety converges onto.

**THE WELD (the brief's central question):**

| pillar | 213 reading | prior entry | Lean status |
|---|---|---|---|
| Newton polytope `Newt(f)` | the IMAGE of the multi-variable `×↦+` valuation `x^a ↦ a` | `prime_factorization.md` (`vp`) | character **built** (`vp_mul`, `vp_pow`); faithfulness `vp_separation`, axes `two_three_unique`; polytope object conceptual |
| fan ↔ toric variety | tropicalize = the (max,+) valuation residue of `V`, `q=+1` settle | `tropical.md` ((max,+)) | (max,+) idempotent pole **built** (`max_idem`); fan/variety object conceptual |
| Bernstein: mixedVol = #sol | the COUNT reading on the polytope (the `×↦+` volume readout) | `cardinality` / `probability` | count-readout **built** (`countTrue_append`); mixedVolume object conceptual |
| moment map `μ: X_Σ → Newt(f)` | `convex_duality.md`'s `f**=clo` image of the torus action | `convex_duality.md` | `clo` closure **built** (`clo_idempotent`, `biconj_idempotent`); momentMap object conceptual |
| the whole correspondence's tag | `q=+1` converge/closure (hull, fan, moment map settle); interior = value-cut residue | `ResidueTag.lean` | tag **built** (`residue_tag_two_poles`, 55/0) |

So **YES** — toric geometry falls out as the **multi-variable `×↦+` valuation character**: the Newton
polytope IS the image of `prime_factorization.md`'s `vp` made multi-variable (monomial-multiply ↦
exponent-add, `vp_mul`/`vp_pow`, faithful by `vp_separation`, axes-independent by `two_three_unique`);
the fan is `tropical.md`'s (max,+) residue of the variety (`max_idem`); Bernstein's mixed volume is
`cardinality`'s count-readout (`countTrue_append`); and the moment map is `convex_duality.md`'s `f**=clo`
image (`clo_idempotent`/`biconj_idempotent`). Toric geometry **welds `prime_factorization` + `tropical` +
`cardinality` + `convex_duality`** under the multi-variable valuation character, with **no new axis**.

## Note for the technique — does toric geometry force a new construct?

**Verdict: EXTEND by weld — no new primitive.** Every slot toric geometry uses already exists:
- **the `×↦+` valuation character** (`prime_factorization.md`'s `vp_mul`/`vp_pow`) — the monomial
  valuation `x^a ↦ a` is its multi-variable form, the Newton polytope its image;
- **the multi-axis faithful coordinate** (`vp_separation`, `two_three_unique`) — the polytope is
  genuinely `ℤⁿ`-dimensional because the variable axes are distinguishable ×-atoms;
- **the (max,+) idempotent pole** (`tropical.md`'s `max_idem`) — tropicalization, the fan as the
  variety's (max,+) residue;
- **the count reading** (`cardinality`/`probability`'s `countTrue_append`) — Bernstein's mixed volume;
- **the `clo` closure** (`convex_duality.md`/`adjunction.md`'s `clo_idempotent`) — the moment map as the
  Legendre dual of the torus action;
- **the `q=±1` residue tag** (`ResidueTag.lean`) — the `q=+1` settle (hull/fan/moment map) vs the
  value-cut residue (variety interior).

The one sharpening (the structural lesson): **toric geometry is the first entry where the valuation
character (`prime_factorization`) and the tropical (max,+) residue (`tropical`) meet on ONE object** —
the Newton polytope is the character's image, the fan is the (max,+) residue of the same data, and the
two are the *same* reading at two resolutions (the polytope = the full image, the fan = the recession/
`T→0` tropical residue). Previously `vp` and (max,+) were two entries; toric geometry shows the (max,+)
fan is the *tropical residue of the same valuation image* whose full body is the Newton polytope. That
cross-tie — *valuation image ⇄ tropical residue, one reading at two resolutions* — is the lesson,
recorded as an EXTEND, not a new axis.

## Verified Lean anchors (file:line:theorem — all grep/Read-verified; scan tallies from `tools/scan_axioms.py` repo-root this session)

| Leg | Theorem (file : name : line) | Status |
|---|---|---|
| ★ **the `×↦+` valuation character** (the monomial valuation `x^a ↦ a` per axis); the polytope = its image | `Meta/Nat/VpMul.lean : vp_mul : 165` (`vp p (m·n)=vp p m+vp p n`), `vp_pow : 183` (`vp p (aᵏ)=k·vp p a`), `vp_self_pow : 204` | ∅-axiom ✓ (**10 pure / 0 dirty**) |
| **valuation faithfulness** (distinct monomials ↦ distinct exponent vectors; per-reading residue 0) | `Meta/Nat/VpSeparation.lean : vp_separation : 172` (`(∀ p prime, vp p m=vp p n) ⟹ m=n`) | ∅-axiom ✓ (**9 pure / 0 dirty**) |
| **axis-independence** (variable axes never trade; polytope genuinely `ℤⁿ`) | `Meta/Nat/FoldCriterion.lean : two_three_unique : 158` (`2^a=3^b ⟹ a=0 ∧ b=0`) | ∅-axiom ✓ (**8 pure / 0 dirty**) |
| ★ **the (max,+) idempotent pole** (tropicalization, the fan as the variety's (max,+) residue) | `Meta/Nat/Iterate213.lean : max_idem : 235` (`Nat.max a (Nat.max a x)=Nat.max a x`), `max_iter_trivial : 246` ("max builds no tower") | ∅-axiom ✓ (**17 pure / 0 dirty**) |
| **the count reading** (Bernstein's mixed volume = the count-readout of the polytope) | `Lib/Math/Probability/Limit/LLN.lean : countTrue_append : 29` (`countTrue(xs++ys)=countTrue xs+countTrue ys`) | ∅-axiom ✓ (**7 pure / 0 dirty**) |
| **the `clo` closure** (the moment map = `convex_duality.md`'s `f**=clo` image of the torus action) | `Lib/Math/Order/GaloisConnection.lean : clo : 104`, `clo_idempotent : 126`; `Lib/Math/Order/FenchelMoreau.lean : biconj_idempotent : 134`, `closed_iff_fixed : 152` | ∅-axiom ✓ (**15/0** + **18/0**) |
| **the `q=±1` residue tag** (the `q=+1` settle of hull/fan/moment map) | `Lib/Math/Foundations/ResidueTag.lean : residue_tag_two_poles : 228`, `golden_is_converge : 180`, `multiplier_unimodular : 86` | ∅-axiom ✓ (**55 pure / 0 dirty**) |

> Axiom-purity note: `VpMul` (10/0), `VpSeparation` (9/0), `FoldCriterion` (8/0), `Iterate213` (17/0),
> `LLN` (7/0), `GaloisConnection` (15/0), `FenchelMoreau` (18/0), `ResidueTag` (55/0) were each re-run
> through `tools/scan_axioms.py` (full `E213.` prefix) from repo root this session — **every cited
> theorem PURE, 0 dirty across all eight load-bearing modules.**

## Conceptual-only legs / located missing leg (honest — NOT grounded in repo Lean)

- **An actual `ToricVariety` / `NewtonPolytope` / `fan` / `mixedVolume` / `momentMap` / `tropicalize`
  object — ABSENT (confirmed by grep).** Across all `lean/E213`, there is **no** `ToricVariety`,
  `NewtonPolytope`, `Fan`/`fan` (as a geometric object — the only `fan`/`Fan` substring hits are
  unrelated identifiers), `mixedVolume`, `momentMap`/`moment_map`, `tropicalize`, `convexHull`, or
  `polytope`. The only `tropical`/`max-plus` strings in the whole tree are two **comments**:
  `Lib/Math/Foundations/UniverseChain/RawDagSize.lean:12` labels the depth-fold "max-plus algebra" (a
  naming convention on `Raw.fold`, not a semiring or fan), and
  `Lib/Math/Cohomology/HodgeConjecture/Bridge/DiscreteGeometry.lean:111` calls graph shortest-paths "a
  tropical/min-plus structure" (a conceptual remark, not a tropicalization map). And the "Newton" hits
  are all unrelated — `NewtonGregory` (finite differences), `NewtonInequalities` (symmetric means),
  `NewtonFirst`/`NewtonSecond`/`NewtonFirst.lean` (ODE/mechanics) — none a Newton *polytope*. This is
  **the single located missing leg**, exactly like `algebraic_geometry.md`'s missing `Spec`/`Ideal`,
  `tropical.md`'s missing tropicalization map, and `convex_duality.md`'s missing `convexConjugate`: the
  reading whose image *is* the polytope (`vp_mul`), the (max,+) residue *machine* (`max_idem`), the
  count-readout (`countTrue_append`), and the `clo` closure (`clo_idempotent`) are wholly present and
  certified; only the **geometric object bundling them** — the polytope/fan/variety/mixed-volume/
  moment-map — is unwritten.
- **Bernstein's theorem as a stated theorem (mixed volume = solution count)** — absent. The count
  *reading* (`countTrue_append`) and the lattice/exponent structure (`vp`) are grounded; the mixed-volume
  functional on a tuple of polytopes and its equality with the generic solution count are unbuilt (they
  inherit the missing `NewtonPolytope` object plus a `Real213`-cut for the *generic* analytic count —
  the same value-cut residue `algebraic_geometry.md` locates for the variety's interior).
- **The fan↔toric-variety equivalence as a stated correspondence** — absent. Tropicalization as the
  (max,+) valuation residue is *predicted* (the (max,+) idempotent pole `max_idem` is built), but no
  `tropicalize : Variety → Fan` map nor a `Fan → ToricVariety` reconstruction object exists; the
  `q=−1` half (the variety's analytic/transcendental interior, the embedding into `(ℂ*)ⁿ`) is the
  `Real213`-value-cut residue + the un-built ambient-space construction (the same located absence
  `algebraic_geometry.md`/`knots.md` mark).
- **The Legendre/`convexConjugate` transform `f*` the moment map uses** — absent, inherited verbatim from
  `convex_duality.md`'s located missing leg: the `clo` closure machine is built (`clo_idempotent`,
  `biconj_idempotent`, `closed_iff_fixed`), but the `sup_x(p·x − f(x))` Legendre transform object the
  moment map is the gradient of is the named unbuilt instance (needs `Real213`).

## Verdict: PREDICTION (welding prime_factorization + tropical + cardinality + convex_duality) + PARTIAL (the toric/polytope/fan/mixed-volume/moment-map object the missing leg)

Toric geometry **predicts and welds** — it does not break the model and adds no axis. **Grounded
∅-axiom:** the **multi-variable `×↦+` valuation character** the Newton polytope is the image of
(`vp_mul`/`vp_pow`, 10/0), its **faithfulness** (`vp_separation`, 9/0) and **axis-independence**
(`two_three_unique`, 8/0); the **(max,+) idempotent pole** the fan/tropicalization is the residue of
(`max_idem`, 17/0); the **count reading** Bernstein's mixed volume is (`countTrue_append`, 7/0); the
**`clo` closure** the moment map is the dual of (`clo_idempotent` 15/0, `biconj_idempotent`/
`closed_iff_fixed` 18/0); and the **`q=±1` residue tag** (`residue_tag_two_poles`, 55/0). The **single
located missing leg** is an actual `ToricVariety`/`NewtonPolytope`/`fan`/`mixedVolume`/`momentMap`/
`tropicalize` object — **confirmed absent by grep** (two comment-only `max-plus`/`min-plus` hits; all
"Newton" hits unrelated) — located precisely: the valuation character whose image *is* the polytope, the
(max,+) residue the fan *is*, the count the mixed volume *is*, and the closure the moment map *is* are
all present and certified; only the **geometric bundling** of them is unwritten.

> **Open Lean target the calculus names precisely:** define the multi-variable monomial valuation
> `monVal : Monomial n → ℤⁿ` as the per-axis `vp`-vector (`x^a ↦ a`), prove it is the `×↦+` character
> (`monVal (m·m') = monVal m + monVal m'`, by `vp_mul` per axis) and faithful (`vp_separation` per
> axis), then define `NewtonPolytope f := ` the convex hull (= idempotent `clo`-closure, `max_idem`/
> `idem_sup`) of `{ monVal a : c_a ≠ 0 }` and show it is the image of `monVal` on the support. This is
> the one weld that would promote the entry from PREDICTION+PARTIAL to a closed derivation — the Newton
> polytope as the image of the multi-variable `vp` character, parallel to `ConvolveRescaleContraction`
> welding the Banach engine to the CLT, or `CyclotomicFive` realising one concrete Galois correspondence.
> The fan (tropicalization), Bernstein (mixed volume), and the moment map (`clo` dual) then inherit the
> same `Real213`-cut residual the variety interior carries.
