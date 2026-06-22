# Decomposition: topological quantum field theory (TQFT)

*213-decomposition of "a TQFT" — Atiyah's axioms (a symmetric monoidal functor `Z : Cob(n) → Vect`,
`Z(∅)=k`, `Z(M⊔N)=Z(M)⊗Z(N)`, gluing = composition), the 2d classification (2d TQFT ⟺ commutative
Frobenius algebra), the pair-of-pants, and state-sum/lattice TQFTs. Per `../README.md` (model v7.1) and
`../SYNTHESIS.md` (the two invariants + the 2-category of readings + the character arrow). A **fresh**
field, but one the corpus has approached from three sides at once: the character arrow's
product-preservation (`category_theory.md`, `representation.md`), the comultiplication/Frobenius
convolution structure (`hopf_algebras.md` — just done), and the 2-cell / functor layer (`two_cells.md`).*

The thesis under test: **a TQFT is the calculus's character arrow promoted to a monoidal functor on
cobordisms.** The character arrow (`×↦·`: `det2_mul`, `legendre_mul`, `psign_mulPerm_hom`) is a
*homomorphism* — a construction-preserving reading whose readout is a number, preserving products. A
TQFT `Z` is the SAME structure one categorical level up: a monoidal functor from cobordisms to `Vect`,
with `Z(M⊔N)=Z(M)⊗Z(N)` — the SAME product-preservation `⊔↦⊗` as the character's `×↦·`, valued in
vector spaces instead of numbers. Gluing of cobordisms = composition (the fold `raw_initial`, the
2-category `refines_trans`/`view_factors_through_morphism`). The boundary `∂` of a cobordism =
homology's `∂` (the `q=±1` orientation bit, `dsq_zero_universal_delta4`). The 2d classification = the
character landing in a **Frobenius structure** = `hopf_algebras.md`'s convolution (`m` + `Δ`, the slash
read both ways); the pair-of-pants (multiplication) + its dual (comultiplication) = `conv` read in both
directions. State-sum TQFTs = the fold-to-normal-form (partition function = a fold over a triangulation).

## The decomposition (C / Reading / Residue)

- **Construction `C`** — *nothing new*. A cobordism is a directed gluing of distinguished pieces: the
  disjoint union `⊔` is the slash (`append`/`combine`), the gluing along a boundary is **composition of
  folds** (`raw_initial`: `Lens.view = Raw.fold`, the unique arrow out of the initial object; vertical
  composition = `refines_trans`). Cob(n) is therefore a category whose 1-cells *are* the calculus's
  reading-arrows: composition = gluing, identity = the cylinder, `⊔` = the monoidal `⊗` on objects. The
  `∂` of a cobordism (its two boundary `(n−1)`-manifolds, in vs out) is the **direction/swap bit `q=±1`**
  (the in/out orientation, `dsq_zero_universal_delta4`'s pairwise sign-cancellation) read on the height
  axis — exactly `homology.md`'s boundary operator run one categorical level up (objects, not chains).

- **Reading `L` — the monoidal functor `Z = ⊔↦⊗`, the character arrow promoted.** `Z` assigns a vector
  space to each `(n−1)`-manifold and a linear map to each cobordism, and its defining law is
  **product-preservation**: `Z(M⊔N)=Z(M)⊗Z(N)`, `Z(∅)=k`, `Z(glue)=Z∘Z` (functoriality on
  composition). This is the calculus's character arrow `m(αβ)=m(α)·m(β)`, `m(unit)=1`, with three slots
  swapped and nothing added:
  - the *operand* product `×` → the disjoint-union `⊔`;
  - the *readout* product `·` → the tensor `⊗`;
  - the *readout codomain* (a number) → a vector space.
  The character is the degenerate `d=1` case (`Z(pt)=k`, `⊗=·`); `Z` is its `Vect`-valued, functorial
  extension — the same arrow `representation.md` already saw running through det/character (the `×↦·`
  homomorphism on the Aut-family). Functoriality `Z(g∘f)=Z(g)∘Z(f)` (gluing = composition) is the
  naturality/2-cell layer `view_factors_through_morphism` (`M.view = h∘L.view`) read horizontally.

- **Residue — the Frobenius/antipode structure, `q=±1`, AND the absent cobordism category.** What the
  monoidal functor *forces but the bare character does not capture* is a **co-operation**: the
  pair-of-pants (a cobordism `S¹⊔S¹→S¹`, the **multiplication** `m`) has a **dual** (the co-pair-of-pants
  `S¹→S¹⊔S¹`, the **comultiplication** `Δ`), because Cob is *self-dual* (turn a cobordism upside down).
  This is precisely `hopf_algebras.md`'s residue: the slash read in **both directions at once**
  (`m`+`Δ`), `m=conv` forward, `Δ=natSplits` backward, with the Frobenius relation = the convolution
  semiring laws (`conv_assoc`/`conv_comm`/`conv_delta_left`/`conv_unit_comm_assoc`). The antipode-flavoured
  unimodular bit (in/out orientation reversal) is the `q=−1` tag (`ResidueTag.multiplier_unimodular`).
  The genuinely-absent part is the **named cobordism category itself** — there is no `Cob(n)`, no ambient
  `n`-manifold, no isotopy quotient on the bordisms (the `two_cells.md`/`knots.md` Side-B isotopy/colimit
  break, recurring verbatim).

## Re-seeing (⟨C | L⟩) — term by term

```
   a TQFT  Z : Cob(n) → Vect   =  ⟨ C (gluing of distinguished pieces; ∂ = q=±1 in/out bit)
                                     | the monoidal functor Z = the character arrow ⊔↦⊗ ⟩
                                     ⊕ Frobenius residue (m + Δ, hopf_algebras' conv both ways), q=±1

   Z(M ⊔ N) = Z(M) ⊗ Z(N)     =  the character's product-preservation  (det2_mul / legendre_mul / vp_mul: ×↦·, one level up to ⊔↦⊗)
   Z(∅) = k                    =  the character's unit law m(unit)=1     (conv_delta_left: δ⋆f=f; the monoidal unit)
   Z(glue) = Z ∘ Z            =  gluing = composition = the fold        (raw_initial: view=fold; refines_trans; view_factors_through_morphism)
   the cobordism = a 1-cell    =  a reading-arrow                         (raw_initial: arrows out of the initial object)
   ∂ of a cobordism (in/out)   =  the q=±1 direction/orientation bit      (dsq_zero_universal_delta4: pairwise sign-cancellation)
   the cylinder (identity)     =  the identity arrow                      (refines_refl)
   2d TQFT ⟺ comm. Frobenius   =  the character landing in a Frobenius structure   (hopf_algebras: conv_unit_comm_assoc — comm. monoid + counit)
   pair-of-pants (mult. m)     =  the slash read FORWARD = conv           (conv_assoc / conv_comm — the fold, ×↦· on mass: mass_conv)
   co-pair-of-pants (comult Δ) =  the slash read BACKWARD = co-fold       (natSplits/splits; conv_comm the cut-reversal swap; hopf_algebras)
   Frobenius relation (m,Δ assoc)=  the conv semiring law                 (conv_unit_comm_assoc; coassoc = conv_assoc dual)
   the counit ε / unit η       =  the convolution unit δ / counit         (conv_delta_left; mu_conv_one: S⋆id=ε on the ×-cut)
   state-sum  Z(M)=Σ_triangulations Π = a fold over a triangulation       (raw_initial: Z = the catamorphism Raw.fold; ⊗ = Σ-glue)
   the monoidal product itself (BUILT, GRA) = additive grade over ⊗       (GRA.Monoidal.product; product_NT_NT_grade: grade(M⊗N)=grade M + grade N)
```

## Revelation

**Collapse + forcing + one located break — and one surprise: a *built* monoidal product with the
character law.**

**Collapse (the spine):** *a TQFT is the character arrow `⊔↦⊗` — product-preservation — promoted from a
number-readout to a `Vect`-valued monoidal functor on cobordisms, with gluing = the fold-composition.*
The corpus's single most-reused object is the character homomorphism `×↦·` (`det2_mul`, `legendre_mul`,
`psign_mulPerm_hom`, `vp_mul` — `SYNTHESIS.md` Invariant A, proven the *same* arrow across seven+ fields).
Atiyah's `Z(M⊔N)=Z(M)⊗Z(N)` is *that arrow's defining law* with the operand product = `⊔`, the readout
product = `⊗`, the codomain = `Vect`. So TQFT does not add a primitive: it is Invariant A at the
2-categorical level, with gluing = composition (`raw_initial`'s `view=fold` + the 2-category
`refines_trans`/`view_factors_through_morphism`) and `∂` = the `q=±1` in/out orientation bit
(`dsq_zero_universal_delta4`, `homology.md`'s boundary read on objects).

**Forcing:** the comultiplication `Δ` (co-pair-of-pants) is *forced*, exactly as in `hopf_algebras.md`:
Cob is **self-dual** (flip a cobordism), so any multiplication `m` (pair-of-pants) has a dual `Δ`. This
is the slash read in both directions — `m=conv` (forward, `conv_assoc`/`conv_comm`), `Δ=natSplits`
(backward), bridged by the convolution semiring (`conv_unit_comm_assoc`). The **2d classification
(2d TQFT ⟺ commutative Frobenius algebra)** is therefore *predicted*: a 2d TQFT is exactly the character
landing in `hopf_algebras.md`'s commutative-convolution Frobenius structure — `m` commutative
(`conv_comm`), associative (`conv_assoc`), with unit `δ`/counit (`conv_delta_left`), and the
Frobenius/antipode compatibility being the same `mu_conv_one` (`S⋆id=ε`) the Hopf note pinned. The
pair-of-pants + co-pair-of-pants are `conv` read both ways; the cap/cup (the disk = `Z(∅→S¹)`/`Z(S¹→∅)`)
are the unit/counit. **State-sum/lattice TQFTs** are forced as the **fold-to-normal-form**: the partition
function `Z(M)=Σ_triangulations Π(local weights)` is the catamorphism `Raw.fold` (`raw_initial`,
triangulation-independence = the uniqueness of the arrow out of the initial object,
`dhom_unique_pointwise`), with `Σ`/`Π` = the `⊗`/glue of the monoidal structure.

**★ The surprise (a genuine in-repo grounding, beyond the thesis):** the repo **already builds a
monoidal product carrying the character law** — `GRA/Monoidal.lean` (13/0 PURE) ships
`product : GRAModel → GRAModel → GRAModel` with a **monoidal unit** `trivial23` (the one-point model =
`Z(∅)=k`'s shadow), left/right unit homs (`leftUnitHom`/`rightUnitHom` = the unit coherence), a **swap
iso** `productSwapIso` with `productSwapIso_involutive` (the **symmetric**-monoidal braiding, `q=±1`
involution), and the load-bearing law **`productGrade(M₁⊗M₂) = grade M₁ + grade M₂`**
(`product_NT_NT_grade`: `grade(M⊗N)=grade M + grade N`). That is the TQFT shape `Z(M⊔N)=Z(M)⊗Z(N)`
read at the *grade* (number) readout — the `×↦+` character (`SYNTHESIS.md` Invariant A, additive twin)
made into a *monoidal-product-preservation* theorem, ∅-axiom. It is not on cobordisms/`Vect`, but it is
the first **built** instance in the corpus of "a monoidal product whose readout is the additive
character" — the exact algebraic skeleton Atiyah's `⊔↦⊗` axiom asks for.

**The located break (honest — Side B of `two_cells.md`/`knots.md`, recurring verbatim):** the **named
cobordism category `Cob(n)`** — the ambient `n`-manifold, the bordisms as objects, and the
**isotopy/diffeomorphism quotient** on them — is genuinely ABSENT, and is the *same* missing primitive
`knots.md` and `fundamental_group.md` hit: an ambient-deformation/colimit quotient no reading's kernel or
self-application generates. The *algebraic* core of TQFT (the character arrow `⊔↦⊗`, the Frobenius
`m`+`Δ` convolution, the fold-as-state-sum, the symmetric-monoidal product with `Z(∅)=k`) is all built or
proof-shaped; the *geometric* carrier (cobordisms-mod-isotopy in `Vect`) sits in the un-built
colimit/`q=−1` corner plus the absent ambient-space construction.

## VALIDATE verdict — **EXTEND + PARTIAL** (one located break: the named cobordism category / isotopy quotient)

No new primitive. A TQFT is `SYNTHESIS.md` Invariant A (the character arrow `×↦·`/`×↦+`) promoted to a
symmetric monoidal functor `⊔↦⊗`, with gluing = the fold-composition (`raw_initial` + the 2-category),
`∂` = the `q=±1` orientation bit (`homology.md`), and the 2d-classification's Frobenius structure =
`hopf_algebras.md`'s convolution (`m`+`Δ`, the slash both ways). Three re-seeing rows are now pinned
beyond what `category_theory.md`/`representation.md`/`hopf_algebras.md` recorded:
1. **`Z(M⊔N)=Z(M)⊗Z(N)` = the character arrow one categorical level up** (`⊔↦⊗` is `×↦·` with operand,
   readout, and codomain slots swapped) — and it is **grounded** by a *built* symmetric-monoidal product
   with the additive-character law (`GRA.Monoidal.product`, `product_NT_NT_grade`, `productSwapIso`,
   13/0 + 23/0). **EXTEND.**
2. **2d TQFT ⟺ commutative Frobenius algebra = the character landing in `hopf_algebras.md`'s convolution**
   (pair-of-pants `m`=`conv` forward, co-pair-of-pants `Δ`=`natSplits` backward, Frobenius law =
   `conv_unit_comm_assoc`, counit/antipode = `mu_conv_one`). **EXTEND** (inherits `hopf_algebras.md`'s
   own PARTIAL: the bialgebra/Frobenius compatibility-as-one-law is the open F1 leg).
3. **The named cobordism category / isotopy quotient is ABSENT** — Side B of the
   `knots.md`/`two_cells.md` break, recurring verbatim. **PARTIAL / located break.**

So: a TQFT is the character arrow as a symmetric monoidal functor on cobordisms — fully native and
Lean-grounded on the algebraic side (character `⊔↦⊗`, monoidal product, Frobenius `m`+`Δ`, state-sum =
fold) **except** the geometric cobordism-category carrier with its isotopy quotient, which is the genuine
open primitive shared with knots/π₁. A clean EXTEND with one honestly-located PARTIAL.

## Verified Lean anchors (file:line:theorem — all grep + `tools/scan_axioms.py`-scanned this session)

| TQFT datum | Theorem/def (file:line) | Purity (module tally) |
|---|---|---|
| `Z(M⊔N)=Z(M)⊗Z(N)` = `×↦·` character (mult.) | `Lib/Math/NumberSystems/Real213/Markov/SternBrocotMarkov.lean:104` `det2_mul` | **130 PURE / 0 DIRTY** ✓ |
| character `×↦·`, Legendre face | `Lib/Math/NumberTheory/ModArith/LegendreMultiplicative.lean:77` `legendre_mul` | **5 PURE / 0 DIRTY** ✓ |
| character `×↦·`, permutation-sign hom | `Lib/Math/NumberTheory/ModArith/Zolotarev.lean:133` `psign_mulPerm_hom` | **11 PURE / 0 DIRTY** ✓ |
| ★ monoidal product (BUILT), w/ unit `trivial23` | `Lib/Math/Algebra/GRA/Monoidal.lean:129` `product` (def), `:58` `trivial23`, `:80` `productGrade` | **13 PURE / 0 DIRTY** ✓ |
| ★ `Z(M⊗N)` grade = `grade M + grade N` (the `⊔↦⊗`/`Z(∅)=k` law) | `Lib/Math/Algebra/GRA/Monoidal.lean:182` `product_NT_NT_grade` | PURE (in the 13) ✓ |
| ★ monoidal unit coherence (`Z(∅)=k`) | `Lib/Math/Algebra/GRA/Monoidal.lean:155` `leftUnitHom`, `:167` `rightUnitHom` | PURE (in the 13) ✓ |
| ★ symmetric-monoidal braiding (`q=±1` swap) | `Lib/Math/Algebra/GRA/HasDistinguishing213.lean:105` `productSwapIso`, `:122` `productSwapIso_involutive` | **23 PURE / 0 DIRTY** ✓ |
| gluing = composition = the fold (`view=fold`) | `Lens/Foundations/SemanticAtom.lean:412` `raw_initial` | PURE (theorem `[PURE]`; module 11/23 mixed) ✓ |
| functoriality / naturality (gluing) | `Lens/Compose/Morphism.lean:37` `view_factors_through_morphism`, `:29` `IsLensMorphism`, `:60` `refines_of_morphism` | **3 PURE / 0 DIRTY** ✓ |
| identity cobordism (cylinder) / vertical ∘ | `Lens/Lattice/Preorder.lean:15` `refines_refl`, `:19` `refines_trans` | **3 PURE / 0 DIRTY** ✓ |
| invertible 2-cell (cobordism iso) | `Lens/Unified.lean:42` `LensIso` (def), `:64` `lensIso_iff_kernel_eq` | PURE ✓ |
| `∂` of cobordism = `q=±1` in/out orientation | `Lib/Math/Cohomology/Delta/V4Capstone.lean:41` `dsq_zero_universal_delta4` | **5 PURE / 0 DIRTY** ✓ |
| Frobenius mult `m` = pair-of-pants (slash forward) | `Meta/Nat/Convolution213.lean:257` `conv_assoc`, `:156` `conv_comm` | **49 PURE / 0 DIRTY** ✓ |
| Frobenius unit/counit `η`/`ε` (cap/cup) | `Meta/Nat/Convolution213.lean:285` `conv_delta_left`, `:313` `conv_unit_comm_assoc` | PURE (in the 49) ✓ |
| Frobenius `m`=`×↦·` on mass (`Z(M⊔N)=⊗`) | `Lib/Math/Probability/Limit/ConvolveProfile.lean:190` `mass_conv`, `:239` `momentNum_conv` | **20 PURE / 0 DIRTY** ✓ |
| antipode/Frobenius axiom `S⋆id=ε` (×-cut) | `Lib/Math/NumberTheory/DirichletIdentities.lean:50` `mu_conv_one` | **20 PURE / 0 DIRTY** ✓ |
| `∂`/orientation = `q=±1` unimodular bit (tag) | `Lib/Math/Foundations/ResidueTag.lean` `multiplier_unimodular`, `residue_tag_two_poles` | **55 PURE / 0 DIRTY** ✓ |

(All tallies from `python3 tools/scan_axioms.py <module>` run from repo root this session; each cited
theorem scanned `[PURE]`. `raw_initial`'s module `SemanticAtom` is mixed 11/23, but `raw_initial` itself
scans `[PURE]` — the DIRTY entries are the classical-`Prop` connectives `topos.md` flags.)

## Dropped / flagged (honest)

- **Named `TQFT` / `Cob(n)` / `cobordism` / `FrobeniusAlgebra` / `monoidalFunctor` / `Atiyah` /
  `pair_of_pants` / `state_sum` — ABSENT (grep-confirmed).** `grep -rniE
  "TQFT|cobordism|atiyah|frobenius algebra|frobenius_algebra|pair.?of.?pants|state.?sum|monoidalFunctor"`
  over `lean/E213/` finds **none of the TQFT-specific objects**. The "Frobenius algebraic properties"
  hits (`ModArith/FP2SqrtD.lean:193`, `FP2Sqrt5.lean:109`) are the *number-theoretic* Frobenius (the
  per-prime ring endomorphism `x↦xᵖ`), **not** a Frobenius algebra — false-friend, flagged. So the
  predicted-not-built named TQFT bundles are confirmed absent; the **structure** (`⊔↦⊗` character,
  monoidal product + unit + braiding, Frobenius `m`+`Δ` convolution, state-sum-as-fold) is all built
  unnamed.
- **A `monoidal` object DOES exist (`GRA/Monoidal.lean`) but is NOT a cobordism/`Vect` monoidal category**
  — it is the monoidal product on the (2,3)-GRA category. Cited *only* as the in-repo grounding for the
  abstract "symmetric monoidal product whose readout is the additive character" skeleton, NOT as a
  cobordism category or a TQFT functor. Flagged so the cite is read as the skeleton, not the field object.
- **The ambient `n`-manifold / cobordism / isotopy quotient — ABSENT (Side B break).** Per
  `two_cells.md` Shape 3 and `knots.md`/`fundamental_group.md`: a quotient by an ambient-isotopy /
  diffeomorphism relation that no reading's kernel or self-application generates, in the un-built
  colimit/`q=−1` corner plus an absent ambient-space construction. The genuine open primitive; flagged
  as the located break, not asserted.
- **`Vect` as the target category** — the corpus has number-readouts and `Mat2`, but no general
  finite-dimensional `VectorSpace`/`⊗` object (the `representation.md` `d>1` / Hilbert-space ceiling,
  shared with `quantum_mechanics.md`/`operator_algebras.md`). `Z` valued in `Vect` is therefore grounded
  only at the `d=1` (number-readout) and the `GRA.product` algebraic-grade level; the genuine
  vector-space-valued functor is the `Real213`/`d>1` residual. Flagged.
- **The bialgebra/Frobenius compatibility-as-one-law** — inherited from `hopf_algebras.md`'s open F1
  (the `Δ_+⇄Δ_×` distributive interlock). The `m`/`Δ`/`η`/`ε`/`S` legs are PURE; the single law fusing
  them into a Frobenius/bialgebra object is the same unwritten leg. Flagged, not cited as built.

### Buildable witness (named)

The natural ∅-axiom closure of this note, beyond `hopf_algebras.md`'s F1: state and prove that the
**`GRA.Monoidal.product` is a symmetric monoidal functor's value at the grade readout** — i.e. promote
`product_NT_NT_grade` (`grade(M⊗N)=grade M + grade N`) + `productSwapIso_involutive` (the symmetric
braiding) + `leftUnitHom`/`rightUnitHom` (the unit) into a single bundled `IsMonoidalGradeFunctor`
statement, exhibiting the **one** object in the corpus that satisfies Atiyah's `Z(M⊔N)=Z(M)⊗Z(N)` +
`Z(∅)=k` + symmetry on a *built* monoidal category. That would promote row 1 from "grounded by pieces"
to a packaged EXTEND. The cobordism carrier (Side B isotopy quotient) stays the located break — a
classical-undecidability-grade boundary, not a missing 213 primitive (per `two_cells.md` Shape 3 /
`colimit_quotient_synthesis.md`).

## Cross-frame

`category_theory.md` (the character arrow + 213-as-CT-shaped; `raw_initial` the catamorphism/state-sum);
`representation.md` (the `×↦·` character as a functor, the `det`/`tr` split the `Vect`-valued ceiling);
`hopf_algebras.md` (the Frobenius `m`+`Δ` convolution = the slash both ways, the 2d-classification's
algebra; inherits its F1 PARTIAL); `two_cells.md` (the 2-category of readings = functoriality/gluing;
Shape 3 isotopy = the cobordism-carrier break); `homology.md` (`∂` = the `q=±1` boundary bit,
`dsq_zero_universal_delta4`); `knots.md`/`fundamental_group.md` (the recurring ambient-isotopy/colimit
quotient = the cobordism category's missing primitive); `SYNTHESIS.md` (Invariant A the character arrow,
Invariant B the `q=±1` tag — TQFT = Invariant A promoted, residue tagged by Invariant B).
