# Decomposition: class field theory / Artin reciprocity

*213-decomposition of "class field theory" — the Artin map (ideles/ray-class group → `Gal(K^{ab}/K)`),
the Artin reciprocity law (the Artin map is well-defined, surjective, kernel = a norm group), the
Frobenius element `Frob_p`, the Kronecker–Weber theorem (every abelian extension of `ℚ` is contained in
a cyclotomic field), with quadratic reciprocity as the order-2 special case. Per `../README.md` (model
v7.1) and `SYNTHESIS.md`'s two invariants. This is the **deepest number-theory consolidation attempt**:
does CFT add a new primitive, or is it `quadratic_reciprocity.md`'s `×↦·` character arrow pushed to its
maximal abelian extent?*

The thesis under test (from the task): **CFT is the calculus's character arrow `×↦·` pushed to its
maximal abelian extent.** Specifically —
1. the **Artin map** (ideles → `Gal(K^{ab}/K)`) IS `quadratic_reciprocity.md`'s `×↦·` character
   (`legendre_mul`, `psign_mulPerm_hom`) generalized from the order-2 quadratic character to *all*
   abelian characters: the construction-preserving reading from the multiplicative idele structure to
   the abelianized Galois group;
2. **Artin reciprocity** (well-defined + surjective, kernel = norm group) = the SAME multiplicativity
   that makes QR work (`floor_sum_rectangle` / `zolotarev_mu`), pushed from order 2 to all orders;
3. the **Frobenius element** `Frob_p` = the `q=±1` / orientation reading per prime — the *local*
   character (the per-prime conjugation/sign);
4. **Kronecker–Weber** (abelian/ℚ = cyclotomic) = the statement that the maximal abelian character is
   the cyclotomic/root-of-unity character — the `RootOfUnityOrthogonality`/`CyclicCharacterOrthogonality`
   corpus the calculus already orthogonality-grounds at all orders mod `p`.

**Headline, stated up front so the rest is honest.** Unlike `quadratic_reciprocity.md` (where the full
law is a strict ∅-axiom theorem), here the picture **splits sharply**. The *character spine* CFT is built
from is overwhelmingly present and PURE — the multiplicative quadratic character (`legendre_mul`), the
permutation-sign homomorphism (`psign_mulPerm_hom`), QR itself (`quadratic_reciprocity`), the cyclotomic
`C₄` Galois group (`galois_group_is_C4`), the per-prime quadratic Frobenius `a+b√D ↦ a−b√D`
(`fp2dFrob_mul`/`zpsd_frob`), and — decisively for Kronecker–Weber — **χ-orthogonality at all orders mod
`p`** (`cyclic_orthogonality_modp`). But the *named CFT objects* — `ArtinMap`, `idele`/`adele`,
`RayClassGroup`, the Galois `Frob_p` *as a Frobenius element of an extension*, `KroneckerWeber` — are
**entirely ABSENT** (grep-confirmed: zero hits). So this is a **PREDICTION + located BREAK**: the calculus
predicts CFT's form precisely (the abelian-maximal `×↦·` character, the local-Frobenius `q=±1` tag, the
cyclotomic-character maximality) and grounds the order-2 case and every orthogonality ingredient, but the
idele/Artin-map/Kronecker–Weber *bundle* is unbuilt — the same `knots.md`/`modular_forms.md`-shaped edge:
the structure named, the global object absent.

## The decomposition (C / Reading / Residue)

- **Construction `C` — the multiplicative idele/ray-class structure on one side, the abelianized
  distinguishing-tower on the other.** CFT relates two constructions: the *arithmetic* side
  (`(ℤ/N)^×`, ray-class groups, the idele class group `C_K = A_K^×/K^×`) and the *Galois* side (the
  abelian extension `K^{ab}/K`, a tower of nested distinguishings, `galois_correspondence.md`'s `C` with
  the Aut-family `Gal(K^{ab}/K)` *abelianized*). The arithmetic side is `quadratic_reciprocity.md`'s
  multiplicative orbit `(ℤ/p)^×` (`fourier.md`'s cyclic `C = ⟨g⟩`) generalized: a *product* of all the
  local multiplicative structures, one per prime/place. In the repo the arithmetic `C` is fully present
  (`(ℤ/5)^×` in `CyclotomicFive`, the local `F_p[√D]`/`ℤ_p[√D]` quadratic extensions in `FP2SqrtD`/
  `ZpSqrtD`); the *idele/adele product over all places* is the absent global object.

- **Reading `L_Artin` — the maximal-abelian `×↦·` character.** The Artin map is the
  construction-preserving reading from the multiplicative arithmetic structure to the abelianized Galois
  group: `c ↦ (the automorphism that acts on K^{ab} by c)`. This is *literally* `parity.md`'s `L₂` /
  `quadratic_reciprocity.md`'s order-2 character (`legendre_mul`: `(ab/p)=(a/p)(b/p)`, `psign_mulPerm_hom`:
  the sign is multiplicative) **with the codomain widened from `{±1}` to the full abelianized
  `Gal`**. The order-2 character `a ↦ (a/p) ∈ {±1}` is the abelian extension `ℚ(√d)/ℚ`; the Artin map is
  the *same arrow* reading into `Gal(K^{ab}/K)` instead of `{±1}`. The **Frobenius element** `Frob_p` is
  `L_Artin` read *locally at one prime* — the per-prime image, the local character. For a quadratic
  extension that local reading is exactly the conjugation `a+b√D ↦ a−b√D` (`fp2dFrob`/`zpsd_frob`), the
  `q=−1` swap bit (`integers.md`'s sign, `galois_correspondence.md`'s conjugation reading).

- **Residue — the `q=±1` tag, two faces.**
  - **Local face (`Frob_p`, the per-prime orientation).** Each prime contributes one orientation bit
    read by the local character: split/inert/ramified is the per-prime `q=±1`/degenerate reading. For
    the quadratic case this is the Frobenius conjugation's sign (`fp2dFrob` is an involution,
    `fp2dFrob_involution`, the `q=−1` antisymmetry pole — the same swap as `galois_correspondence.md`'s
    quadratic conjugation and `lie_theory.md`'s `bracket_antisymm`).
  - **Global face (Artin reciprocity = the character's kernel, `q=+1` converge/closure).** Artin
    reciprocity says `L_Artin` is well-defined and surjective with kernel a *norm group* — i.e. the
    abelian extensions are in order-reversing bijection with the norm-group lattice. This is
    `galois_correspondence.md`'s `Fix ⊣ Inv` closure (`clo_idempotent`, the `q=+1` converge pole)
    *specialized to abelian extensions*: the norm group is the closed element, the residue collapses on
    closed subgroups ↔ abelian subextensions. The **Real213-cut residue** here is the *infinite*
    idele/adele completion (the product over all places, reached by no finite truncation) — the same
    transcendental-cut residue `padic.md`/`modular_forms.md` assign to every completion-over-all-places.

## Re-seeing — `⟨C | L_Artin⟩ ⊕ Residue`

```
   abelian extension K^{ab}/K   =  ⟨ K | adjoin roots, abelianized tower ⟩       (galois_correspondence.md's C)
   Gal(K^{ab}/K)                =  the ABELIANIZED Aut-family                      (groups.md / galois_corr.md)
   idele class group C_K        =  the multiplicative arithmetic C over all places (PRODUCT of local (ℤ/p)^×) [GLOBAL OBJECT ABSENT]
   Artin map  c ↦ (c, K^{ab}/K) =  the ×↦· character into Gal^{ab}                 (legendre_mul / psign_mulPerm_hom, codomain widened)
   Artin reciprocity            =  L_Artin well-defined + surjective, ker = norm group
                                 =  galois_corr.md's Fix⊣Inv closure on abelian subexts (clo_idempotent, q=+1)  [GLOBAL THM ABSENT]
   Frobenius element Frob_p     =  L_Artin read LOCALLY at p = the per-prime orientation/character
                                 =  quadratic case: conjugation a+b√D↦a−b√D (q=−1 swap)  (fp2dFrob / zpsd_frob)
   ── QUADRATIC RECIPROCITY = the order-2 special case (BUILT, the anchor) ──────────
   Legendre symbol (a/p)        =  L_Artin into {±1} for ℚ(√d)/ℚ                   (zolotarev_mu, legendre_mul)
   QR  (q/p)(p/q)=(−1)^…         =  the order-2 Artin reciprocity, one grid m·n      (quadratic_reciprocity)  [BUILT, 11 PURE]
   ── KRONECKER–WEBER = maximal abelian char IS cyclotomic ──────────────────────────
   abelian/ℚ ⊆ cyclotomic       =  the maximal abelian character = the root-of-unity character
   the root-of-unity character  =  Σ_{k<n} ζ^k ≡ 0 at ALL orders mod p             (cyclic_orthogonality_modp)  [INGREDIENT BUILT]
   Gal(ℚ(ζ₅)/ℚ) ≅ C₄            =  a concrete abelian (cyclotomic) Galois group     (galois_group_is_C4)  [BUILT, 4 PURE]
   KroneckerWeber theorem       =  every abelian/ℚ embeds in some ℚ(ζ_N)            [GLOBAL THM ABSENT]
```

Set side by side: **CFT is `quadratic_reciprocity.md`'s order-2 character read into the full abelianized
Galois group instead of `{±1}`.** The classical machinery splits cleanly into a part the repo builds
heavily (the *character spine* — Legendre/QR, the cyclotomic abelian group, the local quadratic
Frobenius, χ-orthogonality at all orders) and the part it does not (the *global idele/Artin-map/Kronecker–
Weber bundle*):

| classical CFT object | the calculus's reading | repo status |
|---|---|---|
| Artin map (ideles → `Gal^{ab}`) | the `×↦·` character, codomain widened from `{±1}` to `Gal^{ab}` | **OBJECT ABSENT**; order-2 instance BUILT (`zolotarev_mu`, `legendre_mul`) |
| Artin reciprocity (ker = norm group) | `galois_corr.md`'s `Fix⊣Inv` closure on abelian subexts, `q=+1` | **GLOBAL THM ABSENT**; QR (order-2 case) BUILT (`quadratic_reciprocity`, 11 PURE) |
| Frobenius element `Frob_p` | `L_Artin` read locally = per-prime `q=±1` orientation | **Galois `Frob_p` ABSENT**; quadratic conjugation BUILT (`fp2dFrob_mul`, `zpsd_frob`) |
| Kronecker–Weber (abelian/ℚ = cyclotomic) | maximal abelian char = the root-of-unity char | **THM ABSENT**; the χ = `Σζ^k≡0` and `C₄` ingredients BUILT (`cyclic_orthogonality_modp`, `galois_group_is_C4`) |
| idele/adele class group `C_K` | the multiplicative arithmetic `C` over all places | **GLOBAL OBJECT ABSENT**; local `(ℤ/p)^×`, `F_p[√D]`, `ℤ_p[√D]` BUILT |

## LEVERAGE — does CFT fall out as the maximal-abelian character? **PREDICTION + located BREAK.**

**Net verdict: PREDICTION + PARTIAL/BREAK.** The calculus predicts CFT's form exactly — CFT = the
`×↦·` character pushed to the maximal abelian extent, with the local Frobenius the per-prime `q=±1`
reading and Kronecker–Weber the cyclotomic-character maximality. The *order-2 special case* (QR) and
*every character ingredient* (the multiplicative quadratic character, the cyclotomic abelian group, the
local Frobenius homomorphism, χ-orthogonality at all orders) are built ∅-axiom; the *global Artin-map /
reciprocity / Kronecker–Weber bundle* is genuinely absent. The four hypotheses, honestly graded:

### Hyp 1 — Artin map = the `×↦·` character, codomain widened. **PREDICTION; order-2 instance BUILT, global map ABSENT.**
The calculus predicts the Artin map is `quadratic_reciprocity.md`'s order-2 character with the codomain
`{±1}` replaced by the abelianized Galois group. The *order-2 instance* is exactly `zolotarev_mu`
(`psign σ_a = (a/p)`: the Legendre symbol IS the permutation-sign reading) and `legendre_mul`
(`(ab/p)=(a/p)(b/p)`: the character is multiplicative — the `×↦·` arrow), both PURE. The widening to a
general abelian codomain is precisely "the same homomorphism reading into a larger cyclic/abelian group",
which the repo grounds at the *character-sum* level (orthogonality at all orders, Hyp 4) but **not as a
named `ArtinMap` object**: grep `ArtinMap`/`artin_map`/`idele`/`adele`/`RayClass` returns zero. So the
arrow is the SAME arrow `quadratic_reciprocity.md` runs (the deepest consolidation datum: the Artin map
is QR's character, not a new primitive), the order-2 case is machine-checked, and the global map is the
located break. PARTIAL.

### Hyp 2 — Artin reciprocity = the same multiplicativity, pushed to all orders. **PREDICTION; QR (order-2) BUILT, the all-order law ABSENT.**
The calculus predicts Artin reciprocity (well-defined + surjective, kernel = norm group) is the SAME
multiplicativity that makes QR work, generalized from order 2 to all abelian characters. The order-2 law
is `quadratic_reciprocity.md`'s fully-built `quadratic_reciprocity` (11 PURE) — the Eisenstein
lattice-double-count `floor_sum_rectangle` (`Σ⌊qx/p⌋+Σ⌊py/q⌋=m·n`), with the reciprocity sign the `q=±1`
parity residue of the grid count `m·n`. Pushing this to all orders is *exactly* the move
`galois_correspondence.md` already made for the closure side: Artin reciprocity is `Fix ⊣ Inv` restricted
to *abelian* subextensions, the kernel (norm group) the `clo`-closed element (`clo_idempotent`, 15/0
PURE, the `q=+1` converge pole). The repo has the closure machine and the order-2 law; **the general
abelian reciprocity law is not stated as a theorem** — it would need the idele norm group, an absent
object. PREDICTION, with the order-2 case Lean-closed and the general law the break.

### Hyp 3 — Frobenius element = the per-prime `q=±1` local character. **PREDICTION; quadratic Frobenius BUILT (a genuine grounding), Galois `Frob_p` ABSENT.**
The calculus predicts `Frob_p` is `L_Artin` read locally at one prime — the per-prime orientation/sign,
the local character. The **quadratic local Frobenius is built ∅-axiom and is a ring homomorphism**:
`FP2SqrtD.fp2dFrob` (`a+b√D ↦ a−b√D`) with `fp2dFrob_mul` (multiplicative, the `×↦·` arrow locally),
`fp2dFrob_add` (additive), `fp2dFrob_involution` (`σ²=id`, the `q=−1` order-2 swap), and the `ℤ_p`-lift
`ZpSqrtD.zpsd_frob` with the same component identities (`zpsd_frob_norm_capstone`, 8/0 PURE). This is the
**simplest genuine Frobenius of CFT** — the order-2 local character on a quadratic extension — and it is
the per-prime conjugation the calculus predicts (the `q=−1` swap = `galois_correspondence.md`'s quadratic
conjugation = `integers.md`'s sign bit). **What is absent**: the *Galois Frobenius element* `Frob_p ∈
Gal(K/ℚ)` of a general extension as a named object (grep `Frobenius` in Lean finds only (a) the numerical
**Frobenius number / Chicken-McNugget** theorem `frobenius_representable` — a false-friend name collision,
NOT the Galois Frobenius — and (b) the quadratic conjugation `fp2dFrob`/`zpsd_frob`). The local-character
*reading* is right and the quadratic case is PURE; the general Galois `Frob_p` is the missing object.
PARTIAL (with a real grounding the thesis predicted).

### Hyp 4 — Kronecker–Weber = maximal abelian char is the cyclotomic char. **PREDICTION; the cyclotomic-character ingredient BUILT at all orders, the global theorem ABSENT.**
The calculus predicts Kronecker–Weber (every abelian/ℚ ⊆ a cyclotomic field) is the statement that the
maximal abelian character is the root-of-unity (cyclotomic) character — and this is *why* the
orthogonality corpus is the right ingredient: a cyclotomic character is one whose values are roots of
unity, and the χ-orthogonality `Σ_{k<n} ζ^k ≡ 0` is the completeness/independence of those characters.
The repo grounds this **at all orders mod `p`**: `CyclicCharacterOrthogonality.cyclic_orthogonality_modp`
(15/0 PURE) proves the order-`n` character sum `Σ_{k<n}(g^{(p−1)/n})^k ≡ 0 (mod p)` for *every* order
`n ∣ p−1` via the finite-field route (no `Real213` cyclotomic `ζ` needed for the existence claim) — the
`Σχ=0` prediction at all orders. And `CyclotomicFive.galois_group_is_C4` (4/0 PURE) exhibits a *concrete
abelian cyclotomic Galois group* `Gal(ℚ(ζ₅)/ℚ) ≅ (ℤ/5)^× ≅ C₄`, with `golden_real_subfield` its order-2
fixed subfield — a worked instance of "abelian extension of ℚ = a piece of a cyclotomic field". So the
*cyclotomic character* Kronecker–Weber identifies as maximal is the SAME `RootOfUnityOrthogonality`/
`CyclicCharacterOrthogonality` object the corpus orthogonality-grounds, and a concrete cyclotomic abelian
group is built. **What is absent**: the global Kronecker–Weber *theorem* (every abelian/ℚ *embeds* in
some `ℚ(ζ_N)`) — grep `Kronecker`/`kronecker_weber`/`maximal_abelian` returns zero. The maximality
*ingredient* (cyclotomic = root-of-unity character, at all orders) is built; the embedding theorem is the
break. PREDICTION.

### Does it consolidate `quadratic_reciprocity.md` + the character arrow? **YES — decisively, at the maximal abelian extent.**
The `×↦·` / `×↦{±1}` character arrow now provably runs through CFT's spine *at the order-2 level and as
the all-order character sum*: `psign_mulPerm_hom`/`legendre_mul` (the order-2 Artin map is the
multiplicative quadratic character), `quadratic_reciprocity` (the order-2 Artin reciprocity law),
`fp2dFrob_mul`/`zpsd_frob` (the local Frobenius is the per-prime multiplicative conjugation), and
`cyclic_orthogonality_modp` (the cyclotomic character is complete at all orders — the Kronecker–Weber
ingredient). So **CFT is `quadratic_reciprocity.md`'s order-2 character pushed to the maximal abelian
codomain — no new primitive, the SAME arrow the corpus runs through ~8 fields** (parity, valuation, det,
entropy, Noether, Fourier, rep-theory, QR — now CFT's order-2 case and its all-order character sum). The
single character `σ_a ↦ (a/p)` widened to `c ↦ (c, K^{ab})` is the whole content; QR is its order-2 case,
Kronecker–Weber its cyclotomic-maximality statement, `Frob_p` its local-per-prime reading.

## Revelation (forcing + collapse + located break)

**Class field theory is ONE `(C, L)` — `quadratic_reciprocity.md`'s `×↦·` character read into the
abelianized Galois group instead of `{±1}` — and it consolidates QR + the cyclotomic orthogonality corpus
+ the quadratic Frobenius + `galois_correspondence.md`'s closure into one statement, with no new
primitive.** This is **collapse + forcing + residue-surfaced + a located break**, four at once:

1. **Collapse — the Artin map IS QR's character.** The Artin map (ideles → `Gal^{ab}`), the Legendre
   symbol (`zolotarev_mu`), and the local quadratic Frobenius (`fp2dFrob`) are **not three objects** —
   they are the *same* multiplicative reading `c ↦ (c, ·)` at three codomains/scopes: `{±1}` (QR), the
   full `Gal^{ab}` (Artin), and one local place (`Frob_p`). The order-2 case is `legendre_mul` +
   `psign_mulPerm_hom`, machine-checked; the widening is the SAME arrow `SYNTHESIS.md` runs through every
   character field. CFT does not add a character — it pushes the QR character to its maximal abelian
   reach.

2. **Forcing — Artin reciprocity is forced as the closure of the abelian-character reading, `q=+1`.**
   Artin reciprocity (kernel = norm group) is not posited — it is `galois_correspondence.md`'s
   `Fix ⊣ Inv` closure (`clo_idempotent`, the `q=+1` converge pole) *restricted to abelian
   subextensions*: the norm group is the closed element, the abelian-extension ↔ norm-group bijection is
   the residue collapsing on closed subgroups. The order-2 case (QR) is forced by the empty-diagonal
   parity residue of one grid (`quadratic_reciprocity`, `floor_sum_rectangle`); the general case is the
   same closure widened.

3. **Residue surfaced — `Frob_p` is the local `q=±1` orientation; Kronecker–Weber is cyclotomic
   maximality.** The Frobenius element is the per-prime reading of the character — the `q=−1` swap bit
   (the quadratic conjugation `fp2dFrob_involution`, the same antisymmetry as `lie_theory.md`'s bracket
   and `integers.md`'s sign). Kronecker–Weber surfaces the *maximal* abelian character as the
   root-of-unity character — the SAME `cyclic_orthogonality_modp`/`RootOfUnityOrthogonality` object the
   corpus already grounds at all orders, with `galois_group_is_C4` a concrete cyclotomic-abelian witness.

4. **The located break (the genuine missing leg).** The *global CFT objects* — `ArtinMap`,
   `idele`/`adele`, `RayClassGroup`, the Galois `Frob_p`, `KroneckerWeber` — are entirely absent
   (grep-confirmed). This is the `modular_forms.md`/`knots.md`-shaped edge: the calculus names the
   structure precisely (the abelian-maximal `×↦·` character, the local-Frobenius `q=±1` tag, the
   cyclotomic-character maximality) and grounds the order-2 case and every character ingredient, but the
   *product-over-all-places* global object (the idele class group, and the maps out of it) is unbuilt —
   the same `Real213`/completion-over-all-places residue `padic.md` locates. The honest shape: the spine
   is built and PURE, the global bundle is open work.

**THE CONSOLIDATION (the thesis's central claim):**

| target hypothesis | 213 reading | prior entry | Lean status |
|---|---|---|---|
| Artin map = the `×↦·` character, codomain widened to `Gal^{ab}` | `quadratic_reciprocity.md`'s order-2 character into a general abelian group | `quadratic_reciprocity.md`/`parity.md` | order-2 instance **BUILT** (`zolotarev_mu`, `legendre_mul`); global `ArtinMap` **ABSENT** |
| Artin reciprocity = same multiplicativity, all orders; ker = norm group | `galois_correspondence.md`'s `Fix⊣Inv` closure on abelian subexts, `q=+1` | `quadratic_reciprocity.md` + `galois_correspondence.md` | QR (order-2) **BUILT** (`quadratic_reciprocity`, 11/0); closure machine **BUILT** (`clo_idempotent`); general law **ABSENT** |
| Frobenius element = per-prime `q=±1` local character | `L_Artin` read locally = the quadratic conjugation `a+b√D↦a−b√D` (`q=−1` swap) | `galois_correspondence.md` (conjugation) + `integers.md` (sign) | quadratic Frobenius **BUILT** (`fp2dFrob_mul`, `zpsd_frob`, hom + involution); Galois `Frob_p` **ABSENT** |
| Kronecker–Weber = maximal abelian char is cyclotomic | the root-of-unity character, complete at all orders | `fourier.md` + `galois_correspondence.md` (`CyclotomicFive`) | χ-orthogonality at **all orders mod p BUILT** (`cyclic_orthogonality_modp`, 15/0); concrete cyclotomic `C₄` **BUILT** (`galois_group_is_C4`, 4/0); embedding theorem **ABSENT** |

So **YES** — CFT falls out as the maximal-abelian `×↦·` character: the Artin map is QR's character widened
(order-2 case built), Artin reciprocity is the abelian-restricted closure (order-2 law built, general law
the break), `Frob_p` is the per-prime local character (quadratic case genuinely built as a homomorphism),
and Kronecker–Weber is the cyclotomic-character maximality (the all-order χ-orthogonality and a concrete
cyclotomic group built). CFT **consolidates `quadratic_reciprocity` + the cyclotomic orthogonality corpus
+ the quadratic Frobenius + `galois_correspondence`'s closure** with **no new axis**. The **precise
missing leg is the global idele/Artin-map/reciprocity/Kronecker–Weber bundle** — the product-over-all-
places object and the maps out of it — not the character arrow (the order-2 case is machine-checked) nor
the cyclotomic ingredient (orthogonality at all orders is PURE) nor the local Frobenius (the quadratic
conjugation is PURE).

## Note for the technique — does CFT force a new construct? **EXTEND by consolidation; one named promotion target.**

No new primitive. Every slot is present:
- **the `×↦·` character** (`quadratic_reciprocity.md`/`SYNTHESIS.md`'s central arrow) — the Artin map is
  it, widened from `{±1}` to `Gal^{ab}`;
- **the `Fix ⊣ Inv` closure** (`galois_correspondence.md`/`adjunction.md`'s `clo`) — Artin reciprocity is
  it restricted to abelian subextensions, `q=+1`;
- **the `q=±1` swap/orientation** (`integers.md`/`lie_theory.md`) — `Frob_p` is the per-prime reading,
  the quadratic case the conjugation involution `fp2dFrob`;
- **the root-of-unity character** (`fourier.md`/`RootOfUnityOrthogonality`/`cyclic_orthogonality_modp`) —
  Kronecker–Weber's cyclotomic maximality is it, complete at all orders.

The one sharpening, and the named open target:

> **Promote the order-2 character to a general abelian character map and bundle the idele class group.**
> The repo has the order-2 Artin map (`zolotarev_mu`: `psign σ_a = (a/p)`), the order-2 reciprocity law
> (`quadratic_reciprocity`), the local quadratic Frobenius as a ring hom (`fp2dFrob_mul`), χ-orthogonality
> at all orders (`cyclic_orthogonality_modp`), and a concrete cyclotomic abelian Galois group
> (`galois_group_is_C4`). The missing weld is the **global object**: an idele/ray-class group as a
> *product of the local `(ℤ/p)^×`* (the calculus predicts the family-product, as `padic.md` predicts the
> completion-family), a general `ArtinMap : C_K → Gal^{ab}` instantiating the `×↦·` character into the
> abelianized Aut-family, and the Kronecker–Weber *embedding* theorem tying the maximal abelian character
> to the cyclotomic one (the orthogonality corpus is the ingredient). This is the one promotion that
> would turn CFT from PREDICTION to a closed derivation — the parallel of `CyclotomicFive` grounding the
> field-Galois leg, or `ConvolveRescaleContraction` welding the Banach engine to the CLT.

## Verified Lean anchors (file:line — all grep + `tools/scan_axioms.py`-verified this session)

| Leg | Theorem (file : name : line) | Status |
|---|---|---|
| ★★★★★ **order-2 Artin reciprocity = quadratic reciprocity (full law)** | `Lib/Math/NumberTheory/ModArith/QuadraticReciprocity.lean : quadratic_reciprocity` (:461) | ∅-axiom ✓ (11 PURE / 0 DIRTY, per `quadratic_reciprocity.md` this session's scan) |
| order-2 Artin map: Legendre symbol = permutation sign (`Frob`/character per prime) | `Lib/Math/NumberTheory/ModArith/ZolotarevMuBridge.lean : zolotarev_mu` (:229) | ∅-axiom ✓ (14 PURE, per `quadratic_reciprocity.md`) |
| ★ the character is multiplicative (`×↦·` arrow = Artin map's defining law) | `Lib/Math/NumberTheory/ModArith/LegendreMultiplicative.lean : legendre_mul` (:77) | ∅-axiom ✓ (**5 pure / 0 dirty**, scanned) |
| sign character is multiplicative (the `×↦·` arrow, parity/Fourier) | `Lib/Math/NumberTheory/ModArith/Zolotarev.lean : psign_mulPerm_hom` (:133) | ∅-axiom ✓ (grep-confirmed; per `quadratic_reciprocity.md`/`fourier.md`) |
| ★★ **local Frobenius (quadratic): conjugation `a+b√D↦a−b√D` is a ring hom** | `Lib/Math/NumberTheory/ModArith/FP2SqrtD.lean : fp2dFrob_mul` (:267), `fp2dFrob_add` (:248), `fp2dFrob_involution` (:220) | ∅-axiom ✓ (**32 pure / 0 dirty**, scanned) |
| ★ local Frobenius lifted to `ℤ_p[√D]` (the `q=−1` swap + norm) | `Lib/Math/NumberSystems/Padic/ZpSqrtDFrob.lean : zpsd_frob` (def, :28), `zpsd_frob_norm_capstone` (:102), `zpsd_frob_second` (:61) | ∅-axiom ✓ (**8 pure / 0 dirty**, scanned) |
| ★★★ **Kronecker–Weber ingredient: cyclotomic χ-orthogonality at ALL orders mod p** | `Lib/Math/NumberTheory/ModArith/CyclicCharacterOrthogonality.lean : cyclic_orthogonality_modp` (:254), `cyclic_orthogonality_exists` (:266), `omega_order_n` (:136) | ∅-axiom ✓ (**15 pure / 0 dirty**, scanned) |
| ★★ **concrete cyclotomic abelian Galois group `Gal(ℚ(ζ₅)/ℚ)≅C₄`** (abelian/ℚ instance) | `Lib/Math/Algebra/Icosahedral/CyclotomicFive.lean : galois_group_is_C4` (:66), `golden_real_subfield` (:79), `cyclotomic_five_unification` (:112) | ∅-axiom ✓ (**4 pure / 0 dirty**, scanned) |
| Artin reciprocity = `Fix⊣Inv` closure on abelian subexts (`q=+1` converge) | `Lib/Math/Order/GaloisConnection.lean : clo_idempotent` (:126), `gc_unique_right` (:140) | ∅-axiom ✓ (15/0, per `galois_correspondence.md`) |
| `q=±1` residue tag (local Frobenius swap = escape/converge poles) | `Lib/Math/Foundations/ResidueTag.lean : ResidueTag`, `multiplier_unimodular` | ∅-axiom ✓ (per `SYNTHESIS.md`) |

## Dropped / flagged citations (honest — NOT grounded in repo Lean)

- **`ArtinMap` / `artin_map` / `idele` / `adele` / `RayClass` / `class_field` / `reciprocity_law` as
  named objects** — **ABSENT** (grep across all `lean/E213`: zero hits). The global idele class group and
  the Artin map out of it are unbuilt. The order-2 instance (`zolotarev_mu`, the character into `{±1}`)
  is the built shadow; the global map is the located break.
- **The Galois Frobenius element `Frob_p ∈ Gal(K/ℚ)`** — **ABSENT as a Galois object.** grep `Frobenius`
  finds only (a) the numerical **Frobenius number / Chicken-McNugget** theorem `frobenius_representable`
  (`ModArith/Frobenius.lean`, 8/0 PURE) and its non-representability companion
  (`FrobeniusNonRepresentable.lean`) — a *false-friend name collision*, NOT the Galois Frobenius — and
  (b) the **quadratic conjugation** `fp2dFrob`/`zpsd_frob` (the genuine local order-2 Frobenius, BUILT and
  cited above). The general `Frob_p` as a conjugacy class in a Galois group is unbuilt. **The Frobenius
  number must not be cited as the CFT Frobenius** — flagged explicitly to prevent the collision.
- **Kronecker–Weber theorem (every abelian/ℚ ⊆ `ℚ(ζ_N)`)** — **ABSENT** (grep `Kronecker`/
  `kronecker_weber`/`maximal_abelian`: zero hits). The cyclotomic-character *ingredient*
  (`cyclic_orthogonality_modp` at all orders, `galois_group_is_C4`) is built; the embedding theorem is
  not.
- **General Artin reciprocity law (well-defined + surjective + norm-group kernel for arbitrary abelian
  ext)** — **ABSENT as a theorem.** The order-2 case (`quadratic_reciprocity`) and the closure machine
  (`clo_idempotent`) are built; the general law would need the idele norm group (absent object).
- **The infinite idele/adele completion (product over all places)** — the `Real213`/completion-over-all-
  places residue, the same boundary `padic.md` locates for the family of completions. Not claimed.

## Verdict: PREDICTION + located BREAK (consolidating QR + the cyclotomic orthogonality corpus + the quadratic Frobenius + galois_correspondence's closure)

Class field theory **predicts and consolidates** — no break to the model, no new axis. **Grounded
∅-axiom:** the order-2 Artin map and reciprocity law (`zolotarev_mu`, `legendre_mul`,
`quadratic_reciprocity`, 11/0); the local quadratic Frobenius as a ring homomorphism + involution
(`fp2dFrob_mul`/`fp2dFrob_involution`, 32/0; `zpsd_frob`, 8/0 — the genuine simplest CFT Frobenius, the
`q=−1` per-prime swap); the Kronecker–Weber *ingredient* — cyclotomic χ-orthogonality at **all orders mod
p** (`cyclic_orthogonality_modp`, 15/0) — and a **concrete cyclotomic abelian Galois group**
`Gal(ℚ(ζ₅)/ℚ)≅C₄` (`galois_group_is_C4`, 4/0); and the `Fix⊣Inv` closure that Artin reciprocity is the
abelian restriction of (`clo_idempotent`, 15/0). The **located break** is the **global CFT bundle** — the
idele/ray-class group, the `ArtinMap` object, the general reciprocity law, the Galois `Frob_p`, and the
Kronecker–Weber embedding theorem — all grep-confirmed absent. The thesis holds: **CFT is
`quadratic_reciprocity.md`'s `×↦·` character pushed to the maximal abelian extent** — the SAME arrow the
corpus runs through ~8 fields, with the local Frobenius the per-prime `q=±1` tag and Kronecker–Weber the
cyclotomic-character maximality the orthogonality corpus already grounds. The order-2 case is
machine-checked, every character ingredient is PURE, and only the global product-over-all-places object is
the named promotion target. **CFT EXTENDS by consolidation; the global idele/Artin-map/Kronecker–Weber
bundle is the located break.**
