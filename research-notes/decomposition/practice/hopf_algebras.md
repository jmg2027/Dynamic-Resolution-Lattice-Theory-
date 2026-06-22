# Decomposition: Hopf algebras / bialgebras

*213-decomposition of "a Hopf algebra / bialgebra", per `../README.md` (model v7.1). A **fresh**
field, but one the repo has circled twice from the side: the comultiplication frontiers
(`frontiers/comultiplication_symmetry.md`, `frontiers/convolution_comultiplication_crossdomain.md`)
already named ℕ's two comultiplications and the antipode as Möbius/binomial inversion. This note tests
whether the seven Hopf data — multiplication `m`, comultiplication `Δ`, unit `η`, counit `ε`, antipode
`S`, the bialgebra compatibility, the antipode axiom `m∘(S⊗id)∘Δ = η∘ε` — decompose into the calculus's
normal form, or whether the **co-structure** (the slash read backwards) is a genuinely missing primitive.*

The thesis under test: a Hopf algebra is the calculus's **distinguishing read in both directions at
once** — `m` = the ×↦· character's fold (combine), `Δ` = the *same* slash read **co-** (the unfold /
duplication of a distinction), `S` = the q=−1 unimodular inverse, convolution `f⋆g = m∘(f⊗g)∘Δ` the
bridge, and the bialgebra compatibility a naturality 2-cell.

## The decomposition (C / Reading / Residue)

- **Construction `C` — the distinguishing, with its co-operation made explicit.** Nothing new is
  added: the slash that glues two distinctions into one (`fold`, `append`, `+`/`×`/`conv`) **already
  has a dual the repo built term-for-term** — `CoAppend213.splits` cuts one list into all its
  `(prefix, suffix)` pairs, with `mem_splits_iff : (l1,l2) ∈ splits l ↔ l1 ++ l2 = l` (the cut *is*
  the +-witness). Its count shadow is `Convolution213.natSplits n = [(i,j) : i+j=n]`. So the
  construction carries, alongside the fold `c ↦ (combine)`, a **co-fold** `c ↦ Σ (split)` — the
  comultiplication is *not* a new primitive but the fold's arrow reversed on the same `C`.

- **Reading `L` — read the slash in BOTH directions and convolve.** Three readings of one `C`:
  - **`m` = the fold (combine).** The ×↦· character of the calculus (`det2_mul`/`vp_mul`/`mass_conv`),
    the slash read forward. Multiplicativity of a profile's total mass `mass(f⋆g)=mass f·mass g`
    (`ConvolveProfile.mass_conv`) is this arrow on the convolution.
  - **`Δ` = the co-fold (split / duplicate a distinction).** `Δ: a ↦ Σ a⁽¹⁾⊗a⁽²⁾` is `natSplits`/
    `splits` exactly: split the index every way. **Calculus-native** — `Δ`'s defining laws are the
    *coalgebra* laws, and they are the fold-laws run backwards on the SAME `natSplits`:
    coassociativity `(Δ⊗I)Δ=(I⊗Δ)Δ` is `conv_assoc` (the triple cut reindexes one way), cocommutativity
    is `conv_comm` (the cut-reversal swap), the counit `ε` is the unit `δ=[1,0,…]` with `conv_delta_left
    : conv δ f = f`.
  - **convolution `f⋆g = m∘(f⊗g)∘Δ` — the bridge, BUILT as a commutative semiring.** `Convolution213.conv`
    is split-then-multiply-then-reglue, *literally* `m∘(f⊗g)∘Δ` with `Δ=natSplits`, `f⊗g` the
    coordinatewise product, `m` the sum-reglue. `conv_unit_comm_assoc` packages it: unit `δ`,
    commutative, associative, bilinear (`conv_add_left`). The Dirichlet cut `dconv` is the *other*
    comultiplication (`Δ_× : n↦Σ_{d·e=n} d⊗e`) with the same algebra (`dconv_eps_one`: `ε`=[n==1] is
    the unit).

- **Residue — the antipode, q=−1.** What the co-fold forces but the bare fold-semiring does not capture
  is an **inverse for the identity under `⋆`**: the antipode `S`, defined by `m∘(S⊗id)∘Δ = η∘ε`, i.e.
  `S ⋆ id = ε` (the counit). This is the q=−1 residue tag (`ResidueTag.multiplier_unimodular`): `S` is
  the unimodular involution, the convolution-inverse. **Built, on both cuts**: `IncidenceInversion`
  states "every convolution has an antipode, and inversion against the structure element is the
  fundamental theorem", with the multiplicative-cut antipode being Möbius `μ` (`mu_conv_one : μ∗1 = ε`,
  the antipode axiom verbatim) and the additive-cut antipode the signed binomial `sb`. The
  fixed-point-free unimodular involution itself is `FoldKlein.bothSwap` (explicitly "the antipode",
  `bothSwap_no_fixed`, `bothSwap_involutive`).

## Re-seeing

```
   a Hopf algebra        =  ⟨ C (distinguishing + its co-fold split) | the slash read m (fold) AND Δ (co-fold), bridged by ⋆ ⟩ ⊕ S (q=−1 inverse)

   m  (multiplication)   =  the fold / ×↦· character           (mass_conv, det2_mul, vp_mul — the slash forward)
   Δ  (comultiplication) =  the co-fold = natSplits/splits     (mem_splits_iff: a split IS a +-witness — the slash backward)
   coassociativity (Δ⊗I)Δ=(I⊗Δ)Δ  =  conv_assoc               (triple cut reindexes — the dual of m-associativity)
   cocommutativity       =  conv_comm                          (cut-reversal swap — the dual of m-commutativity)
   η  (unit)             =  δ = [1,0,…]   (Cauchy)  /  ε=[n==1] (Dirichlet)   (conv_delta_left, dconv_eps_one)
   ε  (counit)           =  the dual unit: pick the constant term / [n==1]    (the same sequence read against the dual product)
   f ⋆ g = m∘(f⊗g)∘Δ     =  conv f g = Σ_{i+j=n} f i · g j      (split-then-multiply-then-reglue, conv_unit_comm_assoc)
   S  (antipode)         =  the ⋆-inverse of id; q=−1 unimodular involution  (mu_conv_one: μ∗1=ε; binomial sb; bothSwap)
   antipode axiom m∘(S⊗id)∘Δ=η∘ε  =  S ⋆ id = ε  =  μ ∗ 1 = ε    (mu_conv_one — the axiom is a Lean theorem on the ×-cut)
   bialgebra compatibility (Δ an algebra map)  =  Δ_+ ⇄ Δ_× distributivity   (OPEN — frontier F1, see Residue/break)
```

## Revelation

**Collapse + forcing + a located break.**

**Collapse (the spine):** *the comultiplication is the calculus's fold-arrow reversed on the same
construction, not a new primitive.* The repo's `CoAppend213`/`Convolution213` files were built to
answer "what is the +-inverse question?" — `splits`/`natSplits` — and the answer is precisely a
**comultiplication**: `Δ(c) = Σ a⁽¹⁾⊗a⁽²⁾` IS "list all the ways `c` splits". So the four coalgebra
axioms collapse onto the four algebra axioms by *cut-reversal*: coassociativity = `conv_assoc`,
cocommutativity = `conv_comm`, counit = `conv_delta_left`. A Hopf algebra is `⟨C | slash forward (m) +
slash backward (Δ)⟩` — the **same slash read in both directions at once**, exactly the thesis.

**Forcing:** convolution `⋆ = m∘(f⊗g)∘Δ` is *forced* — it is the only product you can build from the
two reads (split, multiply pieces, reglue), and it is built end-to-end as a commutative semiring
(`conv_unit_comm_assoc`) with a derivation (`conv_leibniz`/`deriv_is_derivation`). The antipode is
forced as the q=−1 residue: a co-fold demands an inverse for `id` under `⋆`, and `mu_conv_one : μ∗1=ε`
is the antipode axiom `S⋆id=ε` *as a ∅-axiom theorem* on the multiplicative cut, with the signed
binomial the additive twin (`binomial_inversion_via_engine`) — "one antipode under the two cuts of ℕ"
(`incidence_inversion_two_cuts`). The antipode lands on the **same `ResidueTag` q=−1 unimodular bit**
(`multiplier_unimodular`) that runs Cantor/det-sign/∂; the fixed-point-free involution `bothSwap` is
the geometric face of the *same* S.

**The located break (honest — a PARTIAL, in the `knots.md` spirit):** the **bialgebra compatibility**
— "Δ is an algebra homomorphism", i.e. the single law fusing `m` and `Δ` into one structure — is **NOT
built**. The frontier `convolution_comultiplication_crossdomain.md` names this exactly as the open
target **F1**: the ℕ-native compatibility between `Δ_+` (Cauchy cut) and `Δ_×` (Dirichlet cut) induced
by distributivity `a·(b+c)=a·b+a·c`. The two comultiplications and both antipodes are built and PURE;
the *one law that makes the pair a bialgebra* (Δ multiplicative, equivalently the two cuts'
distributive interlock) is the genuine residual. This is not the character arrow (a two-term law) and
not a 2-cell — it is a compatibility *between two co-operations*, structurally adjacent to the
graded-relation slot (README v7.1's missing primitive #2), and is the precise spot the co-structure
stops being free.

## VALIDATE verdict — **EXTEND + PARTIAL** (one located break: the bialgebra compatibility F1)

No new primitive. The co-fold (`Δ`) is the calculus's existing fold-arrow reversed on the same `C`
(`natSplits`/`splits`), so the model's interior is unchanged: the convolution product is the
`generating_functions.md` family-reading product (`ConvolveProfile`), the antipode is the q=−1
`ResidueTag` residue, and the unit/counit are the convolution unit `δ`/`ε`. Three of the
re-seeing rows beyond what `generating_functions.md`/`comultiplication_symmetry.md` recorded are now
pinned as Hopf data:
1. **Δ = co-fold is calculus-native** — coalgebra laws = algebra laws by cut-reversal (`conv_assoc`/
   `conv_comm`/`conv_delta_left`), the slash read co-. Not a missing primitive. **EXTEND.**
2. **the antipode axiom `S⋆id=ε` is a ∅-axiom theorem** — `mu_conv_one` (×-cut) + binomial (+-cut),
   "one antipode, two cuts" (`incidence_inversion_two_cuts`), on the q=−1 `ResidueTag`. **EXTEND.**
3. **the bialgebra compatibility is ABSENT** — F1 (Δ_+ ⇄ Δ_× distributivity) open per the frontier;
   the predicted-not-built leg. **PARTIAL / located break.**

So: a Hopf algebra is the distinguishing read in both directions at once (`m`+`Δ`) plus the q=−1
antipode — fully native and Lean-grounded **except** the bialgebra law that fuses the two directions,
which is the genuine open primitive. This is a clean EXTEND with one honestly-located PARTIAL, not a
forced clean EXTEND.

## Verified Lean anchors (file:line:theorem — all grep + `tools/scan_axioms.py`-scanned this session)

| Hopf datum | Theorem (file:line) | Purity (module tally) |
|---|---|---|
| Δ = co-fold (split = +-witness) | `Meta/Nat/CoAppend213.lean:89` `mem_splits_iff` | **8 PURE / 0 DIRTY** ✓ |
| Δ count shadow + soundness | `Meta/Nat/Convolution213.lean:49` `natSplits` (def), `:55` `natSplits_sound` | **49 PURE / 0 DIRTY** ✓ |
| ⋆ = m∘(f⊗g)∘Δ (the bridge product) | `Meta/Nat/Convolution213.lean:87` `conv` (def) | (in the 49) ✓ |
| coassociativity (Δ⊗I)Δ=(I⊗Δ)Δ | `Meta/Nat/Convolution213.lean:257` `conv_assoc` | PURE (in the 49) ✓ |
| cocommutativity | `Meta/Nat/Convolution213.lean:156` `conv_comm` | PURE (in the 49) ✓ |
| counit / unit η (Cauchy δ) | `Meta/Nat/Convolution213.lean:285` `conv_delta_left`, `:301` `conv_delta_right` | PURE (in the 49) ✓ |
| ⋆ is comm-monoid semiring w/ unit | `Meta/Nat/Convolution213.lean:313` `conv_unit_comm_assoc` | PURE (in the 49) ✓ |
| Leibniz / derivation on ⋆ | `Meta/Nat/Convolution213.lean:350` `conv_leibniz`, `:402` `deriv_is_derivation` | PURE (in the 49) ✓ |
| ★ antipode axiom S⋆id=ε (×-cut) | `Lib/Math/NumberTheory/DirichletIdentities.lean:50` `mu_conv_one` (`μ∗1=ε`) | **20 PURE / 0 DIRTY** ✓ |
| counit ε two-sided unit (×-cut) | `Lib/Math/NumberTheory/DirichletIdentities.lean:115` `dconv_eps_one` | PURE (in the 20) ✓ |
| antipode (×-cut), engine form | `Lib/Math/IncidenceInversion.lean:162` `mobius_inversion_via_ring`, `:152` `mu_conv_one_all` | **9 PURE / 0 DIRTY** ✓ |
| antipode (+-cut), signed binomial | `Lib/Math/IncidenceInversion.lean:132` `binomial_inversion_via_engine` | PURE (in the 9) ✓ |
| ★ one antipode, two cuts (the +/× unity) | `Lib/Math/IncidenceInversion.lean:250` `incidence_inversion_two_cuts` | PURE (in the 9) ✓ |
| m = ×↦· character on ⋆ (mass mult.) | `Lib/Math/Probability/Limit/ConvolveProfile.lean:190` `mass_conv`, `:239` `momentNum_conv` | **20 PURE / 0 DIRTY** ✓ |
| ×-cut convolution multiplicative | `Lib/Math/NumberTheory/DirichletMultiplicative.lean:132` `dconv_mul` | **4 PURE / 0 DIRTY** ✓ |
| S = q=−1 unimodular involution (tag) | `Lib/Math/Foundations/ResidueTag.lean:86` `multiplier_unimodular` | **55 PURE / 0 DIRTY** ✓ |
| S geometric face (fixed-point-free) | `Lens/Number/FoldKlein.lean:52` `bothSwap` (def), `:58` `bothSwap_no_fixed`, `:50` `bothSwap_involutive` | **9 PURE / 0 DIRTY** ✓ |

## Dropped / flagged (honest)

- **Named `HopfAlgebra` / `Bialgebra` / `antipode` (as a Hopf object) / `Coalgebra` (in the Hopf sense)
  — ABSENT (grep-confirmed).** `grep -i "HopfAlgebra|Bialgebra|antipode"` over `lean/E213/` finds
  "antipode" only as (a) `FoldKlein.bothSwap` (the Klein-four fixed-point-free involution) and (b) the
  *incidence-algebra* antipode (`IncidenceInversion`, the Möbius/binomial inverse). "Hopf" appears only
  as "Hopfield" (spin-glass, unrelated). "coproduct"/"Coalgebra" hits are the categorical `Sum`
  coproduct (`Lens/Instances/Sum*.lean`), not the Hopf comultiplication. So the predicted-not-built
  named bundles are confirmed absent; the **structure** (m/Δ/η/ε/S/⋆) is all built unnamed.
- **The bialgebra compatibility (Δ an algebra map) — ABSENT (frontier F1, open).** Per
  `frontiers/convolution_comultiplication_crossdomain.md` §F1: the ℕ-native `Δ_+ ⇄ Δ_×` distributivity
  is the genuine open leg. Flagged as the located break (PARTIAL), not asserted.
- **A single Hopf semiring object bundling both cuts under one index convention** — the frontier's F2
  was CLOSED (`IncidenceInversion`, one antipode engine over both cuts), but a *single Lean term*
  covering both faces over one index convention is still the open rung (per that frontier). Not cited as
  a Hopf bundle.
- **`conv_assoc`/`conv_comm`/`conv_delta_*` cited as the coalgebra laws** is the calculus's reading
  (they are *dual* to the algebra laws of the same product, read as the comultiplication's
  coassoc/cocomm/counit per `comultiplication_symmetry.md`); the repo proves them as convolution-product
  laws, and the slot-programme doctrine identifies them with the cut's swap/coassoc symmetry — flagged so
  the "coalgebra" labelling is read as the decomposition, not a separately-named Lean coalgebra.

### Buildable witness (named)

The natural ∅-axiom closure of this note is **F1**: state and prove the `Δ_+`/`Δ_×` distributive
compatibility on ℕ (the object-level form of `vp` intertwining the two cuts, `vp_mul`/`vp_add_eq_min`),
which would promote the PARTIAL to a full EXTEND by exhibiting the **one** law that makes ℕ's two
comultiplications a single bialgebra. The antipode side is already a theorem (`incidence_inversion_two_cuts`);
only the m/Δ compatibility is unwritten.
