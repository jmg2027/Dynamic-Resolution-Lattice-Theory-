# Decomposition: operator algebras / C*-algebras

*213-decomposition of "a C*-algebra, the spectrum of an operator, the spectral theorem
(self-adjoint / normal), states + the GNS construction, the Gelfand transform (commutative C* ≅
C(X)), positivity (x*x ≥ 0)", per `../README.md` (model v7.1). A **fresh** field in the analysis
cluster, LEVERAGE phase — the bar is PREDICTION/DERIVATION, consolidating `spectral.md` (the finite
`Mat2` spectrum, the `q=+1` real-spectrum reading), `representation.md` (the `×↦·` character on an
Aut-family), `quantum_mechanics.md` (the symmetric-operator pole), and `gaussian_clt.md`/`probability.md`
(the weight axis). This entry tests one thesis: **a C*-algebra is the calculus's spectral character at
infinite resolution, with the `q=+1` real-spectrum pole made the defining axiom.***

THE THESIS (from the task): `spectral.md` grounded the finite case — a symmetric/self-adjoint `Mat2`
has real spectrum (`disc_symmetric_nonneg`, the `q=+1` converge pole, `disc≥0`); `det`/`tr` are the two
Vieta coefficients `e₂,e₁` of one spectrum. A C*-algebra is THE SAME spectral reading pushed to infinite
dimension, with one structural promotion: *self-adjoint ⟹ real spectrum* is moved from a **theorem**
(`spectral.md`) to a **defining axiom**. The `*`-involution is the `q=±1` conjugation/orientation bit
(`x↦x*`, an involution); the Gelfand transform (commutative C* ≅ C(spectrum)) is the **character arrow**
(`×↦·` multiplicative functional into ℂ — `det2_mul`/`legendre_mul` generalized to algebra-homs);
states + GNS are the **weight axis** (a state = a positive normalized weight; GNS = the weight turned
into an inner product); positivity `x*x≥0` is the `q=+1` converge pole. The likely verdict is a
**PARTIAL** — the genuine Hilbert-space / completion primitive is absent, shared with the analysis
cluster (`quantum_mechanics.md`/`measure.md`).

## The decomposition (C / Reading / Residue)

- **Construction `C` — the same operator `×`-construction as `spectral.md`/`representation.md`, no new
  build.** A C*-algebra is an algebra of operators: in the discrete `d=2` setting the elements are
  `Mat2` (`HyperbolicEllipticTrace.Mat2`), the directed-count bundle built by `mul`, carrying the
  orientation/swap bit (sign of `det`) and fold-height `2`. Its multiplication IS `representation.md`'s
  Aut-family composition (`mulPerm_comp`-style), and a representation `ρ : A → B(H)` is exactly
  `representation.md`'s operation-preserving reading. **C*-algebra theory introduces no new
  construction** — the algebra, the spectrum, the involution, and a state are all *readings* of this one
  operator `C`. The genuinely new object would be the *infinite-resolution completion* (a Hilbert
  space) — and that, grep-confirmed, is the located absence (below).

- **Reading — three readings of one operator `C`, all already named in the notebook:**
  - **`L_*` (the involution / `q=±1` conjugation bit):** `x ↦ x*` is the `*`-involution — an
    order-2, fixed-point-toggling reading, the same `q=±1` swap-bit that signs `det`, `∂`, and ℤ's `−`.
    Built ∅-axiom as conjugation on the Cayley–Dickson tower: `CDConjugation.cdConj` with
    **`cdConj_involutive`** (`(x*)* = x`, the defining involution law). The four-fold Klein structure
    `{id, negQ, recQ, bothSwap}` (`FoldKlein`, `multiplier_unimodular`-style) is the `q=±1` reading
    made a group, with `bothSwap` the fixed-point-free antipode `z↦−1/z`. So `*` is *not* a new
    primitive — it is the `q=±1` direction bit applied to the operator algebra. The C*-axiom that
    `(xy)* = y*x*` (anti-homomorphism) is the order-reversal forced by the swap.
  - **`L_spec` / `L_sa` (the spectrum / self-adjoint = `q=+1` real-spectrum reading):** the spectrum of
    an operator is `spectral.md`'s reading verbatim — the multiset of `q=+1` scale-residues (`A·v=λ·v`,
    `v` fixed up to multiplier `λ`). **Self-adjoint (`x = x*`) ⟹ real spectrum** is `spectral.md`'s
    `disc_symmetric_nonneg` (symmetric ⟹ `disc = (a−d)²+(2b)² ≥ 0`, so the spectrum is real, the
    elliptic `disc<0` complex escape structurally unavailable). **The C*-promotion**: where `spectral.md`
    *proves* `disc≥0` for symmetric `Mat2`, the C* framework takes "self-adjoint ⟹ real spectrum" as the
    *defining axiom* of the abstract algebra (the abstract spectrum `σ(x) ⊆ ℝ` for `x=x*` is postulated,
    then `disc_symmetric_nonneg` is the `d=2` *model* that satisfies it). Positivity `x*x ≥ 0` is the
    same `q=+1` corner: `x*x` is self-adjoint with non-negative spectrum (`cdNormSq z = cutMul z z ≥ 0`
    at level 0 — a square is non-negative).
  - **`L_χ` (the Gelfand transform / character arrow `×↦·`):** for a *commutative* C*-algebra, the
    Gelfand transform `A ≅ C(spectrum(A))` sends `x` to the function `χ ↦ χ(x)` on the space of
    **characters** (multiplicative functionals `χ : A → ℂ`, `χ(xy)=χ(x)χ(y)`). A character is exactly
    the calculus's `×↦·` character arrow — `det2_mul` (`det(MN)=det M·det N`) and `legendre_mul`
    (`QR(ab) ⟺ QR(a)⟺QR(b)`) are this same multiplicative-functional reading at the scalar / `{±1}`
    codomain; the Gelfand character generalizes the codomain to ℂ. So "a commutative C*-algebra IS its
    characters" is `representation.md`'s/`fourier.md`'s statement "the algebra is its dual `Â`", read on
    the operator algebra.
  - **`L_ω` (a state / GNS / weight axis):** a state `ω : A → ℂ` is a **positive normalized weight**
    (`ω(x*x) ≥ 0`, `ω(1)=1`) — `probability.md`/`gaussian_clt.md`'s weight-reading on the operator
    algebra (the value-weighted count, total mass `1`). The mass-multiplicativity `mass(f⋆g)=mass f·mass g`
    (`mass_conv`) and additive mean `momentNum_conv` are the weight axis's `×↦·`/`×↦+` characters. GNS is
    the **weight made into an inner product**: `⟨x,y⟩ := ω(x*y)`, turning the positive weight `ω` into the
    Hilbert structure on which `A` acts. This is the weight axis composed with the involution `L_*` — the
    same `weight ∘ character` series-composition `entropy.md` named.

- **Residue — the `q=±1` tag at the converge pole, plus the located completion residue.** The C*-axiom
  selects the `q=+1` corner *by definition*: self-adjoint elements have real spectrum (no `q=−1` complex
  escape), positivity `x*x ≥ 0` is the converge fixed point, and GNS produces an honest (positive-definite)
  inner product. The genuine residue is the **completion to a Hilbert space at infinite resolution** —
  the `Real213`/ℂ + completeness object the analysis cluster repeatedly locates as absent
  (`quantum_mechanics.md`'s Hilbert space, `measure.md`'s `Lp`, `gaussian_clt.md`'s `CompleteMetricModulus`).
  The C*-norm completeness (the `‖x*x‖ = ‖x‖²` C*-identity) is the precise missing primitive — and it is
  grep-confirmed un-built (no `normSq_mul`/multiplicative-norm law exists).

## Re-seeing (⟨C | L⟩)

```
   a C*-algebra A          =  ⟨ operator ×-construction (Mat2/Aut-family) | the *-spectral-weight readings ⟩
   the *-involution x↦x*   =  the q=±1 conjugation/orientation bit; (x*)*=x          (cdConj_involutive)
   (xy)* = y*x*            =  the swap forces order-reversal (the antipode bothSwap)  (FoldKlein.bothSwap)
   self-adjoint x=x*       =  the q=+1 real-spectrum reading (the C*-AXIOM)           (disc_symmetric_nonneg)
   "self-adjoint ⟹ σ(x)⊆ℝ" =  spectral.md's disc≥0 PROMOTED from theorem to axiom    (disc_symmetric_sum_of_squares)
   the spectrum σ(x)       =  the multiset of q=+1 scale-residues of L_spec           (spectral.md, golden_hyperbolic)
   positivity x*x ≥ 0      =  the q=+1 converge pole (a square is non-negative)        (cdNormSq = cutMul z z ≥ 0)
   a character χ:A→ℂ       =  the ×↦· multiplicative-functional arrow                  (det2_mul, legendre_mul)
   Gelfand: A ≅ C(σ(A))    =  "the commutative algebra IS its characters" (the dual Â) (representation.md/fourier.md)
   a state ω:A→ℂ           =  a positive normalized weight (weight axis, mass 1)        (mass_conv, momentNum_conv)
   GNS ⟨x,y⟩=ω(x*y)        =  the weight made into an inner product = weight ∘ L_*      (entropy's weight∘character)
   the C*-identity ‖x*x‖=‖x‖² =  the completion/Hilbert object — RESIDUE (un-built)     (no normSq_mul; LOCATED BREAK)
```

Side by side, a C*-algebra is **one operator-`C` read at the `q=+1` converge corner of the `ResidueTag`,
with the involution as the `q=±1` bit and the character arrow as the Gelfand transform**:

| reading | what it does to the operator `C` | invariant / pole | built anchor |
|---|---|---|---|
| `L_*` involution `x↦x*` | the `q=±1` conjugation bit; `(x*)*=x`; `(xy)*=y*x*` order-reversal | direction `q=±1` | `cdConj_involutive`, `FoldKlein.bothSwap` |
| `L_sa` self-adjoint spectrum | reads the real eigenvalues (the C*-axiom) | **q=+1** | `disc_symmetric_nonneg` |
| `L_χ` Gelfand character | the `×↦·` multiplicative functional into ℂ | character arrow | `det2_mul`, `legendre_mul` |
| `L_ω` state / GNS | positive normalized weight → inner product | weight axis (q=+1 positivity) | `mass_conv`, `momentNum_conv` |
| C*-norm completion | the Hilbert-space `‖x*x‖=‖x‖²` completion | **RESIDUE** | un-built (no `normSq_mul`) |

## Revelation (collapse + forcing + spine)

**The new datum (not a re-skin of `spectral.md`/`quantum_mechanics.md`): the C*-axiom PROMOTES
`spectral.md`'s `q=+1` `disc≥0` theorem to a defining axiom, and Gelfand is the character arrow saying
"the algebra IS its characters."** This is the load-bearing distinction from the neighbors:

- **Forcing — "self-adjoint ⟹ real spectrum" is a *promoted* theorem, not a new postulate.**
  `quantum_mechanics.md` read "Hermitian ⟹ real eigenvalue" as "stay at `q=+1`" — a *consequence*
  certified by `disc_symmetric_nonneg`. The C*-algebra goes one structural step further: it makes
  *self-adjoint ⟹ σ(x) ⊆ ℝ* the **defining axiom** of the abstract object (an abstract C*-algebra is
  *defined* so that self-adjoint elements have real spectrum; the spectral radius equals the norm,
  `r(x)=‖x‖` for `x=x*`). The calculus reads this exactly: the C* framework is `spectral.md`'s `q=+1`
  pole *taken as the constitutive law* rather than derived. `disc_symmetric_nonneg` (PURE) is the
  `d=2` *witness* that the axiom is non-vacuous — the finite model realizing the promoted axiom. So a
  C*-algebra is not a re-skin of `quantum_mechanics.md`'s observable; it is the *axiomatization that
  declares the `q=+1` corner the whole game*.

- **Collapse — the Gelfand transform IS the character arrow (`×↦·`), read on the operator algebra.**
  The Gelfand–Naimark theorem (commutative C*-algebra ≅ `C(spectrum)`) is the statement "the algebra is
  recovered from its multiplicative functionals into ℂ." A multiplicative functional `χ(xy)=χ(x)χ(y)` is
  the calculus's `×↦·` character arrow — the *same* arrow as `det2_mul` (scalar codomain) and
  `legendre_mul` (`{±1}` codomain), with the codomain widened to ℂ. `representation.md` and `fourier.md`
  already proved "the abelian algebra IS its dual `Â`" (1-dim characters = `Hom(A, ℂ)`, orthogonality
  `Σχ=0` at orders 2/3/4/6). Gelfand is *that consolidation read on the C*-algebra*: a commutative
  C*-algebra is its character space, the `×↦·` arrow's image, exactly as `representation.md` said the
  algebra is downstream of the character arrow. **So the character arrow now provably runs through an
  eighth field**: parity, valuation, det, entropy, Noether, Fourier, representation-theory characters,
  and the Gelfand character of a commutative C*-algebra — all one construction-preserving `×↦·` reading.

- **Spine — the `q=±1` tag organizes the whole field.** The `*`-involution is the `q=±1` direction bit
  (`cdConj_involutive`, `FoldKlein` Klein four-group, `multiplier_unimodular`-style); self-adjointness /
  positivity select the `q=+1` converge pole (`disc_symmetric_nonneg`, `cdNormSq = cutMul z z ≥ 0`); a
  state + GNS is the weight axis at the positivity (`q=+1`) corner. The `q=−1` escape would be the
  *non-self-adjoint* / non-normal spectrum (complex, `disc<0`, the elliptic rotation) — exactly the pole
  `spectral.md`/`quantum_mechanics.md` tagged `q=−1`. So the C*-axiom = "restrict the operator algebra to
  the `q=+1` corner of the `ResidueTag`, with the `*`-involution as the `q=±1` bit that defines it."
  `ResidueTag.residue_tag_two_poles` (55/0 PURE) is the formal home; `golden_is_converge` ties the `+1`
  to the literal converge pole.

## VALIDATE — verdict

**Net: PREDICTION + PARTIAL — one located break (the genuine one the task predicted).** A C*-algebra
introduces **no new construction** and consolidates four prior files (spectral + representation +
quantum_mechanics + probability/gaussian_clt) under the two standing invariants (the `×↦·` character
arrow, the `q=±1` residue) with the `*`-involution = the `q=±1` direction bit. The genuine absence —
the Hilbert-space / C*-norm completion object — is grep-confirmed and located precisely, shared with the
analysis cluster. Leg by leg:

- **Leg 1 — the `*`-involution = the `q=±1` conjugation bit. PREDICTION, BUILT.**
  `CDConjugation.cdConj` with `cdConj_involutive` (`(x*)*=x`, 7/0 PURE) is the defining involution;
  `FoldKlein.bothSwap` (the fixed-point-free antipode, the order-reversal that forces `(xy)*=y*x*`) +
  `klein_four_group` (9/0 PURE) is the `q=±1` reading made a group. The involution is *not* a new
  primitive — it is the direction bit (`integers`/`determinant`/`homology`'s `q=±1` sign) on the operator.

- **Leg 2 — self-adjoint ⟹ real spectrum = the `q=+1` corner, the C*-axiom PROMOTED. PREDICTION, BUILT
  at `d=2`.** `disc_symmetric_nonneg` + `disc_symmetric_sum_of_squares` + `symmetric_spectrum_real`
  (9/0 PURE) prove the symmetric discriminant is a sum of squares, so the spectrum is real — the `q=+1`
  corner. The C*-promotion (theorem → defining axiom) is the genuine new datum vs `spectral.md`. The
  worked eigenvalue is φ (`golden_hyperbolic`, the dominant `q=+1` scale-residue). General `d>1` /
  infinite-dim self-adjoint spectral theorem is the inherited open (below).

- **Leg 3 — Gelfand transform = the `×↦·` character arrow. PREDICTION (consolidation).**
  A character `χ(xy)=χ(x)χ(y)` is `det2_mul` (130/0 PURE) / `legendre_mul` (5/0 PURE) with codomain ℂ;
  "commutative C* ≅ `C(σ(A))`" is `representation.md`/`fourier.md`'s "the algebra IS its dual `Â`" read
  on the operator algebra. The character arrow's eighth field, no new work. Honest: the *named* Gelfand
  transform / `C(X)` / spectrum-as-a-space object is absent (the structural prediction is the deliverable).

- **Leg 4 — states + GNS = the weight axis. PREDICTION, weight BUILT.**
  A state = a positive normalized weight; the weight axis is built (`mass_conv` total-mass `×↦·`,
  `momentNum_conv` additive mean, 20/0 PURE). GNS = `weight ∘ L_*` (the inner product `⟨x,y⟩=ω(x*y)`),
  the same series-composition `entropy.md` named. **PARTIAL:** the weight is built; the GNS *inner-product
  space* (a genuine Hilbert structure from a state) is the absent completion object — the same Hilbert
  gap `quantum_mechanics.md` located (`⟨ψ|φ⟩`, `|·|²`). Positivity `ω(x*x)≥0` is the `q=+1` corner
  (`cdNormSq = cutMul z z ≥ 0`).

**The located break (honest, the one the task predicted — the Hilbert-space/completion primitive).**
A C*-algebra is, by definition, a Banach `*`-algebra: a *complete* normed algebra with the C*-identity
`‖x*x‖ = ‖x‖²`. The completion-to-a-Hilbert-space at infinite resolution is **absent**:
1. **The C*-norm and its identity `‖x*x‖=‖x‖²`** — un-built. Grep-confirmed there is **no `normSq_mul`
   / multiplicative-norm law** in `CDNorm.lean` (6/0 PURE has `cdNormSq` and its level unfoldings, but no
   `‖x*x‖=‖x‖²` and no norm-multiplicativity). The norm-squared `cdNormSq` exists as a level-indexed
   non-negative readout *without* the C*-identity welding it to the involution and the spectral radius.
2. **A Hilbert space / inner product / GNS representation** — absent (the same gap
   `quantum_mechanics.md` located; the closest built structure is `CDNorm`'s `cdNormSq`/`cdConj`, a norm
   with conjugation but no inner-product space and no completion).
3. **The named `CstarAlgebra` / `GNS` / `Gelfand` / `HilbertSpace` / `state` objects** — grep-confirmed
   ABSENT (a sweep for `Cstar|C\*-algebra|GNS|Gelfand|HilbertSpace|Hilbert|InnerProduct` returned only
   three *incidental* matches: a "Hilbert-ε" comment in `ArityForcingGeneral.lean:18`, a docstring
   reference in `PhaseChiralBridge.lean:18`, and a comment in `MultSystem.lean` — none is a C*-algebra,
   GNS, Gelfand, or Hilbert-space object). Predicted-not-built, as the task anticipated.

This is the same `Real213`/ℂ + completeness residue the analysis cluster repeatedly hits
(`quantum_mechanics.md`'s Hilbert space, `measure.md`'s `Lp`/`Quot.sound` via `funext`,
`gaussian_clt.md`'s `CompleteMetricModulus`). Located, not failed: the discrete spectral / involution /
character / weight legs are all PURE-anchored; the completion object names a concrete open target (a
C*-norm with `‖x*x‖=‖x‖²` welding `cdNormSq` to `cdConj`, and a GNS inner-product from a state).

## Touches on model v7.1?

**No new primitive; EXTEND + one consolidation note.** The two invariants (character arrow, `q=±1`
residue) and four axes absorb C*-algebra theory with nothing added: the `*`-involution is the `q=±1`
direction bit, self-adjoint/positivity the `q=+1` converge pole, the Gelfand transform the `×↦·`
character arrow, a state the weight axis. The note for the README's batch log:

> **A C*-algebra is the spectral character at the `q=+1` corner, with self-adjoint⟹real-spectrum
> PROMOTED to a defining axiom.** `spectral.md`'s `disc_symmetric_nonneg` (symmetric ⟹ real spectrum,
> a *theorem*) becomes the C*-axiom (*defining* the abstract algebra so self-adjoint elements have real
> spectrum; positivity `x*x≥0` = the converge pole). The `*`-involution = the `q=±1` conjugation bit
> (`cdConj_involutive`, `(x*)*=x`; `FoldKlein.bothSwap` the order-reversing antipode). The **Gelfand
> transform** (commutative C* ≅ `C(σ(A))`) = the `×↦·` character arrow's *eighth* field
> (`det2_mul`/`legendre_mul` into ℂ): "the commutative algebra IS its characters", consolidating
> `representation.md`/`fourier.md`. States + GNS = the weight axis (`mass_conv`/`momentNum_conv`),
> GNS = `weight ∘ involution`. Located break (the predicted one): the Hilbert-space / C*-norm
> completion — `‖x*x‖=‖x‖²` is un-built (no `normSq_mul`), the named `Cstar`/`GNS`/`Gelfand`/`Hilbert`
> objects grep-confirmed absent. Same `Real213`/completeness residue as quantum_mechanics + measure.

This sharpens, not alters, model v7.1: it extends the character arrow to an eighth field and pins the
operator-algebra completion as the shared analysis-cluster gap.

## Verified Lean anchors (file:line:theorem — all grep + `scan_axioms.py`-verified this session; all PURE)

| Leg | Theorem (file:line) | Purity (scan this session) |
|---|---|---|
| ★★★★ the `*`-involution `(x*)*=x` (the `q=±1` conjugation bit) | `Lib/Math/NumberSystems/SignedCut/CD/CDConjugation.lean:50` `cdConj_involutive`; `:21` `cdConj` (def); `:37` `cdConj_involutive_zero` | **7 PURE / 0 DIRTY** ✓ |
| ★★★ the `q=±1` reading as a Klein four-group; `bothSwap` = fixed-point-free antipode (order-reversal) | `Lens/Number/FoldKlein.lean:50` `bothSwap_involutive`; `:31` `bothSwap` (def); `:65` `klein_four_group`; `:58` `bothSwap_no_fixed` | **9 PURE / 0 DIRTY** ✓ |
| ★★★★ self-adjoint ⟹ real spectrum (the `q=+1` corner; the C*-axiom's `d=2` witness) | `Lib/Math/NumberSystems/Real213/Mat2/Mat2SymmetricSpectrum.lean:83` `disc_symmetric_nonneg`; `:67` `disc_symmetric_sum_of_squares`; `:52` `IsSymmetric` (def); `:137` `symmetric_spectrum_real` | **9 PURE / 0 DIRTY** ✓ |
| ★★★★ Gelfand character = `×↦·` multiplicative functional (scalar codomain) | `Lib/Math/NumberSystems/Real213/Markov/SternBrocotMarkov.lean:104` `det2_mul` (`det(MN)=det M·det N`) | **130 PURE / 0 DIRTY** ✓ |
| ★★★ Gelfand character = `×↦·` multiplicative functional (`{±1}` codomain) | `Lib/Math/NumberTheory/ModArith/LegendreMultiplicative.lean:77` `legendre_mul` (`QR(ab)⟺(QR(a)⟺QR(b))`) | **5 PURE / 0 DIRTY** ✓ |
| ★★★ a state = a positive normalized weight (weight axis: `×↦·` mass, `×↦+` mean) | `Lib/Math/Probability/Limit/ConvolveProfile.lean:190` `mass_conv`; `:239` `momentNum_conv` | **20 PURE / 0 DIRTY** ✓ |
| ★★ positivity `x*x ≥ 0` = a square is non-negative (the `q=+1` pole); norm-squared readout | `Lib/Math/NumberSystems/SignedCut/CD/CDNorm.lean:38` `cdNormSq` (def); `:43` `cdNormSq_zero` (`= cutMul z z`) | **6 PURE / 0 DIRTY** ✓ |
| ★★★ the `q=±1` residue tag (the spine; `±1` involution multiplier) | `Lib/Math/Foundations/ResidueTag.lean:228` `residue_tag_two_poles`; `:86` `multiplier_unimodular`; `:180` `golden_is_converge` | **55 PURE / 0 DIRTY** ✓ |
| cross-frame | `spectral.md` (`Mat2Spectrum` det/tr=e₁/e₂, Cayley–Hamilton, `golden_hyperbolic`), `representation.md` (`×↦·` on Aut-family, `Σχ=0`), `quantum_mechanics.md` (symmetric pole), `probability.md`/`gaussian_clt.md` (weight axis) | prior, ∅-axiom ✓ |

## Dropped / flagged (honest — not cited as anchors)

- **The C*-norm + the C*-identity `‖x*x‖ = ‖x‖²`** — grep-confirmed un-built: **no `normSq_mul` /
  norm-multiplicativity / `‖x*x‖=‖x‖²` law** exists in `CDNorm.lean` (the `cdNormSq` readout exists, but
  is not welded to the involution or the spectral radius). The one structural identity that *defines* a
  C*-algebra (vs a bare `*`-algebra) is absent. DROPPED (named open target).
- **A Hilbert space / inner product / GNS representation** — absent (no inner-product vector space in
  `lean/E213`; closest is `CDNorm`'s `cdNormSq` + `cdConj`, a norm with conjugation, no completion).
  The same Hilbert gap `quantum_mechanics.md`/`measure.md` located. CONCEPTUAL.
- **Named `CstarAlgebra` / `GNS` / `Gelfand` / `HilbertSpace` / `state` objects** — grep-confirmed
  ABSENT (only 3 incidental string matches, none a C*/GNS/Gelfand/Hilbert object: `ArityForcingGeneral.lean:18`
  "Hilbert-ε" comment, `PhaseChiralBridge.lean:18` docstring, `MultSystem.lean` comment).
  PREDICTED-NOT-BUILT, as the task anticipated.
- **General `d>1` / infinite-dimensional self-adjoint spectral theorem** (orthonormal eigenbasis, the
  spectral measure / continuous functional calculus) — absent; the `d=2` symmetric spectral theorem
  (`disc_symmetric_nonneg`) is the worked, certified instance. PARTIAL / inherited from `spectral.md`.

### Verified buildable witness (named, not asserted)

The nearest concrete promotion target the legs already support: a **`d=2` commutative C*-toy** — a
commutative sub-`*`-algebra of `Mat2` (e.g. the diagonal/symmetric matrices, where `cdConj` is the
transpose-conjugate and `mul` commutes), with its two real eigenvalues (`disc_symmetric_nonneg` gives
`disc≥0`, so `σ ⊆ ℝ`) as the two-point spectrum `X = {λ₁, λ₂}`, and the Gelfand map `M ↦ (λ₁, λ₂) ∈ ℝ²`
realized as the two evaluation characters `χᵢ(M) = λᵢ` (each `χ(MN)=χ(M)χ(N)` by `det2_mul`-style on the
commuting pair). This would weld `disc_symmetric_nonneg` (real spectrum) + `det2_mul` (the
multiplicative character) into a literal *finite* Gelfand `A ≅ C(X)` with `|X|=2` — the discrete `q=+1`
shadow of Gelfand–Naimark, parallel to the 2-vertex Laplacian toy (`graph_theory.md`) and the 2×2 GOE
toy (`random_matrix.md`). Flagged as buildable; **not yet built** this session (not asserted as an
anchor).
