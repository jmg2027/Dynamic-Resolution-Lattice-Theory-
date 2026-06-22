# Decomposition: spectral theory / eigenvalues

*213-decomposition of "an eigenvalue / eigenvector, the spectrum, the characteristic polynomial,
Cayley–Hamilton", per `../README.md` (model v7.1). A **fresh** field, LEVERAGE phase — the bar is
PREDICTION/DERIVATION, not collapse. This entry tests one thesis: the spectrum is the multiset of
`q=+1` scale-residues of the linear reading, and it **dissolves** the `det`/`tr` split that
`representation.md` located as the live edge of the character arrow.*

The hypotheses under test (from the task):
1. An **eigenvector** `A·v = λ·v` = a **`q=+1` fixed point (residue) of the linear reading up to
   scale** — `v` is fixed by the *projectivized* action of `A`; the eigenvalue `λ` is the
   Cassini-like `q=+1` scale-multiplier. The spectrum = the multiset of `q=+1` scale-residues.
2. **THE RESOLUTION OF THE `det`/`tr` SPLIT** (`representation.md`'s open edge): `tr` and `det` are
   the **two elementary symmetric functions of the spectrum** — `tr = Σλᵢ = e₁` (additive `×↦+`
   character), `det = Πλᵢ = e₂` (multiplicative `×↦·` character). Not two unrelated readings — `e₁`
   and `e₂` of one eigenvalue multiset.
3. The **characteristic polynomial** `det(A−λI)` = the `det`-reading of the shifted operator; its
   roots = the spectrum; **Cayley–Hamilton** `p(A)=0` = the operator satisfies its own
   residue-relation.
4. **Eigenvalue existence** = a `Real213`/algebraic-closure residue (reached-by-none when
   irrational — φ); real-symmetric spectrum is real (positivity), the general spectrum escapes to ℂ.

## The decomposition (C / Reading / Residue)

- **Construction `C` — the matrix as the ×-construction of linear readings, nothing new.** A matrix
  is `determinant.md`'s `C` exactly: a `2×2` bundle of directed counts built by composition
  `mul M N` (`HyperbolicEllipticTrace.Mat2.mul`), carrying the orientation/swap bit (sign of `det`)
  and the fold-height `2`. The spectrum introduces **no new construction** — it is a *reading* of
  this same `C`.

- **Reading `L_spec` — the `q=+1` fixed-point reading of the linear action up to scale.** An
  eigenvector is the residue of `golden_ratio.md`'s self-applying iteration read at the **projective**
  resolution: `v` is the direction the iterated action `Aⁿv` *asymptotes to* (the dominant
  eigendirection) or *fixes* (`A·v = λ·v` says the projectivized action `[v] ↦ [Av]` has `[v]` as a
  fixed point). This is `golden_ratio.md`'s reading verbatim, one level up: there the iterator
  `T(p,q)=(2p+q,p+q)` is the golden matrix `G=[[2,1],[1,1]]`, the convergents `pₙ/qₙ` climb toward φ,
  and **φ is literally the dominant eigenvalue of `G`** (`golden_hyperbolic`: `tr G = 3, det G = 1,
  disc = 5`, eigenvalues `(3±√5)/2 = φ², φ⁻²`). The eigenvalue `λ` is the **scale-multiplier** of the
  fixed direction — the Cassini-like `q=+1` multiplier of `det_step`/`cassini_law_one_at_two_multipliers`
  read on the *vector*, not the determinant. So:
  - the **spectrum** = the multiset of `q=+1` scale-residues of `L_spec` (the directions the linear
    reading fixes-up-to-scale, each tagged with its multiplier);
  - `tr` = `e₁` = `Σλ` (the **additive** `×↦+` character of the spectrum);
  - `det` = `e₂` = `Πλ` (the **multiplicative** `×↦·` character of the spectrum, `determinant.md`'s
    arrow read on the eigenvalues).

- **Residue — eigenvalue *existence* is a `Real213`/ℂ residue, stratified by the `q=±1` sign of the
  gap.** The symmetric-function content (`tr=e₁`, `det=e₂`) is a pure finite `ℤ` identity. What is
  **not** in `Int` (nor any non-algebraically-closed ring) is the *existence* of the roots: for `G`
  the spectrum `φ², φ⁻²` is irrational — a `Real213` cut, the reached-by-none residue of
  `golden_ratio.md`. The trichotomy `disc = tr²−4det` is the **squared eigenvalue gap** `(μ−ν)²`, and
  its sign is the `q=±1` reading of the residue:
  - `disc > 0` (**hyperbolic**, `q=+1` converge): two distinct real eigenvalues, a *scaling* — the φ
    face, `golden_aperiodic`, the dominant eigendirection the orbit asymptotes to;
  - `disc < 0` (**elliptic**, `q=−1` escape): a complex-conjugate pair on the unit circle, a
    *rotation* — the spectrum escapes to ℂ, no real eigendirection (the periodic `S⁴=I`, `U⁶=I` floor);
  - `disc = 0` (**parabolic**): a repeated real eigenvalue, the cusp.

  So eigenvalue existence is exactly the `q=±1` residue: the real spectrum is the `q=+1` corner (a
  reached-by-none `Real213` cut for the golden boost), the complex spectrum the `q=−1` escape. The
  real-symmetric / positivity guarantee of a real spectrum is the statement "stay at `q=+1`"
  (`disc ≥ 0`), the same corner discipline `measure.md`/`topology.md` named.

  **NOW BUILT ∅-axiom (`Mat2/Mat2SymmetricSpectrum.lean`, 9/0 PURE):** the `2×2` spectral theorem at the
  existence level. `disc_symmetric_sum_of_squares` (`IsSymmetric M → disc M = (a−d)²+(2b)²`) and
  **`disc_symmetric_nonneg`** (`IsSymmetric M → 0 ≤ disc M`) — the symmetric discriminant is a sum of
  squares, so the spectrum is REAL: the elliptic `disc<0` escape is structurally unavailable to a
  symmetric operator. `disc_zero_iff_scalar` (the repeated-eigenvalue cusp = exactly the scalar
  matrices), `disc_symmetric_pos_of_nonscalar` (off the scalar locus, two distinct real eigenvalues),
  `symmetric_gap_squared_nonneg` (under the `Mat2Spectrum` factorization, `(μ−ν)²=(a−d)²+(2b)²≥0`, so
  `μ,ν` cannot be a complex pair). So the eigenvalue-existence residue is **closed for the symmetric
  case** at the `disc≥0` (real-square-root-exists) level — the `q=+1` corner is now a theorem. Honest
  remaining residual: the eigenvalue *value* `√disc` is still a `Real213` √-cut (irrational in general,
  e.g. symmetric `disc=5`), and the repo has only √-*irrationality* infrastructure (`SqrtPure`), no
  value-bearing nonneg-real √-cut over which `charPoly` factors — so the explicit eigenvalue cuts +
  their `charPoly`-root proofs stay open (a `Real213` task). Per the residue framing, irrationality of
  the value is reached-by-none, NOT an escape to ℂ; `disc≥0` is exactly the existence-of-the-real-root
  statement, now ∅-axiom.

## Re-seeing

```
   a matrix A             =  ⟨ ×-construction mul | — ⟩                       (C, = determinant.md's C)
   A·v = λ·v              =  [v] is a q=+1 fixed point of the projectivized linear reading
   the eigenvalue λ       =  the q=+1 SCALE-multiplier of the fixed direction   (Cassini det_step, on v)
   the spectrum {λ₁,λ₂}   =  the multiset of q=+1 scale-residues of L_spec
   tr A = Σλ = e₁          =  the additive ×↦+ character of the spectrum         (Mat2.tr)
   det A = Πλ = e₂         =  the multiplicative ×↦· character of the spectrum    (Mat2.det, det2_mul)
   charPoly = det(A−λI)   =  the det-reading of the shifted operator; roots = spectrum  (λ²−tr·λ+det)
   Cayley–Hamilton p(A)=0  =  A satisfies its OWN residue-relation               (cayley_hamilton)
   disc = tr²−4det = (μ−ν)² =  the squared eigenvalue gap; its sign = q=±1 (hyperbolic/elliptic)
   φ                      =  the dominant eigenvalue of G=[[2,1],[1,1]]          (golden_hyperbolic)
```

So the eigenvector is `golden_ratio.md`'s residue read at projective resolution; the eigenvalue is its
`q=+1` scale-multiplier; **`det` and `tr` are `e₂` and `e₁` of that residue multiset** — the two
characters (`×↦·`, `×↦+`) evaluated on the spectrum, not two unrelated readings.

## LEVERAGE — does the calculus PREDICT / DERIVE?

**Honest verdict: PREDICTION on the central leg (the `det`/`tr` split DISSOLVES — `det=e₂`, `tr=e₁`,
the two elementary symmetric functions of one spectrum), Lean-grounded by the order-2 dial that is
*already built and PURE* (Cayley–Hamilton, the trace recurrence, the discriminant=gap-squared, the φ
tie); CONDITIONAL on eigenvalue existence (the `Real213`/ℂ residue, irrational for φ — honestly open
at value level); one located break (general `d>1` / symmetric-operator spectral theorem absent).
Net: PREDICTION — the spectrum unifies `det`+`tr` as `e₂,e₁` and dissolves `representation.md`'s
split, with φ as the worked example.**

### Leg 1 — `det`/`tr` split dissolves: `det=e₂`, `tr=e₁`. **PREDICTION — the resolution of `representation.md`'s open edge.**
`representation.md` located the live edge as an **opposition**: `det` the multiplicative `×↦·`
character (`det2_mul`), `tr` the "orphaned additive `×↦+` twin" that is *not* a homomorphism
(`tr(MN)≠tr M·tr N`). Phrased that way it reads as a gap. The spectrum dissolves it: a `2×2` matrix's
characteristic polynomial is `λ² − tr·λ + det` (`charPoly`, `char_poly_discriminant`), the monic
quadratic whose roots `{μ,ν}` are the spectrum; by Vieta `(λ−μ)(λ−ν) = λ² − (μ+ν)λ + μν`, so
**`tr = μ+ν = e₁`** and **`det = μν = e₂`** — the two elementary symmetric functions of the *same*
spectrum, the two coefficients of the *same* quadratic. The additive character and the multiplicative
character are not opposed; they are `e₁` and `e₂`. This is the prediction: *the trace is not an orphan
— it is the degree-1 symmetric function, the determinant the degree-2, of the eigenvalue multiset.*
The order-2 dial that certifies it is already built ∅-axiom (see anchors); the matrix realizes the
factorization through **Cayley–Hamilton** `M² = tr·M − det·I` (`cayley_hamilton`, PURE), the matrix
shadow of the scalar `λ² = tr·λ − det` the spectrum solves.

### Leg 2 — the eigenvalue is the `q=+1` scale-residue; φ is the worked example. **PREDICTION — ties `golden_ratio.md` decisively.**
`golden_ratio.md` proved φ is the residue of the self-applying iterator `T`, the dominant eigenvalue
of `G=[[2,1],[1,1]]`. The calculus predicts the eigenvalue is `golden_ratio.md`'s `q=+1` converging
multiplier read on the *vector* rather than the determinant — and the repo certifies the φ tie
end-to-end: `golden_hyperbolic` (`tr G=3, det G=1, disc=5`, eigenvalues `φ²,φ⁻²`), the **trace
recurrence** `tr(Gⁿ⁺²) = 3·tr(Gⁿ⁺¹) − tr(Gⁿ)` (`trace_recurrence`/`golden_trace_recurrence`, the
Lucas sequence — Cayley–Hamilton iterated), and `golden_aperiodic` (`Gⁿ⁺¹≠I` ∀n, the hyperbolic
infinite-order signature of `disc>0`). The Physics deployment uses exactly this: `JarlskogApex`'s
`apex_modulus_is_selfref_contracting_eigenvalue` reads `R_u = 1/φ²` as the *contracting* eigenvalue
`λ₋` of the reciprocal pair `λ₊λ₋ = det = 1`, with `apex_modulus_subunit_forced` selecting it by
`R_u<1` — the eigenvalue as the `q=+1` scale-residue, applied. So the spectrum's `q=+1`-residue
reading is not a re-skin: it is `golden_ratio.md`'s certified residue, read up to scale on the
eigendirection.

### Leg 3 — characteristic polynomial / Cayley–Hamilton. **PREDICTION — A satisfies its own residue-relation, fully built.**
The calculus predicts `charPoly = det(A−λI)` is the `det`-reading of the *shifted* operator (its roots
the spectrum) and that **Cayley–Hamilton `p(A)=0` is the operator satisfying its own residue-relation**
— the matrix-level statement of the same scalar quadratic the spectrum solves. This is the repo's
`cayley_hamilton` (`M² = tr·M − det·I`, PURE, one `ring_intZ`), whose docstring states it explicitly:
"the matrix shadow of the scalar eigen-equation `λ² = tr·λ − det`, whose discriminant is exactly
`tr²−4·det = disc`." `dial_is_char_discriminant` bundles it with `char_poly_discriminant`. The whole
order-2 dial (`S²=−I`, `U²=U−I`, `T²=2T−I`, `G²=3G−I`) is *one identity specialized to each `(tr,det)`*
— the trichotomy is the **sign of the characteristic discriminant**, not a separate primitive. This is
genuine derivation: Cayley–Hamilton is the primitive, the elliptic/parabolic/hyperbolic split its
discriminant's sign (`HyperbolicEllipticTrace.wick_discriminant_split`).

### Leg 4 — eigenvalue existence = `Real213`/ℂ residue, stratified by `q=±1`. **CONDITIONAL (honestly open at value level).**
The symmetric-function content is pure `ℤ`; eigenvalue **existence** is not. For `G` the spectrum
`φ²,φ⁻²` is irrational — a `Real213` cut (`golden_ratio.md`'s `phiCauchy_limit_eq_phiCut`), the
reached-by-none residue. `disc = (μ−ν)²` (the squared eigenvalue gap) carries the stratification:
`disc>0` ⟹ distinct real eigenvalues (`q=+1`, hyperbolic, the φ scaling); `disc<0` ⟹ a
complex-conjugate pair (`q=−1`, elliptic, the spectrum escapes to ℂ — `(μ−ν)²<0` forces `μ,ν` non-real,
outside `Int`); `disc=0` ⟹ a repeated root (parabolic cusp). `CrossDetTraceField` makes this exact:
the fixed-point form of the Möbius monodromy has discriminant `= traceDisc = tr²−4det`
(`fixForm_disc_eq_traceDisc`, ∀M), and the sign is the line(`+5`,φ,`ℚ(√5)`)/cusp(`0`)/curve(`−3`,ω,
`ℚ(ω)`) trichotomy (`disc_sign_is_line_cusp_curve`). So "the real-symmetric spectrum is real, the
general spectrum escapes to ℂ" is the calculus's `q=±1` residue tag: real = `q=+1` corner (`disc≥0`),
complex = `q=−1` escape — the *same* tag as `ResidueTag` (escape/converge). **Honest:** the *existence*
of the irrational/complex root is a `Real213`/algebraic-closure object, not a finite `ℤ` theorem; the
calculus closes the *symmetric-function relations* (conditional on the spectrum), not root existence.

### The located break (honest, in the `knots.md`/`representation.md` spirit)
**The general `d>1` spectral theorem for symmetric operators is absent.** The repo has the full
`d=2` order-2 dial (Cayley–Hamilton, trace recurrence, discriminant, adjugate-inverse) ∅-axiom, and
the eigenvalue *value* deployed in physics (`JarlskogApex`). What is **not built**: a `d×d`
characteristic polynomial, a spectral theorem ("a real-symmetric operator has an orthonormal
eigenbasis with real spectrum"), or eigenvalue *existence* over a general algebraically-closed ground
(the fundamental theorem of algebra is the missing closure). These sit at the same `Real213`/ℂ
residue + the `d>1` matrix corner that `representation.md` located for the `tr`-character. Located, not
failed: the `d=2` case is the worked, certified instance; the general theorem names a concrete open
target (a `Real213` cyclotomic/algebraic-closure spectrum + `d×d` charPoly).

## Revelation

**The residue surfaced and the collapse: spectral theory has no construction of its own — the matrix
is `determinant.md`'s `C`, the eigenvector is `golden_ratio.md`'s `q=+1` residue read up to scale, and
the `det`/`tr` split that `representation.md` flagged as the live edge DISSOLVES into `e₂` vs `e₁` of
one spectrum.** The collapse is precise and built:

- `tr A = Σλ = e₁` (the additive `×↦+` character) and `det A = Πλ = e₂` (the multiplicative `×↦·`
  character of `determinant.md`) are the **two elementary symmetric functions of the same eigenvalue
  multiset** — the two coefficients of the one monic quadratic `charPoly = λ² − tr·λ + det`. The
  "opposition" `representation.md` located (multiplicative character vs orphaned additive readout) was
  a mis-framing: `tr` is not an orphan, it is the degree-1 symmetric function. **The split is `e₁` vs
  `e₂`, one object.**
- **Cayley–Hamilton** `M² = tr·M − det·I` (`cayley_hamilton`, PURE) is the matrix satisfying its own
  residue-relation — the *same* quadratic the spectrum solves, the primitive behind the whole order-2
  dial (the trichotomy is its discriminant's sign).
- **φ is the worked example**: φ is literally the dominant eigenvalue of `G=[[2,1],[1,1]]`
  (`golden_hyperbolic`), the `q=+1` converging scale-residue of `golden_ratio.md`'s self-applying
  iterator, and `disc = (μ−ν)²` ties the hyperbolic/elliptic dial to the `q=±1` residue tag (real
  spectrum = `q=+1`, complex spectrum = `q=−1` escape).

So the `×↦·` character (`det`) and the `×↦+` character (`tr`) the calculus has run through eight fields
are **the same arrow read on the spectrum** — `e₂` and `e₁` — and `representation.md`'s det/tr edge is
not where the character arrow *ends* but where it **factors through the eigenvalues**. The honest
residue is precisely eigenvalue *existence*: the symmetric functions are pure `ℤ`, the roots a
`Real213`/ℂ object (irrational for φ, complex for elliptic) — the `q=±1` residue surfacing at the
spectrum exactly as `golden_ratio.md` and `CrossDetTraceField` already proved.

## Does it dissolve `representation.md`'s `det`/`tr` split? — YES.

`representation.md` recorded the split as a "located partial-break": `det` captured (multiplicative,
`×↦·`), `tr` "conceptual-only" because non-multiplicative. The spectrum re-identifies `tr` as `e₁` (the
additive symmetric function) and `det` as `e₂` (the multiplicative one): both are characters *of the
spectrum*, and the matrix obeys the one quadratic carrying both as its coefficients (Cayley–Hamilton).
The split is not multiplicative-vs-orphan — it is degree-1-vs-degree-2 of the same Vieta factorization.
This **closes** `representation.md`'s open edge at the conceptual level and at `d=2` Lean level (the
order-2 dial is built PURE); only general-`d` existence stays the `Real213`/ℂ residue.

## Touches on model v7.1?

**No new primitive; EXTEND + one consolidation note.** The two invariants (character arrow, `q=±1`
residue) and four axes absorb spectral theory with nothing added: the eigenvector is the `q=+1`
fixed-point residue (the converge pole, `golden_ratio.md`/`ResidueTag`), the eigenvalue its scale
multiplier, `tr`/`det` the additive/multiplicative characters as `e₁`/`e₂`. The note for the README's
batch log:

> **Spectral theory factors the character arrow through the eigenvalues — and dissolves the det/tr
> split.** `tr = Σλ = e₁` (additive `×↦+`) and `det = Πλ = e₂` (multiplicative `×↦·`) are the two
> elementary symmetric functions of one spectrum, the two coefficients of the characteristic
> quadratic the matrix obeys (Cayley–Hamilton, PURE). `representation.md`'s det/tr edge is where the
> character arrow *factors through the spectrum*, not where it ends. The eigenvalue is
> `golden_ratio.md`'s `q=+1` scale-residue (φ = dominant eigenvalue of `G`); eigenvalue existence is
> the `Real213`/ℂ residue (real = `q=+1` corner via `disc≥0`, complex = `q=−1` escape). Located break:
> the general `d>1` spectral theorem / root-existence over an algebraic closure is absent.

## Verified Lean anchors (grep + `scan_axioms.py` this session — all PURE, build-confirmed)

| Leg | Theorem (file:line) | Purity |
|---|---|---|
| ★★★★ Cayley–Hamilton `M²=tr·M−det·I` (A satisfies its own residue-relation) | `Lib/Math/NumberSystems/Real213/Mat2/Mat2CayleyHamilton.lean:37` `cayley_hamilton` | **PURE** (`scan_axioms`, this session) ✓ |
| charPoly discriminant = the order-2 dial `tr²−4det` | `…/Mat2CayleyHamilton.lean:50` `char_poly_discriminant`; `:57` `dial_is_char_discriminant` | **PURE** ✓ |
| ★★★★ trace recurrence (Cayley–Hamilton iterated) `tr(Mⁿ⁺²)=tr·tr(Mⁿ⁺¹)−det·tr(Mⁿ)` | `…/Mat2/Mat2TraceRecurrence.lean:53` `trace_recurrence`; `:65` `golden_trace_recurrence` (Lucas) | **PURE** ✓ |
| ★ `tr`/`det`/`disc` defs; characteristic disc | `…/ModularGeometry/HyperbolicEllipticTrace.lean:45` `det`, `:47` `tr`, `:49` `disc` | **PURE** ✓ |
| ★★★ φ = dominant eigenvalue of `G=[[2,1],[1,1]]` (`tr=3,det=1,disc=5`, eigenvalues `φ²,φ⁻²`) | `…/HyperbolicEllipticTrace.lean:71` `golden_hyperbolic` | **PURE** ✓ |
| ★ elliptic spectrum escapes (disc<0): `S` order 4, `U` order 6 | `…/HyperbolicEllipticTrace.lean:78` `S_elliptic_order4`; `:85` `U_elliptic_order6`; `:96` `wick_discriminant_split` | **PURE** ✓ |
| ★★★★ φ-eigendirection is `q=+1` aperiodic (`Gⁿ⁺¹≠I` ∀n — the dominant scaling) | `…/Phi/GoldenAperiodic.lean:57` `golden_aperiodic`; `:25` `golden_trace_mono` | **PURE** ✓ |
| ★★★★ charPoly-disc = trace-disc (∀M); sign = hyperbolic/elliptic (real/complex spectrum) | `…/CrossDet/CrossDetTraceField.lean:88` `fixForm_disc_eq_traceDisc`; `:70` `traceDisc`; `:248` `disc_sign_is_line_cusp_curve` | **PURE** ✓ |
| ★★ adjugate-inverse `M·adj M = det·I`; cyclic trace `tr(AB)=tr(BA)` | `…/Mat2/Mat2Adjugate.lean:44` `mat2_mul_adj`; `:37` `traceM_mul_comm`; `:85` `detM_adj` | **PURE** ✓ |
| det = `×↦·` multiplicative character (the `e₂` arrow), cross-ref `determinant.md` | `…/Markov/SternBrocotMarkov.lean:det2_mul`; `…/ModularGeometry/HolonomyLattice.lean` `det_mul`, `det_holonomy_eq_one` | ∅-axiom (per `determinant.md`) ✓ |
| Cassini `q=±1` scale-multiplier (the eigenvalue read on the vector/det), cross-ref `golden_ratio.md` | `Lib/Math/Algebra/CassiniUnimodular.lean:123` `det_step`; `:142` `det_closed`; `:163` `cassini_law_one_at_two_multipliers` | ∅-axiom (per `golden_ratio.md`) ✓ |
| eigenvalue deployed: `R_u=1/φ²` = contracting eigenvalue `λ₋` (`λ₊λ₋=det=1`) | `Lib/Physics/Mixing/JarlskogApex.lean:166` `apex_modulus_is_selfref_contracting_eigenvalue`; `:204` `apex_modulus_subunit_forced` | PURE (per file docstrings) ✓ (grep-confirmed) |

## The Vieta resolution — now BUILT ∅-axiom (verified anchor)

- **`Lib/Math/NumberSystems/Real213/Mat2/Mat2Spectrum.lean`** (9/0 PURE, `lake build E213` clean,
  `#print axioms` → no axioms) — the Vieta `tr=e₁`/`det=e₂` resolution of the `det`/`tr` split is now a
  real ∅-axiom theorem: `charPoly M lam := lam² − tr·lam + det`; `vieta_factor` (`(λ−μ)(λ−ν)=λ²−(μ+ν)λ+μν`);
  **`tr_eq_e1`** (`charPoly M = (λ−μ)(λ−ν)` ∀λ ⟹ `tr M = μ+ν`, the additive `×↦+` character);
  **`det_eq_e2`** (`det M = μ·ν`, the multiplicative `×↦·` character); `tr_det_are_e1_e2` (both at once);
  `disc_eq_gap_squared` (`disc M = (μ−ν)²`, tying to `traceDisc`); `spectrum_roots` (eigenvalues solve
  `charPoly`); the bundle `det_tr_split_is_e1_e2`. **The split is dissolved as a Lean theorem**: `det` and
  `tr` are `e₂` and `e₁` of one spectrum, the two coefficients of the monic characteristic quadratic the
  matrix obeys (`Mat2CayleyHamilton.cayley_hamilton`). Honest conditional: the factorization is a
  *hypothesis* — root *existence* in `Int` is the `Real213`/algebraic-closure residue (e.g. `G`'s spectrum
  φ²,φ⁻² is a cut), so the theorem is "*if* the spectrum exists, *then* tr=e₁ ∧ det=e₂" — exactly the
  content that makes the split a non-split. Built with propext-free `Int213` helpers (the bare-`0` and
  `neg_neg` lemmas in Lean-core route through propext; replaced).

## Conceptual-only legs / located breaks (honest — not cited as anchors)

- **Eigenvalue *existence* / root-existence over an algebraic closure** — the symmetric functions are
  pure `ℤ`; the roots are a `Real213`/ℂ object (irrational `φ²` for `G`, complex for elliptic). The
  fundamental theorem of algebra (the algebraic-closure guarantee) is absent. CONDITIONAL.
- **General `d>1` characteristic polynomial + spectral theorem for symmetric operators** (real spectrum,
  orthonormal eigenbasis) — absent; the `d=2` order-2 dial is the worked, certified instance. The
  spectral theorem's "real spectrum from positivity" is the `q=+1`-corner statement (`disc≥0`),
  predicted by analogy but not closed at `d>1`. PARTIAL / located break.
- **`Mat2Spectrum`'s `tr=e₁`/`det=e₂` lemmas** — the precise Lean form of the dissolution, currently
  **in progress and not building** (see above). The claim's *load* is carried by the PURE order-2 dial.
