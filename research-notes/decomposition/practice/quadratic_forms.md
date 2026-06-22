# Decomposition: quadratic forms / the Witt ring

*213-decomposition of "a quadratic form `q`, its symmetric matrix, diagonalization, the signature
`(p,n)` = #positive − #negative eigenvalues, Sylvester's law of inertia, the discriminant, isotropy,
the Witt ring `W(k)` (forms mod hyperbolic planes), and Hasse–Minkowski local-global", per
`../README.md` (model v7.1) and `../SYNTHESIS.md` §2–§3 (the two invariants + the q=±1 disc-sign
trichotomy). A **fresh** field, LEVERAGE phase. Sits directly atop `spectral.md` (the spectrum, the
discriminant, `Mat2SymmetricSpectrum.disc_symmetric_nonneg`), `hyperbolic_geometry.md` (the disc-sign
trichotomy as the curvature sign), `determinant.md` (the discriminant = product of eigenvalues),
`integers.md`/K-theory (the difference-Lens group-completion), `parity.md` (the sign character), and
`padic.md`/`class_field_theory.md` (the local-global base-family).*

**Thesis under test:** a quadratic form is the calculus's **q=±1 signature — the disc-sign trichotomy
counted over an eigenbasis.** The signature `(p,n)` = the q=±1 tag applied per eigenvalue and summed
(positive eigenvalue = q+1, negative = q−1: the SAME disc-sign `spectral.md`/`hyperbolic_geometry.md`
read on `Mat2`). Sylvester = the q=±1 tag is reading-invariant. Diagonalization = the spectral
reading. The discriminant = the determinant (Π of eigenvalues = `det = e₂`, the ×↦· character; its
sign = the parity of `n`). The Witt ring `W(k)` = the group-completion (the integers'/K-theory's
difference-Lens) on the monoid of forms, mod the **hyperbolic plane = the q+1⊕q−1 cancelling pair**
(signature 0, the neutral element). Hasse–Minkowski = the local-global base-family. NO new primitive.

## The decomposition (C / Reading / Residue)

- **Construction `C` — the symmetric `Mat2`/cup ×-construction, nothing new.** A quadratic form `q` is
  carried by a symmetric matrix `M` (the polarization `B(x,y) = ½(q(x+y)−q(x)−q(y))`); this is exactly
  `determinant.md`/`spectral.md`'s `Mat2` ×-construction restricted to the symmetric locus
  (`Mat2SymmetricSpectrum.IsSymmetric`), or — in the cohomological instance — the **cup-pairing** on
  middle cohomology, `cup α β = α(a)·β(b) + α(b)·β(a)` (`CupPairing.cup`, the symmetric intersection
  form). The form introduces **no new construction** — it is a *reading* of the symmetric `Mat2`/cup
  bundle the spectral and Hodge clusters already use. The bilinear `B` carries `C`'s direction/swap bit
  (symmetry: `cup_symm_pointwise`, `B(x,y)=B(y,x)`) and fold-height (the rank).

- **Reading `L_sig` — the q=±1 disc-sign tag counted over the eigenbasis.** The form's content is read
  by diagonalizing (the spectral reading: pick an eigenbasis, get `q ≅ diag(λ₁,…,λ_d)`) and then
  **counting the disc-sign per eigenvalue**: each `λᵢ > 0` is tagged q+1, each `λᵢ < 0` q−1, and the
  **signature `(p,n)`** is their count (`p` = #q+1, `n` = #q−1). This is the q=±1 tag of
  `hyperbolic_geometry.md`/`spectral.md` — there read on *one* `Mat2` generator (the sign of
  `disc = (μ−ν)²`); here applied per eigenvalue of a `d`-dimensional form and **summed**. So:
  - the **signature** `(p,n)` = the multiset count of the disc-sign over the spectrum (q+1 vs q−1);
  - the **discriminant** `disc(q) = Πλᵢ = det M = e₂` = the multiplicative ×↦· character read on the
    spectrum (`determinant.md`/`spectral.md`'s `det = e₂`); its **sign = (−1)ⁿ** = the parity of the
    q−1 count (`parity.md`'s sign character on the form);
  - **Sylvester's law of inertia** = `(p,n)` is **independent of the diagonalization chosen** = the
    q=±1 tag is **reading-invariant** (the same `Lens.refines`-invariance the corpus uses for sign /
    det = ±1 across relabelings, `parity.md`/`equivalence.md`).

- **Residue, tagged q=±1.** Two strata.
  - **The signature itself is the q=±1 residue of the form, counted.** `disc≥0` (real spectrum, the
    q=+1 corner, `disc_symmetric_nonneg`) vs the indefinite/definite split is the disc-sign tag; the
    *anisotropic* part of `q` (the non-cancelling residue after removing hyperbolic planes) is the
    **Witt class** — the q=±1 surplus that survives group-completion. **Isotropy** (`∃ v≠0, q(v)=0`)
    is the **q=0 boundary** between the poles: a form is isotropic ⟺ it contains a hyperbolic plane
    (signature-`0` block) ⟺ the parabolic/semi-definite cusp of the trichotomy (`parab_nonorigin_zero`:
    a square form vanishing off the origin — the degenerate "zero away from 0" = the isotropic vector).
  - **The named `QuadraticForm`/`signature`-as-`(p,n)`-of-an-eigenbasis / `WittRing` / `HasseMinkowski`
    objects are ABSENT** at full generality (grep-confirmed below) — the disc-sign trichotomy is built
    AS quadratic forms (`signature_dichotomy`, `signature_trichotomy`, the cup signature `(1,1)`,
    `hodge_index_signature`), but a `d`-variable `QuadraticForm` type, a general `signatureOf`, and a
    `W(k)` group-completion *of forms* are not assembled. Predicted-not-built (the located break).

## Re-seeing — ⟨C | L_sig⟩ ⊕ Residue

```
   a quadratic form q          =  ⟨ symmetric Mat2 / cup-pairing | — ⟩          (C; IsSymmetric, CupPairing.cup)
   the matrix / polarization B =  the ×-construction's symmetric locus          (cup_symm_pointwise, B(x,y)=B(y,x))
   diagonalization q ≅ diag(λ) =  the SPECTRAL reading (eigenbasis)             (spectral.md; Mat2Spectrum)
   the signature (p, n)        =  the q=±1 disc-sign tag COUNTED over the spectrum  (#q+1, #q−1)
       λᵢ > 0  (positive)      =  q+1 (converge pole)                            (cup_plus_plus: cup(α₊,α₊)=2)
       λᵢ < 0  (negative)      =  q−1 (escape pole)                             (cup_minus_minus: cup(α₋,α₋)=−2)
       λᵢ = 0  (isotropic)     =  the q=0 boundary / hyperbolic / parabolic cusp (parab_nonorigin_zero)
   Sylvester's law of inertia  =  the q=±1 tag is READING-INVARIANT (∀ diagonalization)  (Lens.refines-inv.)
   the discriminant disc(q)    =  Πλ = det M = e₂, the ×↦· character; sign = (−1)ⁿ  (determinant.md; det=e₂)
   non-degeneracy              =  pos + neg = rank (no zero eigenvalue)          (hodge_index_full_rank, signature_full_rank)
   the hyperbolic plane H      =  the q+1 ⊕ q−1 cancelling pair, signature (1,1) = 0  (cup form [[0,1],[1,0]])
   the Witt ring W(k)          =  group-completion (difference-Lens) of forms mod H  (PairCompletionUniversal)
   Hasse–Minkowski local-global =  the per-prime base-family of completions       (padic.md base; FP2 per-prime Frob)
```

The single move: a quadratic form is **not a new object** — it is the symmetric `Mat2`/cup
×-construction read through `L_sig` = "diagonalize, then count the q=±1 disc-sign per eigenvalue". The
signature is the disc-sign trichotomy of `hyperbolic_geometry.md`/`spectral.md` **counted over an
eigenbasis** rather than read on one generator; Sylvester is its reading-invariance.

## Re-seeing table (the unification)

| classical quadratic-form object | the calculus's reading | repo status |
|---|---|---|
| the signature `(p,n)` of a form | `L_sig` = #q+1 vs #q−1 of the disc-sign over the spectrum | **BUILT (instances)** (`signature_one_one_witness`, `hodge_index_signature`, `signature` `(k,k)`) |
| diagonalization `q ≅ diag(λ)`, +/− eigenvector classes | the spectral reading; `α₊`/`α₋` with `cup(α₊,α₊)>0`, `cup(α₋,α₋)<0`, `cup(α₊,α₋)=0` | **BUILT** (`alpha_plus`/`alpha_minus`, `cup_plus_plus`/`cup_minus_minus`/`cup_plus_minus`) |
| Sylvester's law of inertia (signature is a complete real invariant) | the q=±1 tag is reading-invariant (`Lens.refines`-invariance) | **structural prediction** (cited in `signature_one_one_witness` docstring; no `∀`-diagonalization theorem) |
| the discriminant `disc(q)` = Πλ; sign = (−1)ⁿ | `det = e₂` = the ×↦· character on the spectrum (`determinant.md`); sign = parity of n | **BUILT** (`det=e₂` per `spectral.md`; `parity.md` sign character) |
| the definite/semidefinite/indefinite trichotomy | the disc-sign q=±1 trichotomy AS forms | **BUILT** (`signature_dichotomy`, `signature_trichotomy`, `golden_indefinite`, `eisenstein_norm_posdef`) |
| the hyperbolic plane `H` = signature (1,1) = the Witt-neutral | the cup form `[[0,1],[1,0]]`, eigenvalues `±1`, the q+1⊕q−1 cancelling pair | **BUILT** (`CupPairing` `[[0,1],[1,0]]`; `BalancedSignature` block = `(1,1)`, `hirzebruch=0`) |
| the Witt ring `W(k)` (forms mod `H`) | the difference-Lens group-completion of the form-monoid mod the q+1⊕q−1 neutral | **ABSENT** (engine built carrier-general: `PairCompletionUniversal`; no form-monoid fed in) |
| Hasse–Minkowski (isotropic over ℚ ⟺ over every ℚ_p and ℝ) | the local-global base-family of completions (the form read per prime) | **ABSENT** (per-prime base/Frobenius built: `padic`, `fp2Frob_involution`; no global assembly) |

## Revelation (collapse + forcing + the q=±1 spine)

**Collapse — the signature IS the disc-sign trichotomy counted; the hyperbolic plane IS the q+1⊕q−1
cancelling pair (the NEW datum).** Three previously-separate things are one:
1. `hyperbolic_geometry.md`/`spectral.md` read the **disc-sign on one `Mat2` generator** (the sign of
   `disc=(μ−ν)²`: hyperbolic/parabolic/elliptic = q−1/cusp/q+1). The signature `(p,n)` is *the same
   tag applied per eigenvalue of a `d`-form and summed* — this is the literal cup-form instance:
   `cup(α₊,α₊)=2>0` (q+1), `cup(α₋,α₋)=−2<0` (q−1), `cup(α₊,α₋)=0` (orthogonal), giving signature
   `(1,1)` (`signature_one_one_witness`, T²). The diagonalizing change-of-basis `P=[[1,1],[1,−1]]`
   carries `[[0,1],[1,0]]` to `diag(2,−2)` — diagonalization = the spectral reading made explicit.
2. The **hyperbolic plane** (the form `[[0,1],[1,0]]`, eigenvalues `±1`, signature `(1,1)`) is exactly
   the **q+1 ⊕ q−1 cancelling pair** — the Witt-ring neutral element. `BalancedSignature` makes this a
   theorem: a form built of `k` such blocks has signature `(k,k)` and **Hirzebruch `σ = pos−neg = 0`**
   (`signature_balanced`, `hirzebruch_zero`) — the signature-0 = Witt-trivial = the q-pair cancellation,
   stated as the balanced case the corpus already computes (T²ⁿ middle cohomology).
3. The **definite/semidefinite/indefinite** classification of binary forms is the SAME disc-sign
   trichotomy realized as forms: `goldenForm a b = a²−ab−b²` (disc `+5`) is **indefinite** (takes a
   negative value, `golden_indefinite`/`signature_dichotomy`, signature `(1,1)`); `eisForm a b =
   a²−ab+b²` (disc `−3`) is **positive-definite** (`eisenstein_norm_posdef`, signature `(2,0)`);
   `parabForm = (m−k)²` (disc `0`) is **semi-definite** with a non-origin zero (`parab_nonorigin_zero`)
   = the isotropic/degenerate cusp. `signature_trichotomy` bundles all three — the disc sign IS the
   form's signature class, and the parabolic cusp IS isotropy (the q=0 boundary).

So the geometric disc-sign trichotomy (`hyperbolic_geometry.md`), the spectral trichotomy
(`spectral.md`), and the arithmetic form classification (definite/indefinite/degenerate) are **ONE**
q=±1 reading — the signature is that tag *counted over an eigenbasis*.

**Forcing — the signature is FORCED to be reading-invariant, and the discriminant FORCED to be the
det character.** (i) `disc = tr²−4det` (binary) / `det M = Πλ` (general) is a pure ℤ polynomial in the
entries, so the discriminant is *forced* to be the ×↦· character on the spectrum (`det=e₂`), not a
chosen invariant; its sign is *forced* to be `(−1)ⁿ` (the parity of the q−1 count) — the `parity.md`
sign character. (ii) Sylvester's reading-invariance is *forced* by the same `Lens.refines`-invariance
that forces `det=±1` and `psign` to be relabel-invariant (`parity.md`/`equivalence.md`): a change of
diagonalizing basis is a `C`-preserving relabeling, and the q=±1 tag projects to a feature invariant
under it. (iii) `disc_symmetric_nonneg` *forces* a symmetric form's spectrum real (the elliptic q−1
escape is structurally barred for a symmetric `Mat2`), exactly Sylvester's "real eigenvalues" premise
— the real signature is the q=+1 corner.

**The q=±1 spine (`SYNTHESIS.md` §3) made the form's signature.** positive eigenvalue = q+1 (converge);
negative = q−1 (escape); the hyperbolic plane = one q+1 and one q−1 that cancel (signature 0, the Witt
neutral, the boundary the spine is symmetric about); isotropy = the q=0 marginal cusp (`parabForm`).
The Witt ring is the group-completion (the difference-Lens `L₋` carrier-polymorphic over the
form-monoid, the SAME `(m,n)↦m−n` arrow as ℤ from ℕ, K₀ from `(iso-classes,⊕)`) **modulo the q+1⊕q−1
neutral** — the signature `p−n` (the Hirzebruch `σ`) being the surviving difference-Lens readout, the
exact analogue of "negative = pair-swap" in `integers.md`.

So a quadratic form = (the q=±1 signature = disc-sign counted over eigenvalues) + (Sylvester = its
reading-invariance) + (Witt ring = group-completion mod the q+1⊕q−1 hyperbolic) + (Hasse–Minkowski =
the local-global base-family) — **no new primitive**.

## VALIDATE verdict — **EXTEND** (deep consolidation: signature = the disc-sign tag counted; two PREDICTION legs; two located breaks)

No new primitive, no interior break. Quadratic forms slot into v7.1: `C` = the symmetric `Mat2`/cup
×-construction (direction/q=±1 + fold-height carried), `L_sig` = the disc-sign tag counted over the
spectrum, `Residue` = the anisotropic Witt class, tagged q=±1. It is a **decisive consolidation**: the
disc-sign trichotomy that `spectral.md` and `hyperbolic_geometry.md` recorded on one generator is now
the **signature counted over a `d`-dimensional eigenbasis**, with the hyperbolic plane revealed as the
q+1⊕q−1 Witt-neutral and the definite/indefinite/degenerate split as the same trichotomy AS forms — all
Lean-grounded at the instance level (`signature_one_one_witness`, `hodge_index_signature`,
`signature_trichotomy`, the `(k,k)` balanced block).

- **PREDICTION leg 1 — Sylvester's law of inertia as a `∀`-diagonalization theorem.** Grounded
  conceptually (the q=±1 tag is `Lens.refines`-invariant, the same invariance carrying `det=±1`/`psign`)
  and at the instance altitude (the docstring of `signature_one_one_witness` *invokes* Sylvester to fix
  `(1,1)` from two orthogonal classes + `dim=2`). The calculus *predicts* a general "signature is
  independent of the diagonalizing basis"; the `∀`-basis theorem (a `signatureOf` invariant of a general
  `QuadraticForm` type) is the named open leg.
- **PREDICTION leg 2 — the Witt ring `W(k)` as a built group-completion of forms.** The engine is built
  and **carrier-polymorphic** (`PairCompletionUniversal.invert_is_the_universal_group_completion`,
  `lift_unique`, 19/0, `Quot`-free, full universal property — the difference-Lens at an arbitrary
  `CommCancelSemigroup`). The calculus *predicts* `W(k)` is this engine at the carrier
  `(forms, ⊕)` mod the hyperbolic neutral — the exact analogue of ℤ at `(ℕ,+)` and K₀ at
  `(iso-classes,⊕)`. The named `WittRing`/form-monoid object that feeds the engine is absent (the same
  shape as the K-theory entry: engine built, object-monoid not fed in).

- **Located break 1 (the `knots.md`/`spectral.md` spirit) — no general `QuadraticForm` / `signatureOf`
  / `WittRing` object.** grep over `lean/E213` for `QuadraticForm`/`WittRing`/`Sylvester`/`HasseMinkowski`/
  `signatureOf` returns no `d`-variable form type, no Sylvester `∀`-theorem, no Witt group-completion of
  forms — only the BUILT *instances* (cup signature, Hodge index, the binary disc-sign forms). The
  general `d>1` spectral theorem (eigenbasis existence over a general ground) is the same `Real213`/
  algebraic-closure residue `spectral.md` located. Predicted-not-built.
- **Located break 2 — Hasse–Minkowski local-global is ABSENT.** grep for `HasseMinkowski`/`local_global`/
  `adele`/`idele` returns nothing. What IS built is the **base-family** the calculus predicts assembles
  it: the per-prime completion family (`padic.md`'s `vp`-indexed completions, the resolution `base`
  parameter of v7), and the per-prime q±1 local character `fp2Frob_involution` (the Frobenius
  involution per prime, the local sign-decision). The *global assembly* ("isotropic over ℚ ⟺ over ℝ and
  every ℚ_p") is the same global bundle `class_field_theory.md` located as absent (the Artin/idele
  bundle) — predicted-not-built, the local-global base-family is the engine.

## Verified Lean anchors (file:line:theorem) — all grep-confirmed, scans from repo root

**The signature = the disc-sign counted over an eigenbasis (the central NEW collapse):**
- `lean/E213/Lib/Math/Cohomology/Surfaces/T2Minimal/Signature.lean:59` `signature_one_one_witness`
  — the cup-pairing on H¹(T²) admits q+1/q−1 orthogonal classes: `cup(α₊,α₊)=2` (`:35` `cup_plus_plus`),
  `cup(α₋,α₋)=−2` (`:38` `cup_minus_minus`), `cup(α₊,α₋)=0` (`:41` `cup_plus_minus`), forcing signature
  `(1,1)` by Sylvester; `:25` `alpha_plus`, `:30` `alpha_minus` (the diagonalizing +/− eigenvectors).
  **PURE (7/0).**
- `lean/E213/Lib/Math/Cohomology/Surfaces/T2Minimal/CupPairing.lean:30` `cup` (the symmetric
  intersection form `[[0,1],[1,0]]` = the hyperbolic plane); `:47`–`:56` `cup_aa`/`cup_ab`/`cup_ba`/
  `cup_bb` (matrix entries `0,1,1,0`); `:63` `cup_symm_pointwise` (B symmetric, **PURE**). **8 PURE /
  1 DIRTY** — `:81` `cup_symm` is sealed-DIRTY (`Quot.sound` via `funext`, the function-valued-equality
  category; the math content is the PURE pointwise twin). Cited honestly.

**The general signature pair `(pos,neg)`, non-degeneracy, and the Hirzebruch σ (balanced/Witt-neutral):**
- `lean/E213/Lib/Math/Cohomology/HodgeConjecture/Pairing/KahlerGradeStructure.lean:142`
  `hodge_index_signature` (`(pos,neg) = (1+2·h²⁰, h¹¹−1)`, the signature pair from grade axioms); `:112`
  `hodge_index_full_rank` (`pos+neg = b₂`, non-degeneracy = no zero eigenvalue); `:90`/`:94`/`:98` `pos`/
  `neg`/`total_b2`; `:192` `hodge_index_master_theorem` (signature across ℙ², ℙ¹×ℙ¹, T²×T²). **PURE (5/0).**
- `lean/E213/Lib/Math/Cohomology/HodgeConjecture/Pairing/BalancedSignature.lean:78` `signature` (`(pos,neg)`);
  `:88` `signature_full_rank` (`pos+neg = total_rank`); `:94` `signature_balanced` (`pos=neg`); `:82`/`:98`
  `hirzebruch`/`hirzebruch_zero` (σ = pos−neg = 0, the q+1⊕q−1 cancellation = Witt-trivial = a sum of `k`
  hyperbolic blocks); `:146` `T2n_pattern_master_A` (signature `(k,k)` for T²ⁿ, n=1..5). **PURE (11/0).**

**The definite / semidefinite / indefinite trichotomy AS quadratic forms (the disc-sign = signature class):**
- `lean/E213/Lib/Math/Algebra/CayleyDickson/Integer/EisensteinSignature.lean:117` `signature_dichotomy`;
  `:108` `golden_indefinite` (`goldenForm 1 0 = 1 ∧ goldenForm 1 1 = −1`, disc `+5`, indefinite = sig
  (1,1)); `:98` `eisenstein_norm_posdef`, `:66` `eisForm_nonneg` (disc `−3`, positive-definite = sig
  (2,0)); `:49` `eisForm`, `:105` `goldenForm`, `:41` `sq_nonneg`. **PURE (13/0).**
- `lean/E213/Lib/Math/Algebra/CayleyDickson/Integer/ParabolicSignature.lean:71` `signature_trichotomy`
  (indefinite line / semi-definite cusp / definite curve, bundled); `:50` `parab_nonneg`, `:56`
  `parab_nonorigin_zero` (`parabForm 1 1 = 0`, disc `0`, the isotropic/degenerate q=0 boundary); `:46`
  `parabForm`. **PURE (4/0).**

**The disc-sign trichotomy on the generator (ties to `spectral.md`/`hyperbolic_geometry.md`):**
- `lean/E213/Lib/Math/NumberSystems/Real213/CrossDet/CrossDetTraceField.lean:248`
  `disc_sign_is_line_cusp_curve` (the line/cusp/curve = indefinite/degenerate/definite trichotomy);
  `:88` `fixForm_disc_eq_traceDisc` (the universal `formDisc(fixForm M) = tr²−4det`, ∀M). (per
  `hyperbolic_geometry.md`, 20/0 PURE.)
- `lean/E213/Lib/Math/NumberSystems/Real213/Mat2/Mat2SymmetricSpectrum.lean:83` `disc_symmetric_nonneg`
  (symmetric ⟹ disc≥0 ⟹ real spectrum — the q=+1 corner, Sylvester's "real eigenvalues" premise). (per
  `spectral.md`/`hyperbolic_geometry.md`, 9/0 PURE.)

**The discriminant = det = e₂ (the ×↦· character) + the sign character (parity of n):**
- `det = e₂` (`Πλ`, the multiplicative ×↦· character on the spectrum): `Mat2Spectrum.det_eq_e2`
  (per `spectral.md`); the sign character (parity = sign = relabel-invariant): `parity.md` /
  `lean/E213/Lib/Math/NumberTheory/ModArith/Zolotarev.lean:133` `psign_mulPerm_hom` (the order-2 ×↦{±1}
  character; the Legendre/QR multiplicativity `psign_mulPerm_qr`). (cross-ref, per `parity.md`/`spectral.md`.)

**The Witt ring = the carrier-polymorphic difference-Lens group-completion (engine built):**
- `lean/E213/Lens/Number/Nat213/Tower/PairCompletionUniversal.lean:215`
  `invert_is_the_universal_group_completion` (the universal group-completion of an arbitrary
  `CommCancelSemigroup`, `Quot`-free; `lift_unique` the uniqueness). **PURE (19/0).** The engine `W(k)`
  needs; the form-monoid is the absent input.

**The q=±1 tag (Invariant B) + the local-global base-family (Hasse–Minkowski engine):**
- `lean/E213/Lib/Math/Foundations/ResidueTag.lean:228` `residue_tag_two_poles`; `:86`
  `multiplier_unimodular` (the ±1 bit). **PURE (55/0).**
- `lean/E213/Lib/Math/NumberTheory/ModArith/FP2Sqrt5.lean:148` `fp2Frob_involution` (the per-prime q±1
  local Frobenius character — the local leg of the local-global family). **PURE (91/0).** (the global
  Hasse–Minkowski assembly is absent; the base-family is the engine, per `padic.md`/`class_field_theory.md`.)

**Scan tallies (`python3 tools/scan_axioms.py E213.<module>`, from repo root, this session):**
`T2Minimal.Signature` 7/0 · `T2Minimal.CupPairing` 8/1 (the lone DIRTY is `cup_symm`, sealed funext;
content PURE in `cup_symm_pointwise`) · `KahlerGradeStructure` 5/0 · `BalancedSignature` 11/0 ·
`EisensteinSignature` 13/0 · `ParabolicSignature` 4/0 · `PairCompletionUniversal` 19/0 · `ResidueTag`
55/0 · `FP2Sqrt5` 91/0. All PURE except the one sealed-DIRTY `cup_symm` (flagged below).

## Dropped / flagged (honest)

- **The general `QuadraticForm` / `signatureOf` / `WittRing` / `HasseMinkowski` objects — ABSENT,
  predicted-not-built.** grep over `lean/E213` for `QuadraticForm`/`WittRing`/`Sylvester`/`HasseMinkowski`/
  `local_global`/`adele`/`idele` returns **no Lean object** (only docstring mentions of Sylvester in
  `T2Minimal/Signature.lean` and the Hodge-index narrative). The `d>1` form type, the Sylvester
  `∀`-diagonalization theorem, the Witt group-completion *of forms*, and the global Hasse–Minkowski
  assembly are confirmed absent — the located breaks. The disc-sign trichotomy is built **as binary/cup
  forms** (instances), not as a general signature calculus.
- **`cup_symm` (function-valued symmetry) is sealed-DIRTY** (`Quot.sound` via `funext`) — NOT cited as a
  PURE anchor; the load-bearing symmetry is the PURE pointwise `cup_symm_pointwise`. The propext/funext
  1-categorical ceiling (`SYNTHESIS.md` §5.4) surfaces here exactly as in `measure.md`/`category_theory.md`.
- **`signature_mul`-style multiplicativity (the Witt-*ring* product, tensor of forms ↦ product of
  signatures)** is conceptual-only here — the ⊗-product structure on forms is not built; only the
  additive `⊕`-monoid (group-completion input) is named. The ring structure of `W(k)` is the open leg
  beyond the group-completion.
- **Hasse–Minkowski's exhaustiveness leg** (these completions are *all* of them, Ostrowski) is the same
  open exhaustiveness leg `padic.md` named — the base-family is built per prime, totality is not.
- **Verified buildable witness — NONE newly asserted.** Every cited fact is a grep-confirmed,
  scanned-PURE existing theorem (the cup signature `(1,1)`, the definite/indefinite/degenerate
  trichotomy, the `(k,k)` balanced block with σ=0, the group-completion engine). No new `decide` witness
  is proposed beyond the confirmed anchors. A natural buildable target the calculus predicts: a general
  binary-form `signatureOf (a,b,c)` reading off the sign of `disc = b²−4ac` and the sign of `a` into a
  `(p,n)` pair, with `signature` of the hyperbolic block `= (1,1)` — a `decide`-checkable consolidation
  of the three trichotomy files into one `signatureOf`, predicted closable but not asserted closed here.
