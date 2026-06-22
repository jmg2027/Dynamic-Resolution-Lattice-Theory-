# Decomposition: symmetric functions / the ring Λ / λ-rings

*213-decomposition of "the ring Λ of symmetric functions; the bases — elementary `e_λ`, complete
homogeneous `h_λ`, power sums `p_λ`, monomial `m_λ`, Schur functions `s_λ`; Newton's identities
(`e ↔ p`); the Jacobi–Trudi formula; Λ = the universal λ-ring; the Hopf-algebra structure; the
relation to GL_n representations (Schur–Weyl); the characteristic map to symmetric-group characters",
per `../README.md` (model v7.1) and `../SYNTHESIS.md` (the two invariants; ESPECIALLY the
`det/tr = e₁/e₂` Vieta finding `Mat2Spectrum.det_tr_split_is_e1_e2`, the `cᵢ = eᵢ` Chern
generalization, the SIGNATURE `= eᵢ`, the recurring elementary-symmetric `eᵢ`). A **CONSOLIDATING
capstone**, not a fresh field: Λ is the field that **names the `eᵢ`** the corpus keeps rediscovering.
Sits directly atop `representation.md` (the character arrow's home; the `det`/`tr` split),
`characteristic_classes.md` (Chern `cᵢ = eᵢ` of curvature), `determinant.md`/`spectral.md`
(`det = e_n`, Vieta), `quadratic_forms.md` (signature = an `eᵢ`-style count), `hopf_algebras.md`
(Λ is a Hopf algebra; the convolution/co-fold structure), `parity.md` (the sign character),
`generating_functions.md` (the GF bases).*

**The thesis under test (the capstone):** the ring Λ of symmetric functions is the calculus's
**UNIVERSAL HOME of the elementary-symmetric `eᵢ`**. The `eᵢ` that recur across the corpus —
`det/tr = e₁/e₂` of a spectrum (`Mat2Spectrum.det_tr_split_is_e1_e2`), Chern `cᵢ = eᵢ` of curvature
(`characteristic_classes.md`), the signature (an `eᵢ`-style disc-sign count, `quadratic_forms.md`),
Vieta coefficients (`Mat2CayleyHamilton.cayley_hamilton`) — **ARE the elementary symmetric functions**,
and Λ is where they live universally. Concretely: Λ = the **×↦· character's coefficient ring** — the
`eᵢ` are the coefficients of `∏(1 + xᵢ t)` = the universal characteristic polynomial / universal `det`.
Newton's identities (`e ↔ p`) = the **×↦· ↔ ×↦+ character bridge** (`eᵢ` = the multiplicative/det
reading; `p_k = Σ xᵢ^k` = the additive/trace-power reading). Schur `s_λ` = the GL_n irreducible
characters (`representation.md`'s characters; Schur–Weyl = the rep-theory bridge). Λ as a Hopf algebra
(`hopf_algebras.md`) with the `e/h/p/s` bases = the character ring. **NO new primitive** — Λ is the
universal home of the `det/tr = eᵢ` pattern the corpus keeps rediscovering, the ×↦· character's
coefficient ring.

## The decomposition (C / Reading / Residue)

- **Construction `C` — the spectrum (an unordered multiset of values), nothing new.** A symmetric
  function takes `n` (or `∞`) indeterminates `x₁,…,x_n` and projects to a **permutation-invariant**
  readout — i.e. its operand is the *unordered multiset* `{x₁,…,x_n}`, which is exactly the **spectrum**
  the corpus already carries: the eigenvalue multiset `{μ,ν}` of a `Mat2` (`Mat2Spectrum`, factored via
  `hfac : charPoly M = (λ−μ)(λ−ν)`), the three roots `{a,b,c}` of `NewtonInequalities`, the curvature
  spectrum of `characteristic_classes.md`, the form's eigenvalues of `quadratic_forms.md`. The
  symmetric group `S_n` acting by relabeling the variables IS `groups.md`'s Aut-family on the index set;
  Λ's defining invariance (`f(x_{σ1},…) = f(x₁,…)`) is `noether`'s `q=+1` Aut-invariance applied to that
  relabeling action. So `C` introduces no construction: it is the spectrum + its `S_n`-relabeling Aut,
  both already in the model.

- **Reading `L` — the character of the spectrum, read in two bases that are one arrow's two
  directions.** Λ's bases are not parallel objects; they are the two directions of the character arrow
  (Invariant A) plus their cross-readings:
  - **`eᵢ` = the multiplicative ×↦· coefficient reading.** `eᵢ` = the coefficient of `t^i` in
    `∏ⱼ(1 + xⱼ t)` — *literally the universal characteristic polynomial / universal `det`*. For the
    2-element spectrum this is `e₁ = x₁+x₂` and `e₂ = x₁x₂`, which the repo proves are exactly `tr` and
    `det` (`Mat2Spectrum.tr_eq_e1` / `det_eq_e2`). For the 3-element spectrum it is `e₁=a+b+c`,
    `e₂=ab+bc+ca`, `e₃=abc` — **named verbatim in the module header** of `NewtonInequalities.lean` and
    used inline as `(a+b+c)`, `(ab+bc+ca)`, `abc` in `newton1`/`newton2` (no standalone `def eᵢ`). So the `eᵢ` are the
    `det`/`×↦·` character (`det2_mul`) read at every degree of one spectrum.
  - **`p_k = Σ xⱼ^k` = the additive ×↦+ power reading.** The power sums are the **trace-powers**:
    `p_1 = tr`, and generally `p_k = tr(M^k)` over the spectrum. This is the additive `×↦+` twin
    (`vp_mul`-style: additive on `⊕`/disjoint union of spectra). `p_1 = e₁ = tr` is the place the two
    readings *coincide* (degree 1), exactly `representation.md`'s observation that for 1-dim characters
    `tr = det =` the scalar.
  - **`h_λ`/`m_λ`/`s_λ` = cross-readings of the same spectrum.** `h_i` (complete homogeneous) = the
    coefficient reading of `∏ 1/(1−xⱼt)` (the *other* GF, `generating_functions.md`'s family-reading);
    `m_λ` (monomial) = the raw orbit-sum (the bare relabeling-orbit count); `s_λ` (Schur) = the GL_n
    irreducible character (`representation.md`'s `d>1` trace-character), the bialternant
    `s_λ = det(x_j^{λ_i+n−i}) / det(x_j^{n−i})` — a *ratio of two alternants* (numerator and the
    Vandermonde denominator).

- **Residue — two strata, tagged `q=±1`, exactly the `representation.md`/`characteristic_classes.md`
  pattern.**
  1. *The named ring Λ and its `s_λ`/Jacobi–Trudi machinery is the `Real213`/`d>1`-character residue.*
     The `eᵢ`/`p_k` at fixed small degree are built (`e₁,e₂` = `Mat2Spectrum`; `e₁,e₂,e₃` =
     `NewtonInequalities`); the **named** `Λ`, the universal `e_λ/h_λ/p_λ/m_λ/s_λ` bases as one graded
     ring, the Jacobi–Trudi determinant, and the λ-ring structure are ABSENT (grep-confirmed) — the
     predicted-not-built named object. The Schur `s_λ` specifically is the `d>1` trace-character that
     `representation.md` located as the precise `det`/`tr` break, plus the Vandermonde-determinant
     denominator that the repo does **not** have (`Combinatorics/Vandermonde.lean` is the *binomial
     convolution* identity, NOT the alternant `∏(xᵢ−xⱼ)`; see Dropped).
  2. *The `q=±1` sign character.* The alternating/sign reading `ε(σ)` (the determinant of the
     permutation, the antisymmetric companion of the symmetric `eᵢ`) is `parity.md`'s `L₂` into `{±1}`
     (`psign_mulPerm_hom`); it is what splits "symmetric" (`q=+1`, the `eᵢ`) from "antisymmetric"
     (`q=−1`, the Vandermonde alternant). The Jacobi–Trudi / bialternant lives on exactly this
     `q=±1` symmetric/antisymmetric split.

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   the variables x₁,…,x_n            =  the spectrum (unordered multiset)               (Mat2Spectrum's {μ,ν}; NewtonInequalities' {a,b,c})
   S_n relabeling invariance         =  groups.md Aut-family + noether's q=+1 invariance  (psign_mulPerm_hom; det_holonomy_eq_one)
   the ring Λ                        =  the ×↦· character's COEFFICIENT RING            (the universal home of det/tr=eᵢ — the NEW datum)
   elementary eᵢ = [tⁱ] ∏(1+xⱼt)     =  the universal det / char-poly coefficients      (det_tr_split_is_e1_e2; cayley_hamilton; NewtonInequalities e1/e2/e3)
       e₁ = Σxⱼ = tr                 =  the additive coefficient (degree-1 coincidence)  (Mat2Spectrum.tr_eq_e1)
       e₂ = Σxᵢxⱼ = det (2 vars)     =  the multiplicative coefficient                   (Mat2Spectrum.det_eq_e2)
       e_n = ∏xⱼ = det (n vars)      =  the full multiplicative ×↦· character            (det2_mul = c(E⊕F)=c(E)c(F))
   power sums p_k = Σxⱼ^k            =  the additive ×↦+ trace-power reading             (p_1=tr; vp_mul-style additivity on ⊕)
   Newton's identities (e ↔ p)       =  the ×↦· ↔ ×↦+ character bridge (det ↔ trace-power) (the SAME det/tr Vieta, generalized to all degrees)
   complete homogeneous h_i          =  [tⁱ] ∏ 1/(1−xⱼt) = the other family-GF           (generating_functions.md family-reading)
   monomial m_λ                      =  the bare relabeling-orbit count                  (groups.md orbit; the raw count-Lens)
   Schur s_λ                         =  the GL_n irreducible character (bialternant)     (representation.md's d>1 tr-character; ABSENT named)
   Jacobi–Trudi s_λ=det(h_{…})       =  Schur as a det of complete-homogeneous = a char-poly reading  (det reading; ABSENT)
   the sign/alternating character ε  =  parity.md's L₂ into {±1} (the q=−1 antisymmetric twin)  (psign_mulPerm_hom)
   Λ as a Hopf algebra              =  the character ring with co-fold Δ + antipode S    (hopf_algebras.md: conv/CoAppend213; mu_conv_one)
   the characteristic map ch: R(S_n)→Λ =  the rep-theory ↔ symmetric-function bridge      (representation.md's Σχ=0 / character corpus)
```

The single move: **symmetric functions are not a new edifice** — Λ is the universal **coefficient ring
of the ×↦· character** (the `eᵢ`), the additive `×↦+` twin gives the power sums `p_k`, and Newton's
identities are the `det/tr = eᵢ` Vieta relation the corpus already proved, read across all degrees. The
field NAMES the `eᵢ` the corpus keeps rediscovering and packages them as one universal ring.

## Re-seeing table (the unification)

| classical symmetric-function object | the calculus's reading | repo status |
|---|---|---|
| the spectrum `{x₁,…,x_n}` (Λ's operand) | the eigenvalue multiset / roots | **BUILT** (`Mat2Spectrum` `{μ,ν}` via `hfac`; `NewtonInequalities` `{a,b,c}`) |
| `S_n` relabeling invariance | `groups.md` Aut-family + `noether` `q=+1` invariance | **BUILT** (`psign_mulPerm_hom`, `det_holonomy_eq_one`) |
| ★ elementary symmetric `eᵢ` | the universal `det`/char-poly coefficient (the ×↦· character at degree `i`) | **BUILT for `e₁,e₂` (2 vars) and `e₁,e₂,e₃` (3 vars)** (`tr_eq_e1`, `det_eq_e2`, `NewtonInequalities`); general `n` structural |
| `e₁ = tr`, `e₂ = det` (2-var) | the `det/tr = e₁/e₂` Vieta split | **BUILT** (`det_tr_split_is_e1_e2`, 9/0) |
| power sums `p_k = Σxⱼ^k` | the ×↦+ additive trace-power twin | `p_1 = tr` **BUILT**; `p_k` as `tr(M^k)` structural |
| ★ Newton's identities `e ↔ p` | the ×↦· ↔ ×↦+ character bridge (`det` ↔ trace-power) | structural: the `det/tr` Vieta generalized; the closed-form `e↔p` recursion is the PREDICTION leg |
| Newton's *inequalities* `e₁²≥3e₂`, `e₂²≥3e₁e₃` | the SOS log-concavity of the `eᵢ` (3-var) | **BUILT** (`NewtonInequalities.newton1`, `newton2`, 5/0) |
| complete homogeneous `h_i` | the other family-GF `∏1/(1−xⱼt)` coefficient | `generating_functions.md` family-reading; no named `h_λ` |
| monomial `m_λ` | the bare relabeling-orbit count | `groups.md` orbit / count-Lens; no named `m_λ` |
| Schur `s_λ`, Jacobi–Trudi | the GL_n irreducible character / det of `h`'s | structural (= `representation.md`'s `d>1` `tr`-character); **ABSENT named** |
| the sign character `ε(σ)` / Vandermonde alternant `∏(xᵢ−xⱼ)` | `parity.md`'s `L₂` (`q=−1`) / the antisymmetric twin | `psign` **BUILT**; the alternant `∏(xᵢ−xⱼ)` **ABSENT** (the named `Vandermonde.lean` is the binomial convolution, not the alternant) |
| Λ as a Hopf algebra (`e/h/p/s` bases) | the character ring + co-fold `Δ` + antipode `S` | **BUILT unnamed** (`conv`/`CoAppend213`, `mu_conv_one`); named `Λ`-Hopf object ABSENT |
| the characteristic map `ch : R(S_n) → Λ` | the rep-theory ↔ symmetric-function bridge | structural: `representation.md`'s `Σχ=0` corpus; no named `ch` |
| Schur–Weyl duality (`GL_n ↔ S_n`) | two Aut-families reading one tensor space | structural / ABSENT |
| the named ring `Λ` / λ-ring / `s_λ`-basis | the universal coefficient ring | **ABSENT** (predicted-not-built; the located break) |

## Revelation (collapse + forcing + spine — the universal `eᵢ` home)

**Collapse — Λ is the universal home of the `eᵢ`; the corpus's scattered `eᵢ` are ONE object's
readings. This is the NEW datum (not a re-skin of `representation.md`/`characteristic_classes.md`).**
The corpus rediscovered the elementary symmetric functions in at least four independent fields:
- `det/tr = e₁/e₂` of a 2×2 spectrum (`Mat2Spectrum.det_tr_split_is_e1_e2`, the SYNTHESIS Vieta find);
- `e₁,e₂,e₃` of a 3-element spectrum, *named in the module header* of `NewtonInequalities.lean` (`e1=a+b+c`,
  `e2=ab+bc+ca`, `e3=abc`), with Newton's log-concavity inequalities proved ∅-axiom;
- Chern `cᵢ = eᵢ` of the curvature spectrum (`characteristic_classes.md`, `c(E)=det(I+Ω)`);
- the signature `(p,n)` of a quadratic form as the disc-sign `eᵢ`-style count over an eigenbasis
  (`quadratic_forms.md`; `disc = Πλ = det = e₂`).
Symmetric functions is the field that **names these as one universal object**: the `eᵢ` are the
coefficients of `∏(1+xⱼt)` — the *universal characteristic polynomial*, the universal `det` — and Λ is
the ring they generate. Every one of the corpus's `eᵢ` is `∏(1+xⱼt)`'s coefficient evaluated at a
particular spectrum (matrix eigenvalues, curvature eigenvalues, root triple, form eigenvalues). So
`determinant.md` (the `det` character), `spectral.md`/`representation.md` (`det/tr=e₁/e₂`),
`characteristic_classes.md` (`cᵢ=eᵢ`), `quadratic_forms.md` (signature/discriminant), and
`NewtonInequalities` **are all symmetric-function theory the whole time** — Λ is their universal
coefficient ring. This is the consolidating capstone: it names the universal object behind the
recurring `eᵢ`.

**Forcing — Newton's identities ARE the `det/tr = eᵢ` Vieta relation, forced as the ×↦· ↔ ×↦+ bridge.**
Newton's identity `p_1 = e_1`, `p_2 = e_1 p_1 − 2 e_2`, … relates the additive power sums `p_k` (the
`×↦+` trace-power reading) to the multiplicative elementary functions `eᵢ` (the `×↦·` det reading). For
the 2-element spectrum this is exactly the corpus's already-proved content: `p_1 = e_1 = tr`
(`tr_eq_e1`), and `p_2 = tr(M²) = e_1² − 2e_2 = tr² − 2det` is the trace half of Cayley–Hamilton
`M² = tr·M − det·I` (`cayley_hamilton`) traced. So Newton's identities are **not a new mechanism** —
they are the `det/tr = e₁/e₂` Vieta relation (`det_tr_split_is_e1_e2`) read across all degrees,
the `×↦· ↔ ×↦+` character bridge that runs through the whole corpus. `eᵢ` is the multiplicative
reading, `p_k` the additive reading, and Newton's identity is the forced translation between them — the
same arrow as `representation.md`'s `det`-vs-`tr`, now identified as the defining relation of a field.

**The `q=±1` spine (`SYNTHESIS.md` §3) on Λ.** The symmetric/antisymmetric split is the spine's two
poles on the relabeling action:
- the **symmetric** functions (`q=+1`, the `eᵢ`/`p_k`/`h_λ`/`s_λ`) are the relabeling-*invariant*
  reading — `noether`'s `q=+1` conserved character of the `S_n`-action;
- the **antisymmetric** companion (`q=−1`) is the **Vandermonde alternant** `∏(xᵢ−xⱼ)` and the sign
  character `ε(σ) = det` (the `q=−1` unimodular bit, `parity.md`'s `L₂`, `psign_mulPerm_hom`);
- the **Schur bialternant** `s_λ = (alternant)/(Vandermonde)` lives on exactly this `q=±1` quotient: a
  `q=−1` antisymmetric numerator divided by the `q=−1` antisymmetric denominator gives a `q=+1`
  symmetric result. So Schur functions sit at the `q=±1` ratio — the symmetric character recovered as a
  ratio of two antisymmetric alternants, the `signature_dichotomy` `q=±1` count of `quadratic_forms.md`
  in its sharpest form.

So symmetric functions = (the universal `eᵢ` home = the ×↦· character's coefficient ring, `det`/Vieta
universalized) + (Newton's identities = the `e↔p` = ×↦·↔×↦+ character bridge) + (Schur = the GL_n
characters, `representation.md`, on the `q=±1` alternant ratio) + (Hopf structure, `hopf_algebras.md`)
— **no new primitive**. It is the universal home of the `det/tr=eᵢ` pattern the corpus keeps
rediscovering.

## VALIDATE verdict — **EXTEND** (consolidating capstone: Λ = the universal `eᵢ` home; one PREDICTION leg; one located break)

No new primitive, no break in the interior. Symmetric functions slot entirely into the v7.1 model: `C` =
the spectrum + `S_n`-relabeling Aut (`groups.md`/`noether`, carrying direction/`q=±1` + fold-height/
degree), `L` = the bidirectional character (`eᵢ` = `det`/×↦· coefficient at each degree; `p_k` = the
×↦+ trace-power twin; `s_λ` = the `d>1` trace-character on the `q=±1` alternant ratio), `Residue` = the
named `Λ`/`s_λ`/Jacobi–Trudi/λ-ring object (the `d>1`-character + Vandermonde-alternant residue). It is
the **deepest consolidation in the notebook**: the `det/tr = e₁/e₂` Vieta find, the Chern `cᵢ=eᵢ`, the
signature, and the Newton e1/e2/e3 are now seen as readings of **one universal object** — Λ, the ×↦·
character's coefficient ring.

- **PREDICTION leg (honest):** the calculus *predicts* the form of the full Λ machine — `eᵢ` = the
  universal char-poly coefficient (forced by Vieta, closed for `n=2,3`), `p_k` = the additive twin
  (`p_1` closed), Newton's identities `e↔p` = the ×↦·↔×↦+ bridge (the 2-var case is
  `det_tr_split_is_e1_e2` + `cayley_hamilton` traced; the general-degree recursion is grounded by
  analogy, not independently closed), `s_λ` = the GL_n character (= `representation.md`'s `d>1`
  `tr`-character, conceptual), and the Hopf structure (= `hopf_algebras.md`'s built `conv`/`Δ`/`S`,
  with the bialgebra compatibility the same open F1). The `e₁,e₂` (2-var) and `e₁,e₂,e₃` (3-var)
  elementary functions are **closed**; general `n`, the `h/m/s` bases, and the `e↔p` recursion at all
  degrees are predicted-by-analogy.

- **Located break (the `representation.md`/`characteristic_classes.md` spirit):** the **named ring Λ**
  — a graded `Λ` with the `e_λ/h_λ/p_λ/m_λ/s_λ` bases, the **Jacobi–Trudi** determinant, the
  **Vandermonde alternant** `∏(xᵢ−xⱼ)` (genuinely absent — the repo's `Vandermonde.lean` is the
  binomial convolution `ΣC(m,k)C(n,r−k)=C(m+n,r)`, a name-collision, NOT the alternant), the Schur
  `s_λ` bialternant, the λ-ring operations, the characteristic map `ch`, and Schur–Weyl duality — is
  ABSENT (grep-confirmed). The Schur side is precisely the `d>1` trace-character `representation.md`
  located as the `det`/`tr` break, and the alternant is the same `Real213`/`d>1`-character residue.
  This is the same located break, not a new one.

## Verified Lean anchors (file:line:theorem) — all grep-confirmed, scans from repo root this session

**★ The elementary symmetric functions `eᵢ` of a spectrum (the central NEW collapse — the `eᵢ`
universalized):**
- `lean/E213/Lib/Math/Foundations/NewtonInequalities.lean:47` `newton1` (`3(ab+bc+ca) ≤ (a+b+c)²`,
  i.e. `e₁² ≥ 3e₂` for `e₁=a+b+c`, `e₂=ab+bc+ca`, the **3-variable elementary symmetric functions
  defined by name** in the module header §"elementary symmetric functions"); `:64` `newton1_doubled`;
  `:72` `newton2` (`3(a+b+c)abc ≤ (ab+bc+ca)²`, i.e. `e₂² ≥ 3e₁e₃` with `e₃=abc`); `:92`
  `newton2_doubled`. The Maclaurin remark (`:97`) states these ARE "the log-concavity (Newton)
  relations for the elementary symmetric functions in three variables." **PURE (5/0).**
- `lean/E213/Lib/Math/NumberSystems/Real213/Mat2/Mat2Spectrum.lean:103` `det_eq_e2`
  (`det M = μ·ν = e₂`, the multiplicative ×↦· coefficient); `:115` `tr_eq_e1` (`tr M = μ+ν = e₁`, the
  additive ×↦+ coefficient); `:204` `det_tr_split_is_e1_e2` (both + `disc=(μ−ν)²` + `spectrum_roots`,
  the `det/tr` split dissolved as the two elementary symmetric functions of one spectrum); `:167`
  `disc_eq_gap_squared`; `:186` `spectrum_roots`. **PURE (9/0).**
- `lean/E213/Lib/Math/NumberSystems/Real213/Mat2/Mat2CayleyHamilton.lean:37` `cayley_hamilton`
  (`M² = tr·M − det·I` = `M² = e₁·M − e₂·I`, the characteristic-polynomial / Newton-identity-`p_2`
  generator); `:50` `char_poly_discriminant`; `:57` `dial_is_char_discriminant`. **PURE (4/0).**

**The ×↦· character (`eᵢ` = the universal `det`) and the ×↦+ twin (power sums = trace-powers):**
- `lean/E213/Lib/Math/NumberSystems/Real213/Markov/SternBrocotMarkov.lean:104` `det2_mul`
  (`det(MN)=det M·det N`, the ×↦· arrow = `e_n` multiplicative). (per `determinant.md`)
- `lean/E213/Lib/Math/NumberTheory/PrimeValuation.lean:96` `vp_mul` (`vp(ab)=vp a+vp b`, the ×↦+
  additive character = the additivity of `p_k` on `⊕`). (per `characteristic_classes.md`/`exponential.md`)

**The `S_n` relabeling Aut-family + the sign/alternating character (the `q=−1` antisymmetric twin):**
- `lean/E213/Lib/Math/NumberTheory/ModArith/Zolotarev.lean:106` `mulPerm_comp` (Cayley: the family is
  an Aut-family); `:133` `psign_mulPerm_hom` (`psign(a·b)=psign a·psign b`, the sign character `ε(σ)`
  into `{±1}` = `parity.md`'s `L₂`, the `q=−1` unimodular bit underneath the Vandermonde alternant).
  (per `parity.md`/`representation.md`)
- `lean/E213/Lib/Math/NumberTheory/ModArith/LegendreMultiplicative.lean:77` `legendre_mul` (the order-2
  ×↦· character, the multiplicative companion). (per `representation.md`)

**The class-function / `q=+1` invariance (Λ's `S_n`-invariance):**
- `lean/E213/Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean:136`
  `det_holonomy_eq_one` (`noether`'s `q=+1` conserved character = the relabeling-invariance of a
  symmetric function). (per `representation.md`/`noether`)

**Λ as a Hopf algebra (the character ring + co-fold Δ + antipode S, per `hopf_algebras.md`):**
- `lean/E213/Lib/Math/NumberTheory/DirichletIdentities.lean:50` `mu_conv_one` (`μ∗1=ε`, the antipode
  axiom `S⋆id=ε` as a ∅-axiom theorem). **PURE (20/0).** (per `hopf_algebras.md`)
- `lean/E213/Meta/Nat/UnitList.lean:53` `append_comm` (the +-atom indistinguishability = the symmetric
  base case, `parity.md`'s scalar pole). (per `prime_factorization.md`)

**The `q=±1` residue tag (the spine, per `SYNTHESIS.md` §3):**
- `lean/E213/Lib/Math/Foundations/ResidueTag.lean:86` `multiplier_unimodular`; `:228`
  `residue_tag_two_poles`; `:180` `golden_is_converge`. **PURE (55/0).** (per `SYNTHESIS.md`)

**Scan tallies (`python3 tools/scan_axioms.py E213.<module>`, from repo root, this session):**
`NewtonInequalities` 5/0 · `Mat2Spectrum` 9/0 · `Mat2CayleyHamilton` 4/0 · `SchurInequality` 3/0
(name-collision; not Schur functions — see Dropped) · `PowerSums` 10/0 (name-collision; Faulhaber, not
symmetric power sums — see Dropped) · `Vandermonde` 13/0 (name-collision; binomial convolution, not the
alternant — see Dropped). All PURE, 0 DIRTY. (`det2_mul`, `vp_mul`, `mu_conv_one`, `psign_mulPerm_hom`,
`legendre_mul`, `ResidueTag` cited per neighbor notes, grep-confirmed at the lines above.)

## Dropped / flagged (honest)

- **The named ring `Λ` / λ-ring / `s_λ`-basis / Jacobi–Trudi / monomial `m_λ` / complete-homogeneous
  `h_λ` / characteristic map `ch` / Schur–Weyl — ABSENT, predicted-not-built.** grep over `lean/E213`
  (case-insensitive) for `symmetric_function`/`symmetricFunction`/`elementarySymmetric`/`Schur` (as
  Schur functions)/`Jacobi_Trudi`/`JacobiTrudi`/`monomial_symmetric`/`complete_homogeneous`/
  `lambdaRing`/`lambda_ring`/`powerSum`/`PowerSums` (as `p_k=Σxᵢ^k`) returns **no symmetric-function
  Lean object**. The named `Λ`/`s_λ`/Jacobi–Trudi/λ-ring objects are confirmed absent — the located
  break, the `d>1`-character + Vandermonde-alternant residue (the same boundary `representation.md`
  located at the `det`/`tr` split).
- **THREE name-collisions, flagged so they are NOT mistaken for symmetric-function content:**
  - `Lib/Math/Combinatorics/PowerSums.lean` (10/0 PURE) is **Faulhaber figurate sums** `Σ_{i≤n} i^k`
    (`gauss_sum`, `sum_odd`, `sum_squares`, `nicomachus`, `sum_fourth/fifth/sixth`) — NOT the
    symmetric-function power sums `p_k = Σ xⱼ^k`. A genuine ∅-axiom corpus, but a different object
    (sum over indices `i≤n`, not over a spectrum). Reported, not cited as a `p_k` anchor.
  - `Lib/Math/Combinatorics/Vandermonde.lean` (13/0 PURE) is the **binomial convolution identity**
    `Σ_k C(m,k)C(n,r−k) = C(m+n,r)` (`vandermonde`, `sum_choose_sq`) — NOT the Vandermonde
    *determinant/alternant* `∏(xᵢ−xⱼ)` that underlies Schur's bialternant. The alternant is genuinely
    ABSENT; the binomial identity is a different object. Reported, not cited as the alternant anchor.
  - `Lib/Math/Foundations/SchurInequality.lean` (3/0 PURE) is **Schur's inequality**
    `Σ x^t(x−y)(x−z) ≥ 0` — NOT Schur *functions* `s_λ`. (It IS a symmetric-polynomial inequality, so
    adjacent, but not the Schur basis.) Reported, not cited as a Schur-function anchor.
  - The many `Newton` grep hits in `Lib/Physics/AlphaEM/` and `Analysis/Cauchy/NewtonGregory` are
    **Newton's *method*** (root-finding) / the **Newton forward-difference basis** — NOT Newton's
    *identities* `e↔p`. The Newton's-*inequalities* content (`NewtonInequalities.lean`) IS the genuine
    elementary-symmetric object and is cited above.
- **`eᵢ` is grounded for `e₁,e₂` (2 vars) and `e₁,e₂,e₃` (3 vars) only.** `det_tr_split_is_e1_e2`
  closes `e₁,e₂` (2-var, `Mat2`); `NewtonInequalities` defines and uses `e₁,e₂,e₃` (3-var). The general
  `eᵢ` for `n` variables (the universal `∏(1+xⱼt)`) is grounded by analogy, not independently closed —
  stated as the open leg.
- **Newton's *identities* `e↔p` (as opposed to the inequalities) are grounded only via the 2-var
  Vieta + Cayley–Hamilton.** `p_1=e_1=tr` and `p_2=e_1²−2e_2=tr²−2det` (the trace of `cayley_hamilton`)
  are the 2-var case; the general-degree `e↔p` recursion is the PREDICTION leg, not a named theorem.
- **The bialgebra compatibility (Λ as a *bi*algebra, Δ an algebra map)** — ABSENT, the same open
  frontier F1 `hopf_algebras.md` located (`Δ_+ ⇄ Δ_×` distributivity). The `conv`/`CoAppend213`
  co-fold and the antipode `mu_conv_one` are built; the bialgebra law fusing them is the residual.
- **BUILT witness (this session):** the load-bearing collapse is already a set of `decide`/`ring`-grade
  theorems (`det_tr_split_is_e1_e2`, `cayley_hamilton`, `newton1`, `newton2`, all scanned PURE). The
  predicted additional witness — **Newton's identities**, the power-sum ↔ elementary-symmetric character
  bridge — is now **closed ∅-axiom** in `NewtonInequalities.lean`:
  - `newton_id_p2 : a²+b²+c² = (a+b+c)² − 2(ab+bc+ca)` (`p₂ = e₁p₁ − 2e₂`), and
  - `newton_id_p3 : a³+b³+c³ = (a+b+c)(a²+b²+c²) − (ab+bc+ca)(a+b+c) + 3abc` (`p₃ = e₁p₂ − e₂p₁ + 3e₃`),

  each a single `ring_intZ` identity, both `#print axioms`-clean (module now **7/0**, was 5/0). This is
  the genuine degree-2/degree-3 `×↦+ ↔ ×↦·` character bridge — the power sums `p_k` (additive trace-powers)
  written through the elementary `eᵢ` (multiplicative det-coefficients) — not a re-skin: Newton's identities
  are core symmetric-function theory, the degree-graded companion to the closed `newton1`/`newton2`
  log-concavity inequalities. The named ring Λ and the `e/h/p/m/s_λ` bases remain ABSENT (the `d>1` break).
