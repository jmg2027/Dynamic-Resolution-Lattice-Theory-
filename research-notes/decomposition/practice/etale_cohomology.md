# Decomposition: étale cohomology + the Weil conjectures (ℓ-adic cohomology of varieties over 𝔽_q, the Frobenius action, the zeta function Z(X,t)=∏_x(1−t^{deg x})^{−1}, rationality / functional equation / Riemann Hypothesis |α|=q^{w/2} (Deligne), the Lefschetz trace formula #X(𝔽_q)=Σ(−1)ⁱ tr(Frob|Hⁱ))

*A FRESH decomposition per `../README.md` (model v7.1). Unlike `motives.md` (names the `⟨C|L⟩` half) or
`homological_algebra.md` (names the `Residue(L,C)` half), this entry is a **CONVERGENCE note**: étale
cohomology + the Weil conjectures is not a new decomposition target so much as **three already-decomposed
threads meeting on one object** (a variety over a finite field). The hypothesis to **test, not re-skin**:

> Étale/Weil = (1) `lefschetz_degree.md`'s **trace-weighted alternating diagonal** + (2)
> `zeta_euler.md`/`modular_forms`'s **×↦· Euler product over points** + (3) `motives.md`'s **ℓ-adic
> realization Lens on the universal motive** — converging on varieties over 𝔽_q, with the Weil RH being the
> **q=±1 WEIGHT made an eigenvalue-magnitude purity constraint**, and the functional equation the **q=±1
> reflection** (Poincaré duality Hⁱ↔H^{2n−i}, the same s↔k−s reflection as `modular_forms.md`). NO new
> primitive: it is the character arrow + the trace-diagonal + the motive, all on 𝔽_q-varieties, with the
> arithmetic **Frobenius** = the self-map whose fixed points are the 𝔽_q-points — and that Frobenius is
> the SAME per-prime `q=±1` local involution the corpus already builds (`FP2SqrtD.fp2dFrob`).*

This is the strongest convergence the notebook has reached: a single classical object (Z(X,t) over 𝔽_q)
that is, simultaneously, three of the calculus's already-grounded readings, with the deepest theorem
(Deligne's RH) being the q=±1 weight tag forcing eigenvalues onto a circle.

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a **variety X over 𝔽_q together with its arithmetic Frobenius self-map `F`**, read
  as a cochain complex. Two read-off axes, exactly as in `lefschetz_degree.md`/`motives.md`:
  1. the **cohomology complex** — Hⁱ_ét(X̄, ℚ_ℓ), the same simplicial/cochain nesting every cohomology note
     reads (`homological_algebra.md`'s `C`, `Delta/Core.delta`), carrying a **fold-height** (the
     cohomological degree i = the weight grading w) and a **direction/orientation bit `q=±1`** (the
     alternating sign (−1)ⁱ);
  2. the **arithmetic Frobenius `F : X → X`** (`x ↦ x^q` on coordinates), read as a **self-endomorphism**
     against the diagonal Δ — the SAME self-pointing shape `lefschetz_degree.md` reads (`f ∩ Δ`,
     `OneDiagonal`'s `f : A → A → B`). The crucial arithmetic fact: **the fixed points of `Fⁿ` are exactly
     the 𝔽_{qⁿ}-points** — `X(𝔽_{qⁿ}) = Fix(Fⁿ)` — because `x^{qⁿ}=x` ⟺ `x ∈ 𝔽_{qⁿ}`. The corpus builds
     this very Frobenius at the per-prime field level: `FP2SqrtD.fp2dFrob p x = (a, p−b)` is the conjugation
     σ on 𝔽_{p²}=𝔽_p[√D] (`σ(a+b√D)=a−b√D`), the degree-2 local Galois Frobenius, with `fp2dFrob_involution`
     (σ²=id, the q=±1 per-prime involution) and `fp2dMul_self_frob` (x·σ(x)=Norm — the norm via Frobenius).

- **Reading `L` — THREE readings of one `C`, the convergence:**
  - **`L_Leff` (the Lefschetz trace, alternating-summed down the height)** — `#X(𝔽_q) = Σ_i (−1)ⁱ
    tr(F* | Hⁱ)`. This is `lefschetz_degree.md`'s `L_χ↓` *verbatim*: the **trace** = the additive `×↦+`
    character `tr=e₁=Σλ` (`Mat2Spectrum.tr_eq_e1`), the **(−1)ⁱ** = `homology.md`'s q=±1 orientation bit
    (`simplex_face_euler_zero`, `dsq_zero`), and the self-map `F` whose `∩Δ` is counted is the Frobenius.
    "Count 𝔽_q-points" = "count Frobenius fixed points" = the trace-weighted diagonal intersection. So the
    Lefschetz trace formula for Frobenius is the **arithmetic instance** of the topological Lefschetz number,
    `F` replacing a general self-map.
  - **`L_Z` (the zeta function, the ×↦· Euler product over points)** — `Z(X,t) = ∏_{x∈|X|} (1−t^{deg x})^{−1}
    = exp(Σ_{n≥1} #X(𝔽_{qⁿ}) tⁿ/n)`. The Euler product over closed points IS `zeta_euler.md`'s generating
    reading: weight the whole construction-family (here the closed points of X) by a multiplicative kernel
    and product. `zeta_euler.md`'s thesis — `Σ = ∏` is the distributive law of the faithful coordinate
    (`summatory_mul`, `dconv_mul`), the local factor a geometric series (`geom_sum`) — applies term for
    term: each point contributes `(1−t^{deg x})^{−1}`, the geometric series of its powers, and the product
    over points is `modular_forms`/`zeta_euler`'s ×↦· generating function. The point-count zeta and the
    arithmetic ζ are the same `L_Z` reading at different bases.
  - **`L_ét` (étale cohomology = the ℓ-adic realization Lens)** — Hⁱ_ét(X̄, ℚ_ℓ) is `motives.md`'s ℓ-adic
    realization: a Lens `L` on the universal motive `C`, factoring through it
    (`view_factors_through_morphism`), one of the Betti/de Rham/ℓ-adic readings of the same motive
    (`lensIso_iff_kernel_eq` the comparison isos). Étale cohomology is the reading that makes `L_Leff` and
    `L_Z` computable: the Frobenius acts on each Hⁱ, its eigenvalues are the αᵢ, and the trace formula
    expresses the point-count through them.

- **Residue — the `q=±1` tag, here read THREE ways at once (the convergence's payoff):**
  - **q=−1 escape** — Frobenius fixed-point-free behavior / the obstruction residue Hⁱ for 0<i<2n (the
    "interesting" cohomology, the cycle-not-coboundary `NonzeroBetti` shape).
  - **q=+1 converge** — H⁰=ℚ_ℓ and H^{2n}=ℚ_ℓ(−n) (the trivial/top cohomology, the contractible/exact poles),
    and the eigenvalue-magnitude *purity* circle (below).
  - **★ The Weil RH as the q=±1 WEIGHT made spectral** — Deligne's theorem `|α| = q^{w/2}` for every
    Frobenius eigenvalue α on Hʷ. The fold-height **w** (the cohomological degree = the weight grading,
    `isPart_wf`) is read off as a **magnitude constraint**: the eigenvalues sit on a circle of radius
    `q^{w/2}`, *forced* by the weight. This is "purity" — the eigenvalue magnitude is determined by the
    cohomological weight (the height axis). The q=±1 unimodular bit (`multiplier_unimodular`, |q|=1) is here
    promoted: `|α/q^{w/2}| = 1`, the unit circle, the eigenvalue's *direction* free, its *magnitude* pinned
    by the height. The functional equation `Z(X,1/qⁿt) = ±q^{...}t^{...}Z(X,t)` is the **q=±1 reflection** —
    Poincaré duality Hⁱ ≅ H^{2n−i} (the same s↔k−s height-reflection as `modular_forms.md`'s functional
    equation), the orientation bit flipping i ↔ 2n−i.

## Re-seeing — ⟨C | L⟩ ⊕ Residue (the three threads converging)

```
   X / 𝔽_q + Frobenius F     =  ⟨ cohomology complex Hⁱ + the self-map F | three readings ⟩
   X(𝔽_q) = Fix(F)            =  the Frobenius fixed points = f ∩ Δ  (OneDiagonal shape; FP2SqrtD's σ locally)
   #X(𝔽_q)=Σ(−1)ⁱtr(F*|Hⁱ)  =  L_Leff: lefschetz_degree.md's trace-weighted alternating diagonal, F = the self-map
       the trace tr(F*|Hⁱ)    =  the ×↦+ character e₁=Σλ                 (Mat2Spectrum.tr_eq_e1)
       the (−1)ⁱ              =  homology.md's q=±1 orientation bit       (simplex_face_euler_zero, dsq_zero)
       "≠0 ⟹ has a fixed pt"  =  Lawvere contrapositive                  (no_surjection_of_fixedpointfree)
   Z(X,t)=∏_x(1−t^{deg x})⁻¹  =  L_Z: zeta_euler/modular_forms's ×↦· Euler product over points
       the local factor       =  geometric series of point-powers        (geom_sum)
       Σ↔∏ over points        =  the faithful-coordinate distributive law (summatory_mul, dconv_mul)
   Hⁱ_ét(X̄,ℚ_ℓ)             =  L_ét: motives.md's ℓ-adic realization Lens on the universal motive
       realization = functor  =  a Lens factoring through C              (view_factors_through_morphism)
       comparison isos        =  two readings, equal kernel              (lensIso_iff_kernel_eq)
   rationality of Z(X,t)      =  Z = ∏ det(1−F*t|Hⁱ)^{(−1)^{i+1}} (the trace formula assembled = L_Z via L_Leff)
   ★ Weil RH |α|=q^{w/2}     =  the q=±1 WEIGHT (fold-height w) made an eigenvalue-magnitude PURITY circle
       weight w               =  the cohomological degree = fold-height   (isPart_wf)
       |α/q^{w/2}|=1          =  the unimodular q=±1 bit                   (multiplier_unimodular)
   functional equation        =  the q=±1 REFLECTION: Poincaré duality Hⁱ↔H^{2n−i} (modular_forms s↔k−s)
   the arithmetic Frobenius F =  x↦x^q; locally the per-prime σ on 𝔽_{p²}, σ²=id (FP2SqrtD.fp2dFrob_involution)
       x·σ(x) = Norm          =  the norm via Frobenius                   (FP2SqrtD.fp2dMul_self_frob)
```

| classical étale/Weil object | = the 213 reading | already in note | Lean anchor (grep-confirmed) |
|---|---|---|---|
| Lefschetz trace formula `#X(𝔽_q)=Σ(−1)ⁱtr(F*\|Hⁱ)` | `L_Leff`: trace-weighted alternating diagonal | `lefschetz_degree.md` | `tr_eq_e1`, `simplex_face_euler_zero`, `no_surjection_of_fixedpointfree` |
| `tr(F*\|Hⁱ)` | the `×↦+` character `e₁=Σλ` | `lefschetz_degree.md`, `spectral.md` | `Mat2Spectrum.tr_eq_e1` (`:115`) |
| the `(−1)ⁱ` alternating sum | q=±1 orientation bit | `homology.md`, `de_rham.md` | `simplex_face_euler_zero` (`:125`), `dsq_zero_universal_delta4` (`:41`) |
| Frobenius fixed pts = 𝔽_q-points | `f ∩ Δ` self-pointing the construction | `lefschetz_degree.md`, `cardinality.md` | `no_surjection_of_fixedpointfree` (`:51`); locally `FP2SqrtD.fp2dFrob` |
| arithmetic Frobenius `x↦x^q` (involution per prime) | the per-prime q=±1 local Galois conjugation | `galois_cohomology.md` (CFT local Frob) | `FP2SqrtD.fp2dFrob_involution` (`:220`), `fp2dMul_self_frob` (`:318`) |
| zeta `Z(X,t)=∏_x(1−t^{deg x})⁻¹` | `L_Z`: the `×↦·` Euler product over points | `zeta_euler.md`, `modular_forms.md` | `summatory_mul` (`:74`), `dconv_mul` (`:132`), `geom_sum` (`:30`) |
| étale Hⁱ = ℓ-adic realization | a Lens factoring through the universal motive | `motives.md` | `view_factors_through_morphism` (`:37`), `lensIso_iff_kernel_eq` |
| ★ Weil RH `\|α\|=q^{w/2}` | q=±1 WEIGHT made eigenvalue-magnitude purity | `motives.md` (Tate weight), `spectral.md` | `isPart_wf` (`:199`), `multiplier_unimodular` (`:86`), `residue_tag_two_poles` (`:228`) |
| functional equation | q=±1 reflection: Poincaré duality Hⁱ↔H^{2n−i} | `modular_forms.md` (s↔k−s) | `multiplier_unimodular`; (the reflection bit; FenchelMoreau antitone analogue) |
| motivic Galois / Frob conj. class | `Aut` of the universal Lens (q=+1) | `motives.md`, `noether.md` | `det_holonomy_eq_one` (`:136`) |

So **the Lefschetz trace formula, the zeta function, étale cohomology, and the Weil RH are FOUR readings
converging on one object** — and each reading is one the calculus already ran in a separate note. Étale/Weil
is the point where `lefschetz_degree.md` (the diagonal), `zeta_euler.md` (the Euler product), and
`motives.md` (the realization Lens) **meet on 𝔽_q-varieties**, with the RH being Invariant B's tag promoted
to a spectral magnitude constraint.

## LEVERAGE — does the convergence fall out, and what is built vs absent?

**Verdict: PREDICTION (the convergence is genuine and the legs are grounded) + substantial PARTIAL — the
named étale/Weil objects are ABSENT, but each of the three converging threads is grounded in built ∅-axiom
Lean, AND the arithmetic Frobenius (the new load-bearing piece) is BUILT at the per-prime field level
(`FP2SqrtD`, 32/0 PURE).** This is not a fourth re-skin of lefschetz/zeta/motives: the NEW datum is the
*convergence itself* — one object simultaneously being the trace-diagonal + the Euler product + the ℓ-adic
realization — plus the RH-as-purity reading (the weight tag made a magnitude constraint). Leg by leg, honest.

**(1) The Lefschetz trace formula for Frobenius IS `lefschetz_degree.md`'s trace-weighted diagonal —
GROUNDED, `F` instantiating the self-map.** `#X(𝔽_q)=Σ(−1)ⁱtr(F*|Hⁱ)` is `L_χ↓` with the self-map being
the arithmetic Frobenius. The three sub-legs are exactly `lefschetz_degree.md`'s, each PURE: the trace
`tr=e₁` (`Mat2Spectrum.tr_eq_e1`, `:115`, 9/0), the alternating `(−1)ⁱ` (`simplex_face_euler_zero`, `:125`,
10/0; `dsq_zero_universal_delta4`, `:41`, 5/0), and the diagonal/fixed-point engine
(`no_surjection_of_fixedpointfree`, `:51`, 11/0). The ARITHMETIC specialization — "fixed points of `F` =
𝔽_q-points" — is what makes Lefschetz count solutions over finite fields; the corpus grounds the Frobenius
self-map locally (leg 4). So `#X(𝔽_q)` is the diagonal intersection number `lefschetz_degree.md` reads,
with `F` the self-map and the q-power-fixed-points the diagonal hits.

**(2) The zeta function IS `zeta_euler.md`'s ×↦· Euler product over points — GROUNDED at the
finite/coprime-split + local-factor level.** `Z(X,t)=∏_x(1−t^{deg x})^{−1}` is the generating reading of
`zeta_euler.md`/`modular_forms.md`, the family being the closed points |X|. The `Σ↔∏` distributive law is
`summatory_mul` (`:74`) / `dconv_mul` (`:132`) (both PURE); the local factor `(1−t^{deg x})^{−1}` is the
geometric series `geom_sum` (`:30`, PURE) at ratio `t^{deg x}`. The only difference from the rational-prime
ζ of `zeta_euler.md` is the base: points of X over 𝔽_q rather than primes of ℤ — the same `L_Z` reading at
a different base (the `base` sub-parameter of the resolution axis, `padic.md`). So the zeta-of-a-variety is
not a new object — it is `zeta_euler.md`'s Euler product re-based to a 𝔽_q-variety.

**(3) Étale cohomology IS `motives.md`'s ℓ-adic realization Lens — GROUNDED as the realization-as-Lens
factorization.** Hⁱ_ét(X̄, ℚ_ℓ) is one of the Betti/de Rham/ℓ-adic readings of the universal motive,
factoring through it by `view_factors_through_morphism` (`Morphism.lean:37`, 3/0 PURE), the comparison isos
the kernel-equalities `lensIso_iff_kernel_eq` (`Unified.lean:64`). The "ℓ-adic" qualifier is a *base* choice
(the prime ℓ ≠ p at which coefficients are taken) — again the resolution `base` parameter. So étale
cohomology is `motives.md`'s realization Lens, instanced at the ℓ-adic base.

**(4) ★ The arithmetic Frobenius is BUILT at the per-prime field level — the new load-bearing piece.** This
is the genuinely new in-repo anchor this convergence note rests on (beyond re-citing lefschetz/zeta/motives).
`FP2SqrtD.fp2dFrob p x = (x.1 % p, (p − x.2 % p) % p)` (`:82`) is the Galois conjugation σ on 𝔽_{p²} =
𝔽_p[√D] — `σ(a+b√D) = a − b√D` — which is the degree-2 **arithmetic Frobenius** (the p-power map on the
field extension). The corpus proves it is a ring homomorphism (`fp2dFrob_add` `:248`, `fp2dFrob_mul` `:267`),
an **involution** `σ²=id` (`fp2dFrob_involution` `:220` — the q=±1 per-prime local character, the same
involution `SYNTHESIS §3` cites as "CFT Frob_p involution per prime"), and that `x·σ(x) = (Norm, 0)`
(`fp2dMul_self_frob` `:318` — the **norm via Frobenius**, the local point-count/norm relation). The whole
module is **32/0 PURE** (freshly scanned). The docstring even records the Frobenius–Legendre Lens:
`(√D)^p ≡ (D/p)·√D` — σ fixes √D iff D is a QR mod p (split) else flips it (inert) — the q=±1 split/inert
dichotomy of the local Frobenius, tying directly to `legendre_mul` (`:77`, the ×↦· character). So the
Frobenius self-map of leg 1 is not hand-waved: the corpus builds it for degree-2 extensions of every prime
field, with its involution (q=±1), its ring-hom (character) and its norm (x·σ(x)) all PURE.

**(5) ★ The Weil RH = the q=±1 weight made an eigenvalue-magnitude purity constraint — the deepest reading,
GROUNDED conceptually on the weight grading + the unimodular tag.** Deligne's `|α|=q^{w/2}` reads the
fold-height **w** (the cohomological weight, `isPart_wf` `:199`, 22/0 PURE — the well-founded degree
`motives.md` calls the Tate weight) as a *magnitude*: the eigenvalues lie on the circle of radius `q^{w/2}`.
This is the purity statement — the eigenvalue magnitude is *forced* by the cohomological weight (the height
axis), not free. In the calculus this is Invariant B's unimodular bit promoted: `multiplier_unimodular`
(`:86`, |q|²=1) is the discrete ±1 version; the Weil RH says `|α/q^{w/2}|=1`, the *continuous* unit circle,
the eigenvalue direction free but its magnitude pinned by the height. The functional equation (Poincaré
duality Hⁱ↔H^{2n−i}) is the q=±1 reflection, the same height-reflection s↔k−s as `modular_forms.md`. The
honest boundary: the eigenvalue *magnitude as a real number* `q^{w/2}` is a `Real213`-cut residue (the
spectral-existence-for-`disc<0` residue `spectral.md` locates) — the discrete weight grading is built
(`isPart_wf`), the magnitude-circle constraint is the reading, the real value `q^{w/2}` the located residue.

**Honest boundary — Lean-built vs absent.**
- *Lean-built (∅-axiom, scanned PURE):* (a) the **trace-weighted diagonal** — `Mat2Spectrum.tr_eq_e1` (9/0),
  `simplex_face_euler_zero` (10/0), `dsq_zero_universal_delta4` (5/0), `no_surjection_of_fixedpointfree`
  (11/0); (b) the **×↦· Euler product over points** — `summatory_mul`, `dconv_mul`, `geom_sum` (the
  finite/coprime-split + local-factor legs of `zeta_euler.md`); (c) the **realization-as-Lens** —
  `view_factors_through_morphism` (3/0), `lensIso_iff_kernel_eq`; (d) ★ the **arithmetic Frobenius** —
  `FP2SqrtD.fp2dFrob` + `fp2dFrob_involution`/`fp2dFrob_mul`/`fp2dFrob_add`/`fp2dMul_self_frob`
  (**32/0 PURE**, freshly scanned); (e) the **weight grading + q=±1 tag** for the RH reading — `isPart_wf`
  (22/0), `ResidueTag`/`multiplier_unimodular`/`residue_tag_two_poles` (55/0); (f) the **×↦· character +
  split/inert Frobenius** — `legendre_mul` (5/0), `det2_mul` (PURE), `det_holonomy_eq_one` (26/0).
- *Conceptual-only / the precise missing legs:* **the named étale/Weil OBJECTS are ABSENT.** Grep over
  `lean/E213` for `etale`/`Weil`(conjecture)/`zetaVariety`/`zeta_function`/`Deligne`/`RiemannHypothesis`/
  `WeilConjecture`/`pointCount`/`rationalPoint`/`countPoints`/`frobeniusEigen`/`num_points` returns **zero
  étale/Weil declarations** (the only `Weil` hits are the **Weil operator J = ⋆** of the Hodge-Riemann
  cluster, `HodgeRiemannJ.lean` — a *different* object, the signed Hodge star, NOT the Weil conjectures; the
  only `etale`/`Deligne`/`RiemannHypothesis` hits are zero / docstring mentions in `Foundations/Positivity`,
  `Foundations/ProofISALifts`). There is **no** `EtaleCohomology`/`Hⁱ_ét` object, **no** `Z(X,t)` zeta-of-a-
  variety, **no** `#X(𝔽_q)` point-count, **no** Frobenius action *on cohomology groups* `F* : Hⁱ→Hⁱ`
  (the same missing graded-functoriality leg as `lefschetz_degree.md`'s `f_*:Hⁱ→Hⁱ`), **no** Weil-RH
  eigenvalue-magnitude theorem, **no** functional-equation/Poincaré-duality object. This is the SAME shape
  as `motives.md`'s missing `Motive`/`WeilCohomology` and `lefschetz_degree.md`'s missing `Lefschetz`/
  `degree` object: every *converging leg* (trace-diagonal, Euler product, realization Lens, the Frobenius
  self-map, the weight/tag) is built and PURE; the **named étale/Weil objects that would weld them onto
  𝔽_q-varieties** are the located open legs.

So: **PREDICTION on the convergence (étale/Weil = the trace-diagonal + the ×↦· Euler product + the ℓ-adic
realization Lens, converging on 𝔽_q-varieties, with the RH = the q=±1 weight made eigenvalue-magnitude
purity and the functional equation = the q=±1 Poincaré reflection), cashed at the level of the three
already-grounded threads + the BUILT per-prime arithmetic Frobenius; PARTIAL because the
étale/zeta-of-variety/point-count/Frobenius-on-cohomology/Weil-RH OBJECTS are absent — the named open legs,
not hand-waves.**

## Revelation (collapse: étale/Weil = the convergence of three already-decomposed threads on 𝔽_q-varieties)

**Collapse — the Lefschetz trace formula, the zeta function, and étale cohomology are ONE object read three
ways, meeting on the variety-over-𝔽_q.** This is the convergence the entry exists to record. The same
`#X(𝔽_q)` is (i) the trace-weighted diagonal intersection (`L_Leff` = `lefschetz_degree.md`'s reading, `F`
the self-map), (ii) the n-th log-coefficient of the Euler product (`L_Z` = `zeta_euler.md`'s reading, points
the family), and (iii) computed through the Frobenius eigenvalues on étale cohomology (`L_ét` =
`motives.md`'s ℓ-adic realization Lens). Rationality of `Z(X,t)` IS the assembly
`Z = ∏_i det(1−F*t|Hⁱ)^{(−1)^{i+1}}` — the trace formula (`L_Leff`) packaged as the Euler product (`L_Z`)
through the realization (`L_ét`). The three threads are not three theorems an identity relates; they are one
`⟨C|L⟩` read with three Lenses, all of which the calculus has already grounded separately.

**Collapse 2 — the character is read a SIXTH way, on a 𝔽_q-variety.** `lefschetz_degree.md` read the
`tr`/`det` character a fifth way (summed down the height against a self-map). Étale/Weil reads it on the
*arithmetic* self-map (the Frobenius), with the per-prime local Frobenius being the corpus's BUILT q=±1
involution σ (`FP2SqrtD.fp2dFrob_involution`) — σ²=id the unimodular bit, x·σ(x)=Norm the norm-character,
σ split/inert ⟺ (D/p)=±1 the `legendre_mul` ×↦· character. So the Frobenius is the character arrow's
arithmetic self-map, and the trace formula reads it down the cohomological height.

**Residue-surfaced — the Weil RH is the q=±1 tag made a SPECTRAL magnitude constraint.** The deepest single
finding: Deligne's `|α|=q^{w/2}` is Invariant B (the q=±1 residue tag) promoted from a discrete ±1 bit to a
continuous magnitude pinned by the fold-height. The weight **w** (`isPart_wf`, the height axis = the Tate
weight of `motives.md`) is read off as the *radius* of the circle the eigenvalues sit on; the unimodular bit
(`multiplier_unimodular`, |q|=1) becomes `|α/q^{w/2}|=1`. "Purity" = "the eigenvalue magnitude is forced by
the cohomological weight" = "the q=±1 tag is read as a magnitude graded by the height." The functional
equation is the q=±1 reflection (Poincaré duality Hⁱ↔H^{2n−i}), the same s↔k−s height-reflection as
`modular_forms.md`. So the hardest theorem in the cluster (Deligne's RH) is the calculus's weight tag read
spectrally — not a new primitive, the height axis × the unimodular bit made a magnitude constraint.

**EXTEND by convergence; no new axis.** The interior model v7.1 holds: étale/Weil are the character arrow
(Invariant A, both modes: `tr` additive in `L_Leff`, the Euler product multiplicative in `L_Z`) × the q=±1
residue tag (Invariant B, made a magnitude constraint by the RH) × the realization Lens (`motives.md`) ×
the diagonal engine (`lefschetz_degree.md`), read across {fold-height (the weight w / the (−1)ⁱ grading),
direction (the orientation bit / the Poincaré reflection), resolution+base (the ℓ-adic base, the 𝔽_q base)}.
The one genuine cluster of absences — the étale/zeta-of-variety/Frobenius-on-cohomology/Weil-RH objects — is
located precisely: the variety-over-𝔽_q twin of `lefschetz_degree.md`'s missing graded bundle and
`motives.md`'s missing `WeilCohomology` object. Every converging leg is built and PURE (including, newly, the
arithmetic Frobenius at `FP2SqrtD`, 32/0); only the named objects welding them onto 𝔽_q-varieties are open.

## Note for the technique

- **Étale/Weil is the notebook's sharpest CONVERGENCE datum.** Where `motives.md`/`homological_algebra.md`
  were *reflexive* (the calculus naming its own halves), this entry is *convergent*: three previously-
  separate decompositions (`lefschetz_degree.md`, `zeta_euler.md`, `motives.md`) turn out to be three
  readings of one classical object. The lesson: the calculus predicts that a field which "ties together" the
  trace formula, the zeta function, and a cohomology theory should decompose as *exactly those three already-
  grounded readings on one `C`* — and étale/Weil does, with no fourth primitive.

- **The Weil RH sharpens Invariant B: the q=±1 tag has a CONTINUOUS magnitude form.** SYNTHESIS records the
  tag as a discrete ±1 bit (`multiplier_unimodular`). Deligne's purity shows the tag's natural continuous
  form: the eigenvalue magnitude `q^{w/2}` *graded by the fold-height w*. So the unimodular bit and the Weil
  weight are one object — the residue's multiplier read discretely (±1) or as a height-graded magnitude
  (`q^{w/2}`). The named target this predicts: a `WeilWeight`/`purity` reading welding `isPart_wf` (the
  height) to `multiplier_unimodular` (the unit-circle constraint) — the magnitude-circle as the height-graded
  version of the ±1 tag.

- **The arithmetic Frobenius is the corpus's CONCRETE handle on the Weil cluster.** Unlike
  `lefschetz_degree.md` (whose self-map is abstract), étale/Weil's self-map is built: `FP2SqrtD.fp2dFrob` is
  the degree-2 local Frobenius σ for every prime, with σ²=id (q=±1), σ a ring-hom (character), x·σ(x)=Norm
  (the norm via Frobenius), and σ's split/inert behavior = `legendre_mul`'s ×↦· QR character. The buildable
  witness this names: a **`fp2dFrob`-fixed-point count** = "#fixed points of σ^n on 𝔽_{p²}" tied to the
  geometric-series local zeta factor, and the **`(√D)^p ≡ (D/p)·√D` Euler relation** as a Lean theorem (the
  Frobenius–Legendre bridge, currently only in the docstring) — a toy "Lefschetz/zeta for the 1-point
  variety Spec 𝔽_{p²}" with the Frobenius being `fp2dFrob`. Not built this session; flagged as the located
  target, the arithmetic analogue of `lefschetz_degree.md`'s proposed trace-weighted-Lawvere witness.

---

## Verified Lean anchors (file:line:theorem — all grep/Read-verified on `lean/E213`; purity via `tools/scan_axioms.py`, run from repo root this session)

| Leg | Theorem (file : line : name) | Status |
|---|---|---|
| ★ **arithmetic Frobenius σ on 𝔽_{p²} (the self-map whose fixed pts = 𝔽_q-points), involution = q±1** | `Lib/Math/NumberTheory/ModArith/FP2SqrtD.lean:82 fp2dFrob` (`σ(a+b√D)=a−b√D`); `:220 fp2dFrob_involution` (σ²=id); `:248 fp2dFrob_add`, `:267 fp2dFrob_mul` (σ a ring-hom); `:318 fp2dMul_self_frob` (`x·σ(x)=Norm`) | **∅-axiom PURE, scanned 32/0** ✓ |
| ★ **Lefschetz trace summand = `×↦+` character `tr=e₁=Σλ`** | `…/Real213/Mat2/Mat2Spectrum.lean:115 tr_eq_e1`; `:103 det_eq_e2`; `:204 det_tr_split_is_e1_e2` | **PURE, scanned 9/0** ✓ |
| ★ **the `(−1)ⁱ` alternating sum = q±1 orientation bit** (`L(id)=χ`) | `Lib/Physics/Simplex/FaceTerms.lean:125 simplex_face_euler_zero`; `Lib/Math/Cohomology/Delta/V4Capstone.lean:41 dsq_zero_universal_delta4` | **PURE, scanned 10/0, 5/0** ✓ |
| ★ **`#X(𝔽_q)=Fix(F)` = the diagonal/Lawvere engine** (fixed-point-free ⟹ residue) | `Lens/Foundations/OneDiagonal.lean:51 no_surjection_of_fixedpointfree`; `:43 lawvere_fixed_point` | **PURE, scanned 11/0** ✓ |
| ★ **zeta `Z(X,t)=∏_x(...)` = the `×↦·` Euler product over points** (Σ↔∏ + local geometric factor) | `Lib/Math/NumberTheory/SummatoryMultiplicative.lean:74 summatory_mul`; `…/DirichletMultiplicative.lean:132 dconv_mul`; `…/GeometricSeries.lean:30 geom_sum` | **∅-axiom PURE** ✓ |
| ★ **étale Hⁱ = the ℓ-adic realization Lens** (a Lens factoring through the universal motive) | `Lens/Compose/Morphism.lean:37 view_factors_through_morphism`; `Lens/Unified.lean:64 lensIso_iff_kernel_eq` | **PURE, scanned 3/0** ✓ |
| ★ **Weil RH `\|α\|=q^{w/2}` = the q±1 WEIGHT (fold-height) made an eigenvalue-magnitude constraint** | `Theory/Raw/Lambek.lean:199 isPart_wf` (the weight grading); `Lib/Math/Foundations/ResidueTag.lean:86 multiplier_unimodular` (`\|q\|=1`), `:228 residue_tag_two_poles`, `:180 golden_is_converge` | **PURE, scanned 22/0, 55/0** ✓ |
| split/inert Frobenius = the `×↦·` QR character; motivic-Galois Aut (q+1) | `…/ModArith/LegendreMultiplicative.lean:77 legendre_mul`; `…/Real213/Markov/SternBrocotMarkov.lean:104 det2_mul`; `…/ModularGeometry/HolonomyLattice.lean:136 det_holonomy_eq_one`, `:313 first_loop_is_the_fold` | **PURE (legendre_mul 5/0; det_holonomy 26/0; det2_mul PURE)** ✓ |
| the residue = the non-surjected diagonal (faithful, never total); the q±1 tag two poles | `Lens/Foundations/FlatOntologyClosure.lean:61 object1_not_surjective`, `:47 object1_injective` | **PURE, scanned 7/0** ✓ |
| cross-frame | `lefschetz_degree.md` (the trace-weighted diagonal, `L_χ↓`), `zeta_euler.md`/`modular_forms.md` (the ×↦· Euler product), `motives.md` (the ℓ-adic realization Lens, the Tate weight), `galois_cohomology.md` (the CFT local Frobenius), `homology.md`/`de_rham.md` (the (−1)ⁱ / ∂²=0), `spectral.md` (eigenvalue magnitude = `Real213` residue) | prior, ∅-axiom ✓ |

**Fresh purity scans (this session, `tools/scan_axioms.py` from repo root):**
- `E213.Lib.Math.NumberTheory.ModArith.FP2SqrtD` — **32 pure / 0 dirty** (incl. `fp2dFrob`,
  `fp2dFrob_involution`, `fp2dFrob_add`, `fp2dFrob_mul`, `fp2dMul_self_frob`).
- Re-confirmed from neighbor sessions (grep-verified at the cited file:line this session): `tr_eq_e1`
  (`Mat2Spectrum:115`, 9/0), `simplex_face_euler_zero` (`FaceTerms:125`, 10/0),
  `dsq_zero_universal_delta4` (`V4Capstone:41`, 5/0), `no_surjection_of_fixedpointfree` (`OneDiagonal:51`,
  11/0), `view_factors_through_morphism` (`Morphism:37`, 3/0), `object1_not_surjective`/`object1_injective`
  (`FlatOntologyClosure:61,47`, 7/0), `isPart_wf` (`Lambek:199`, 22/0), `residue_tag_two_poles`/
  `multiplier_unimodular` (`ResidueTag:228,86`, 55/0), `legendre_mul` (`LegendreMultiplicative:77`, 5/0),
  `det_holonomy_eq_one` (`HolonomyLattice:136`, 26/0).

## Dropped / flagged (predicted-not-built — honest, grep-confirmed absent)

- **No étale cohomology / Weil-conjecture / zeta-of-variety OBJECT in `lean/E213`.** Grep (case-insensitive)
  for `etale`/`Weil`(conjecture)/`zetaVariety`/`zeta_function`/`Deligne`/`RiemannHypothesis`/`WeilConjecture`
  returns **zero étale/Weil declarations**. The only `Weil` matches are the **Weil operator J = ⋆** (the
  signed Hodge star) in the Hodge-Riemann cluster (`Cohomology/Hodge/HodgeRiemannJ.lean`,
  `HodgeConjecture/Pairing/HodgeRiemann.lean`) — a *different* object (a polarization/complex structure,
  J²=−I), NOT the Weil conjectures; plus prose mentions of "Weil RH" in `Foundations/Positivity.lean:18`
  and `Foundations/ProofISALifts.lean:101` (docstring shadows, no theorem). The only `Deligne`/`etale`/
  `RiemannHypothesis` hits are zero. Flagged predicted-not-built.
- **No point-count / Frobenius-on-cohomology object.** Grep for `pointCount`/`point_count`/`rationalPoint`/
  `countPoints`/`num_points`/`frobeniusEigen`/`weil_rh`/`weilConj` returns **zero**. There is no
  `#X(𝔽_q)` point-count, no `Z(X,t)` zeta, and — the precise missing leg shared with `lefschetz_degree.md`
  — **no induced Frobenius action `F* : Hⁱ→Hⁱ` on cohomology groups**, so the trace formula summands
  `tr(F*|Hⁱ)` cannot be assembled. The cohomology groups exist (`Cochain`, `delta`, `kerSizeDelta`, Betti
  numbers); the functorial self-map on them does not. Flagged predicted-not-built.
- **`Frobenius.lean` (`NumberTheory/ModArith/Frobenius.lean`) is NOT the arithmetic Frobenius.** Grep
  confirms it is the **Chicken-McNugget / numerical-semigroup Frobenius number** (`frobenius_representable`,
  `residue_hit` — the largest non-representable `Na+Mb`), unrelated to the Galois/arithmetic Frobenius.
  The relevant arithmetic Frobenius is `FP2SqrtD.fp2dFrob` (cited above). Flagged to avoid mis-citation.
- **The Weil-RH eigenvalue magnitude `q^{w/2}` as a real number — `Real213`-cut residue, located not built.**
  The discrete weight grading is built (`isPart_wf`) and the unimodular constraint is the ±1 tag
  (`multiplier_unimodular`); the real-valued magnitude `q^{w/2}` and the eigenvalue *existence* for the
  Frobenius spectrum are the same `Real213`/ℂ spectral-existence residue `spectral.md` locates (eigenvalue
  existence for `disc<0` is the q=−1 escape). Honest: the purity *reading* (magnitude forced by weight) is
  grounded; the real value is reached-by-none.
- **Buildable witness NAMED (not built this session):** a toy "Lefschetz/zeta for `Spec 𝔽_{p²}`" — the
  Frobenius-fixed-point count of `fp2dFrob`'s σⁿ tied to the geometric-series local zeta factor — plus the
  **Frobenius–Legendre bridge `(√D)^p ≡ (D/p)·√D` as a Lean theorem** (currently only in `FP2SqrtD`'s
  docstring, `:18-22`): σ fixes √D ⟺ (D/p)=+1 (split, q=+1) else flips it (inert, q=−1), welding
  `fp2dFrob` to `legendre_mul`. This is the arithmetic analogue of `lefschetz_degree.md`'s proposed
  trace-weighted-Lawvere witness; the pieces (`fp2dFrob` 32/0, `legendre_mul` 5/0, `geom_sum`) are all PURE,
  only the bridge theorem is open. Flagged as the located, verified-buildable target.
