# Decomposition: Iwasawa theory (the cyclotomic ℤ_p-extension K_∞=∪K_n, the Iwasawa algebra Λ=ℤ_p[[T]], Λ-modules, the class-number growth |Cl(K_n)|~p^(μpⁿ+λn+ν), the characteristic ideal, the Main Conjecture)

*A FRESH, deep decomposition per `../README.md` (model v7.1) and `SYNTHESIS.md`'s two invariants (the
character arrow `×↦·`/`×↦+`, the `q=±1` residue tag). It sits at the join of three neighbors:
`padic.md` (KEY — the p-adic resolution, the `base` sub-parameter on `L_res`),
`generating_functions.md` (Λ=ℤ_p[[T]] = the power-series semiring `PowerSeriesSemiring`),
`class_field_theory.md` + `galois_cohomology.md` (JUST DONE — the class group as an idele/H¹-style residue),
`modular_forms.md` (the L-function, the Euler product, p-adically). The thesis under TEST, not re-skin:*

> **Iwasawa theory is the calculus's p-adic resolution TOWER (`padic.md`'s `base`=p axis run as a
> ℤ_p-tower), with the class number = a residue read at each level, packaged as a power series (the
> modulus made into Λ=ℤ_p[[T]]).** Four legs:
> 1. **K_∞=∪K_n** = `padic.md`'s p-adic resolution ASCENDED into a tower — the SAME resolution-iteration
>    as the spectral-sequence page-tower / RG iteration / completion-of-completions, here the ℤ_p-cyclotomic
>    tower, with the level index `n` the `(ℕ,+)`-graded resolution count (`ResolutionShift.IsResolutionShift_compose`).
> 2. **Λ=ℤ_p[[T]]** = the power-series semiring (`PowerSeriesSemiring.power_series_semiring`) — the completed
>    group ring = the modulus/approximant packaged as a formal series, the residue's finite signature
>    (continued-fractions' modulus doctrine) as a power series in `T`.
> 3. **|Cl(K_n)|~p^(μpⁿ+λn+ν)** = the residue read at level `n` (the class group = `galois_cohomology`'s
>    H¹-style obstruction / `class_field_theory`'s idele residue), its growth governed by the
>    characteristic-ideal invariants μ,λ,ν (the modulus's leading data).
> 4. **Main Conjecture (p-adic L = characteristic ideal)** = the character (`modular_forms`' L-function,
>    the `×↦·` Euler product, p-adically) EQUALS the residue's characteristic invariant — the **deepest
>    character=residue tie** in the notebook: the `×↦·` L-function = the `q=±1` residue's characteristic
>    signature.

**Headline, stated up front so the rest is honest.** This is a **PREDICTION with most legs prose-only**,
plus **two genuine grounded surprises and one located gap**. The *named Iwasawa objects* — `Iwasawa`,
`Lambda` / `ℤ_p[[T]]` as the completed group ring, `characteristicIdeal`, `mainConjecture`, `classNumber` /
`ClassGroup`-of-a-tower, `mu_invariant` / `lambda_invariant` — are **entirely ABSENT** (grep-confirmed:
zero hits for `Iwasawa`/`characteristicIdeal`/`mainConjecture`/`mu_invariant`/`lambda_invariant`). But the
*structural skeleton* is grounded harder than expected at two points: (a) the **tower** is built — the
completion-of-completions `CompletionTower` is the resolution tower returning home with the **modulus the
only thing that ascends**, and `ResolutionShift.IsResolutionShift_compose` proves the level grades **add**;
(b) the **power-series Λ** is built — `PowerSeriesSemiring.power_series_semiring` is a closed ∅-axiom formal
power-series semiring with `T`=`xVar` the grading generator. The class-number residue has a real ∅-axiom
toy (`EisensteinClassNumber.reduced_disc_neg3_unique` = `h(−3)=1`, class-number-one as a finite count); the
Main Conjecture is **prose-only** and the p-adic L-function is the **located gap** (the analytic/`Real213`
residue, exactly the boundary `modular_forms.md`/`zeta_euler.md` name for every infinite L-series). So:
**PREDICTION + located gap at the p-adic L-function.**

## The decomposition (C / Reading / Residue)

- **Construction `C` — the cyclotomic ℤ_p-tower of fields K_∞=∪K_n, which is `padic.md`'s
  approximant-sequence-with-modulus run as a TOWER.** `C` is the *same* shape as `padic.md`'s p-adic
  completion `C` — a refinement sequence whose digits/levels stabilize, with a modulus — but now **ascended
  into a ℤ_p-extension tower**: `K_0 ⊂ K_1 ⊂ … ⊂ K_n ⊂ … ⊂ K_∞`, `Gal(K_n/K_0) ≅ ℤ/pⁿ`,
  `Gal(K_∞/K_0) ≅ ℤ_p = lim ℤ/pⁿ`. Each level `K_n` is the p-adic resolution read at depth `n` (`padic.md`'s
  `ZpSeq.trunc x n`, the truncation to depth `n`); the tower is the *iteration* of that resolution, the
  literal `padic.md`-`base`=p axis ascended. This is the same `C` as: the spectral-sequence page tower
  (`spectral_sequences.md`, `E_{r+1}=H(E_r)`, the resolution re-entering as its own operand), the RG
  resolution-iteration, and the **completion-of-completions** the repo builds explicitly — `CompletionTower`:
  group thresholds, then group the groupings, and it *returns home* (`tower_is_single_inner`, `rfl`), with
  the modulus the only thing that ascends. The ℤ_p-cyclotomic tower is that completion-tower with `base`=p.
  In-repo the bare Galois `G` at the bottom is grounded by the cyclotomic instance
  `Gal(ℚ(ζ₅)/ℚ) ≅ C₄` (`galois_group_is_C4`, 4/0 PURE) — a concrete cyclotomic abelian Galois group; the
  *infinite ℤ_p-tower* itself (the `lim ℤ/pⁿ` as a named object) is absent.

- **Reading `L_Λ` — the power-series / completed-group-ring reading, bundling the tower into one Λ-module.**
  Λ=ℤ_p[[T]] reads the whole tower at once: a Λ-module `M = lim M_n` (the inverse limit of the level-`n`
  data, e.g. the p-parts of the class groups Cl(K_n)) is the **family-reading** of `generating_functions.md`
  — the count/obstruction at each level `n` bundled into one object, with `T = γ − 1` (`γ` a topological
  generator of `Gal(K_∞/K_0)=ℤ_p`) the **grading/bookkeeping coordinate**, exactly `generating_functions.md`'s
  `xVar` (the position-1 indicator, NOT a scalar). The completed group ring `ℤ_p[[Gal]] ≅ ℤ_p[[T]]` IS the
  power-series semiring `PowerSeriesSemiring` with `T`=`xVar` the degree-1 grading generator
  (`power_series_semiring`, 33/0 PURE): Λ is the modulus/approximant *packaged as a formal series*, the
  residue's finite signature (continued-fractions' modulus doctrine) written in `T`. The Iwasawa structure
  theorem — every finitely-generated torsion Λ-module is pseudo-isomorphic to a finite sum
  `⊕ Λ/(p^{μ_i}) ⊕ ⊕ Λ/(f_j(T)^{m_j})` — is the **`L_Λ` normal form**: the family-reading factored into its
  elementary divisors, exactly `generating_functions.md`'s "a rational GF = a denominator whose roots are the
  residue's fixed points", read in Λ.

- **Residue — the `q=±1` tag, two faces (level-residue and characteristic signature).**
  - **Per-level residue (`q=−1`/`q=+1`) — the class group Cl(K_n).** Cl(K_n) is `class_field_theory.md`'s
    idele-class residue / `galois_cohomology.md`'s H¹-style obstruction read at level `n`: the
    "forced-but-not-captured" surplus of the arithmetic of K_n (a nontrivial class group = a `q=−1`
    obstruction, exactly the `NonzeroBetti` `b₁=1` shape `galois_cohomology.md` cites for nonzero `H¹`; the
    PID/class-number-one case = the `q=+1` empty residue, the `reduced_betti_d4_contractible` `ker=im` shape).
    Its **growth across the tower** `|Cl(K_n)|_p = p^{μpⁿ+λn+ν}` is the residue read at each rung — the
    modulus's leading data. The class-number-one (empty-residue) pole is the repo's grounded toy:
    `EisensteinClassNumber.reduced_disc_neg3_unique` (`h(−3)=1`, 1/0 PURE) proves the disc-`−3` reduced form
    is unique by a finite count — a real ∅-axiom class-number-as-a-count, the simplest `q=+1` instance.
  - **Characteristic signature (the leading data) — the characteristic ideal char(M) = (p^μ · ∏ f_j(T)^{m_j}).**
    The growth invariants μ (the `p`-power part), λ (= `Σ deg f_j`, the `T`-power part), ν (the bounded
    tail) ARE the modulus's finite signature: `λ` = the `T`-degree of the characteristic power series = the
    `generating_functions.md` denominator degree, `μ` = its `p`-adic content. The characteristic ideal is the
    residue's `q=±1` characteristic invariant — the analogue of the rational-GF denominator
    `1−x−x²` whose roots are φ's Cassini fixed points (`q=+1`), here a power series in `T` whose
    "zeros" pin the class-group growth.
  - **The deepest residue (`Real213`-cut) — the p-adic L-function.** The Main Conjecture's other side, the
    p-adic L-function `L_p(s,χ)` interpolating the values `L(1−n,χ)`, is the `Real213`/p-adic-cut residue
    (`modular_forms.md`'s analytic-`L(f,s)` residue, the same boundary `zeta_euler.md` assigns every infinite
    series). Reached by no truncation, only narrowed to — and the located gap of this decomposition.

## ★ The Main Conjecture — the deepest character=residue tie

`(char(X_∞)) = (L_p)` — the characteristic ideal of the unramified Iwasawa module X_∞ EQUALS the ideal
generated by the p-adic L-function. In the calculus this is **not a sporadic identity**: it is the deepest
form of the corpus's two-invariant collapse. The **left side** is the `q=±1` *residue's characteristic
signature* (the class-group-growth modulus, packaged in Λ — Invariant B, the residue tag). The **right side**
is the `×↦·` *character* read p-adically: `L_p` is `modular_forms.md`/`zeta_euler.md`'s Dirichlet/Euler
generating function (`L(f,s)=Σ aₙ/nˢ`, Euler product `Σ_n=Π_p`, the UFD `×↦·` distributive law
`summatory_mul`), interpolated to the p-adic resolution. So the Main Conjecture says:

> **the character (the L-function, Invariant A) = the residue's characteristic invariant (the class-group
> growth, Invariant B), as one ideal in Λ.**

This is the **tightest sighting of the two load-bearing invariants on one object** in the entire notebook —
deeper than `generating_functions.md`'s "the two characters on one convolution", because here it is the
*character arrow itself* set equal to the *residue tag's* signature. It is the same `character ⇄ residue`
binding `galois_cohomology.md` found at one degree (Hilbert 90: the `×↦·` character's `H¹` *vanishes*, a
`q=+1` empty residue), now promoted to a **full equality of the character's whole p-adic series with the
residue's whole characteristic series**. Where Theorem 90 said "the character's first residue is empty", the
Main Conjecture says "the character's p-adic series *is* the residue's characteristic series" — the residue
and the character are two readings of one Λ-element. This passes the re-skin guard as a *prediction tying two
previously-separate corpus invariants at the deepest level*, not a re-description.

**Honest:** there is **no `mainConjecture` theorem**, no `pAdicL`, no `characteristicIdeal` object. The tie
is the *identification* of the two sides with the corpus's two invariants; the equality is prose-only and
its right side (the p-adic L-function) is the located `Real213`-cut gap.

## Re-seeing — ⟨C | L_Λ⟩ ⊕ Residue

```
   cyclotomic ℤ_p-tower K_∞=∪K_n   =  ⟨ approximant-with-modulus | L_res(base=p) ⟩ ASCENDED into a tower   (padic.md's C, iterated)
   Gal(K_∞/K_0) ≅ ℤ_p = lim ℤ/pⁿ   =  the p-adic resolution tower's index group                            (galois_group_is_C4 = bottom rung)  [ℤ_p-tower OBJECT ABSENT]
   level index n (the rung)        =  the (ℕ,+)-graded resolution count, grades ADD up the tower            (IsResolutionShift_compose, E₂+E₁)
   "group thresholds, then group the groupings; returns home, modulus ascends" = the tower IS completion-of-completions  (CompletionTower.tower_is_single_inner, rfl)
   Λ = ℤ_p[[T]] = ℤ_p[[Gal]]        =  the power-series semiring, T = the grading generator                  (power_series_semiring; xVar)  [completed group ring OBJECT ABSENT]
   a Λ-module M = lim M_n          =  generating_functions.md's family-reading (level-n data bundled)         (L_gen)  [inverse-limit OBJECT ABSENT]
   Iwasawa structure thm (⊕ Λ/(p^μ)⊕Λ/(f^m)) = L_Λ normal form = the GF denominator / elementary divisors    (generating_functions.md)  [ABSENT]
   class group Cl(K_n)             =  class_field_theory's idele residue / galois_cohomology's H¹ obstruction, at level n   [Cl-of-tower ABSENT]
   class-number-one (Cl=1)         =  the q=+1 empty residue (ker=im, reduced_betti shape)                    (reduced_disc_neg3_unique = h(−3)=1, BUILT 1/0)
   nontrivial Cl                   =  the q=−1 obstruction (NonzeroBetti b₁=1 shape)                          (loopClass_not_coboundary, the analogue)
   growth |Cl(K_n)|_p = p^(μpⁿ+λn+ν) = the residue read at each rung; μ,λ,ν = the modulus's leading data       [growth formula ABSENT]
   characteristic ideal char(M)=(p^μ·∏f_j(T)^{m_j}) = the residue's q=±1 characteristic signature; λ=Σdeg f_j = T-degree  [ABSENT]
   ★ Main Conjecture  (char X_∞) = (L_p)  =  CHARACTER (×↦· L-function, Invariant A) = RESIDUE signature (Invariant B)  [the deepest tie; PROSE-ONLY]
   p-adic L-function L_p(s,χ)       =  modular_forms' analytic-L residue, p-adically = the Real213-cut RESIDUE  [the LOCATED GAP]
   the L-function's Euler side      =  zeta_euler's Σ_n=Π_p (UFD ×↦· distributive law)                          (summatory_mul, BUILT)
```

| classical Iwasawa object | the calculus's reading | repo status |
|---|---|---|
| cyclotomic ℤ_p-extension K_∞=∪K_n | `padic.md`'s p-adic resolution (`base`=p) ascended into a tower | tower SHAPE **BUILT** (`CompletionTower`, `IsResolutionShift_compose`); ℤ_p-tower OBJECT **ABSENT** |
| Λ = ℤ_p[[T]] (completed group ring) | the power-series semiring, `T` = grading generator (`generating_functions.md`) | semiring **BUILT** (`power_series_semiring`, 33/0); completed-group-ring OBJECT **ABSENT** |
| Λ-module / structure theorem | `generating_functions.md`'s family-reading + GF-denominator normal form | the GF normal-form reading **BUILT**; Λ-module OBJECT **ABSENT** |
| class group Cl(K_n) | `class_field_theory`'s idele residue / `galois_cohomology`'s H¹ obstruction, at level `n` | class-number-one toy **BUILT** (`reduced_disc_neg3_unique`); H¹/idele mechanism BUILT (`NonzeroBetti`); Cl-of-tower **ABSENT** |
| growth `p^(μpⁿ+λn+ν)`, char ideal, μ/λ/ν | the residue read per rung; the modulus's leading data / `q=±1` signature | growth formula + char ideal **ABSENT** |
| Main Conjecture `(char X_∞)=(L_p)` | **character (Invariant A) = residue signature (Invariant B)** | **PROSE-ONLY** (the deepest tie); the Euler/`×↦·` side BUILT (`summatory_mul`) |
| p-adic L-function `L_p(s,χ)` | the `Real213`/p-adic-cut residue (`modular_forms`'s analytic-L) | **LOCATED GAP** (`Real213` residue) |

## LEVERAGE — leg by leg, honest about how much is prose-only

**Net verdict: PREDICTION + located gap at the p-adic L-function.** The calculus predicts Iwasawa theory's
form precisely — the tower = `padic.md`'s resolution ascended, Λ = the power-series modulus, the class number
= the per-level residue, the Main Conjecture = character=residue — and **two legs are grounded harder than a
pure-prose prediction** (the tower and the power-series Λ), one has a real ∅-axiom toy (class-number-one),
and the Main Conjecture + p-adic L-function are the prose-only / located-gap edge. No new primitive.

### Leg 1 — K_∞=∪K_n = `padic.md`'s p-adic resolution ascended into a tower. **PREDICTION; tower SHAPE genuinely BUILT, ℤ_p-tower OBJECT absent (PARTIAL — a grounded surprise).**
The calculus predicts the cyclotomic tower is `padic.md`'s `base`=p resolution *iterated* — the SAME
resolution-iteration as spectral-sequence pages / RG / completion-of-completions. This is grounded harder
than expected: **`CompletionTower` builds exactly the tower-of-completions and proves it returns home** —
`tower_is_single_inner` (`:89`, by `rfl`): a level-2 tower (a sequence-of-completed-sequences, completed)
collapses to one inner completion read at the outer modulus, *creating no new object*, with **the modulus
the only thing that ascends** (file docstring §2; `tower_value_stable`, `:113`). That is the ℤ_p-tower's
defining shape: each K_n is one completion-rung, K_∞ the tower, and the structure that accumulates up the
tower is the modulus (here Λ's `T`-grading). And the **level index `n` is the `(ℕ,+)`-graded resolution
count whose grades ADD up the tower** — `ResolutionShift.IsResolutionShift_compose` (`:130`, 17/0 PURE):
composing resolution-shifts of grades `E₁,E₂` gives grade `E₂+E₁`, so ascending the tower `n` rungs is grade
`n` — the same `(ℕ,+)`-graded page-composition `spectral_sequences.md` cites. So the *tower as a
resolution-iteration with additive level grading and a modulus that ascends* is BUILT ∅-axiom. **What is
absent**: the named cyclotomic ℤ_p-extension object — `Gal(K_∞/K_0)≅ℤ_p=lim ℤ/pⁿ` as a Lean type (the
bottom rung `Gal(ℚ(ζ₅)/ℚ)≅C₄` is built, `galois_group_is_C4` 4/0, but the infinite tower is not). PARTIAL,
with the tower-shape a genuine grounding the thesis predicted.

### Leg 2 — Λ=ℤ_p[[T]] = the power-series modulus. **PREDICTION; the power-series semiring BUILT, the completed-group-ring OBJECT absent (PARTIAL — a grounded surprise).**
The calculus predicts Λ is `generating_functions.md`'s power-series semiring — the modulus/approximant
packaged as a formal series in `T`, with `T`=`xVar` the grading generator (NOT a scalar). This is grounded:
**`PowerSeriesSemiring.power_series_semiring` (`:373`, 33/0 PURE) is a closed ∅-axiom formal-power-series
semiring** on `CoeffSeq := Nat → Nat`, with `xVar` the degree-1 grading generator, commutativity/
associativity/distributivity/two-sided unit, and the **`×↦·` multiplicative character on the welded product**
`massN_toCoeffSeq_conv` (`:361`). So "Λ = the modulus as a power series in `T`, with multiplication the
Cauchy convolution and a multiplicative character" is BUILT — the ring underlying Λ. **What is absent**: the
*completed group ring* identification `ℤ_p[[Gal(K_∞/K_0)]] ≅ ℤ_p[[T]]` (the isomorphism `γ↦1+T`), and the
ℤ_p-coefficient version (the semiring is over ℕ, not ℤ_p — the p-adic coefficients are `padic.md`'s `ZpSeq`,
built separately, not welded into this semiring). The *power-series object* is real and PURE; the
*group-ring-as-power-series* and *ℤ_p-coefficient* welds are the open legs. PARTIAL, the second grounded leg.

### Leg 3 — class number = the per-level residue; growth = the modulus invariants. **PREDICTION; class-number-one toy BUILT, the growth formula absent.**
The calculus predicts |Cl(K_n)| is the residue read at level `n` (the idele/H¹ obstruction of K_n), its
growth `p^(μpⁿ+λn+ν)` governed by the characteristic-ideal invariants. The residue *mechanism* is grounded
both poles: the **`q=+1` empty-residue (class-number-one) pole has a real ∅-axiom toy** —
`EisensteinClassNumber.reduced_disc_neg3_unique` (`:49`, 1/0 PURE): the disc-`−3` reduced form is unique
(`h(−3)=1`), a class number computed as a finite count by reduction inequalities, "no reciprocity, no
descent, all ∅-axiom over ℕ" — the form-class counterpart of `ℤ[ω]` being a PID. And the **`q=−1` nonzero
residue** is the `galois_cohomology.md` mechanism: a nontrivial class group is the `NonzeroBetti`
`loopClass_not_coboundary` `b₁=1` shape (the idele/H¹ obstruction made concrete), tagged via `ResidueTag`
(`cycle_vs_contractible_qpm`: cycle=`escape`/`q=−1` vs contractible=`converge`/`q=+1`). So the class group
= the per-level `q=±1` residue is grounded at the mechanism level, with a genuine class-number toy. **What
is absent**: Cl(K_n) *as a tower-indexed family*, the **growth formula** `p^(μpⁿ+λn+ν)` (no
`class_number_growth` theorem), and the μ,λ,ν invariants as named objects. The single-level class number is
a finite count (built, toy); the *asymptotic across the tower* is prose-only. PARTIAL.

### Leg 4 — Main Conjecture = character L = residue characteristic signature. **PREDICTION; the deepest tie, PROSE-ONLY; the p-adic L-function the located gap.**
The calculus predicts the Main Conjecture `(char X_∞)=(L_p)` is the equality "character (Invariant A) =
residue's characteristic signature (Invariant B)" — the deepest two-invariant sighting (§ above). The
**`×↦·`/Euler side is BUILT**: `L_p` is `zeta_euler.md`/`modular_forms.md`'s Dirichlet/Euler generating
function, whose Euler product `Σ_n=Π_p` is the UFD `×↦·` distributive law — `summatory_mul`
(`SummatoryMultiplicative.lean:74`, ∅-axiom), `vp_mul` (`PrimeValuation.lean:96`, the multiplicative
character supplying the p-adic modulus, `padic.md`'s `base`). The **residue-signature side** is the Λ-packaged
class-group-growth modulus (Leg 3 + the power series of Leg 2). **What is absent**: the equality itself
(`mainConjecture`), the **p-adic L-function `L_p(s,χ)`** as an analytic object (the `Real213`/p-adic-cut
residue — the SAME boundary `modular_forms.md` names for analytic `L(f,s)` and `zeta_euler.md` for ζ-values:
the discrete/combinatorial structure is closed, only the value-cut is reached-by-none), and the
characteristic ideal. The interpolation property (`L_p(1−n)=` a modified `L(1−n,χ)`) needs the p-adic
analytic continuation — the located gap. PROSE-ONLY for the conjecture; the located gap is precisely the
p-adic L-function's value-cut.

### Does it avoid re-skinning `padic.md`/`modular_forms.md`? **YES — the new datum is the tower + the power-series Λ + the Main-Conjecture tie.**
`padic.md` gave the p-adic resolution at ONE level (`base`=p, the completion ℚ_p). The new datum here is that
**Iwasawa's ℤ_p-tower is that `base`=p resolution ASCENDED into a tower** — grounded by `CompletionTower`
(completion-of-completions returns home, modulus ascends) + `IsResolutionShift_compose` (level grades add),
which `padic.md` did not touch. `generating_functions.md` gave the power-series semiring; the new datum is
that **Λ=ℤ_p[[T]] IS that semiring read as the completed group ring of the tower's Galois group** (`T=γ−1`).
`modular_forms.md` gave the L-function/Euler character; the new datum is the **Main Conjecture as the
deepest character=residue equality** (Invariant A = Invariant B's signature in Λ), promoting
`galois_cohomology.md`'s Theorem-90 `character⇄residue` tie from "the character's first residue vanishes"
to "the character's whole p-adic series equals the residue's whole characteristic series". Three new ties,
no re-skin.

## Revelation (collapse + forcing + spine)

**Collapse + forcing + the spine, with a PROSE-ONLY deepest leg, honestly flagged.** Iwasawa theory is ONE
`⟨C | L_Λ⟩ ⊕ Residue`: `padic.md`'s p-adic resolution `C` ascended into a tower, read through the
power-series/completed-group-ring `L_Λ`, leaving the class-group-growth residue whose characteristic
signature the Main Conjecture sets equal to the p-adic L-function's `×↦·` character. Four collapses at once:

1. **Collapse — the tower IS the calculus's resolution-iteration.** K_∞=∪K_n, the spectral-sequence page
   tower (`E_{r+1}=H(E_r)`), the RG iteration, and the completion-of-completions are **one object**:
   `padic.md`'s resolution re-entering as its own operand. `CompletionTower.tower_is_single_inner` (by `rfl`)
   proves the tower returns home with the modulus the only ascending datum; `IsResolutionShift_compose`
   proves the level grades add `(ℕ,+)`. The cyclotomic ℤ_p-tower is that completion-tower at `base`=p — no
   new primitive, the resolution axis ascended.

2. **Forcing — Λ is FORCED to be the power-series modulus.** Given the tower's `(ℕ,+)`-graded level index and
   `generating_functions.md`'s rule "the family-reading's product is the Cauchy convolution (the only product
   respecting `xⁱxʲ=x^{i+j}`)", Λ=ℤ_p[[T]] is forced as the power-series semiring with `T` the grading
   generator — `power_series_semiring` (33/0 PURE) is that ring. The completed group ring is the modulus
   *packaged as a formal series*, not a new construct.

3. **Residue surfaced — the class number is the per-level `q=±1` residue; μ,λ,ν are the modulus's leading
   data.** Cl(K_n) is `class_field_theory`'s idele residue / `galois_cohomology`'s H¹ obstruction read at
   rung `n` (the `NonzeroBetti` `b₁=1` shape for nontrivial Cl, the `reduced_disc_neg3_unique` `h(−3)=1`
   class-number-one toy for the `q=+1` empty pole), and its growth is the residue read across the tower, the
   characteristic ideal its `q=±1` signature — `λ` = the `T`-degree (the GF-denominator degree of
   `generating_functions.md`), `μ` = the `p`-content.

4. **The spine — the Main Conjecture is the deepest `character ⇄ residue` tie (Invariant A = Invariant B).**
   `(char X_∞)=(L_p)`: the `×↦·` character (the p-adic L-function, the Euler product `Σ_n=Π_p`,
   `summatory_mul`/`vp_mul`) EQUALS the `q=±1` residue's characteristic signature (the class-group growth,
   Λ-packaged). This is the tightest two-invariant collapse in the notebook — the character arrow set equal
   to the residue tag's signature, promoting Theorem 90's `q=+1` first-residue *vanishing* to a full
   *equality* of the two p-adic series. **Honest:** this leg is PROSE-ONLY (no `mainConjecture`, no `L_p`,
   no `characteristicIdeal`); the `×↦·`/Euler side is built, the equality and its `Real213`-cut L-function
   are the located gap.

## The precise located gap

The genuine absence is **the p-adic L-function `L_p(s,χ)` and the Main-Conjecture equality** — the
`Real213`/p-adic-cut residue, the same value-cut boundary `modular_forms.md` (analytic `L(f,s)`),
`zeta_euler.md` (ζ-values), and `padic.md` (the completion limit) all locate. The discrete/combinatorial
skeleton is closed (tower shape, power-series Λ, class-number-as-count toy); only the *analytic
interpolation* (the p-adic L-value, the characteristic-ideal equality) is reached-by-none. Alongside it, the
*named Iwasawa objects* (the ℤ_p-extension, the completed group ring, the Λ-module structure theorem, the
char ideal, μ/λ/ν, the growth formula) are absent — the same `class_field_theory.md`/`modular_forms.md`-shaped
edge: the structure named precisely, the global/analytic objects open.

## VALIDATE — verdict

**PREDICTION + located gap (no break, no new axis; model v7.1 holds).** Iwasawa theory predicts and
consolidates: the tower = `padic.md`'s resolution ascended (tower-shape BUILT), Λ = the power-series modulus
(semiring BUILT), the class number = the per-level `q=±1` residue (class-number-one toy BUILT), the Main
Conjecture = the deepest character=residue tie (PROSE-ONLY). The located gap is the **p-adic L-function**
(the `Real213`-cut residue) and the named Iwasawa objects. No new primitive — `C` is `padic.md`'s resolution
iterated, `L_Λ` is `generating_functions.md`'s power-series family-reading, the residue is the
class-field/Galois-cohomology obstruction, and the Main Conjecture is Invariant A = Invariant B's signature.

## Verified Lean anchors (file:line:theorem — all grep/Read-verified on `lean/E213` this session; purity scanned via `tools/scan_axioms.py` from repo root)

| Leg | Theorem (file:line : name) | Status |
|---|---|---|
| ★★ **the tower IS completion-of-completions, returns home, modulus ascends (Leg 1)** | `Lib/Math/Analysis/CompletionTower.lean:89 tower_is_single_inner` (`rfl`), `:99 tower_stays_in_cut`, `:113 tower_value_stable`, `:57 completion_idempotent` | **∅-axiom PURE, scanned 7/0** ✓ |
| ★ **the level index = `(ℕ,+)`-graded resolution; grades ADD up the tower (Leg 1)** | `Lib/Math/Analysis/ResolutionShift.lean:130 IsResolutionShift_compose` (`grade E₂+E₁`), `:73 IsResolutionShift`, `:179 IsResolutionShift_cutHalfIter` | **∅-axiom PURE, scanned 17/0** ✓ |
| ★★ **Λ=ℤ_p[[T]] = the power-series semiring, T=xVar the grading generator (Leg 2)** | `Lib/Math/Combinatorics/PowerSeriesSemiring.lean:373 power_series_semiring`, `:361 massN_toCoeffSeq_conv` (`×↦·` char on the product), `:163 conv_comm'`, `:168 conv_assoc'` | **∅-axiom PURE, scanned 33/0** ✓ |
| ★ **class number as a finite count — class-number-one (`h(−3)=1`), the `q=+1` empty-residue pole (Leg 3)** | `Lib/Math/Algebra/CayleyDickson/Integer/EisensteinClassNumber.lean:49 reduced_disc_neg3_unique` | **∅-axiom PURE, scanned 1/0** ✓ |
| nontrivial class group = the `q=−1` obstruction (idele/H¹ residue, the analogue) | `Lib/Math/Cohomology/Examples/NonzeroBetti.lean:134 loopClass_not_coboundary`, `:111 betti_one_cycle`, `:173 cycle_vs_contractible_qpm` | ∅-axiom PURE (56/0, per `galois_cohomology.md`) ✓ |
| the resolution re-entering as its own operand (tower = spectral-sequence iteration) | `Lens/Foundations/ResidueReentry.lean:85 residue_perpetually_reenters`, `:63 residue_reentry_never_closes` | **∅-axiom PURE, scanned 14/0** ✓ |
| ★ Main-Conjecture `×↦·`/Euler side: L-function Euler product `Σ_n=Π_p` (UFD distributive law) (Leg 4) | `Lib/Math/NumberTheory/SummatoryMultiplicative.lean:74 summatory_mul`; `Lib/Math/NumberTheory/PrimeValuation.lean:96 vp_mul` (the p-adic `base` modulus) | ∅-axiom (per `zeta_euler.md`/`padic.md`) ✓ |
| `q=±1` residue tag grading the class-group residue (Invariant B) | `Lib/Math/Foundations/ResidueTag.lean : ResidueTag`, `multiplier_unimodular`, `residue_tag_two_poles` | ∅-axiom PURE (55/0, per `SYNTHESIS.md`) ✓ |
| the bottom rung's Galois group (cyclotomic abelian `G`) | `Lib/Math/Algebra/Icosahedral/CyclotomicFive.lean:66 galois_group_is_C4` (`Gal(ℚ(ζ₅)/ℚ)≅C₄`), `:79 golden_real_subfield` | ∅-axiom PURE (4/0, per `class_field_theory.md`) ✓ |
| the per-prime `q=±1` local character (CFT/Frobenius, the L-function's local factor) | `Lib/Math/NumberTheory/ModArith/FP2SqrtD.lean : fp2dFrob_mul`, `fp2dFrob_involution` | ∅-axiom PURE (32/0, per `class_field_theory.md`) ✓ |

**Fresh purity scans (this session, `tools/scan_axioms.py` from repo root):**
`E213.Lib.Math.Analysis.CompletionTower` — **7 pure / 0 dirty** (incl. `tower_is_single_inner`,
`tower_stays_in_cut`, `tower_value_stable`, `completion_idempotent`).
`E213.Lib.Math.Analysis.ResolutionShift` — **17 pure / 0 dirty** (incl. `IsResolutionShift_compose`).
`E213.Lib.Math.Combinatorics.PowerSeriesSemiring` — **33 pure / 0 dirty** (incl. `power_series_semiring`,
`massN_toCoeffSeq_conv`). `E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinClassNumber` —
**1 pure / 0 dirty** (`reduced_disc_neg3_unique`). `E213.Lens.Foundations.ResidueReentry` —
**14 pure / 0 dirty** (incl. `residue_perpetually_reenters`).

## Dropped / flagged citations (honest — NOT grounded in repo Lean)

- **`Iwasawa` / `iwasawa` as named objects** — **ABSENT** (grep over all `lean/E213`: zero hits). The
  cyclotomic ℤ_p-extension theory is not built as a field.
- **`Lambda` / `ℤ_p[[T]]` as the completed group ring `ℤ_p[[Gal]]`** — **ABSENT as the Iwasawa algebra.**
  The *power-series semiring* `power_series_semiring` is built (over ℕ, with `xVar`); the
  completed-group-ring identification `ℤ_p[[Gal(K_∞/K_0)]]≅ℤ_p[[T]]` and the ℤ_p-coefficient version are
  not. The semiring is the built shadow; the Iwasawa algebra object is the open weld.
- **`characteristicIdeal` / `characteristic_ideal`** — **ABSENT** (grep: zero hits). The residue's
  characteristic signature is the conceptual reading; no Lean object.
- **`mainConjecture` / `main_conjecture` / `pAdicL` / `p_adic_L`** — **ABSENT** (grep: zero hits). The Main
  Conjecture is PROSE-ONLY; the p-adic L-function is the located `Real213`-cut gap. The `×↦·`/Euler side
  (`summatory_mul`, `vp_mul`) is the built shadow.
- **`mu_invariant` / `lambda_invariant` / `class_number` (of a tower) / the growth formula
  `p^(μpⁿ+λn+ν)`** — **ABSENT** (grep: zero hits). The single-level class number is a finite count
  (`reduced_disc_neg3_unique`, built toy); the μ,λ,ν invariants and the asymptotic across the tower are
  prose-only.
- **The Λ-module structure theorem (pseudo-isomorphism to `⊕Λ/(p^μ)⊕Λ/(f^m)`)** — **ABSENT.** The
  family-reading + GF-denominator normal form is the conceptual reading (`generating_functions.md`); no
  Λ-module object or structure theorem.
- **The infinite cyclotomic ℤ_p-tower `lim ℤ/pⁿ` / `Gal(K_∞/K_0)≅ℤ_p`** — **ABSENT as a named object.** The
  tower SHAPE is built (`CompletionTower`, `IsResolutionShift_compose`) and the bottom rung
  (`galois_group_is_C4`); the infinite ℤ_p-extension is the open object.
- **The p-adic L-function `L_p(s,χ)` (analytic interpolation)** — the `Real213`/p-adic-cut residue, the same
  boundary `modular_forms.md`/`zeta_euler.md`/`padic.md` locate. Not claimed; the located gap of this
  decomposition.

## Verified buildable witness (suggested, NOT built this session)

A **class-number-growth toy at two tower rungs**: the disc-`−3` class-number-one count
(`reduced_disc_neg3_unique`, `h=1` = `p^0`, the `q=+1` empty-residue base) contrasted with a discriminant of
class number `p` (a single `q=−1` obstruction), tagged via `ResidueTag` (`converge` vs `escape`), exhibiting
the `n=0` vs `n=1` growth `p^(λ·n)` with `λ=1` at the lowest two levels — the Iwasawa-growth analogue of
`NonzeroBetti`'s nonzero-`H¹` vs `reduced_betti`'s empty-`H¹`, read across two rungs. This would turn Leg 3
from a single-level toy to a two-rung *growth* witness. Flagged as the located target; not built.

## Verdict: PREDICTION + located gap at the p-adic L-function

Iwasawa theory **predicts and consolidates** — no break, no new axis. **Grounded ∅-axiom (the surprises):**
the **tower** as completion-of-completions returning home with the modulus ascending
(`CompletionTower.tower_is_single_inner`, 7/0) and the level grades adding `(ℕ,+)`
(`IsResolutionShift_compose`, 17/0); **Λ=ℤ_p[[T]]** as the power-series semiring with `T` the grading
generator and a `×↦·` character on the product (`power_series_semiring`/`massN_toCoeffSeq_conv`, 33/0); the
**class number as a finite count** at the `q=+1` empty-residue pole (`reduced_disc_neg3_unique`, `h(−3)=1`,
1/0), with the `q=−1` obstruction the `galois_cohomology` `NonzeroBetti` mechanism; the **Main-Conjecture
`×↦·`/Euler side** (`summatory_mul`, `vp_mul`). The **PROSE-ONLY / located gap** is the **Main Conjecture
equality and the p-adic L-function** (the `Real213`-cut residue) plus every named Iwasawa object
(`Iwasawa`/`Lambda`-as-group-ring/`characteristicIdeal`/`mainConjecture`/μ,λ,ν/growth-formula — all
grep-confirmed absent). The thesis holds: **Iwasawa theory = `padic.md`'s p-adic resolution TOWER + the
power-series modulus Λ + the class-number per-level residue + the Main Conjecture as the deepest
character=residue tie** — `padic`'s tower (ascended) + the power-series modulus + the residue, with the Main
Conjecture binding Invariant A (the `×↦·` L-function) to Invariant B (the `q=±1` residue's characteristic
signature). The tower-shape and the power-series Λ are genuinely built; the class number has a real toy; the
Main Conjecture and the p-adic L-function are the prose-only deepest leg and the located gap. **Iwasawa
theory EXTENDS by consolidation (PREDICTION); the p-adic L-function is the located gap.**
