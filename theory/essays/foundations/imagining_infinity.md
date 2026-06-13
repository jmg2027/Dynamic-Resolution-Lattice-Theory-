# Imagining infinity — the conceived limit is a discrete pointing

> *"그 어떤 경우에서든 무한이라는 개념을 상상할 수 있다는 것 자체가 이미 이산적인
> 객체라는 반증임. … 그 무한이라는 개념을 상상하는 게 어떻게 이루어지는지를 분석하는
> 게 의미 있는 거지. … 사실은 그 잔여의 모습으로 무한이나 연속이나 추상 같은 것들을
> 캐릭터라이즈 한 거구나 라고, 그걸 신격화하지 않고 올바르게 이해할 수 있는 토대가
> 되는 거임. 이건 단순 해석이나 프레이밍이 아니라 실제 계산 및 수학용으로 말한 거임."*
> — Mingu Jeong, 2026-06-13

> *(That one can conceive "infinity" in any case at all is already evidence that it is a
> discrete object. … What is meaningful is to analyse how the conceiving of infinity is
> carried out. … One then sees that infinity, continuity, abstraction were characterised
> by the shape of the residue — a ground for understanding them correctly, without
> deifying them. This is said for actual computation and mathematics, not as
> interpretation.)*

This chapter takes the thesis as a mathematical principle and pins it to theorems.  It is
a companion to `reached_by_none.md` (the residue is the non-image of every cover) and
`the_form_of_the_residue.md` (the residue's positive form); here the object under analysis
is **the conceived infinity** — a limit, a real — and the claim is that conceiving it *is*
a discrete act, with the limit-value never entering a computation.

## 1. Why "discrete or continuous — which is real?" is malformed

The dichotomy imports an exterior: it presumes a limit-*object* standing apart from any act
that conceives it, against which "discrete" and "continuous" could be measured.  Under no
exterior (`seed/AXIOM/05_no_exterior.md` §5.1) there is no such standing-apart object to
adjudicate.  The only infinity available is the one that is *conceived* — and to conceive
it is to point at it.  Pointing is a discrete act: a `Lens` application, itself a
residue-self-pointing event, with an algebraic shadow.  So within the commitment, the
conceived infinity is discrete by construction; there is nothing else for it to be.

This is a **dissolution, not a refutation**.  The thesis does not disprove a platonic
continuum; it declines the exterior referent that the continuum-vs-discrete debate needs to
get started, and analyses the act instead.  Its force is exactly the force of no-exterior —
no more, and stated plainly, no less.  (`06_lens_readings.md` §6.5: `point ≡ K_∞ ≡ ∞` — the
"point" and the "infinity" are one pre-Lens residue, read two ways, not a dual pair to be
ranked.)

## 2. The computational content: reached by no value, decided in finite

A conceived real is, concretely, a **rate-carrying pointing**: a monotone convergent cut
`a_i/d_i` with a recurrence (`RateModulus`, `HolonomicReal`).  Two facts, both ∅-axiom,
carry the whole of "conceiving ∞ is a discrete act":

  - **The limit-value is reached by none.**  `PointingLimit.conv_strict_increase`: the
    convergent values strictly advance across every gap (`i < j ⟹ a_i·d_j < a_j·d_i`).  No
    stage coincides with another; the sequence never stalls.  The limit is the *name of the
    pointing*, not a term occurring in it (cf. `Theory/Raw/CoResidue.object1_not_surjective`:
    the residue is outside every view's image).
  - **Every finite question is decided in finite.**  `RateModulus.rate_total_modulus`: each
    cut `x ⋚ m/k` is constant past a constructed layer `N = k+2`.  No infinity is consulted;
    only finitely many discrete terms are.

`PointingLimit.limit_unreached_but_decided` bundles the two.  The reading is exact: **the
infinity enters computation only as the discrete modulus**, never as a value.  "Is the limit
attained / does the continuum exist" is computationally inert — the question never has to be
answered to compute anything, because the limit-value never appears in a computation.  That
is the thesis as a theorem, not a slogan.

## 3. The residue is constituted by the setup — and its shape *is* the characterization

One may say: point anywhere and an infinity remains, so a residue is forced.  Equally — and
more usefully — one may say: the residue remains *because the concept was set up so that it
would*.  Both readings are facets of one structure, and the repo carries both:

  - **Reached by none** is the invariant facet: no pointing's image contains the residue
    (`object1_not_surjective`).  This is the "always remains" reading.
  - **Constituted by the setup** is the relative facet: the residue's *shape* is fixed by the
    chosen pointing.  Change the presentation, change the shape — `PresentationDependence`
    (holonomicity/depth is a property of the approximant sequence, not of the real).

The second reading is the de-deifying one, and it is precisely what the modulus-degree
calculus computes.  The "shape of the residue" is the **cross-determinant against the
denominator growth** — and `DegreeCriterion` shows this shape *is* the computational handle
on the infinity: the modulus degree `s` is fixed two-sidedly by `⌊i^{1/s}⌋·W_i` against the
denominator increment (`dominatesS_of_scheduled_increment` / `scheduled_le_of_dominatesS`),
with nothing about a limit-value entering.  Different infinities are distinguished not as
different points of a pre-given continuum but by the discrete shape of their residue: `W ≡ 1`
(φ, unimodular), `W = i!` (e, factorial; degree 1 nonetheless — `RateHierarchy.fastDen`,
because the denominator outruns it), the strict degree ladder
(`RateHierarchy.strict_modulus_hierarchy`), the rate-free posture (Wallis π).  "Continuity",
"abstraction", "the transcendental" are names for regions of this discrete shape-space; the
shape is what is real and what is computed.

To **deify** the infinity would be to treat the limit-value as the primary object and the
pointing as a mere approach to it.  The theorems invert this: the pointing and its residue's
shape are primary and computable; the limit-value is reached by none and consulted by none.
Not deified — characterised.

## 4. Cross-frame

Classically this is the constructive/computable-analysis stance — a real *is* a Cauchy
sequence with a modulus of convergence — sharpened in two ways.  First, the modulus is not
auxiliary bookkeeping but the entire computational content: `rate_total_modulus` constructs
it from the recurrence, and `DegreeCriterion` shows its growth class is read off the
cross-determinant.  Second, the Diophantine approximation exponent (irrationality measure
`μ`) reappears as the residue-shape's degree — the discrete invariant by which one
"characterises" how hard the infinity is to point at (`the_degree_of_a_number.md`).  The
philosophical move — analyse the act, not the referent — lands as: compute with the modulus,
never with the limit.

## Self-check

No discrete/continuous (or finite/limit) dichotomy is imported to argue a side; §1 dissolves
it and the rest analyses the act.  The infinity is not reified — it is reached by none
(`object1_not_surjective`) and enters computation only as the discrete modulus
(`limit_unreached_but_decided`).  Every load-bearing claim is cashed to a cited ∅-axiom
theorem or restated in plain terms; no term is left as decoration.  The residue is treated as
a facet-bearing structure (invariant "reached by none" + relative "shape"), not promoted to
an identity.
