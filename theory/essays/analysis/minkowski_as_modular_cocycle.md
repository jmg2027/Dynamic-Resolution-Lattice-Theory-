# The Minkowski `?` is the residue's modular cocycle

## Triggering question

> The analytic Minkowski `?` — the value at an irrational, the order-completion of
> the question-mark function — keeps appearing as a "reached-by-none" residue.  Is
> it merely an escape, or does it carry a *positive* modular structure native to
> the residue?

## 213-native answer

`?` is not only an escape.  On the Stern-Brocot tree it is a **1-cocycle of the
modular group, valued in the Markov data** — the residue-internal shadow of
Eichler–Shimura.  Three facts, all ∅-axiom, fix this:

> **defect** — `?` is not additive under the L/R generators; its failure *is* the
> bounding Markov number (the Frobenius cross-determinant).
> **twist** — under each generator the defect transforms by the `SL(2,ℤ)`
> Cayley–Hamilton action — the Markov-equation Vieta jump `m' = 3·m·m − m`.
> **period** — at weight 2 the period polynomial degenerates to the residue, and
> the period relation is the `√(−1)` congruence `m ∣ u² + 1`.

The "twisted additivity" of a 1-cocycle, `c(gh) = c(g) + g·c(h)`, is exactly the
content already proved in `Real213/SternBrocotMarkov`; `Real213/MinkowskiCocycle`
reads it as the cocycle it is.

## Derivation

**The carrier.**  The combinatorial `?` is the order-isomorphism between the
continued-fraction (Stern-Brocot) and dyadic numerations of a real — one
`List Bool` tree under two unimodular labellings (`OdometerSternBrocotUnit`:
`minkowski_skeleton`, `minkowski_compile`, `dyadic_local_order` +
`sb_mediant_local_order`).  Every node is `det = 1` in `SL(2,ℤ)`
(`mInterval_det`), the unit `det P = NS − NT = 1`.

**Defect = Markov data.**  The residue→number map fails to be additive under the
generators; the two cross-determinants are the bounding Markov numbers:
`u_r·m_t − u_t·m_r = m_l` (`markovRes_cross`) and `u_t·m_l − u_l·m_t = m_r`
(`markovRes_cross_left`).  Bundled, unimodular, in
`MinkowskiCocycle.minkowski_is_markov_valued_cocycle`: the failure of `?` to be a
homomorphism *is* the Markov data itself — a cocycle valued in the lattice module.

**Twist = Cayley–Hamilton.**  A 1-cocycle's defining relation is the twist
`g·c(h)`.  Here the generator acts by `M² = tr(M)·M − I` (`det = 1`), so under each
L/R descent the Markov defect transforms by the **Markov-equation Vieta jump**
`m' = 3·m_bound·m_node − m_other` (`minkowski_cocycle_twist`, via `markoff_vieta`
and the entry-shape `tr = 3·m`).  The coefficient module is the Markov triple; the
group action is Cayley–Hamilton; the defect is the neighbour Markov number — the
full cocycle datum on the tree.

**Off the tree.**  The defect is a *universal* bilinear identity on all integer
matrices, `M.a·(MN).c − M.c·(MN).a = det M · N.c` (`cocycle_defect_general`),
unimodular exactly on `SL(2,ℤ)` — the first honest step of the full-group
extension (`markoff_frobenius` is its `det = 1` case).

**Weight-2 period = `√(−1)`.**  In Eichler–Shimura the period polynomial of a
weight-`k` form is a class in `H^1(SL(2,ℤ), V_{k−2})`.  At **weight 2** (`V_0`) the
period degenerates to the residue, and the two period relations collapse to the
`√(−1)` congruence: at every node the residue squares to `−1` modulo the Markov
number, `m_t ∣ u_t² + 1` (`minkowski_weight2_period_relation`,
`markovNum_dvd_res_sq_succ`), explicit form `u_t² + 1 = (m_t + d − b)·m_t`.  The
residue *is* the weight-2 period of the `?`-cocycle.

**The golden extremal.**  The general period relation runs, along the slowest
(period-1, all-`1` continued fraction) descent, into the **Fibonacci spine**:
`fib(2n+3) ∣ fib(2n+2)² + 1` (`MinkowskiGoldenExtremal.golden_is_extremal_weight2_period`,
`fib_spine_sqrt_neg_one`).  This is the golden ratio `φ` — the worst-approximable
number, the Lagrange-spectrum floor `√5` — realised as the extremal case of the
cocycle's period, with the Cassini `W = ±1` floor being the residue unit
(`golden_min_attained_on_fib`, `golden_anisotropic`).  So the Markov/Lagrange
minimum is not external data: it is where the `?`-cocycle's period runs along the
residue's own golden spine.

## Dual-function

| Classical reading | 213 reading |
|---|---|
| `?` is a singular, nowhere-smooth real function | `?` is a modular 1-cocycle; its "singularity" is the escape (`reached_by_none`), its *structure* is the cocycle |
| Eichler–Shimura: periods ↔ `H^1(SL(2,ℤ), V_k)` | the weight-2 period IS the Markov `√(−1)` congruence — built ∅-axiom |
| Markov / Lagrange spectrum is a theory of forms | the spectrum is the cocycle's value-set; `φ`/`√5` its extremal period |
| `φ` is "the most irrational number" | `φ` is the period-1 spine, the slowest descent, the cocycle's extremal instance |
| cocycle, period, Markov triple, golden form are separate objects | they are one residue cocycle read at defect / period / module / extremal |

## Cross-frame convergence

The same structural fact appears on five surfaces, all `det = 1 = NS − NT`:

| Surface | Appearance | Citation |
|---|---|---|
| Modular cocycle | defect = bounding Markov number | `minkowski_is_markov_valued_cocycle` |
| Group action | twist = Cayley–Hamilton/Vieta jump | `minkowski_cocycle_twist` |
| Number theory | weight-2 period = `√(−1)` congruence | `minkowski_weight2_period_relation` |
| Diophantine | `φ` = extremal period (Lagrange `√5`) | `golden_is_extremal_weight2_period` |
| Geometry | universal defect `det M · N.c` on `M₂(ℤ)` | `cocycle_defect_general` |

These are not analogies: each is a `ring_intZ`/`decide` consequence of the single
unimodular unit, the residue's `NS − NT = det P = 1`.

## What is NOT claimed (the honest boundary)

The cocycle is built **on the Stern-Brocot tree** (the L/R sub-semigroup of
`SL(2,ℤ)`).  Genuinely open: the full-group cocycle composition law on non-tree
generators; the **higher-weight** period integrals and the analytic
`H^1(SL(2,ℤ), V_k)` identification; and the multifractal Hölder spectrum of `?`.
These obstructions are **constructive, not axiom-cost** — and narrower than first
thought.  Integration is ∅-axiom-native here: the repo builds its own dyadic
Riemann integral (`Real213/CutIntegral`, `DyadicRiemann`) *and* a
fundamental-theorem-of-calculus / antiderivative integral on the flux formalism
(`Lib/Math/Analysis/Integration/{Antiderivative,IntegralViaAnti,ClassicAnti}`,
`FluxMVT`).  The **polynomial power rule is already closed**: the period
integrands `z²`, `z³` (`square_calc`, `cube_calc`) integrate exactly via FTC
(`MinkowskiHigherWeightPeriod.higher_weight_period_integrands_integrate`,
`∫_0^1 d(z^n) = 1`), and the weight-2 period has a dyadic-integral representative
too (`MinkowskiPeriodIntegral.weight2_period_integral_pure`).  So the real-variable
integration the higher-weight period needs is *built*.  And the period relations'
**generators are present too**: `S` (order 4, the Gaussian unit `i`) and `U`
(order 6, the Eisenstein unit `ω`) — the `{4,6}` torsion of `PSL(2,ℤ)`
(`UTracePeriodic.elliptic_orders_four_and_six`) — govern `r|(1+S)=0` and
`r|(1+U+U²)=0`, and the weight-2 period is exactly `S`'s eigenvalue
(`MinkowskiPeriodRelations.weight2_period_is_S_eigenvalue`,
`MarkovModularBridge`).  And the **slash action on `V_{k−2}` is now built** (weight
4): `MinkowskiPeriodPolynomial` realises `S`/`U` on the degree-2 coefficient module
and solves the period relations — the weight-4 period polynomial is **`1 − X²`**
(`period_satisfies_relations`), the unique line `ℤ·(1 − X²)` annihilated by both
`r|(1+S)=0` and `r|(1+U+U²)=0` (`relations_closed_form`, `period_line_in_kernel`),
the `−1`-eigenvector of `S` cycled with order 3 by `U`.  And the contour itself
need not be analytic: in the **modular-symbols** formalism the period over the
geodesic `{α, β}` is a formal class, and the **Manin trick** decomposes it into
unimodular symbols `{p/q, r/s}` (`det = ±1`) — exactly the Stern-Brocot/Farey
neighbours the repo builds.  `MinkowskiModularSymbol.manin_unimodular_decomposition`
proves the mediant subdivision preserves the determinant, so the contour's
*combinatorial skeleton* is the Stern-Brocot path of unimodular pieces, ∅-axiom.
What genuinely remains is then only the **analytic atom** — the value of `f`'s
period over a *single* unimodular symbol — the combinatorial decomposition into
those atoms being done.  This atom is **not** the reached-by-none residue: it is a
**Cut** (a real, `Nat → Nat → Bool`), the `toCauchy` *fold* of a computable
approximant sequence (the form's `q`-expansion; for the weight-4 Eisenstein case
the atom is the **holonomic** `ζ(3)`, whose convergents satisfy Apéry's P-recursive
recurrence, `Cauchy/DepthAperyCubic`).  A holonomic real has a *constructed*
modulus (`theory/math/analysis/holonomic_modulus.md`) — a finite-state fold — so it
is a constructible cut, *reached by its own fold*, only not yet built here (the
`q`-expansion machinery is the construction task).  The genuine residue is the
**non-holonomic** surplus — the cut with no finite-state modulus
(`reached_by_none.md`, `non_holonomicity_as_finite_state_escape.md`) — which the
classical modular periods are not.  So the residue supplies the combinatorial
cocycle, the period polynomial `1 − X²`, and the Manin contour; the analytic atom is
a *fold to be constructed*, not a residue to be pointed at.

## Self-check

- Importing a comparison frame? No — `?` is read in 213-native primitives
  (defect / twist / period), with the classical Eichler–Shimura named as the dual
  reading, not the standard 213 is "measured against."
- View promoted to identity?  Guarded: the cocycle is the *positive* (name/source)
  face; the escape (`reached_by_none`, no-back face) is the complementary face —
  both faces of one residue, neither the whole.
- Overreach?  The honest boundary above marks weight-2/tree as closed, higher
  weight/full-group/multifractal as open.

## Constructive accessibility

```lean
#check @minkowski_is_markov_valued_cocycle   -- defect = bounding Markov number, unimodular
#check @minkowski_cocycle_twist              -- twist = Cayley–Hamilton / Vieta jump
#check @cocycle_defect_general               -- defect = det M · N.c on all of M₂(ℤ)
#check @minkowski_weight2_period_relation    -- weight-2 period = √(−1) congruence
#check @golden_is_extremal_weight2_period    -- φ = extremal instance (Lagrange √5)
#check @weight2_period_is_S_eigenvalue       -- weight-2 period = S-eigenvalue ((1+S) generator)
#check @higher_weight_period_integrands_integrate  -- z²/z³ integrate exactly via FTC
#check @period_satisfies_relations            -- 1 − X² is the weight-4 period polynomial
#check @period_line_in_kernel                 -- the period space is the line ℤ·(1 − X²)
```

All ∅-axiom (`tools/scan_axioms.py` PURE).

## Cross-references

- `theory/essays/foundations/reached_by_none.md` — the complementary escape face.
- `theory/math/analysis/markov_spectrum.md`, `markov_uniqueness.md` — Pillar 2.
- `theory/essays/p_orbit/{stern_brocot_as_universal_lattice,the_modular_geodesic_lens}.md`
  — the Stern-Brocot / modular-surface readings.
- `lean/E213/Lib/Math/NumberSystems/Real213/{MinkowskiCocycle,MinkowskiGoldenExtremal,
  SternBrocotMarkov,OdometerSternBrocotUnit}.lean` — sources.
