# Session Handoff — 2026-06-02

## Branch
`claude/non-holonomicity-rGhug` — pushed.  Working tree clean.  All new theorems ∅-axiom.

## Latest: merged `main` (27 commits) + integrated the divergence-depth / Casoratian thread

Brought main's **divergence-depth / Casoratian / Lens-Tower** material into the branch and
connected it to the non-holonomicity work (build green, foundations PURE):

  - **`DepthMonotoneSynthesis.lean` (2 PURE)** — joins the two readings of finite depth: main's
    *algebraic* `finite_depthZ_iff` (`polyDepthZ d s ↔ s = newtonZ c d`) and my *order-theoretic*
    `polyDepthZ_evMono`.  `newtonZ_evMono` (every Newton polynomial is eventually monotone) +
    `s2Z_not_polynomial` (popcount equals **no** polynomial — the ring-escape read through the
    characterization; "the generating ring" is now literally the polynomial ring).
  - **`CFiniteHomogRec.lean` (3 PURE)** — closes the hierarchy: C-finite ⊆ P-recursive.
    `order2_homogRec`/`order3_homogRec` (a constant-coefficient recurrence *is* `HomogRec`);
    `trib_homogRec` places **Tribonacci** (the `SecondCasoratian` witness) inside the holonomic
    class — the opposite pole from Thue–Morse.  Chain now end-to-end: polynomial ⊆ C-finite ⊆
    P-recursive ⊊ non-holonomic, with the **Casoratian (discrete Wronskian) as the order detector**.

Essay rewritten with the end-to-end hierarchy section + Casoratian framing.

**Discriminant↔hierarchy thread — DONE** (`EllipticPeriodicTier.lean`, 9 PURE).  The order-2
recurrence `s(n+2)=p·s(n+1)−q·s(n)` companion `comp p q` has `comp_disc : disc = p²−4q` = the
`HyperbolicEllipticTrace` φ/π discriminant.  `comp_eq_S` (`comp 0 1 = S`), `comp_eq_U`
(`comp 1 1 = U`): the elliptic generators *are* periodic order-2 companions; `periodic_elliptic_S/U`
(period 4 / 6) + `elliptic_S_homogRec` place elliptic at the periodic bottom tier, hyperbolic
(`comp 3 1`, disc 5) growing.  The φ/π pole work and the depth hierarchy are one structure at the
order-2 rung.  Essay updated.

## The autonomous-machine axis is **closed tight** (Morse–Hedlund iff + full Thue–Morse)

State after this leg (all ∅-axiom, pushed):
  - `MorseHedlund.lean` **16 PURE** — `bool_autoRec_iff_evPeriodic`: `AutoRec` over the
    `{0,1}`-embedding **⟺** eventually periodic.  Forward = `bool_autoRec_periodic` (pigeonhole);
    converse = `bool_evPeriodic_autoRec` (period `p`+threshold `N` ⟹ window `N+p`, single-slot
    rule `F w = w N`).  Escaping `AutoRec` ⟺ aperiodic, **no slack**.
  - `ThueMorseAperiodic.lean` **42 PURE** — the canonical dense witness, complete: definition
    (`tmF`/`tmF_canon` fuel-structural), recurrence (`tm_even`/`tm_odd`/`tm_pair_differ`),
    **run-length ≤ 2** (`tm_run_le_two`: no three consecutive equal), **aperiodicity**
    (`tm_not_evPeriodic`, period-descent), the **dense escape** (`tm_morse_not_autoRec`), the
    **automatic structure** (`tm_eq_popParity` = popcount mod 2), the **ring-escape** (`s2` =
    popcount unbounded yet non-monotone: `s2_not_eventually_monotone`, `s2_unbounded`,
    `s2_pw2`/`s2_ones`), the **witness unification** (`isPow2_eq_s2_one`: sparse `χ` and dense `tm`
    are one automaton `s2`, different output maps — `s2_eq_one_iff`, `isPow2_true_iff`,
    `s2_eq_{zero,one}_imp`), and an **actual continued fraction** (`tmCF` = `{1,2}`-valued:
    `tmCF_mem`, `tmCF_ge_one`, `tmCF_not_autoRec` via shift-invariance `autoRec_shift`).
  - **Location, sharp**: `χ` escapes both machine classes (zero-runs); Thue–Morse escapes
    `AutoRec` only — its `¬ HomogRec` is *not* ∅-axiom-closable (run-length ≤ 2 forbids the
    zero-run certificate; the real obstruction is the deep automatic∧aperiodic⟹non-holonomic
    theorem, sharing π's open status).

### Ring-escape bridge — CLOSED (big infra build, 49 PURE across 3 files)
The `eventually_monotone_of_polyDepth` bridge — flagged open last leg — is now a full ∅-axiom
theorem.  Three new files:
  - **`Meta/Int213/Order.lean`** (34 PURE) — the `Int` ordering layer the repo lacked (Lean-core
    `Int.le_trans`/`lt_trichotomy` carry `propext`): `le_trans`/`lt_trans`/`lt_of_le_of_lt`,
    `lt_irrefl`, `add_le_add_*`, `pos_zero_or_neg`, negation-reverses-order, `ofNat` embedding —
    from inductive `Int.NonNeg` + `ring_intZ`.  Reusable foundation.
  - **`Cauchy/PolyDepthMonotone.lean`** (11 PURE) — `polyDepthZ_evMono`: every finite-Δ-depth
    integer sequence is eventually monotone.  LPO-free sign trichotomy on the constant top
    difference (`c>0` strict-increase descent / `c<0` negation / `c=0` faithful-`Int` depth-drop).
  - **`Cauchy/ThueMorseRingEscape.lean`** (4 PURE) — `s2Z_not_polyDepthZ : ¬ ∃ d, polyDepthZ d
    s2Z`: popcount has no finite difference-depth (MonoFromZ ⊥ `s2_not_eventually_monotone`;
    AntiFromZ ⟹ bounded ⊥ `s2_unbounded`).

### Both cores CONCLUDED (located, not forced — per "map the boundary" discipline)
  - **Dense `HomogRec`** — `HomogRecPeriodic.evPeriodic_homogRec` (1 PURE) closes the elementary
    half (`EvPeriodic ⟹ HomogRec`, via an `if`-guarded `lead`/`R`).  With `AutoRec ⟺ EvPeriodic`,
    the *entire* residual content is the one classical theorem `HomogRec ∧ bounded ⟹ EvPeriodic`,
    which is non-elementary (time-varying transition defeats the finite-state pigeonhole; zero-run
    is the only elementary handle, and `tm_run_le_two` denies it past order 2).  Verdict: dense
    escape ≡ bounded-P-recursive theorem, hard half outside elementary reach — π's neighbour.
  - **π** — classically open, provably no ∅-axiom shadow (FGS irreducibly analytic; bottoms at
    Gauss–Kuzmin normality; even PQ-unboundedness open).  The deliverable is the *map*: escape
    ∅-axiom-certified for constructed witnesses on every elementary axis; both unreachable cores
    pinned to named classical theorems.  Verdicts written in the essay ("The verdict on the two
    cores") + `G185`.

## Earlier this leg: Thue–Morse — dense Morse–Hedlund witness + automatic structure → `Cauchy/ThueMorseAperiodic.lean` (21 PURE)

**Automatic half (`tm_eq_popParity`).**  Thue–Morse *lacks* term-window memory (`AutoRec`,
escape above) but *has* digit memory: `tm n = ` parity of the binary digit-sum `popcount(n)`
(`s2` fuel-structural; `s2_even : s2(2n)=s2(n)`, `s2_odd : s2(2n+1)=s2(n)+1`; `succ_parity`
parity-flip; strong-induction match against `tm`'s even/odd recurrence).  This pins the exact
divergence of the two finite-state notions — finite memory *in the digits of the index*
(automatic, Thue–Morse has) vs *in the previous terms* (window-recurrence, Thue–Morse lacks).
Classically automatic ∧ aperiodic ⟹ non-holonomic (Cobham/Christol); both hypotheses now
∅-axiom, the term-window escape is the elementary shadow.  Essay + G185 updated.

### Dense aperiodicity half (`tm_morse_not_autoRec`)
The dense non-holonomicity axis is now **non-vacuous on the canonical example**.  `tm`
(Thue–Morse, run-length `≤ 2`) defined by fuel-structural recursion (`tmF` + `tmF_canon`
fuel-irrelevance; well-founded recursion leaks `propext`); recurrence `tm_even : tm(2n)=tm(n)`,
`tm_odd : tm(2n+1)=¬tm(n)`, hence `tm_pair_differ`.  **Aperiodicity** (`tm_not_evPeriodic`) by
self-similar period-descent: `even_descent` (period `2q`→`q`), `odd_descent` (period `2r+1`→`2r`),
strong induction on the period bottoming at period `1` = `tm_pair_differ`.  Result:
`tm_morse_not_autoRec := aperiodic_not_autoRec tm tm_not_evPeriodic` — a concrete *dense*
inhabitant of the Morse–Hedlund escape (previously only the long-run `isPow2`).  Wired into the
`Cauchy` umbrella; essay + `G185` updated.  Closes the open-frontier item "a genuinely dense
formalised instance awaits only its own aperiodicity".

## What Was Done This Session (π non-holonomicity marathon, cont.)

### π's boundedness frontier → `Cauchy/PositiveFloorUnbounded.lean` (13 PURE)
The structural reason the CF-holonomicity tiers above periodic live on **unbounded** partial
quotients, proved constructively (no LPO):
- **`positive_floor_unbounded`** — a positive *constant* top finite-difference
  (`polyDepth (m+1) s`, `liftK (m+1) s 0 ≥ 1`) ⟹ `s` **unbounded** with an *explicit* witness
  `n = N+(B+1)`.  Engine: positive top diff ⟹ `Δᵐs` strictly increasing everywhere;
  `evStrictMono_down`/`evStrictMono_descend` push it down to `s`; `evStrictMono_unbounded`
  telescopes.
- **`bounded_floor_zero`** — decidable-on-`ℕ` contrapositive: bounded depth-`(m+1)` ⟹ top
  difference `= 0`.
- **`positive_linear_exact`** — depth-1 positive-floor closes to the *exact* `s n = s 0 + c·n`
  (truncation vanishes for `c ≥ 1`); the ∅-axiom positive-linear case of the Newton–Gregory-
  blocked `QuasiPolyCF ⟹ poly-bounded` bridge.
- **`ePQ_unbounded`** — e's `2k+2` section has positive top difference ⟹ e's partial quotients
  unbounded *through the structural theorem*.
- **3 agents** (literature / red-team / repo-infra).  Promoted to
  `theory/math/analysis/cf_holonomicity_hierarchy.md` (frontier + boundedness subsection);
  scratch `research-notes/G173_pi_cf_boundedness_frontier.md`.

**Honest scope (red-team-corrected):** the theorem covers *positive-degree polynomial sections
only*.  Periodic floor (`φ`,`√2`) is not finite-difference-depth; the `2ⁿ` gap is exponential
(no finite depth) — both OUTSIDE the hypothesis class, NOT explained by this lemma.  "bounded
⟹ eventually constant" = LPO (Mandelkern 1988), deliberately NOT ∅-axiom (mirrors
`MonotonicBounded`).  Propext landmine caught: `Nat.sub_eq_zero_of_le` → replaced by
`Nat.sub_le_sub_right`+`Nat.sub_self`.

### Marathon-3 (all three branches attempted, this session-leg)
- **Branch 2 DONE** — `Real213/HyperbolicEllipticTrace.lean` (5 PURE): the φ/π split is the sign
  of `Δ = tr²−4` (golden `[[2,1],[1,1]]` hyperbolic `Δ=5`; `S,U` elliptic orders 4,6 `Δ<0`);
  Wick `cos(iθ)=cosh θ` = the sign flip.  Formalizes C-π2.
- **Branch 3 DONE** — `theory/math/analysis/phi_pi_poles.md`: theorem-anchored essay (φ/π poles,
  pentagon forbidden axis, *holonomicity is a property of the pointing*); registered in
  `theory/math/INDEX.md` (12 analysis sub-clusters).
- **Branch 1 DONE (recon)** — `research-notes/G175`: FGS analytic obstruction has **no ∅-axiom
  shadow** (Fuchs–Frobenius + Stokes summability + Tauberian transfer, irreducibly complex);
  **π unreachable** (bottoms out at open Gauss–Kuzmin normality).  *New finding*: a second
  ∅-axiom-reachable obstruction finer than Klazar — **Garrabrant–Pak mod-2 forbidden-factor**
  (P-recursive ℤ-seq's `aₙ mod 2` omits a factor; arXiv:1505.06508) — but it too is vacuous on
  π.  Queued ∅-axiom targets (neither reaching π): Champernowne-parity (needs GP Lemma 1.2.1 +
  `v₂` infra), Thue–Morse/Sturmian (needs full TM aperiodicity + bounded-P-rec⟹periodic; repo
  has only partial TM + the `expSeq` pigeonhole template).  No new Lean (disciplined outcome for
  an open analytic problem: map the boundary, don't force an unverified proof).
  **Correction to G173**: "P-recursive ⟹ eventually periodic mod m" is false for *unbounded*
  (Banderier–Luca); the forbidden-factor statement is the correct unbounded analog.

### Ontology arc — `research-notes/G174` (φ/π as residue projections; conjectures C-π1..4)
The φ↔π conceptual thread, ∅-axiom-anchored where possible: π = the continuous-symmetry /
(operation=object, §6.2) projection of the residue's self-reference; φ = its discrete
fixed-point projection.  **New ∅-axiom anchor**: `Real213/PentagonGoldenTrace.lean` (6 PURE) —
`φ = 2cos(π/5)` algebraic skeleton (`phi_quad`, `pentagon_trace_quad/unit`), norm-`−1` golden
units (`phi_norm`, `pentagon_trace_norm`) carrying the det-1 descent.  Conjectures: C-π1
(continuous-symmetry image, not the residue itself), C-π2 (φ↔π = hyperbolic↔elliptic / Wick
`cos(iθ)=cosh θ`), C-π3 (π = det-1 bracket between allowed axes 4,6 around forbidden 5 — the
*reachable* Wallis face, `DepthPiQuartic`), C-π4 (operation=object ⟹ no rule/state split ⟹
non-holonomic — the CF pole face is §6.2's shadow).  Tier-1 conceptual; proven anchors only.

### Key agent findings (for next session)
- π's partial-quotient **boundedness is OPEN** — not even a sharp conjecture; unboundedness is
  only the Gauss–Kuzmin heuristic, and π is not known GK-normal.  (Correct G170's "conjecturally
  unbounded" wording.)
- "**bounded integer P-recursive ⟹ eventually periodic**" IS a (classical) theorem — mod-`m`
  periodicity of the polynomial recurrence coefficients (Garrabrant–Pak).  Not ∅-axiom here.
- **Klazar bound** (holonomic ⟹ `|aₙ| ≤ cⁿ·(n!)^d`): super-`(n!)^d` growth ⟹ non-holonomic —
  route to a *genuinely* non-holonomic witness (C10, next).

---

## Prior session (branch `claude/goal-g166-A6MVE`, merged to `main` at `c1ed6a7`)

### 1. Merged `origin/main` (88 commits) into the branch
Resolved 5 conflicts (umbrella imports, `IntensionalCompletability` add/add cross-branch
convergence, `tower_native_completeness.md`, HANDOFF).  Adapted `RefinedCompletabilityEngine`
to main's `crossDetSmall_rescale_antitone` API.  Verified PURE + full build.

### 2. Spiral-axis exhaustiveness + binary cover + crystallographic bridge
- `CayleyDickson/Integer/ImaginaryQuadraticUnitTrichotomy.lean` (9 PURE).
  `unitForm_generic_axis` (Diophantine: `a²+d·b²=1`, `d≥2` ⇒ only `±1`),
  `imaginary_quadratic_unit_trichotomy` (axis = closed range `{2,4,6}`),
  `maximal_order_no_complex_unit` (the `d≡3 mod4` reduced form too), `axis_binary_cover`
  (`{2,4,6}=2·{1,2,3}`, midpoint `μᵏ=−1` = Cassini sign), `crystallographic_cosines`
  (Eisenstein `ztrace(ζ6^k)=2cos(2πk/6)={1,−1,−2,−1,1,2}`).
- `CayleyDickson/Tower/SpiralAxisCrystallographic.lean` (1 PURE): `{2,4,6}` = even half of
  crystallographic `{1,2,3,4,6}` = `2·{1,2,3}` (verified bridge to `crystallographic_restriction`).

### 1. (from main) The divergence-depth / Apéry-zeta math (`Lib/Math/Cauchy/`)
- **`DepthAperyCubic` (23 PURE)** — the Apéry zeta coefficient-degree statistic: ζ(2)
  recurrence coefficients (`(n+1)²`, `11n²+11n+3`, `n²`) are `polyDepth 2`; ζ(3) (`n³`,
  `34n³−51n²+27n−5`, `(n−1)³`, reindexed `n=m+2` to clear ℕ truncation) are `polyDepth 3`;
  depths pinned **exactly** (`aperyTop_depth_exact`, `zeta2Top_depth_exact`).
  **Honest correction (red-team agent):** coefficient degree is *incidental to irrationality*
  (ζ(4) order-2 doesn't prove it; Catalan β(2) order-2 OPEN; ζ(5) order-3) — the e→ζ(2)→ζ(3)
  degree run does NOT continue; ζ(3) deg-3 is the exception above the order-2 sporadic family.
- **`DepthQuadraticGeneric` (7 PURE)** — `quadratic_polyDepth : ∀ A B C, polyDepth 2
  (A·n²+B·n+C)` (whole order-2 sporadic family) via Newton-form transfer + `polyDepth_congr`.
  `quad_eq` now closes with `by ring_nat` (the old hand `add4_reorder` deleted).
- **`DepthCubicGeneric` (5 PURE)** — `cubic_polyDepth : ∀ A B C D, polyDepth 3 (A·n³+…)`,
  crux `cube_eq` (`n³ = 6·C(n,3)+6·C(n,2)+n`); all multivariate reorders via `by ring_nat`.
- **`CasoratianStep` (5 PURE)** — subtraction-free discrete-Wronskian law `c₂Cₙ=−c₀Cₙ₋₁`
  (`casoratian_step`; middle coeff cancels) + `telescope` (`(∏P)g(n)=(∏Q)g(0)`).
- **`CasoratianSigned` (17 PURE)** — the signed Casoratian over **ℕ-pairs** (`NatPairToInt`:
  ℤ = ℕ-pair, sign = axis swap).  `casoratian_signed` (= `casoratian_step` repackaged),
  `telescope_pair` (ζ(3) constant `+6/n³`), `telescope_pair_alt` (ζ(2) alternating `±5/n²`,
  `iterNeg n` = `(−1)ⁿ`), `cube_casoratian_telescope`.  **The "needs ℤ" caveat dissolved
  213-natively** — sign is the residue's binary axis-distinguishing.
- **`CassiniSigned` (2 PURE)** — the residue floor's Cassini cross-determinant
  `fib(n+2)fib(n)−fib(n+1)²=(−1)ⁿ⁺¹` as the **depth-0** signed Casoratian (`cassini_pair`):
  magnitude 1 (det-P/φ floor) + sign Oscillate.
- **`DepthResidueFloor` (2 PURE)** — `self_pointing_depth_ladder`: depth read in 213 as
  drift from the `P`/φ Cassini floor — e:1 → ζ(2):2 → ζ(3):3.
- **`DepthSelfReference` (3 PURE)** — `diff` realises the Converge/Escape outcomes of
  `Lens.SelfReferenceThreeOutcomes` (`W` settles at unit `1=det P=NS−NT`; `2ᵏ` never closes).
- **`PolynomialDepth` (13 PURE)** — ★ the general **degree = depth** theorem:
  `polyDepthZ_polySeq : ∀ a d, polyDepthZ d (polySeq a d)` (`polySeq a d n = Σ_{i≤d} aᵢ·nⁱ`,
  any ℤ coeffs), via the finite-depth **ring** (`idZ` depth 1, `powSeq i` depth i by
  `polyDepthZ_mul`, `polyDepthZ_mono`+`polyDepthZ_add`) — no Stirling.  `aperyLeadZ_depth`:
  the ζ(3) coeff `34n³−51n²+27n−5` (negative coeffs) has depth 3 over ℤ with **no reindex**
  (vs the ℕ version's `n=m+2`); `aperyLeadZ_value` = 117 at n=2.
- **`DepthCharacterization` (13 PURE)** — ★ the capstone: `finite_depthZ_iff` (`polyDepthZ d s ↔ ∃ c, s = newtonZ c d` — finite divergence depth ⟺ degree-≤d polynomial; ⟹ `reconstruct`, ⟸ new ℤ binom-column depth `polyDepthZ_binomColZ`) + exactness `newtonZ_depth_drop` (depth = degree exactly).  Unifies this branch's ℕ ladder with the concurrent ℤ `reconstruct`.

### 3. π non-holonomicity MARATHON → `Cauchy/HurwitzianCF.lean` (21 PURE)
The CF-holonomicity hierarchy on the **partial-quotient sequence** `(aᵢ)` (third spiral-layer
reading).  `QuasiPolyCF p a` (= Hurwitzian: polynomial on each residue class mod p).  Tiers:
**0** `periodic_quasipoly` (quadratic irrationals); **1** `e_cf_quasipoly` (e=[2;1,2k,1] is
`QuasiPolyCF 3` — folklore "Hurwitzian ⟹ holonomic" made explicit) + `tan_cf_quasipoly`;
certificate `polyDepth_diff_recurrence` (`Δ^{d+1}=0`); **properness** `geometric_not_quasipoly`
(`2ⁿ ∉ QuasiPolyCF`, yet C-finite ⟹ `QuasiPolyCF ⊊ C-finite ⊊ holonomic` STRICTLY);
μ=2 bridge half `ePQ_linear_bound`/`tanPQ_linear_bound`.  **4 research agents** (literature,
repo-infra, red-team, synthesis).  Promoted `theory/math/analysis/cf_holonomicity_hierarchy.md`.

### 4. μ-positioning grounded (vs the irrationality measure)
A 4th research agent vs literature confirmed: the rate modulus `N(m,k)` IS the
irrationality-measure function `ψ(q)` (genuinely finer than μ = its limsup); divergence depth
is ORTHOGONAL + presentation-dependent (does NOT separate numbers); the CF-tier separates e/π.

### 5. Markov spectrum from the repo's own forms (`Real213/GoldenFormMarkov` 9 PURE, `MarkovTree` 13 PURE)
- `golden_anisotropic` (Vieta descent `(m,k)↦(k,m−k)`, no mod-5): golden form `m²−mk−k²`
  (disc 5) is the **first Markov form**, value `√5` = Lagrange minimum (φ).  `silver_anisotropic`
  (reuses `sqrt2_irrational`): disc-8 form, `√8`.  `golden_min_attained_on_fib` (= `fib_cassini_norm`):
  the `W=±1` floor IS the form's minimum, on φ's Fibonacci convergents.
- `markov_vieta` (Vieta jumping preserves `x²+y²+z²=3xyz`, coeff `3=NS`, no-subtraction
  invariant `x²+y²=z·z'`), `markov_tree_branch`, `markov_symm`, `markov_fibonacci_branch`
  (odd Fib 1,2,5,13,34) + `markov_pell_branch` (odd Pell 1,5,29,169) = the two spines,
  `markov_first_fork` ((1,2,5) forks to Fibonacci/Pell = Stern-Brocot binary node).
- Promoted `theory/math/analysis/markov_spectrum.md`.

### 6. Modular tower + Lagrange extremes
- `Real213/ModularElliptic.lean` (7 PURE): `modular_generator_orders` — `S` order 4, `U`
  order 6, det 1; `PSL(2,ℤ)=ℤ₂*ℤ₃`, elliptic orders `{4,6}` = Gaussian/Eisenstein axis,
  `−I` central = Cassini 2.  (Grounds a user-proposed axis/lattice/shape table — note G171.)
- `Real213/LagrangeExtremes.lean` (4 PURE): φ = spectrum floor (all-1s CF, `Periodic 1`,
  `QuasiPolyCF 1`, partial quotients pointwise minimal); π = opposite pole (unbounded pq).

## Current Precision Results (0 free parameters)
**No physics constants changed this session** (all work is pure math: irrationality /
approximation / Markov spectrum).  Precision table unchanged — see
`catalogs/physics-constants.md` (1/α_em, m_μ/m_e 0.48 ppb, R∞ 4.3 ppb, Ω_Λ, etc.) and
`catalogs/falsifiers.md`.  DRLT Validation Standard status unchanged.

## Open Problems (Priority Order)

### 1. π non-holonomicity (the marathon headline) — classically OPEN
`(aᵢ)` of π not P-recursive.  NOT closable ∅-axiom.  Provable neighbours closed
(`HurwitzianCF`, `PositiveFloorUnbounded`, `NonHolonomicWitness`, `ZeroRunNonHolonomic`).  The
**genuine non-holonomic tier is now inhabited ∅-axiom by TWO orthogonal certificates**: `(n!)ⁿ`
(`superFact_nonHolonomic`, growth/Klazar — C10) and the bounded powers-of-2 indicator
(`ZeroRunNonHolonomicWitness.chi_nonHolonomic`, zero-run + homogeneity — sparse axis).  Neither
reaches π (dense, slowly-varying).  **But π is provably NOT
reachable by that growth route** (π's p.q. don't grow super-factorially), so π's tier-3
membership needs a *different* obstruction.  **Next (C11):** the FGS *asymptotic-shape*
obstruction (holonomic ⟹ `C·ρ⁻ⁿ·n^θ·(log n)^κ`), incompatible with π's Gauss–Kuzmin
statistics — the genuinely hard, still-open core (and conditional on π GK-normal, also open).
See `research-notes/G173` + `G170`.

### 2. ζ(3) Apéry divergence depth — DEFERRED TO ANOTHER BRANCH (user)
The depth tower `e=3 → π=6 → ζ(3)=?` via the Apéry recurrence
`n³aₙ=(34n³−51n²+27n−5)aₙ₋₁−(n−1)³aₙ₋₂`.  Would precise the "constant+depth" of G171's
3-axis row.  **Do NOT build here.**

### 3. Markov uniqueness ↔ Stern-Brocot indexing — classically OPEN
The binary fork + two spines are anchored (`markov_first_fork`).  A full ∅-axiom bijection
`Markov triples ↔ Stern-Brocot rationals` needs the L/R-word indexing; injectivity = the
Markov uniqueness conjecture (open).  See `research-notes/G172` thread A.

### 4. `QuasiPolyCF ⟹ polynomially-bounded` (general) — Newton–Gregory blocked
General growth bound fails over `ℕ` truncated subtraction for non-monotone polyDepth
sequences (Newton–Gregory reconstruction breaks).  Only witness-specific linear bounds done
(`ePQ_linear_bound`, `tanPQ_linear_bound`).  Don't re-attempt the general version naively.

## Unresolved from This Session (dead ends — don't repeat)
- **Newton–Gregory converse** (`polyDepth d s ⟹ s = newton form`) FAILS over `ℕ`: truncated
  `diff` corrupts non-monotone sequences (e.g. `[2,0,2,…]`).  So T4 general μ=2 bridge blocked.
- **propext landmines** (cost many DIRTY→PURE fixes; for next time): `rw` on an `Iff` pulls
  `propext`; `rw` inside an `ite` *condition* pulls `propext` (use `if_pos`/`if_neg`);
  leaking core lemmas to AVOID — `Nat.mul_assoc`, `Nat.mul_right_comm`, `Nat.add_mul`,
  `Nat.mul_add_mod`, `Nat.mul_add_div`, `Nat.pow_mul`, `Nat.pow_add`, `Nat.add_left_cancel`,
  `Nat.mul_lt_mul_right` (Iff), `Int.natAbs_eq_zero`, `Int.mul_neg`, `Int.eq_of_mul_eq_mul_left`.
  PURE replacements: `NatHelper.{add_mul,mul_assoc}`, `PureNat.pow_add`, `Int.natAbs_eq`, and
  local `add_left_cancel_pure`/`sq_lt_sq`/`pow_mul_pure`/`mul_sub_pure_le` (in GoldenFormMarkov/
  HurwitzianCF).  `abbrev` (not `def`) for Prop-shapes you want `decide` to see.

## Next
Options (none uniquely forced — ask user):
- **Hecke-group Lagrange spectra** (deepen thread C: `2cos(π/q)` ↔ spectrum) — needs cos infra.
- **Lagrange spectrum `<3` discrete part** entirely from anisotropic forms (extend
  `GoldenFormMarkov` along the Markov tree).
- New direction entirely.  (ζ(3) is on another branch.)

## Three-tier state
- **Promotions this session**: `theory/math/analysis/cf_holonomicity_hierarchy.md`,
  `theory/math/analysis/markov_spectrum.md` (both new chapters); updated
  `spiral_coordinate_classification.md` frontier, `tower_native_completeness.md`,
  `theory/math/INDEX.md` (now 11 analysis sub-clusters).
- **Promotion candidates**: `Real213/{ModularElliptic, LagrangeExtremes}` and
  `crystallographic_cosines` are PURE but only noted in research-notes G171/G172 — could fold
  into a short `theory/math/analysis/modular_lagrange.md` if the thread continues.
- **Active scratchpad**: `research-notes/G170` (π non-holonomicity marathon, conjectures
  C1–C7), `G171` (modular tower table), `G172` (three Lagrange threads).
- **Promotions this session**: `theory/math/analysis/divergence_depth_characterization.md` (the
  divergence-depth thread, mirroring the closed Lean; G171 notes archived to `research-notes/archive/`).
- **Promotion candidates**: `Cauchy/{DepthAperyCubic, PolynomialDepth, CasoratianSigned}` +
  the `Meta` `ring` infra — eligible for a `theory/math/analysis/divergence_depth.md` chapter
  per `theory/PROMOTION_CRITERIA.md`.
- **Active scratchpad**: `research-notes/G171_*` (this thread), `G170` (π), `G178` (νF, other
  session).

## File Map
```
NEW Lean (all ∅-axiom):
  lean/E213/Lib/Math/Cauchy/ZeroRunNonHolonomic.lean                       ← bounded non-holonomicity criterion: zero-run + homogeneity (3 PURE) [this session]
  lean/E213/Lib/Math/Cauchy/ZeroRunNonHolonomicWitness.lean                ← powers-of-2 indicator: bounded, non-holonomic (18 PURE) [this session]
  lean/E213/Lib/Math/Real213/HyperbolicEllipticTrace.lean                  ← φ/π = hyperbolic/elliptic, disc sign, Wick (5 PURE) [this session]
  lean/E213/Lib/Math/Real213/PentagonGoldenTrace.lean                      ← φ=2cos(π/5) skeleton, norm−1 golden units (6 PURE) [this session]
  lean/E213/Lib/Math/Cauchy/NonHolonomicWitness.lean                       ← (n!)ⁿ genuinely non-holonomic, Klazar envelope (22 PURE) [this session]
  lean/E213/Lib/Math/Cauchy/PositiveFloorUnbounded.lean                    ← positive top diff ⟹ unbounded (13 PURE) [this session]
  lean/E213/Lib/Math/Cauchy/HurwitzianCF.lean                              ← CF-holonomicity tiers (21 PURE)
  lean/E213/Lib/Math/CayleyDickson/Integer/ImaginaryQuadraticUnitTrichotomy.lean ← axis {2,4,6} exhaustive + cosines (9)
  lean/E213/Lib/Math/CayleyDickson/Tower/SpiralAxisCrystallographic.lean   ← {2,4,6}=even half of {1,2,3,4,6} (1)
  lean/E213/Lib/Math/Real213/GoldenFormMarkov.lean                         ← golden/silver Markov forms √5,√8 (9)
  lean/E213/Lib/Math/Real213/MarkovTree.lean                               ← Vieta tree, spines, fork (13)
  lean/E213/Lib/Math/Real213/ModularElliptic.lean                          ← PSL(2,ℤ)=ℤ₂*ℤ₃ orders 4,6 (7)
  lean/E213/Lib/Math/Real213/LagrangeExtremes.lean                         ← φ floor / π pole (4)
NEW theory chapters:
  theory/math/analysis/cf_holonomicity_hierarchy.md                        ← Hurwitzian / π frontier
  theory/math/analysis/markov_spectrum.md                                  ← √5,√8, Vieta tree, spines
NEW research notes:
  research-notes/G170_pi_cf_nonholonomicity.md                             ← marathon + conjectures C1–C7
  research-notes/G171_modular_tower_axes.md                                ← axis/lattice/shape table analysis
  research-notes/G172_lagrange_threads.md                                  ← Stern-Brocot / φ-π / cosines
MODIFIED:
  lean/E213/Lib/Math/Real213.lean, CayleyDickson.lean, Cauchy.lean         ← umbrella imports
  lean/E213/Lib/Math/Real213/{SpiralCoordinate,RefinedCompletabilityEngine}.lean ← capstone + merge-adapt
  theory/math/INDEX.md, theory/math/analysis/spiral_coordinate_classification.md ← index + frontier
```
