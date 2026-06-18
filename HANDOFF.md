# Session Handoff — 2026-06-17 (marathon continued: arithmetic-function + classical-theorem breadth)

## Branch
`claude/frontier-research-agents-h5okq9` — pushed, ahead of `origin/main`.
Authoritative build `cd lean && lake build E213.Lib` → **green (1972 modules)**.
Strict ∅-axiom intact: every theorem added is `#print axioms`-empty.

## LTE (lifting-the-exponent) — ✅ **FULLY CLOSED ∅-axiom (2026-06-18)**

**`LiftingExponentGeneral.lte`** : `v_p(aⁿ − bⁿ) = v_p(a−b) + v_p(n)` for an odd prime `p` (`3 ≤ p`),
`p ∣ (a−b)`, `p ∤ b`, `b < a`, `n ≥ 1`.  All PURE.  Proof architecture (bottom-up):

- **`BinomialTwoVar.add_pow`** — two-variable binomial theorem `(b+d)ⁿ = Σ_k C(n,k) b^{n−k} dᵏ`
  (was the big missing infra; repo had only the `b=1` `binomSum`).
- **`LiftingExponentPP.{vp_add_eq_min, dvd_sumTo, le_vp_sumTo}`** — ultrametric package
  (strict-minimum valuation law + sum-divisibility lower bound).
- **`LiftingExponentMain.lifting_prime_power`** : `v_p(aᵖ−bᵖ) = v_p(a−b)+1` — the hard kernel
  (binomial: `(b+d)ᵖ−bᵖ = p·b^{p−1}·d + R`; middle `v_p = v_p(d)+1`, tail `v_p ≥ v_p(d)+2` via
  `p∣C(p,k)` + the `k=p` term `dᵖ` using `p≥3`; `vp_add_eq_min` pins it).
- **`LiftingExponentCoprime.lifting_coprime`** : `v_p(aᵐ−bᵐ) = v_p(a−b)` for `p∤m` (same decomp,
  middle `v_p = v_p(d)` since `p∤m`, no `p∣C` needed).
- **`LiftingExponentGeneral.{vp_pow_pk, lte}`** — Step A iterates the kernel `k` times
  (`v_p(a^{pᵏ}−b^{pᵏ}) = v_p(a−b)+k`); Step B factors `n = pᵏ·m` (`k=v_p n`, `p∤m`) and applies
  the coprime case.  Pure `sub_pos_pure` replaces propext-dirty `Nat.sub_pos_of_lt`.

Also landed: `LiftingExponent.{cofactor_sub_dvd, cofactor_not_dvd}` (ℤ cofactor congruence — the
original `p∤exp` algebraic core) + `PowSubPowFactor.pow_sub_pow_factor` (explicit ℤ factorization).
Craft: well-founded-recursion trap — calling the theorem under induction recursively (instead of
`ih`) silently pulls `propext`; always use `ih`.

## Continuation (2026-06-17) — closures landed PURE this segment

Driven autonomously after the debate marathon; each closure built, axiom-scanned PURE,
committed, pushed; `E213.Lib` green throughout.  Breadth across three domains:

1. **σ_m (divisor-power sum) fully closed** — `Lib/Math/NumberTheory/`:
   `DiffPowDvd.{ofNat_pow_eq_ipow, ipow_base_mul}` (cast-power bridge `↑(pⁱ)=(↑p)ⁱ` +
   base-mult `(xy)ⁿ=xⁿyⁿ`); `SigmaPrimePowGeom.sigma_prime_pow_geom` (geometric form);
   `SigmaDivisorClosed.{sigma_prime_pow_divisor_geom, sigma_m_mul, sumZ_bridge}` —
   the genuine divisor sum `(pᵐ−1)·σ_m(pᵏ)=p^{m(k+1)}−1` AND multiplicativity
   `σ_m(ab)=σ_m(a)σ_m(b)`.  Closed form + multiplicativity ⇒ σ_m on every n from its
   factorization (generalizes the repo's σ/τ + euclid_perfect).  Smoke σ₂(12)=210.
2. **Classical metric geometry** — `Lib/Math/Geometry/`:
   `StewartTheorem.{stewart_identity, stewart_scaled, apollonius}` (Stewart's theorem +
   median/Apollonius, integer squared-distance `sq`, via `ring_intZ`);
   `MetricIdentities.{british_flag, parallelogram_law, pythagoras}` (residual `2(u·v)`
   killed by perpendicularity via `eq_of_sub_eq_zero`).
3. **Hockey-stick identity** — `Lib/Math/Combinatorics/HockeyStick.{hockey_stick,
   hockey_stick_column}` — Σ C(r+i,r)=C(r+n+1,r+1), Pascal induction.
4. **Binomial-mean identity** — `Lib/Math/Combinatorics/BinomialMean.binomial_weighted_row_sum`
   — Σ k·C(m,k)=m·2^{m-1} (choose_succ_mul + sumTo_mul_left + pascal_row_sum).
5. **General divisor-sum multiplicativity** — `SigmaDivisorClosed.divisorSumZ_mul_of_completely_mult`
   — `divisorSumZ(ab) g = divisorSumZ a g · divisorSumZ b g` for any completely-mult `g`
   (coprime a,b>0); `sigma_m_mul` is now a one-line corollary.  Reusable infra.
6. **Signed lattice area / shoelace** — `Lib/Math/Geometry/LatticeArea` — doubled signed area
   `area2 = det(B−A,C−A)`; `shoelace`, `area_additivity` (barycentric), translation/cyclic/swap
   symmetry, `Collinear`; **`area2_sq_eq_gram`** (2D Lagrange `area2²=AB²AC²−(u·v)²`),
   **`law_of_cosines`**, **`cayley_menger`** (`16·Area²=4AB²AC²−(AB²+AC²−BC²)²`, the area↔distance
   bridge), **`area2_linMap`/`area2_unimodular`** (signed area scales by `det`; SL₂(ℤ) preserves it).

The Geometry cluster is now 3 files (StewartTheorem, MetricIdentities, LatticeArea) sharing the
integer `Pt`/`sq`/`area2` vocabulary — a rounded elementary Euclidean geometry over ℤ.

**Surmounted a flagged wall**: Cayley–Menger (degree-8) defeats `ring_intZ` directly, but
decomposing through lower-degree lemmas (`area2_sq_eq_gram` deg-4 + `law_of_cosines` deg-2) and an
**abstract assembly lemma** that keeps `AB²,AC²,BC²,dot,area2` as opaque atoms closes it cleanly.
**Reusable technique**: factor any high-degree polynomial identity through intermediate named
quantities held abstract — the `ring_intZ` degree-ceiling is not a hard wall.

**Repo is exhaustively complete for named classical theorems** — confirmed already-closed by
grep: Gauss totient, Euclid perfect, σ/τ mult, Nicomachus + Faulhaber k≤6, Vandermonde + ΣC²,
pascal_row_sum, Lagrange + Cauchy–Schwarz, Brahmagupta–Fibonacci, Gaussian two-square, Wilson,
FLT, Fibonacci-GCD (`Combinatorics/FibonacciGcd.fib_gcd`), TauParity, SigmaParity, Lucas, Kummer.
Remaining HIGH-VALUE OPEN frontiers are all heavy / tactic-bound:
  - **General Rolle/MVT** over arbitrary differentiable functions — needs the extreme-value
    theorem over Real213 (compactness); current MVT is *witness-at* (square/cube only).  Heavy.
  - **Jacobi triple product** (truncated) — pentagonal-number induction.  MEDIUM-HARD.
  - **LTE** (lifting the exponent) — vp infra exists; needs the mod-p binomial step.  MEDIUM.
  - ~~**Cayley–Menger / Heron-squared**~~ — ✅ **CLOSED** (`LatticeArea.cayley_menger`) via the
    abstract-atom decomposition above; the `ring_intZ` timeout was sidestepped, not fought.

Craft notes: `ring_intZ` treats `^` as opaque (expand to `*`), won't cancel `t+(−t)` (use
`sub_self_zero`+`zero_mul`/`mul_zeroZ`), times out beyond ~degree-6 multivariate (decompose
through abstract-atom lemmas), and does **not** iota-reduce pair projections `(a,b).1` (feed it a
`show` with projections pre-applied); `1*x` needs `one_mulZ`; and `Int.ofNat_mul`'s rw pattern
`↑(?n*?m)` needs `show Int.ofNat (a*b) = … from Int.ofNat_mul a b`.

---
## Prior segment — 2026-06-16 (multi-agent debate marathon)

## Branch (prior)
Authoritative build `cd lean && lake build E213.Lib` → green (1959 modules then).
Strict ∅-axiom intact: every theorem added this session is `#print axioms`-empty.

## What Was Done This Session

A continuous **multi-agent debate marathon**: panels (proposer / skeptic /
synthesizer) on seven high-value / high-difficulty frontiers, each returning the
sharpest insight + one ∅-axiom buildable brick + the honest wall.  Six new bricks
+ one honesty correction landed PURE; all integrated into the green `E213.Lib`.

### Bricks landed (all `#print axioms` → empty)

1. **Yang–Mills confinement — spectral face** (`Lib/Physics/YangMills/ColoredGap.lean`).
   `colored_form_identity`: explicit SOS certificate for the operator `Δ₀² − massGap·Δ₀`,
   `⟨Δ₀f,Δ₀f⟩ − 4⟨Δ₀f,f⟩ = 2·(2(f₀+f₁+f₂) − 3(f₃+f₄))² + 6·(f₃−f₄)²` for every config.
   The two squares are exactly the gapped `vTop` (λ=10) and `vTemp` (λ=6) directions.
   `colored_rayleigh_ge` (the operator inequality `Δ₀(Δ₀−massGap·I)⪰0`), `colored_gap`
   (via `lichnerowicz_abstract`, **every colored eigenmode has λ ≥ massGap = 4**).
   Closes angle 1 of `yang_mills_confinement.md`.

2. **Atom-forcing criterion — the kernel** (`Meta/AxisSeparation.lean`).
   `subsingleton_iff_collapses`: the one-hot readout collapses ⟺ the atom axis is a
   subsingleton — the checkable form of "faithful ⟺ distinguishing".  (Corrected the
   panel's first-draft `iff`, which was vacuously false at the subsingleton pole.)

3. **Lorentz metric signature** (`Lib/Physics/Mixing/LorentzSignature.lean`).
   `lorentz_signature_one_three`: `diag(−1,+1,+1,+1)`, signature `(1,3)` via orthogonal
   basis + `det≠0`, sourced `neg=NT−1`, `pos=NS`, `dim=NS+(NT−1)`.  Killed the wrong
   `⋆²`-eigenvalue route (`⋆²=−1` is `(4,0)`, not Lorentzian).  Advances open #4 below.

4. **Chebyshev ψ-lower, base √2→2** (`MultSystemValue.lean`, `ChebyshevLower.lean`).
   `four_pow_le_succ_mul_central_binom` (`4ⁿ ≤ (2n+1)·C(2n,n)`) and `four_pow_le_lcm_mul`
   (`4ⁿ ≤ (2n+1)·lcm(1..2n)`, the textbook `ψ(2n) ≥ 2n·ln2 − ln(2n+1)`).

5. **Markov strip-reframe cap** (`Real213/Markov/MarkovUniqueness.lean`).
   `proper_divisor_of_zhang_modulus_lt_two_c`: every proper divisor of `3c±2` is `< 2c`
   ⇒ `3c±2` is the **terminal** parametric family (a map cap, not a kernel advance).

6. **ζ(3) numerator — harmonic recurrence over the genuine lcm³** (`Zeta3Numerator.lean`).
   `harmonic_recurrence_lcm`: instantiates `harmonic_part_recurrence` at `ℓ = lcm(1..N)³`,
   discharging both divisibility hypotheses via `cube_dvd_lcm_cube`.

### Wave 2 bricks (second debate round)

7. **Hodge conjecture for T⁴ — the biconditional** (`Cohomology/Surfaces/AbelianSurfaceHodge.lean`).
   `hodge11_iff_algebraic` + `neron_severi_T4`: `IsHodge11 F ↔ IsAlgebraic F`
   (`NS(T⁴)=H^{1,1}∩H²`, full Lefschetz (1,1) for `T⁴`) + rank-`4` ℤ-independent
   generator basis + the genuine gap `H^{1,1}⊊H²`.  ∅-axiom-decidable (fixed rational `J`).

8. **Metric signature wiring** (`Physics/Mixing/LorentzSignature.lean`).
   `time_axis_is_order2_via_NT`: the negative axis is canonically the `NT`-sourced
   order-2 (`i`) axis — count `NT−1`, tied to `NT²=4` and `Λ¹ ⋆²=−1` by shared source.
   Honest scope: the strong "MUST be the `⋆²=−1` carrier" is unreachable (`⋆²` is
   uniform `(4,0)` on `Λ¹`).

Honesty fix: `gravity_reconnection_hinge_holonomy.md` cited the **deleted**
`GravityShadow.lean`; corrected with the panel verdict ("gravity = real part" is a
relabeling; standing walls recorded).

### Wave 3 bricks (third debate round)

9. **Hodge-index theorem for T⁴** (`Cohomology/Surfaces/AbelianSurfaceHodge.lean`).
   `cupT4_nsComb`: `Q(nsComb a b c d) = 2(ab − c² − d²)` (general); `hodge_index_signature_T4`:
   orthogonal basis with one `+2` (the ample polarization) and three `−2` ⇒ signature
   `(1,3)` on the rank-4 Néron–Severi lattice — completes the T⁴ Hodge package.

Conceptual yield (Millennium triage panel): the no-witness wall is a **trichotomy** —
(1) signed cancellation (RH, BSD, NS vortex term), (2) uniformity over an unbounded
descent (Markov-H, Collatz, P-vs-NP), (3) **two-Lens interaction** (abc, deep BSD: the
witness would have to count across the `+`/`×` independence the repo *proves* via
`vp_separation` — a heuristic obstruction made structural).  Top buildable frontiers
surfaced: **Bertrand's postulate** (reachable; keystone = primorial bound `∏_{p≤N} p ≤ 4ⁿ`,
~1 week) and the **Selberg sieve SOS positivity** (same shape as `colored_confinement_master`).

### Wave 4 bricks (Bertrand infrastructure — autonomous)

10. **★ Primorial bound `∏_{p≤N} p ≤ 4ᴺ` — CLOSED ∅-axiom** (Erdős's Bertrand keystone).
    `Primorial.primorial_le_four_pow` (PURE), built on the full chain landed this session:
    - `primesIn_split` + `listProd_append` (`MultSystemValue.lean`) — the Erdős window split.
    - `binom_eq_choose` (`BinomChooseBridge.lean`) — Lens `binom` = Lib `choose` (identical
      Pascal recursion; resolves the layer/def hazard via the `Lens.Number` umbrella).
    - `odd_central_binom_le : C(2m+1,m) ≤ 4^m` (`OddCentralBinom.lean`) — `choose_symm` +
      `pascal_row_sum` + sum helpers + `four_pow_eq`.
    - `prime_dvd_odd_binom` + `window_prod_le_odd` + `primorial_le_four_pow` (`Primorial.lean`)
      — the vp divisibility (over the `fact=factorial` bridge), the window bound, the parity
      strong-induction.
    A famous theorem, ∅-axiom.  Corollaries landed: `upper_window_count_pow_le`,
    `prime_count_window_le` (`(N/2+1)^{π(N)−π(N/2)} ≤ 4ᴺ`, a Chebyshev-type π bound).
    Corollaries: `upper_window_count_pow_le`, `prime_count_window_le`.
    **All component lemmas for Erdős's Bertrand are now ∅-axiom** — the `(2n/3,n]` vanishing
    window landed via the (already-closed) `Legendre.legendre` + the pure
    `NatDiv213.div_eq_of_sandwich`: `BertrandWindow.prime_not_dvd_central_binom_mid`.  What
    remains for *full* Bertrand is purely the **assembly** (no new ingredient): partition
    `C(2n,n)=∏p^{vₚ}` over the four prime ranges, the crossover inequality past `N₀≈468`
    (the hard pure-`Nat` asymptotic), and the finite prime chain.  Roadmap:
    `research-notes/frontiers/bertrand_postulate.md`.

11. **Hodge T⁴ — full H² signature** (`AbelianSurfaceHodge.lean`).  `transc_complement_signature`
    (PURE): the transcendental complement `{e02−e13, e03+e12}` is signature `(2,0)` (both
    `+2`, orthogonal, orthogonal to all 4 NS generators, neither `(1,1)`), completing the full
    intersection-form signature `(3,3) = (1,3)_NS ⊕ (2,0)_transc` on `H²(T⁴;ℤ)=ℤ⁶`.

### Corpus-broadening (autonomous, scout-driven) — reliable ∅-axiom bricks, 10+ domains

Per "primacy = breadth" (`07_primacy.md` §7.1), a steady stream of self-contained ∅-axiom
bricks across domains, each `#print axioms`-empty, each committed + pushed:
- **Number theory**: `Norm3` (a²±3b² closures + x²−3y²=1 group law), `Norm5` (the golden
  ℚ(√5) norm a²±5b² + x²−5y²=1, fundamental (9,4)), `lucasZ_double` (L_{2m}=L_m²−2(−1)ᵐ),
  `eval_pmoSucc_one` (1 is a root of Tⁿ−1) + `one_pow_int`, `mediant_cross_diff`
  (Stern–Brocot det) + `mediant_den_gt`.
- **Cohomology/signature**: `ℙ²` (1,0), `ℙ¹×ℙ¹` (1,1) intersection-form witnesses.
- **Discrete curvature**: Gauss–Bonnet for K₄, cube Q₃, Petersen, K₅ + Forman `−2`/`−4`.
- **Algebra**: `octonion_nonassoc` (closed a code-marked "deferred" gap), `cyc3_order3`
  (S₃ 3-cycle), `cyclicAdd_assoc` (ℤ/n monoid).
- **Information**: `entropy_additive`, `surprise_additive` (dyadic chain rule).
- **p-adic**: `vAt_le` (valuation bounded by search depth).
- **Physics-combinatorics**: `so10_counts` (SO(10) forced integer counts from d=5).
- **Analysis/measure**: `measure_union_le`, `cardinality_le_union` (monotonicity).
- **Finite-sum infra**: `foldl_add_acc`, `sigmaList_cons`/`_append`/`_congr` (reusable).
- **Topology**: `signFlip_no_fixpoint` (order-2 antipode is fixpoint-free).
- **Linear algebra**: `Vec.inner_comm` (inner product symmetric).
- **Golden bridge**: `lucas_fib_isNorm5neg` (Lucas–Fibonacci pair realizes the ℚ(√5) norm).

- **Probability**: `discreteNum_append` (linearity of expectation numerator).
- **Holonomy**: `det_holonomy_append` (det∘holonomy is a monoid hom).
- **Continuants**: `continuant_append_entry` (K(l₁++l₂) top-left via K(l₁)·K(l₂)).
- **CD algebra**: `conj_mul_basis` (conjugation anti-hom at the octonion basis pair).
- **GRA**: `canonicalGradeMap_a_slash_b` (grade(slash a b) = 5 = NS+NT, d read off GRA).
- **Power sums**: `two_mul_sum_first` (2·Σk=n(n+1)), `six_mul_sum_sq_first` (6·Σk²=n(n+1)(2n+1)).
- **gcd lattice**: `gcd213_assoc` (gcd associativity; gcd commutative-monoid laws complete).

Scout-driven loop (cycles 3–7): each cycle finds verified gaps in distinct domains; all
closed ∅-axiom, committed + pushed.  Reusable craft: pure-lemma map for the propext-tainted
core (`Meta.Int213/Nat.*`; note `Nat.mul_assoc`/`dvd_trans`/`mul_eq_zero`/`div_eq_of_lt_le`
all carry propext — use `mul_assoc_213`/local `dvdTrans`/`Int213.mul_eq_zero`/`div_eq_of_sandwich`),
`sigmaList_*` for finite sums.  **Remaining scout-7 leads (deferred, MED):** σ_m(p^k)
geometric closed form (needs `ipow_mul`), `cutMul_assoc` (needs cutEq-under-cutMul congruence).

### Honesty correction (wave 1)
`research-notes/frontiers/rebuild_roadmaps/proton_electron_ratio_rebuild.md` —
the Stage-1 bracket claim was **numerically false** (`6π⁵ ∈ (1835.60, 1839.82)`
from `π∈(311/99,22/7)` pins no consecutive integers).  Corrected; `6π⁵` recorded
as numerology (only `6 = NS·NT` is atomic; the `π⁵` exponent has two mutually
inconsistent in-repo justifications) per the derive-don't-reconcile discipline.

### Main conceptual yield — the no-witness duality
`research-notes/frontiers/multi_agent_marathon_2026_06_16.md`.  Two panels (RH and
Markov) independently hit the same wall shape: **a conjecture is ∅-axiom-reachable in
213 exactly when its content has a count-Lens (finite/unsigned/local) witness, and
walled when its content is a *cancellation* (RH: signed sum `M(N)=Σμ`, "signed-
cancellation has no count-Lens witness") or a *uniformity over unbounded descent*
(Markov: "the uniform residue has no local witness").**  Same wall, two readings.

## Current Precision Results (0 free parameters)
| Observable | DRLT | Observed | Error |
|---|---|---|---|
| `1/α_em` ×10⁹ | 137,035,999,111 | 137,035,999,084 | 27×10⁻⁹ ≈ 0.2 ppb |
YM mass gap `= c·min(NS,NT) = 4 > 0` (PURE); **colored modes gapped λ ≥ 4** (new).

## Open Problems (Priority Order)
1. **YM confinement angle 2** (Wilson-loop area law) — honest wall: no embedding on
   `K_{3,2}` ⇒ no enclosed "area"/string tension; holonomy machinery proves the ℕ⁺
   sector loop-free.  No internal handle found yet.
2. **ζ(3) numerator — kernel recurrence** — no clean WZ certificate (harmonic factor
   leaves the proper-hypergeometric class); multi-session by hand.  `zeta3_wz/numerator_plan.md`.
3. **Metric signature** — `(1,3)` form built; deriving *which* axis is the `−` (vs a
   reading) and wiring to `⋆²=−1` is the next positive step.
4. **PNT constant = 1 / RH** — walled (the no-witness duality above); only bracket
   sharpening is ∅-axiom (`four_pow_le_lcm_mul` is the latest rung).
5. **Markov `H`** — terminal; `3c±2` now provably the last linear-invariant family.

## Notes for next session
- `ring_intZ` compares canonical forms and chokes on `0+`/`0*` noise — pre-strip with
  pure `Meta.Int213.{zero_add,zero_mul,add_comm}` (the core `Int.zero_add` etc. carry
  `propext`).  `simp`/`simp only` inject `propext` — avoid; use `rw`/`decide`/`rfl`.
- `decide` refuses goals with free variables (a guard) — use explicit Nat lemmas.
- Core Nat lemmas that carry `propext`/`Classical`: `Nat.lt_of_mul_lt_mul_left`,
  `Nat.sub_pos_of_lt`, `Nat.le_sub_of_add_le`.  Pure replacements exist / derive easily.
- Full `E213.Lib` build exceeds a single 600s timeout when a deep module (e.g.
  `MultSystemValue`) is touched; it resumes from cache on a second invocation.

## File Map
```
lean/E213/Lib/Physics/YangMills/ColoredGap.lean        ← colored-mode spectral positivity (PURE)
lean/E213/Meta/AxisSeparation.lean                     ← atom-forcing kernel (PURE)
lean/E213/Lib/Physics/Mixing/LorentzSignature.lean     ← signature (1,3) (PURE)
lean/E213/Lens/Number/Nat213/{MultSystemValue,ChebyshevLower}.lean ← 4ⁿ≤(2n+1)·lcm rung
lean/E213/Lib/Math/NumberSystems/Real213/Markov/MarkovUniqueness.lean ← strip-reframe cap
lean/E213/Lib/Math/NumberTheory/Zeta3Numerator.lean    ← harmonic_recurrence_lcm
research-notes/frontiers/multi_agent_marathon_2026_06_16.md ← the no-witness duality + brick table
```
