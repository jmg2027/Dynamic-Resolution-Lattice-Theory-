# Multi-agent debate marathon — 2026-06-16

A round of continuous multi-agent panels (proposer / skeptic / synthesizer per
frontier) across seven high-value / high-difficulty frontiers, each returning the
sharpest insight + one ∅-axiom buildable brick + the honest wall.  Bricks that
landed PURE this session are listed with their theorem; the cross-domain meta-insight
is recorded at the end.

## Bricks landed (∅-axiom, this session)

| Frontier | Theorem (file) | What it is |
|---|---|---|
| Yang–Mills confinement | `colored_confinement_master` (`Physics/YangMills/ColoredGap.lean`) | SOS certificate `Δ₀²−massGap·Δ₀ = 2(2(f₀+f₁+f₂)−3(f₃+f₄))² + 6(f₃−f₄)²` ⇒ every colored eigenmode has `λ ≥ massGap = 4`. The **spectral face of confinement** (angle 1 closed). |
| Atom-forcing criterion | `subsingleton_iff_collapses` (`Meta/AxisSeparation.lean`) | The one-hot readout collapses ⟺ the atom axis is a subsingleton. The checkable kernel of "faithful ⟺ distinguishing". |
| Metric signature | `lorentz_signature_one_three` (`Physics/Mixing/LorentzSignature.lean`) | Diagonal form `diag(−1,+1,+1,+1)`, signature `(1,3)` via orthogonal basis + `det≠0`, sourced `neg=NT−1`, `pos=NS`. |
| PNT / Chebyshev | `four_pow_le_lcm_mul` (`ChebyshevLower.lean`) | `4ⁿ ≤ (2n+1)·lcm(1..2n)` — `ψ`-lower base sharpened `√2`→`2`. |
| Markov uniqueness | `proper_divisor_of_zhang_modulus_lt_two_c` (`Markov/MarkovUniqueness.lean`) | Every proper divisor of `3c±2` is `< 2c` ⇒ `3c±2` is the terminal parametric family (map cap). |

Plus an honesty correction: the `proton_electron_ratio_rebuild` roadmap's Stage-1
bracket claim was **numerically false** (`6π⁵ ∈ (1835.60, 1839.82)` from `π∈(311/99,22/7)`
pins no consecutive integers); `6π⁵` recorded as numerology, not 213-forced.

## The cross-domain meta-insight: the **no-witness duality**

Two panels — Riemann/PNT and Markov — independently hit the *same shape* of wall, and
naming it once is the marathon's main conceptual yield:

> **A conjecture is ∅-axiom-reachable in 213 exactly when its content has a
> count-Lens (finite / unsigned / local) witness; it is walled exactly when its
> content is a *cancellation* or a *uniformity* with no such witness.**

The two instances are duals of one statement:

- **Riemann Hypothesis** — RH is about *cancellation in a signed sum* (`M(N)=Σμ(n)`,
  the difference-Lens of the prime count).  Its size **is** the zero locations: no
  modulus `M(k)` certifies the exponent `½` without already knowing the zeros.  By
  contrast `π`, `ψ`, `lcm` are **unsigned monotone counts** with elementary two-sided
  estimates — so Chebyshev (both halves), the density `π(N)/N→0`, and the `√2→2`
  sharpening are all ∅-axiom.  PNT's "constant = 1" = the computable bracket narrowing
  to `{1}`; collapsing it needs the Erdős–Selberg bilinear step, which has **no
  ∅-axiom shadow**.  Diagnosis: **signed-cancellation has no count-Lens witness.**

- **Markov / Frobenius** — the uniqueness kernel is realizability of a `√(−1)`-suborbit
  of discriminant `9c²−4`.  The distinguishing data provably *leaves `c`* at every
  Vieta descent step (the modulus strictly shrinks), so no fixed-`c` finite signature
  carries it.  Every closed family (`pᵏ`, `2pᵏ`, `3c±2`) is **local in `c`**; the
  `3c±2` lever is now provably the last of its kind (the strip-reframe cap).  Diagnosis:
  **the uniform residue has no local witness.**

These are the same wall read two ways: *signed-cancellation* (RH) and *uniformity over
an unbounded descent* (Markov) are each the negation of a count-Lens / local-finite
witness.  This sits beside the CLAUDE.md "Limit/infinity deified" failure-mode and the
`residue_shape_doctrine`: in 213 a horizon constant is reachable **as a narrowing
computable bracket** precisely when an unsigned monotone count underlies it — and the
genuine open conjectures are exactly those whose content is the *absence* of such a
witness (signed cancellation, or a residue uniform over an unbounded orbit).  Pointing
at that residue **is** the conjecture (Frobenius 1913 / the zero-free region), not a
bounded step — the terminal-localization pattern, now seen to be a general phenomenon.

## Wave 2 — bricks landed (∅-axiom)

| Frontier | Theorem (file) | What it is |
|---|---|---|
| Hodge conjecture (T⁴) | `neron_severi_T4` (`Cohomology/Surfaces/AbelianSurfaceHodge.lean`) | The biconditional `IsHodge11 F ↔ IsAlgebraic F` (`NS(T⁴)=H^{1,1}∩H²`, the full Lefschetz (1,1) for `T⁴`) + rank-`4` ℤ-independent generator basis (`nsComb_injective`) + the genuine gap `H^{1,1}⊊H²`. ∅-axiom-decidable because `J` is a fixed *rational* operator. |
| Metric signature wiring | `time_axis_is_order2_via_NT` (`Physics/Mixing/LorentzSignature.lean`) | The negative axis is canonically the `NT`-sourced order-2 (`i`) axis — count `NT−1`, tied to `NT²=4` and the `Λ¹ ⋆²=−1` by shared `NT` source. |

Plus an honesty fix: `gravity_reconnection_hinge_holonomy.md` cited the **deleted**
`GravityShadow.lean` as a live target; corrected, with the panel's verdict that
"gravity = real part" is a relabeling (the Hermitian split is content-free) and the
standing walls (no `G_N`/scale, blocked `h`-curvature, the `b₁=2` vs `b₁=8` forbidden
bridge) recorded.

Wave-2 walls confirmed: general Hodge (continuous `J` / `(2,2)`-torsion / transcendence
— uncrossable by finite `decide`); the strong "the `−` axis MUST be the `⋆²=−1` carrier"
(⋆² is uniform `(4,0)` on `Λ¹` — no asymmetry to single out one axis).

## Wave 3 — bricks + a sharpened diagnostic

**Brick landed (∅-axiom):** `hodge_index_signature_T4`
(`Cohomology/Surfaces/AbelianSurfaceHodge.lean`) — the **Hodge-index theorem for `T⁴`**:
the intersection form `cupT4` on the rank-4 Néron–Severi lattice has signature `(1,3)`
(one positive = the ample polarization `nsComb 1 1 0 0`, `Q=+2`; three negative = the
primitive `(1,1)` classes, `Q=−2`; all cup-orthogonal).  General self-intersection
`Q(nsComb a b c d) = 2(ab − c² − d²)`.  Completes the T⁴ Hodge package
(`neron_severi_T4` + this).

### The no-witness wall is a **trichotomy** (Millennium triage panel)

Applying the duality to the full famous-problem landscape refined it from a binary
(signed-cancellation vs unbounded-uniformity) into **three** negations of a count-Lens
witness:

1. **Signed cancellation** — RH (`M(N)=Σμ`), BSD (`L(E,s)`, the `aₚ` sum), Goldbach's
   minor arc, Navier–Stokes' vortex-stretching `∫ω·∇u·ω`.  A difference-Lens `m−n` with
   no unsigned shadow.
2. **Uniformity over an unbounded descent** — Markov-`H`, Collatz, P-vs-NP (uniform
   circuit lower bound; natural-proofs *is* a no-local-witness theorem), the Navier–Stokes
   supercritical scale-cascade.  The distinguishing datum leaves every modulus.
3. **Two-Lens interaction (new, 213-native)** — abc, deep BSD.  The witness would have to
   count *across* the `+`/`×` independence the repo **proves** structurally
   (`vp_separation`, `TwoThreeUnique`, the `^`-wall): no shared generator ⇒ no joint
   count.  abc's wall is the additive–multiplicative incompatibility — *visible as a
   proven obstruction* only because 213 has `vp_separation`, where classically it is
   heuristic.  This is the marathon's deepest new conceptual yield: 213 turns a heuristic
   into a structural obstruction.

R/P/W table: BSD W, Navier–Stokes W (doubly: signed + cascade), P-vs-NP W, Goldbach P
(per-instance R, ∀ walled), twin primes P (sieve positivity R-adjacent, ∞ walled),
Collatz W, RH W, abc W (two-Lens).

### Top buildable frontiers surfaced (not yet built — multi-week each)

- **Bertrand's postulate** — full Bertrand is ∅-axiom-reachable with current machinery
  (`IntSqrt.isqrt` for √, `FloorLog` for log, `decPrime` for the finite chain, the Kummer
  + window-product layer for Erdős's engine).  **Critical missing keystone:** the
  primorial bound `∏_{p≤N} p ≤ 4ⁿ` (`primorial_le_four_pow`, a new
  `Lens/Number/Nat213/Primorial.lean`) — strong induction, odd-`N` split, reusing
  `primesIn`/`listProd_dvd`/`four_pow_le_succ_mul_central_binom`.  ~1 week, MEDIUM, no
  axiom risk.  The single highest-value ∅-axiom number-theory target.
- **Selberg/Maynard sieve SOS positivity** (twin-prime row) — `Σ_n (Σ_{d|n} λ_d)² ≥ 0`,
  the *only* famous-problem sub-statement whose core is an **unsigned positive quadratic
  form** — the exact shape already closed in `colored_confinement_master`,
  `cauchy_schwarz_gridZ`, `lagrange_pair_identity`.  Closes the sieve's positivity
  machinery (not twin-prime-∞, still walled by Bombieri–Vinogradov).  The landscape's best
  SOS foothold.

## Autonomous segment (waves 4–5) — Bertrand + diversified

Driven autonomously after the debate waves.  **All component lemmas of Erdős's Bertrand
postulate are now ∅-axiom** (only the final assembly — prime-range partition + crossover
inequality + finite chain — remains, no new ingredient):

| Lemma (file) | Content |
|---|---|
| `primorial_le_four_pow` (`Primorial.lean`) | `∏_{p≤N} p ≤ 4ᴺ` — Erdős's keystone |
| `binom_eq_choose` (`BinomChooseBridge.lean`) | the Lens/Lib binomial defs coincide |
| `odd_central_binom_le` (`OddCentralBinom.lean`) | `C(2m+1,m) ≤ 4ᵐ` |
| `prime_dvd_odd_binom`, `window_prod_le_odd` (`Primorial.lean`) | the `(m+1,2m+1]` window |
| `prime_not_dvd_central_binom_mid` (`BertrandWindow.lean`) | **the `(2n/3,n]` vanishing** (via Legendre) |
| `prime_count_window_le`, `upper_window_count_pow_le` | Chebyshev-type `π` corollaries |

Diversified reliable bricks (all PURE, `decide`/witness-style):
- **Hodge T⁴ full signature** `(3,3) = (1,3)_NS ⊕ (2,0)_transc` (`transc_complement_signature`).
- **Surface signatures**: `ℙ²` `(1,0)` (`P2Minimal`), `ℙ¹×ℙ¹` `(1,1)` (`P1Squared`).
- **Discrete Gauss–Bonnet** for non-bipartite/named graphs `K₄, Q₃(cube), Petersen, K₅`
  + Forman `−2` (3-regular), `−4` (4-regular).

Recurring ∅-axiom craft notes (added to the toolkit): `ring_intZ`/`ring_nat` choke on
`0*x`/`0+x` and bare variable-negation factors (`-d`) — pre-strip; core `Nat`/`Int`
lemmas `lt_of_mul_lt_mul_left`, `add_right_cancel`, `div_eq_of_lt_le`, `mul_eq_zero`,
`pow_mul`, `mul_neg` carry `propext`/`Classical` — pure replacements exist
(`Meta.Int213.*`, `Meta.Nat.{PureNat,NatDiv213}.*`, `div_eq_of_sandwich`) or derive via
the `lt_or_ge`+`mul_le_mul_left`+`not_lt` cancellation pattern.

## Focused capstone (wave 6) — σ_m fully closed

After "take one focused target", the divisor-power sum `σ_m(n) = Σ_{d∣n} dᵐ` was closed
end-to-end as a 213-native arithmetic function (∅-axiom):

| Lemma (file) | Content |
|---|---|
| `ofNat_pow_eq_ipow` (`DiffPowDvd.lean`) | cast-power bridge `↑(pⁱ) = (↑p)ⁱ` (ℕ→ℤ coercion commutes with powering) |
| `ipow_base_mul` (`DiffPowDvd.lean`) | `(xy)ⁿ = xⁿyⁿ` — `ipow` completely multiplicative in the base |
| `sigma_prime_pow_geom` (`SigmaPrimePowGeom.lean`) | abstract geometric form `(pᵐ−1)·Σᵢ p^{mi} = p^{m(k+1)}−1` |
| `sigma_prime_pow_divisor_geom` (`SigmaDivisorClosed.lean`) | **genuine divisor sum** `(pᵐ−1)·σ_m(pᵏ) = p^{m(k+1)}−1` (via prime-power reindex + cast bridge) |
| `sigma_m_mul` (`SigmaDivisorClosed.lean`) | **multiplicativity** `σ_m(ab)=σ_m(a)σ_m(b)` for coprime a,b (product reindex + complete-mult cell factor + double-sum separation) |

Closed form + multiplicativity together determine `σ_m` on every `n` from its
factorization — generalizing the repo's existing `σ`(=σ₁)/`τ`(=σ₀) and the
`euclid_perfect` machinery to all `m`.  `sumZ_bridge` reconciles the two textually-identical
corpus `sumZ` recursions (geometric-series vs Möbius-divisor) so the toolboxes compose.
Craft note: `Int.ofNat_mul`'s rewrite pattern is `↑(?n*?m)` (coercion), which does NOT
syntactically unify with an explicit `Int.ofNat (a*b)` goal — force it with
`show Int.ofNat (a*b) = Int.ofNat a * Int.ofNat b from Int.ofNat_mul a b`.

## Honest walls recorded (not reached this session)

- **YM confinement angle 2** (Wilson-loop area law): no embedding on the abstract
  `K_{3,2}` ⇒ no enclosed "area", no absolute string tension to state; the existing
  holonomy machinery proves the ℕ⁺ sector loop-free (no exponential-in-loop decay there).
- **ζ(3) numerator integrality**: the H₃-term and kernel-term *integrality* are
  reachable (pure divisibility via `cube_dvd_lcm_cube` / `heart_lcm`), but the kernel
  *recurrence* has **no clean WZ certificate** (the harmonic factor leaves the
  proper-hypergeometric class) — a certifiability wall, multi-session by hand.
- **m_p/m_e**: `6π⁵` is a ~19 ppm coincidence; pinning it needs a fast (Machin/arctan)
  π cut that does not exist, and even then certifies a coincidence, not a derivation.
- **RH**: no ∅-axiom shadow at all (the signed-cancellation wall above).
