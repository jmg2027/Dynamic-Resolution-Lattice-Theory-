# G139 — Cohomology open-frontier marathon

**Branch**: `claude/cohomology-marathon-qOxOX`.
**Status**: Active.

Multi-session marathon advancing the five `theory/math/cohomology/`
open frontiers carried over from G138:

  · `bipartite.md` — universal `∀ NS NT c, kerSizeDelta0Direct = 2`.
    Blocker: no `GraphWalk/` infra.  Estimate 5–8 sessions.
  · `k32_higher_cohomology.md` — general Steenrod `cup_i` (i ≥ 2),
    non-vacuous Adem / Cartan, Massey triple `⟨ω, ω, ω⟩`.
  · `fractal.md` — structural Gram self-energy derivation,
    ∀-coprime eventual periodicity, truth-table Lean witness.
  · `cupaw.md` — self-referential lex-cup Leibniz ∀(k, l).
    Decomposition machinery (Decomp + UniversalLift + AlgLift{α, β})
    already in place.
  · `hodge_conjecture.md` — HC²¹³ variant automation.

## Strategy

Each closure ships as 213-native ∅-axiom PURE.  Cardinality
cut-off applications follow the Pell / Lucas / Fibonacci /
Tribonacci template from G134 §7.  Higher cup_i and Massey
extend the K_{3,2}^{(c=2)} Steenrod-algebra stack from G132.

## Phase 1 — CLOSED

All three Phase 1 closures CLOSED + PROMOTED:

  1. **G139-A Padovan cut-off** — CLOSED
     (`Lib/Math/Cohomology/Fractal/PadovanCutoff.lean`, 30 PURE).
     Triple Hunter-generator coincidence at odd indices
     `(P_3, P_5, P_7) = (NT, NS, d) = (2, 3, 5)` in arithmetic
     progression (step 2), sister to Fibonacci's consecutive-index
     `(F_3, F_4, F_5)` window.  Fourth catalogue hit `P_8 = 7`.
     Cut-off boundaries: depth-1 at `n ≥ 30` (latest in the
     family), depth-2-restricted at `n ≥ 59`.
     Promoted into `theory/meta/cardinality_cutoff_applications.md`.
  2. **G139-B Filled5CellExtension** — CLOSED
     (`Lib/Math/Cohomology/Bipartite/Filled5CellExtension.lean`,
     13 PURE).  Single 5-cell σ⁵ extending the pyramid tower
     σ³ → σ⁴ → σ⁵.  Establishes `H⁴ = 0`, `H⁵ = 0` at 5-skeleton.
     Massey-triple landing-space audit: `⟨ω, ω, ω⟩ ∈ H⁵ = 0`
     VACUOUSLY trivial at 5-skeleton; non-vacuous Massey needs
     6-skeleton extension + cobounding-chain construction.
     Promoted into
     `theory/math/cohomology/k32_higher_cohomology.md`.
  3. **G139-C Eventually-constant mod 11** — CLOSED
     (`Lib/Math/Cohomology/Fractal/ConfigCountModular.lean` §I).
     `configCountD_5_succ_mod_11` (n : Nat) :
       configCountD 5 (n + 1) % 11 = 1.
     Via `5^(n+1) mod 10 = 5` fixed-point absorption (since
     `gcd(5, 10) ≠ 1`).  Sister to the `(5, 41)` constant
     `9 = NS²` closure.  Promoted into
     `theory/math/cohomology/fractal.md` modular-fingerprint
     table.

## Phase 2 — CLOSED (3 closures, 81 PURE new)

  4. **G139-D Narayana cow cut-off** — CLOSED
     (`Lib/Math/Cohomology/Fractal/NarayanaCutoff.lean`, 31 PURE).
     Direction C 7th sequence.  Recurrence
     `N_{n+3} = N_{n+2} + N_n` (one-shift cousin of Padovan).
     Opens with `(N_3, N_4) = (NT, NS)` mirroring Fibonacci, then
     peels off at `N_5 = 4 ≠ d = 5`.  ★ GAPPED over `{5, 7}`:
     sandwiches `4 < 5 < 6` and `6 < 7 < 9`.  Third hit at
     `N_8 = 13`.  Distinct fingerprint among Direction C
     sequences.
  5. **G139-E Jacobsthal cut-off** — CLOSED
     (`Lib/Math/Cohomology/Fractal/JacobsthalCutoff.lean`, 26 PURE).
     Direction C 8th sequence.  Recurrence
     `J_{n+2} = J_{n+1} + 2 J_n`.  Closed form
     `J_n = (2^n − (−1)^n) / 3`.  Consecutive `(NS, d)` window
     at `(J_3, J_4) = (3, 5)`, multiplicative coincidence
     `J_6 = 21 = NS · 7`.  Always odd for `n ≥ 1`.  Fastest
     growth — earliest depth-1 crossing at `n ≥ 14`.
  6. **G139-F Padovan modular fingerprint** — CLOSED
     (`Lib/Math/Cohomology/Fractal/PadovanModular.lean`, 24 PURE).
     ★ Parametric `Pad_mod_2_period_7` (∀ n, Pad (n + 7) % 2
     = Pad n % 2) via 3-step nested induction + add_mod_gen.
     Pisano-period analogue for the Padovan sequence
     (orbit on `2³ = 8` mod-2 triples visits 7 distinct states).
     Decide-checked period-13 (mod 3) and period-24 (mod 5)
     spot checks.

## Phase 3 — CLOSED (4 closures, 40 PURE new)

  7. **G139-G CupAW Leibniz (4, 2, 1)** — CLOSED
     (`Lib/Math/Cohomology/CupAW/Leibniz4Mixed.lean` +2 PURE).
     Sister to (4, 1, 2) on Δ³; 1024 pattern pairs × 4 indices
     decided.  Closes the (4, 2, 1) bidegree noted in the
     Leibniz4Mixed docstring but previously unproven.
  8. **G139-H TribonacciModular** — CLOSED
     (`Lib/Math/Cohomology/Fractal/TribonacciModular.lean`, 14 PURE).
     `Trib_mod_2_period_4` parametric — 3-step nested induction
     with 3 IH terms.
  9. **G139-I FibonacciModular** — CLOSED
     (`Lib/Math/Cohomology/Fractal/FibonacciModular.lean`, 12 PURE).
     `Fib_mod_2_period_3` parametric — classical Pisano period
     π(2) = 3.  Cleanest 2-step Pisano-analogue.
 10. **G139-J NarayanaModular** — CLOSED
     (`Lib/Math/Cohomology/Fractal/NarayanaModular.lean`, 12 PURE).
     `Nara_mod_2_period_7` parametric — Pisano-period TWIN to
     Padovan: same period, different cycle.

Pisano-analogue trio now covers Fibonacci (π=3, 2-step),
Tribonacci (π=4, 3-step), Padovan (π=7, 3-step), Narayana (π=7,
3-step twin to Padovan).

## Phase 4 — CLOSED (1 closure, 11 PURE new)

 11. **G139-K ∀-coprime eventual periodicity** — CLOSED
     (`Lib/Math/Cohomology/Fractal/EventualPeriodicity.lean`, 11 PURE).
     ★★★★★ `configCountD_eventually_periodic` —  universal
     `∃ T n₀, ∀ n ≥ n₀, configCountD d (n + T) % p
     = configCountD d n % p` under FLT hypothesis.
     Forward-only pigeonhole on the exponent-layer Markov chain
     `expSeq d m n := d^n % m` (transition
     `expSeq (n+1) = (expSeq n * d) % m` by mul_mod_left_pure)
     + forward propagation via Nat induction +
     `configCountD_mod_pure` bridge.  Strict ∅-axiom via
     match-pattern `p = p' + 2`, `NatHelper.*` lemmas, no `omega`.
     Sister to `MulOrderPigeonhole.exists_modPow_period` but
     INVERSE-FREE — handles the `gcd(d, p-1) ≠ 1`
     eventually-constant regime, witnessed at `(5, 11)`.

## Phase 5 — CLOSED (5 closures, 35 PURE new)

 12. **G139-L LucasModular** — CLOSED (new file, 17 PURE).
     `Lucas_mod_2_period_3` parametric — shared orbit with
     Fibonacci.  `Lucas_mod_3_period_8` parametric — same period
     as Fibonacci, distinct orbit.  Cross-sequence cycle-sharing
     decide-check vs Fibonacci on the mod-2 cycle.
 13. **G139-M PadovanModular extension** — CLOSED (+2 PURE).
     `Pad_mod_3_period_13` parametric — upgrade of prior
     decide-spot-check.
 14. **G139-N FibonacciModular extension** — CLOSED (+4 PURE).
     `Fib_mod_3_period_8` parametric — classical Pisano π(3) = 8.
 15. **G139-O TribonacciModular extension** — CLOSED (+5 PURE).
     `Trib_mod_3_period_13` parametric — 3-step nested induction
     with double `add_mod_gen` modular reduction.
 16. **G139-P NarayanaModular extension** — CLOSED (+7 PURE).
     `Nara_mod_3_period_8` parametric — Narayana one-shift
     recurrence diverges from Padovan's mod-3 period 13.

Pisano-analogue trio now complete across five sister sequences
at BOTH mod 2 AND mod 3:

| Sequence  | π(2) | π(3) |
|-----------|------|------|
| Fibonacci |   3  |   8  |
| Lucas     |   3  |   8  |
| Padovan   |   7  |  13  |
| Tribonacci|   4  |  13  |
| Narayana  |   7  |   8  |

## Phase 6 — CLOSED (4 closures, 29 PURE new)

 17. **G139-Q JacobsthalModular** — CLOSED (new file, 14 PURE).
     Three parametric closures: `Jac_succ_mod_2` (eventually
     constant `1` from `n = 1`; structurally distinguished),
     `Jac_mod_3_period_6`, `Jac_mod_5_period_4`.  The `2 J_n`
     term vanishes mod 2 (mul_mod_right) and reduces by
     mul_mod_right_pure at higher moduli.
 18. **G139-R LucasModular extension mod 5** — CLOSED (+5 PURE).
     `Lucas_mod_5_period_4` — cycle `(2, 1, 3, 4)`, shortest in
     the Lucas modular fingerprint.
 19. **G139-S PadovanModular extension mod 5** — CLOSED (+5 PURE).
     `Pad_mod_5_period_24` parametric — 3-step nested induction.
 20. **G139-T FibonacciModular extension mod 5** — CLOSED (+5 PURE).
     `Fib_mod_5_period_20` parametric — classical π(5) = 20.

Pisano-analogue grid across six sister sequences:

| Sequence  | π(2) | π(3) | π(5) |
|-----------|------|------|------|
| Fibonacci |   3  |   8  |  20  |
| Lucas     |   3  |   8  |   4  |
| Padovan   |   7  |  13  |  24  |
| Tribonacci|   4  |  13  | 31 ⊘ |
| Narayana  |   7  |   8  | ⊘    |
| Jacobsthal| const|   6  |   4  |

(⊘ = deferred — periods too long for clean parametric proofs in
this phase.)

## Phase 7 (next session candidates)

  · Tribonacci mod 5 period 31 / Narayana mod 5 (longer base
    verifications required).

  · CupAW Leibniz (5, 1, 2) — pattern decide may be at the
    heart-beat threshold; (3, 1, 2) likely vacuous.
  · K_{3,2} higher Steenrod `Sq^3`, `Sq^4` (vacuous at
    4-skeleton) and Sq^2 explicit chain-level at 4-skeleton.
  · 6-skeleton extension with multi-cell attaching for
    non-vacuous H⁵.
  · HC²¹³ variant automation — extending the 31-capstone Hodge
    stack.

## Phase 8+ (deferred)

  · Truth-table `Fintype`-style witness (`Fintype.card`-equivalent
    in 213-native Lean).
  · `GraphWalk/` infrastructure (multi-session).
  · Gram self-energy structural step (physics-layer).
  · Self-referential lex-cup Leibniz ∀(k, l) full parametric.

## Cross-references

  · `theory/math/cohomology/{bipartite, k32_higher_cohomology,
    fractal, cupaw, hodge_conjecture}.md` — chapters.
  · `theory/meta/cardinality_cutoff_applications.md` — G134
    six-direction template.
  · `HANDOFF.md` — G138 corpus synthesis carry-over.
