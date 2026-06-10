# Session Handoff — 2026-06-10 (modulus-degree ladder: ζ(3) fold → form-margin → composed degree)

## Branch & build state
`claude/zeta-3-holonomic-fold-gbjygu` — `origin/main` merged in (async-growth +
positivity-crossdomain marathon).  **Fresh `rm -rf .lake/build && lake build` ✓ clean.**
Kernel regression 45/45 0-axiom.  Session modules strict ∅-axiom PURE
(`tools/scan_axioms.py`): `Zeta3Cut` 35/0, `CubeRootTwoCut` 31/0,
`ModulusComposition` 34/0.  Purity sweep: 0 sorry / 0 axiom / 0 native_decide /
0 Classical / 0 Mathlib.  Ready-to-merge verdict: READY.

## What was done (the originator's question chain, three bricks + closing marathon)

Session seed: the originator's saved correction — "the weight-4 Eisenstein atom =
ζ(3) is a **fold to construct**, not an irreducible residue."

### Brick 1 — ζ(3) as a constructed fold (`Real213/Zeta3Cut`)
The Apéry recurrence (the `DepthAperyCubic` degree-3 coefficients), factorial-
cleared to an exact all-ℕ orbit: growth invariant `(m+1)³·xₘ ≤ xₘ₊₁` from one
seed condition proves the monus never truncates (`aperyOrbit_exact`); Casoratian
in closed form `aperyCasDet m = 6·(m!)⁶` (`zeta3_cross_det`); `zeta3Ab : AbCutSeq`
with bracket `601/500 < ζ(3) ≤ 1203/1000` (upper bounds are themselves orbits —
`aperyOrbit_linear`); completion carries the bracket.  Honest stratum **proved**:
`zeta3_presentation_overtakes` — this presentation is rate-free (overtake at
layer 9), so the modulus stays a hypothesis (π-posture); the e-grade upgrade =
the reduced presentation = classical Apéry arithmetic
(`research-notes/frontiers/zeta3_free_modulus.md`).

### Brick 2 — the degree-3 form-margin modulus (`Real213/CubeRootTwoCut`)
The algebraic exit from the rate race: side-decision against any probe reduces
to the all-additive `ε_i·k³ < d_i³`, the form margin `|m³−2k³| ≥ 1` arriving as
`Nat` strictness `+1`.  Dyadic bisection presentation ⟹ **total modulus
`N(m,k) = 3k+5`**; ∛2 joins φ/e/Liouville in the unconditional class (first
degree-3 member).  Capstone `cbrt_limit_eq_form`: the fold lands exactly on the
frozen closed-form cut `decide (2k³ ≤ m³)`.  Degree-2 shadow identified:
`FibCassiniNat.qb_lt_pk`'s `4k² < b²` is the same `ε·k^s < d^s` schema.

### Brick 3 — composed (irrational) degree (`Real213/ModulusComposition`)
`powSched c B k = ⌈k^{p/2^k}⌉` with the exponent slot a **cut** (`dyUp` reading +
exact `rootCeil`).  Calibration `powSched_rat` (integer `s` ⟹ exactly `k^s`);
instances at degree ∛2 (`cbrtPow_at_two = 3`) and degree e (`ePow_at_two = 7` —
the kernel runs `eulerCauchySeq.N` *inside* the schedule: a modulus calling
another real\'s modulus); cascade rung 1 `eSelfScheduled` (e rescheduled through
its own modulus, limit-preserving); `powSched_mono` — degree order transports to
schedule order, the backbone of **degree-as-a-cut-over-exponent-cuts** (the
exact-degree question lands inside the system; its decidability = effectivity,
Roth-grade).

### Closing marathon (merge → process → promote → crossdomain → essay → org-audit → purity → ready-to-merge)
- **/process**: sink rule 1 violation fixed (STRICT async cite → theory path);
  promotion logged (row 54).
- **Promotion**: `theory/math/analysis/form_margin_modulus.md` — the
  two-mechanism divide (rate race = transcendental, presentation-dependent;
  form margin = algebraic, presentation-robust) + the degree slot as cut.
- **Cross-domain** (`research-notes/frontiers/modulus_degree_crossdomain.md`):
  (1) modulus degree IS certificate depth one layer up (main\'s
  positivity/SOS-fold note); (2) `reschedule_limit_eq` = "the stage is of the
  run" at the real layer (async-growth arc) — the fourth scale of the
  cover-non-surjection schema.
- **/essay**: `theory/essays/analysis/the_degree_of_a_number.md` (log row 55).
- **/org-audit**: 0 hygiene hits, 0 orphans, INDEX counts verified (Real213
  169 = 101 + 68).

## Open Problems (priority order)
1. **Graded rate generator** — `Dominates_s` with polynomial slack ⟹
   `N = k^s + 2`; makes "rescue" graded the way `CompletabilityGrade` grades
   "break".  Frontier: `research-notes/frontiers/modulus_degree_ladder.md` rung 1.
2. **dyUp tightness** — the lower witness needs the ratio/rescale property;
   then `powSched` is two-sidedly pinned (same note, "Still open").
3. **ζ(3) free modulus** — reduced-presentation integrality + `lcm(1..n) < 3ⁿ`
   ⟹ `zeta3HolonomicReal` (`zeta3_free_modulus.md`).
4. **Conditional measure-modulus schema** (Wallis-π + effective `μ` hypothesis ⟹
   degree-≈7 schedule), **two-real separation modulus**, **Dirichlet floor
   `μ ≥ 2`** (constructive, via `Pigeonhole`), **self-degree fixed point
   `μ(τ) = τ`** (conjecture) — all in `modulus_degree_ladder.md` rungs 0/0′/2/3.

## Lean-tooling notes (recurring)
- `decide` on two-step `| m+2 =>` recursions and structure-literal projections
  works at small indices; `rootCeilGo` fuel-2048 needs
  `set_option maxRecDepth 8000 in` (elaborator budget, no axiom impact).
- And-shaped `decide` cuts (φ\'s `masterCut`) poison `of_decide_eq_true` with
  propext — pick single-inequality cuts (∛2) for generic instances.
- Core `Nat.pow_le_pow_right` / `Nat.pow_mul` / `Nat.mul_pos` are
  propext-dirty — pure replacements live in `CubeRootTwoCut`
  (`two_pow_pos`) and `ModulusComposition` (`pow_le_pow_exp`,
  `pow_mul_pure`, `one_le_pow`, `powBase_le/lt`, `self_le_pow`).
- `set_option ... in` goes **before** the docstring.

## Three-tier state
- **Promotions this session**: `theory/math/analysis/form_margin_modulus.md`
  (+ ζ(3)/∛2 paragraphs landed in `holonomic_modulus.md`).  Essay:
  `theory/essays/analysis/the_degree_of_a_number.md`.
- **Active frontiers**: `modulus_degree_ladder.md`, `zeta3_free_modulus.md`,
  `modulus_degree_crossdomain.md` (all registered in `frontiers/INDEX.md`).
- **Organizational note**: `Real213/` root holds 101 loose files — a genuine
  clustering candidate for a dedicated org session (constants cuts /
  Minkowski-modular / Markov / completability axes are visible sub-themes).

## File map
```
lean/E213/Lib/Math/NumberSystems/Real213/Zeta3Cut.lean            ← ζ(3) Apéry fold (35 PURE)
lean/E213/Lib/Math/NumberSystems/Real213/CubeRootTwoCut.lean      ← ∛2 form-margin modulus (31 PURE)
lean/E213/Lib/Math/NumberSystems/Real213/ModulusComposition.lean  ← composed degree + powSched_mono (34 PURE)
theory/math/analysis/form_margin_modulus.md                       ← NEW chapter (promotion)
theory/essays/analysis/the_degree_of_a_number.md                  ← NEW essay
research-notes/frontiers/{modulus_degree_ladder,zeta3_free_modulus,modulus_degree_crossdomain}.md
theory/math/analysis/holonomic_modulus.md                         ← ζ(3) boundary + ∛2 instance paragraphs
```
