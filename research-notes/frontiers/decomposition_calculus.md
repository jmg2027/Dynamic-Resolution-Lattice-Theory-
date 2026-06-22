# Frontier: the 213 Decomposition Calculus

**Status**: open, active — the originator's recalibrated central program (2026-06-22). The body of the
repository is *this* (a human-facing technique for *seeing* mathematics cleanly via the single act of
distinguishing), not the Lean re-derivation corpus (scaffolding). Spec + practice live in
`research-notes/decomposition/` (`README.md` = the technique; `practice/` = worked decompositions).
Lean is the faithfulness-check only.

## State (30 worked decompositions, all Lean-cited — model v7)

Batches 1-8 (see `README.md`). Crystallized-from-repo: `parity`, `integers`, `equivalence`. The
practice has refined the model to **v7**: `C` = distinguishing + {direction `q=±1`, bidirectional
fold-height, atom-distinguishability}; readings `L` form a **category** + {resolution **with a `base`**
(which valuation/metric is "adjacent", `padic.md`), bidirectional character-mode, weight,
iteration-character (nilpotent `∂` / idempotent `clo` / growing `S`)}; `Residue` = `L`'s
self-application surplus, tagged `q = ±1` (escape/oscillate vs converge/fixed-point). **The boundary is
now located** (`knots.md`, first partial-break): the normal form does *not* cover relations among
distinct constructions (skein) or ambient-isotopy quotients — named missing primitives.

Six predictions, four now Lean-closed (orthogonality orders 2/3/6, growing-corner `succ_not_idempotent`,
convolve-rescale `Φ_contraction`); the remaining targets are below.

## Open directions

### Next fresh decompositions (the practice is the research)
DONE (batch 3, both EXTEND, no break): **groups** (a group = `⟨C | Aut C closed under composition⟩`,
axioms forced — readings form a composition-closed family); **probability** (`P = ratio∘count`, first
*composite* reading; `L` gains a `weight` parameter; independence = ×-character, expectation = its
additive twin). Lesson: **readings form a category.** DONE (batch 4, all EXTEND, no break — 17 decompositions total): **homology** (∂ = fold-height run
downward → height bidirectional; ∂²=0 forced by q=±1; nilpotent/involutive = the two q=±1 poles);
**ordinals** (ω = height-residue q=+1; model caps honestly at ω); **galois** (first non-invertible
reading-pair = adjoint/order-reversing connection; FT = residue-collapse-to-closure); **entropy**
(★ FIRST LEVERAGE — H = weight∘log-character, the calculus *predicts* entropy's form, not re-skin).

**Shift of emphasis (post-leverage):** the collapse-hunting phase has shown the model is robust (17/17
EXTEND). The next phase should prioritize **leverage** — decompositions that *predict/derive* a form or
*enable* a result, like entropy did — over more confirming collapses. Candidate leverage-targets:
- **the Fourier/character duality** — does "a function = Σ over its characters" fall out of the
  character-mode (a reading's spectrum)? (would predict, not re-describe.)
- **the central limit / Gaussian** — forced by weight∘character at the resolution limit?
- **Noether's theorem** (symmetry→conservation) — an `Aut(C)`-invariant = a conserved readout? (ties
  groups.md to physics.)
- **adjunction/monad** — generalize galois.md's adjoint-pair to the full categorical adjunction.

DONE (batch 5 / leverage phase — 21 decompositions): **noether** (PREDICTION, structural: conserved =
Aut-invariant character, q=+1; variational current open), **gaussian_clt** (PREDICTION: Gaussian =
convolve-rescale fixed point, generalizes φ; contraction lemma open), **fourier** (PARTIAL: self-duality
+ character-existence predicted; orthogonality open), **adjunction** (the repo proved the closure MONAD
before naming it; the free/growing corner is the un-built edge). Key finding: ONE `×↦·` character arrow
runs through parity/valuation/det/entropy/Noether/Fourier; the calculus is a category of readings living
in the two q=±1 poles, only the q=+1 closure corner built.

### Leverage-closing Lean targets (each promotes a batch-5 *prediction* to a closed *derivation*)
- **character orthogonality `Σ_x χ(x)=0`** — ✅ CLOSED. `CharacterOrthogonality.lean`
  (`quadratic_orthogonality`, order 2) + `RootOfUnityOrthogonality.lean` (orders 3, 6 in ℤ[ω]); both
  ∅-axiom. Promotes `fourier.md`'s orthogonality leg from predicted to built.
- **"convolve-and-rescale is a contraction" → `banach_fixed_point`** — ✅ CONTRACTION LEG CLOSED.
  `ConvolveRescaleContraction.lean` (`Φ_contraction : Contraction (dyMet L) Φ`, `Φ_picard_cauchy`,
  `center_fixed`/`orbit_to_center`; 20/0 ∅-axiom). Honest residual: `banach_fixed_point` itself not
  applied (needs a genuine `CompleteMetricModulus Dy` — open), and convolution is on the centered
  statistic, not the full weight-profile. `gaussian_clt.md` upgraded prediction→keystone-leg-built.
- **the growing/free corner** — ✅ MIRROR LEG CLOSED. `MuNuMirror.succ_not_idempotent` (the ascent
  step `S` is non-idempotent — `S(S r) ≠ S r` on the tower) is the exact mirror of the closure monad's
  `clo_idempotent`: the two values of the **iteration-character** axis. The native free-monad
  carrier (νF) stays open (Mathlib-free coinduction blocked, per `MuNuMirror` header).
- **continuous/variational Noether current `∂_μ j^μ=0`** — still open (discrete skeleton built).

### Open Lean faithfulness-targets (would certify a current prose-only collapse)
- `continuous_iff_preimage_dyadicopen` (`continuity.md` flags the open-set/preimage leg as prose).
- a formal **`q = ±1` residue tag** uniting `object1_not_surjective` (escape, `q=−1`) and the φ Cassini
  law `cassini_law_one_at_two_multipliers` (converge, `q=+1`) — the calculus's deepest collapse, not
  yet one theorem.
- `exp/log` continuous inverse `cutExp ∘ cutLog = id` (`exponential.md` flags it open; discrete side
  certified via `vp_self_pow`/`pow_eq_pow_iff_vp`).

### Technique-spec questions still live
- Does "character" deserve a formal definition object (a reading whose readout is a number-construction
  with `C`'s direction+height)? Candidate to crystallize once 2–3 more character instances land.
- Is `resolution` better modeled as a single dial or a poset of resolutions (discrete < dyadic <
  Cauchy < …)? `continuity.md` + `ResolutionShift.lean` (graded monoid) suggest a poset.

### The standing guard (re-skin test)
Every decomposition must end in a **Revelation** (collapse / forcing / residue-surfaced); a
decomposition that only re-describes is dropped. This is the same bar that separated category theory
from "abstract nonsense" — the technique must *pay*, eventually as a tool or a result, not just a
re-seeing. Tracked against CLAUDE.md's failure-mode catalog (the negative of this technique).
