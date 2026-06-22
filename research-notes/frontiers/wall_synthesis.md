# Frontier: defeating the "principled constructive wall" (Banach engine, ∅-axiom)

**Status**: CLOSED (Route A, modulated engine).  The wall is defeated ∅-axiom.
Built (all PURE, `#print axioms` → no axioms):
- `lean/E213/Lib/Math/Analysis/BanachFixedPointModulated.lean` — the reusable
  generic engine: `CompleteMetricModulusMod` (modulus-as-data completeness),
  `picard_cauchy_mod`, `CompleteMetricModulusMod.banach_fixed_point_modulated`
  (fixed point with NO bare `lim`), `trivCompleteMod` non-vacuity.
- `lean/E213/Lib/Math/Probability/Limit/DyadicCompletion.lean` §8-10 — the
  `DyC L` instance: `diag_reg_mod` (modulus-explicit diagonal regularity),
  `cmodMon` (monotone running-max reindexer), `regDiagPoint` (the subsampled
  diagonal = genuine identity-modulus `DyC L`), `climconv_regDiag` (the crux,
  finite-`Nat` qtri convergence proof), `completeDyMod` (first NON-trivial
  inhabitant of the engine), and the headline `gaussian_center_fixed_via_engine`
  — the Gaussian center `inj L (0,0)` as a located fixed point of `Φhat`
  obtained THROUGH the engine (not the by-hand `orbit_to_center_completion`).

Note vs the original plan: step 1's `climconv` was discharged NOT for the
`stab`/`limPoint` freeze (whose freeze-permanence is genuinely delicate) but for
the cleaner *modulated* limit — the plain diagonal **subsampled against the
supplied modulus** (`regDiagPoint`), which is identity-modulus regular by
construction.  With the modulus as data this needs no freeze and no choice; the
freeze-permanence subtlety is sidestepped, not resolved.  `limPoint`/`stab`
remain in the file as the bare-interface artifact.

---

**Original plan (converged)** — three independent mathematical schools (constructive
Bishop–Bridges, computable-analysis/domain-theory, reverse-math/proof-theory) attacked the wall
separately and **agree on the diagnosis and the fix**. Memos: `wall_constructive.md`,
`wall_computable.md`, `wall_reverse_math.md`. This file synthesizes them into one Lean plan.

## The wall (recap)

`Lib/Math/Analysis/BanachFixedPoint.lean`'s `CompleteMetricModulus` bundles a **total**
`lim : (Nat → X) → X` (no Cauchy hypothesis as an argument) with `climconv` claiming `lim`
converges for **every** bare Cauchy sequence. `Probability/Limit/DyadicCompletion.lean` built a
genuine quotient-free completion `DyC L` (regular Cauchy sequences), the lifted
`Φhat_contraction`, and `orbit_to_center_completion` (the Gaussian center as a true
completion-limit) — all ∅-axiom PURE. But `banach_fixed_point` cannot be instantiated for `DyC L`:
a total choice-free `lim` correct on all *bare* Cauchy sequences is constructively impossible.

## The converged diagnosis — an INTERFACE DEFECT, not a hole in the math

All three schools land on the same point, in their own vocabulary:

| School | The wall named | The separating line |
|---|---|---|
| Reverse math | bare `lim`+universal `climconv` smuggles **countable choice `AC₀,₀`** ("every Cauchy sequence has a modulus") | modulus-as-**existential** (`∀m ∃N`, above RCA₀) vs modulus-as-**data** (RCA₀/BISH, choice-free) |
| Constructive (Bishop) | `lim` consumes a **bare** sequence; the modulus is hidden | a *regular*/modulated Cauchy sequence carries its modulus, so `limMod` is total + choice-free |
| Computable (TTE/domain) | a **typing artifact**: `lim` is typed on bare sequences, not on **names** | a completion point IS a name (regular Cauchy sequence = admissible representation); `lim` on names is total |

**One sentence:** the bare `lim`/universal `climconv` asks for a strictly *stronger* (choice-requiring)
statement than the Banach fixed-point theorem actually needs; the theorem itself is ∅-axiom once the
modulus is treated as **data** rather than chosen.

## The decisive leverage (unanimous) — the modulus is already in hand

- **`picard_cauchy` already produces the explicit modulus `N(m)=m`** (`BanachFixedPoint.lean:154`,
  witnessed by `refine ⟨m, ?_⟩` at `:159`). A contraction supplies its own convergence rate. So a
  modulated engine needs **no** generic bare-sequence `lim` — it hands over the modulus it already
  holds. `N=m=id` means the Picard orbit is *literally* a Bishop regular sequence — the same shape as
  `DyC L`'s carrier.
- **The repo already does modulated limits elsewhere.** `CauchyCutSeq` (`Analysis/CauchyComplete.lean:18`)
  stores the modulus as a structure field `N : Nat→Nat→Nat` and reads the limit off it:
  `limit ccs := fun m k => ccs.cs (ccs.N m k) m k` (`:24`). So the repo's *own* real-number completion
  is modulated; `CompleteMetricModulus`'s bare `lim` is the **outlier**, not the norm.
- **The names-not-points stance is native, not imported.** `seed/AXIOM/05_no_exterior.md §5.5`
  ("Self-completion — every pointing is already complete", `:223`) and
  `theory/essays/foundations/reached_by_none.md` already identify a point with its convergent
  process. The TTE "name carrier" is the repo's own ontology.

## The concrete Lean plan (the wall-breaker)

Two presentations of the same fix; pick the cleaner once prototyped.

**Route A (modulated interface) — Bishop/reverse-math.**
1. Add `CompleteMetricModulusMod` (next to `CompleteMetricModulus`): completeness whose `lim` takes the
   modulus as input — `limMod : (s : Nat → X) → (N : Nat → Nat) → IsCauchyWithModulus s N → X` — plus a
   `climconvMod` law. This is total and choice-free (the modulus is an argument, not an existential).
2. State `banach_fixed_point_modulated`: a `Contraction` + its `picard_cauchy`-modulus ⟹ a fixed point
   reached as the modulated limit. No bare `lim` anywhere.
3. Instantiate with `Φhat_contraction` (`DyadicCompletion.lean:316`) → the Gaussian center as a fixed
   point **through a reusable engine**, ∅-axiom.

**Route B (name carrier) — TTE/domain-theory.**
1. Add `NameComplete` whose carrier IS the regular-sequence type (`DyC L` is already exactly this), so
   `lim` is honestly total because the `stab`/freeze is internalized in the carrier.
2. `fixed_point_of_contraction_via_name` — same proof skeleton as `banach_fixed_point`, the fixed point =
   the *presented colimit* of the explicit Picard chain (Kleene `⊔ₙ Tⁿ`), summoned by no completeness
   axiom. `telescope_regular` (`DyadicCompletion.lean:191`) is the generic chain→name lemma.

**Shared first obligation (both routes, the one genuinely unwritten piece):** prove `climconv` for
`limPoint`/`DyC L` — that the stabilizing diagonal converges to a Cauchy `S`. The panel agrees this is a
**finite `Nat`-arithmetic 3ε / freeze-eventually-stops argument**, ∅-axiom, dischargeable with the
existing `diag_reg` / `telescope_regular` / `qtri` toolkit already in the file. (The current
`DyadicCompletion.lean` docstring was corrected: it had claimed `completeDy`/`climconv` were built — they
are not; the file proves `orbit_to_center_completion` directly, bypassing the engine.)

## Honest residual (a feature, not a defect)

The modulated/name route carries **representation-dependence**: the modulus is part of the input, so the
bare "∀ Cauchy sequence" quantifier does slightly less than it appears. This is exactly the repo's own
**presentation-dependence** stance (`Real213/PresentationDependence`, the `completability_is_intensional`
frontier) — holonomicity/depth is a property of the *pointing*, not the real. So the residual aligns with
213's grain rather than cutting against it: the fixed point is reached by no bare sequence, only by a
*presented* (modulated) one — `object1_not_surjective` at the analysis level.

## Verdict

The wall is **defeatable ∅-axiom** — it was never a math obstruction, only a too-strong interface. The
work is: (1) discharge `climconv` for `limPoint` (finite Nat-arithmetic), (2) add a modulated/name
completeness interface + a `banach_fixed_point_modulated`/`…_via_name` engine, (3) instantiate with
`Φhat_contraction` to land the Gaussian center through a reusable engine. All cited pieces grep-verified.
