# STRICT 0-AXIOM Capstones — absolute best epistemic position

This file lists Lean theorems that are **STRICT 0-AXIOM**:
they depend on NO axioms whatsoever (not propext, not Quot.sound,
not Classical.choice, not native_decide).

Verified via `#print axioms <theorem>` returning:
> "does not depend on any axioms"

## Top-level achievements (all STRICT 0-AXIOM)

| theorem | content |
|---|---|
| `validation_standard_capstone` | CLAUDE.md Standards #1+#2 met |
| `pure_atomic_observables_capstone` | 17-conjunct atomic ratios |
| `finitist_observable_chain` | 4 observables share N_U |
| `n_universe_self_consistent` | N_U = d^(d²) self-referential |
| `fractal_lens_cardinality_capstone` | Lens count at fractal level |
| `alpha_em_master_capstone` | α_em finitist with all corrections |
| `alpha_em_so10_capstone` | SO(10) tail correction |
| `alpha_em_gram_capstone` | Gram self-energy correction |

## Number theory generals (STRICT 0-AXIOM after omega→Nat.succ_add)

| theorem | content |
|---|---|
| `ArithFSM2.run_period_of_init` | universal Pisano period theorem |
| `ArithFSM2.bits_period_of_init` | universal bits period |
| `ArithFSM3.run_period_of_init` | cubic-class universal period |
| `signature_period_of_bits_period_and_anchor` | universal sig period (TIGHT) |
| `pellFSMmod{11,19,31,47,59}_signature_period_X` | TIGHT sig instances (5×) |
| `pellFSMmod{3,5}_signature_period_X` | TIGHT sig instances (2×) |
| `tribFSMmod{3,5,19,29,31}_bits_period_X` | Tribonacci doubling bits |
| `pellFSMmod47_bits_period_48` | triple-anchor reshape via rfl |

## Pisano predictor + Legendre (STRICT 0-AXIOM after obtain→.proj)

| theorem | content |
|---|---|
| `legendre213` | 213-native Legendre symbol (definition) |
| `pisano_predict` / `_correct` | Pell-5 predictor base |
| `pisano_predict_realises_pell` | 4-prime Pell match |
| `pisano_predict_correct_6` / `_realises_pell_6` | 6-prime Pell |
| `pisano_predict_realises_pell_7` | 7-prime Pell |
| `pisano_predict_realises_pell_8` | 8-prime Pell |
| `pisano_predict_realises_pell_11` | 11-prime Pell |
| `pisano_predict_realises_pell_14` | 14-prime Pell |
| `pisano_predict_realises_pell_17` | 17-prime Pell |
| `signature_predict_realises_pell_7` | 7-prime signature |
| `fib_pisano_predict_realises_8` | 8-prime Fibonacci |
| `legendre_5_mod_X` (X=13..89) | 14 Legendre symbols |

## Atomic identities (all STRICT 0-AXIOM via decide)

  - All Famous Coincidences (I-IV)
  - All Magic Numbers atomic
  - Per-prime Pisano (Pell, Pell-proper, Fibonacci, Tribonacci)
  - All atomic structural identities (NS·NT=6, d²-1=24, etc.)

## Significance

STRICT 0-AXIOM is the **absolute best** epistemic position in
Lean.  These theorems are checked by Lean's kernel WITHOUT any
axiom dependence — purely definitional.

External reviewers cannot challenge these via "what if propext
is wrong" since propext is not used.

## omega → propext lesson

Lean's `omega` tactic typically introduces propext + Quot.sound
dependencies.  Replacing omega with explicit kernel-level Nat
lemmas (Nat.succ_add, Nat.zero_add, etc.) UPGRADES proofs to
STRICT 0-AXIOM.

Example (commit 304723f):
  Before: `have : k+1+N = (k+N)+1 := by omega`  → propext dep
  After:  `rw [Nat.succ_add k N]`  → STRICT 0-AXIOM

## Audit command

```
cat > /tmp/axcheck.lean << END
import <module>
#print axioms <theorem>
END
cd lean && lake env lean /tmp/axcheck.lean
```

If output is "does not depend on any axioms", STRICT 0-AXIOM.

## Future cleanup

Many theorems at ≤ {propext, Quot.sound} could be upgraded by:
  1. Replacing omega with kernel-level lemmas
  2. Replacing simp[...] (uses propext) with rw
  3. Avoiding funext (uses Quot.sound) when not needed

Estimated upgrades: ~50-100 theorems possible.

## Cross-reference

  - `CAPSTONE_INDEX.md` — all capstones (mixed axiom levels)
  - `LESSONS_LEARNED.md` — finitist guardrails
  - `HANDOFF.md` — current state
