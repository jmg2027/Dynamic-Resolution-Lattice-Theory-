# G23 — Pisano Marathon Anatomy: How Shapes Compose Within a Marathon

**Author:** Claude (inspection); Mingu Jeong (methodology directive)
**Date:** 2026-05-XX (continues G17–G22)
**Companion file:**
  - `research-notes/G17_inspect_pisano_marathon.md` (full extraction of all 26 decls)

## §0  Why this marathon

`Math/Cohomology/Dyadic/Pisano/` is small enough to read in full:

```
9 files / 26 declarations / 1 def + 25 theorems
```

Marked PURE in HANDOFF, mathematically focused (Pell-bit-period
prediction via Legendre lens at primes), and *not* written by Claude
recently — so it's a fair empirical sample.

This note traces how the 5 dominant shapes (G22) actually COMPOSE
inside one self-contained marathon.

## §1  Marathon-level structure

Files in temporal order (correspond to `_N` capstones extending the
prime list):

```
File                  | Adds primes      | New decls
─────────────────────┼──────────────────┼─────────────
Predictor.lean       | 3, 5, 7, 11      | 1 def + 2 thms
Predictor6.lean      | 13, 19           | 2 thms
Predictor7.lean      | 17               | 2 thms
Predictor8.lean      | 23               | 2 thms
Predictor11.lean     | 29, 31, 37       | 4 thms
Predictor14.lean     | 41, 43, 47       | 4 thms
Predictor17.lean     | 53, 59, 61       | 4 thms
Predictor20.lean     | 67, 71, 73       | 3 thms
Predictor22.lean     | 79, 89           | 2 thms
─────────────────────┼──────────────────┼─────────────
                     | 22 primes total  | 1 def + 25 thms
```

Each file adds 1–3 new primes and re-bundles ALL accumulated primes
into a fresh capstone.  The capstone GROWS as the marathon grows.

## §2  The single anchor — `pisano_predict`

```lean
def pisano_predict (p : Nat) (hp : 1 < p) : Nat :=
  let leg := (legendre213 5 p hp).val
  if leg = 0 then 2 * p          -- ramified
  else if leg = 1 then (p - 1) / 2  -- split (QR)
  else p + 1                     -- inert (NQR)
```

This single formula reads the Legendre symbol of 5 modulo p and
returns the predicted Pell bit period.  Three branches, one per
ramification class.

Δ.B (G21) — combinatorial function definition.  ~10 lines.

## §3  Two recurring theorem-shapes within the marathon

### Type A (15 of 26 decls, 58%)  — atomic Legendre value

```lean
theorem legendre_5_mod_29 :
    legendre213 5 29 (by decide) = ⟨1, by decide⟩ := by decide
```

Slot-combo: `decide` only (Shape 1 from G22).
Cost: 1 line of theorem + 1 line of decide.
Per-prime delta: 1 decl (one for each new prime added in that file).

### Type B (5 decls)  — full FSM-period realisation capstone

```lean
theorem pisano_predict_realises_pell_N :
    (∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by decide)) = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + pisano_predict 5 (by decide)) = pellFSMmod5.bits k)
    ∧ ... ∧
    (∀ k, pellFSMmod_pN.bits (k + pisano_predict pN (by decide)) = pellFSMmod_pN.bits k)
    := by
  refine ⟨?_, ?_, ..., ?_⟩
  · intro k; rw [pisano_predict_correct.1]; exact pellFSMmod3_bits_period_4 k
  · intro k; rw [pisano_predict_correct.2.1]; exact pellFSMmod5_bits_period_10 k
  ...
```

Slot-combo: `AND, FORALL, anon, decide, exact, intro, refine, rw`
(a "huge combo" — combo #5 in G22's per-file ordering, but distinct
from the simpler `AND, anon, decide, refine` capstone in §3).
Cost: ~3 lines per conjunct (intro, rw, exact).
Per-prime delta: ONE NEW LINE inside the goal + one line in proof.

### Type C (3 decls) — `pisano_predict_correct_N` numerical bundle

```lean
theorem pisano_predict_correct_6 :
    pisano_predict 3 (by decide) = 4
    ∧ pisano_predict 5 (by decide) = 10
    ∧ pisano_predict 7 (by decide) = 8
    ∧ pisano_predict 11 (by decide) = 5
    ∧ pisano_predict 13 (by decide) = 14
    ∧ pisano_predict 19 (by decide) = 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
```

Slot-combo: `AND, anon, decide, refine` (Shape 5 from G22).
Cost: per-prime, 1 line in goal + 1 `?_` in refine.

## §4  Per-prime delta (the marathon's "unit cost")

Adding prime p_new to the marathon:

  1. Prove `legendre_5_mod_p_new : legendre213 5 p_new = ⟨_, _⟩` by `decide`
     → **1 atomic Type A theorem** (Shape 1).

  2. (When file is a `_N` capstone update):
     - Add 1 line to `pisano_predict_correct_N`'s ∧-chain
       (Type C, Shape 5) — extends decide-bundle by one conjunct.
     - Add 1 line to `pisano_predict_realises_pell_N`'s ∧-chain
       (Type B, complex combo) — extends with `∀ k, ...`-conjunct;
       proof gets 1 new `· intro k; rw [...]; exact <FSM-period-lemma>`.

  3. Pre-existing dependency: `pellFSMmod_p_new_bits_period_<n>` must
     exist elsewhere (in `ArithFSM.ToBitFSM.*` cluster).  This is the
     marathon's **upstream input** — the actual period proofs.

So the Pisano marathon is, structurally:

  > "Given a pre-existing catalog of FSM-period proofs at primes p_i,
  >  show that a single Legendre-driven formula `pisano_predict`
  >  retrieves the right period for each p_i."

The marathon is a **lifting / unification operation** — it doesn't
re-prove the periods, it shows one formula realises them all.

## §5  Shape composition diagram

```
         pisano_predict (def, Δ.B)
                   │
            (single formula anchor)
                   │
       ┌───────────┼───────────────────────────┐
       ▼           ▼                           ▼
  Type A         Type C                    Type B
  (Shape 1)    (Shape 5)            (extended Shape 5)
   decide      ∧ + decide           ∧ + ∀ + intro/rw/exact

  legendre     pisano_predict       pisano_predict_realises_pell_N
   _5_mod_p    _correct_N           (the actual realisation claim)
                                              │
                                              ▼
                                      uses pre-existing
                                       pellFSMmod_p_bits_period_n
                                       (upstream catalogue)
```

Three theorem shapes, one anchor, one upstream input.  The whole
marathon's weight rests on the one upstream catalogue.

## §6  What this expresses

The Pisano marathon is **evidence accumulation**:

  · ANCHOR (1 def):  the predictive formula
  · ATOMIC EVIDENCE (15 decls): one Legendre value per prime
  · NUMERICAL CHECK (3 decls):  formula yields the right number per prime
  · REALISATION CHECK (5 decls): formula's number IS the FSM period

Every new prime added extends the evidence.  The MARATHON is "how
many primes can we run this through and still get the right answer?"
The answer is currently 22 primes (3..89), each closed by `decide`
on Legendre + `decide` on the predict value + one FSM-period
upstream lemma.

This is empirically what 213 calls a "marathon" — single conjecture
formula + scaling evidence base + FORMAL verification of each
match.  No abstract argument that the formula MUST work; instead,
exhaustive verification at increasingly many instances.

## §7  Other marathons likely to have the same shape

By analogy (not yet verified):
  · **Pell.LensTriple**, **Pell.LensCapstone** in `Dyadic/Pell/`
  · **Trib.CRTCapstone** in `Dyadic/Trib/`
  · **Pisano.Predictor*** family (this one)
  · **ThreeFamilyCapstone** combining Pell + Fib + Trib
  · **TwoLayerPredictor** (signature + bit predictors)

Each likely follows: anchor formula → atomic decide evidence at
parameter instances → numerical bundle → realisation against
upstream catalogue.

If verified, this would be a **marathon archetype** — one common
shape that ~20% of 213's capstone proofs follow.

## §8  Open: cross-marathon shape comparison

  · Read CayleyDickson marathon: same anchor + scaling structure?
  · Read Hodge involution marathon: 5-stratum bundle, but is the
    anchor a `def` or a `theorem`?
  · Read AlphaEM marathon: physics-track marathon — does the
    pattern hold cross-domain?

Each would need a similar deep dive (a few specimens per file).
The infrastructure (`tools/theorem_inspect.py`) handles this cheaply.
