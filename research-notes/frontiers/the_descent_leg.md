# The descent leg — wire the act to the unfolding (the central open frontier)

**Core open problem.** The corrected 진의 (`the_substance_test.md` §CORRECTION) is that *mathematics
is the forced unfolding of the one primitive act of distinguishing*. A 3-agent panel (2026-06-22)
established **mechanically** that this is **not yet instantiated in the Lean**:

> Of 1571 files in `lean/E213/Lib/Math`, **1512 (96%) import neither `E213.Theory.Raw` nor
> `E213.Lens`.** The disciplines are built directly on Lean's native `Nat`/`Int`. Even
> `Theory/Raw` reads *out* into native `Nat` (`Raw.leaves : Nat`, `Raw.depth` via `Nat.add_comm`) —
> it **borrows** ℕ, it does not **generate** it.

So the generative chain the thesis needs — `Raw (slash) → Lens-reading → discipline` — is **severed**:
the act (`Theory/Raw/*`) and the unfolding (`Lib/Math/*`) are two adjacent codebases that share a
build target, not a derivation. Most of the corpus is excellent ∅-axiom **re-derivation** of classical
mathematics over native carriers; it is not **generation from the primitive**. (This is not a defect of
the theorems — they are real and PURE — but of the *claim* the originator now makes about them.)

## What "closing the descent leg" requires (the falsifiable target)

A worked case where a classical result is **re-obtained as a Lens reading of a `Raw` construction**,
with the chain load-bearing *in the proof*, not just the prose:

1. **Generate ℕ from `Raw`.** Promote `Raw.depth` / `Raw.leaves` / the `RawRecurrence` spine
   (`|S_n| = 2 + C(|S_{n-1}|,2)` → 2,3,5,12,68, the originator's discovered recurrence) into a
   *naturals object* `Nat₂₁₃` defined from the distinguishing, with its `succ`/`+`/`*` as
   Lens-readings of `slash`-operations — **not** Lean's `Nat`. The honest bar (skeptic's Attack 1):
   account for what is borrowed from the kernel (inductive, Pi, `Bool`) vs. generated.
2. **Re-derive one discipline over `Nat₂₁₃`.** Take a single downstream classical theorem already
   PURE over native `Nat` — candidates: `φ = μ ∗ id`, σ_m multiplicativity, or a figurate identity —
   and re-state + re-prove it over `Nat₂₁₃` via the Lens-arrow, ∅-axiom. This is the first genuine
   "discipline = the distinguishing's reading" demonstration.
3. **Forcing, not matching.** Strengthen the initiality story (`Lens/Initiality`, `raw_initial`) so a
   *specific* classical structure is the **unique** distinguishing-preserving reading, not merely *a*
   reading that happens to match (skeptic's Attack 2: the primitive must be shown non-interchangeable
   with rivals — negation-first, relation-first).

## Existing partial material (the seeds)

- `Lib/Math/Foundations/UniverseChain/RawRecurrence.lean` — the **one** genuine `Raw → count`
  generation (`|S_n| = 2 + C(|S_{n-1}|,2)`); consumed by exactly one file
  (`Algebra/SelfSimilarityBridge.lean`). Essentially isolated — the seed of leg 1.
- `Lens/Number/Nat213/*` — a `Raw`-native numeral reading (`numeral`, `numeral_ne_b`); check how far
  it already is a usable `Nat₂₁₃` vs. a thin wrapper.
- `Lens/Initiality.lean`, `Theory/Raw/Lambek.lean`, `Theory/Raw/MuNuMirror.lean` — the
  initiality/μF-νF apparatus for leg 3.

## Why this is the central frontier (not peripheral)

Per the correction, *this is the work*: without the descent leg, the breadth of ∅-axiom re-derivations
witnesses **constructivity per domain** (real, the census artifact) and Line A witnesses **unity across
some domains via shared engines** (`genSwap`, `det2_mul`, `lcm`-meet) — but *neither* witnesses
**generation from the act**. The descent leg is the only thing that would make "mathematics is the
distinguishing's unfolding" a demonstrated theorem-chain rather than an asserted slogan.

## Honest risk

This is large and may not close cleanly: reconstructing ℕ from `Raw` without silently re-importing the
kernel's inductive ℕ is exactly where the skeptic's circularity attack (Attack 1) bites. The
deliverable may end up being a *precise accounting* of what is genuinely generated vs. borrowed — which
is itself valuable (it converts the slogan into a measured claim), even if full generation is out of
reach. Time-box and report honestly, win or lose (the G206 template).

## Pointers
- Diagnosis + corrected 진의: `the_substance_test.md` §CORRECTION (2026-06-22).
- Generation already deposited (the *other* prong): `Lens/OneDiagonal.lean` (the residue as the
  engine of the limitative theorems), `theory/essays/foundations/the_one_diagonal.md`.
