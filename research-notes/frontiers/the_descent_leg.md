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

## UPDATE (2026-06-22, later): generation headline closed; leg-2 discipline progressing

- **Generation headline — CLOSED** (`Lens/Number/Nat213/Generation.lean`, 4 PURE): ℕ₊ is the
  *canonical* leaves-Lens reading of iterated distinguishing, as theorems (not comments):
  `value_eq_leaves` (`value = Lens.leaves.view`, the `⟨1,1,(·+·)⟩` catamorphism),
  `succ_is_distinguishing` (`succ n = slashOrSelf n Raw.b` — `+1` IS a slash event),
  `generation_capstone` (`Lens.leaves.view (numeral n) = n+1`). So "ℕ₊ = the count-Lens reading of
  iterated self-distinguishing" is now a theorem routed through the canonical Lens — leg-1 is closed
  for ℕ₊ (the "ergonomic parallel" caveat is dissolved: the count is the canonical Lens).
- **Leg-2 discipline — progressing** (`Divisibility.lean`, 13 PURE, all over `Nat213`): divisibility
  is a **partial order** (`dvd_antisymm` + `mul_eq_one`), **order-refining** (`dvd_imp_eq_or_lt`:
  divisor ≤ dividend), **bounded below** (`one_dvd`) and **open above** (`dvd_no_top` — no top,
  forced by the primitive's non-closure). A discipline computed entirely on the distinguishing's ℕ₊.
- **Remaining (the genuinely hard part):** leg-2 *depth* — route a deeper discipline (primality /
  unique factorisation, or a figurate identity) over `Nat213`; and leg-3 *forcing/uniqueness* — show
  the distinguishing primitive is **non-interchangeable** with rivals (negation-first, relation-first),
  i.e. strengthen `Lens/Initiality` so the classical structure is the *unique* distinguishing-preserving
  reading. The latter is the skeptic's Attack-2 target and the deepest open work.

## CORRECTION (2026-06-22): leg 1 is ~80% done — the gap is leg 2

A direct read of `Lens/Number/Nat213/` revises Agent B's import-count diagnosis. The Raw-native ℕ
**already exists with its own arithmetic**, not as a thin wrapper:

- `Nat213/Raw.lean` — the Method-A Raw chain: **`one := Raw.a`, `succ n := slashOrSelf n Raw.b`**
  (the successor *is* a `slash`/distinguishing operation against `b`). So ℕ₊ is literally the
  iterated self-distinguishing of the atom. `numeral_succ`, `value_succ_of_ne` PURE.
- `Nat213/Peano.lean` — an inductive ℕ₊ (`| one | succ`) with its **own** `add`/`mul` (defined on
  `Nat213`, *not* Lean's `Nat`) and the full commutative-semiring-minus-zero law set proven by
  induction over `Nat213`, ∅-axiom: `add_comm/assoc`, `mul_comm/assoc`, `add_mul`/`mul_add`,
  `add_left_cancel`, `mul_left_cancel`. **Plus the forcing theorems** — `no_additive_identity_at_one`,
  `no_closed_subtraction`, `no_absorbing_element`: the no-zero / no-subtraction / no-absorption shape
  is *forced* by the primitive (Raw has ≥1 atom), not chosen. **This is the "distinguishing forces the
  structure" content the skeptic (Attack 2) demanded** — a rival "ℕ-with-0" primitive is provably
  foreign here.
- `Nat213/Bridge.lean` — the iso: `toRaw : Peano → Raw`, `value_toRaw`, `toRaw_injective` (PURE).

So leg 1 (ℕ generated from the distinguishing, with forced structure) is **substantially present**.
What remains:

- **The real gap (leg 2):** per the Bridge's "Option C", the *abstract number-theoretic operations
  live on Lean `Nat`*; the Raw side "carries only the chart representative." So every **discipline**
  (φ=μ∗id, σ_m, LTE, …) is proven over Lean `Nat` and bridged — **none is computed over
  `Nat213.Peano` using its own `add`/`mul`.** The first genuine descent-leg deposit: take one
  classical theorem and prove it **over `Nat213.Peano`** (its operations), ∅-axiom, with no detour
  through Lean `Nat` in the statement. Candidates that fit a zero-free ℕ₊: a distributive/factoring
  identity, a divisibility fact, or a figurate identity rephrased without 0.
- **Leg 3 (forcing/uniqueness):** the Peano file is still flagged "ergonomic parallel, not
  lens-derived" though `Bridge` makes it iso to the lens-derived chain. Upgrade: show the `Peano`
  `succ`/`add` *are* the Lens-readings of the `Raw` `slash`-operations (not merely iso at the
  `value`/`toNat` level), and strengthen `Lens/Initiality` so this reading is the **unique**
  distinguishing-preserving one (rules out rival primitives).

## Other seeds

- `Lib/Math/Foundations/UniverseChain/RawRecurrence.lean` — the `Raw → count` recurrence
  (`|S_n| = 2 + C(|S_{n-1}|,2)`, → 2,3,5,12,68); consumed by one file. The combinatorial spine.
- `Lens/Initiality.lean`, `Theory/Raw/Lambek.lean`, `Theory/Raw/MuNuMirror.lean` — initiality/μF-νF
  apparatus for leg 3.

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
