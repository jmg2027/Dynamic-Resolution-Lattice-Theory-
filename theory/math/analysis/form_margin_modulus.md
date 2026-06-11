# The form-margin modulus and the composed degree — the algebraic exit, and degree as a slot

**Status**: Closed core.  Source of truth:
`lean/E213/Lib/Math/NumberSystems/Real213/{Zeta3Cut,CubeRootTwoCut,ModulusComposition}`,
all strict ∅-axiom (35 + 31 + 34 PURE / 0 DIRTY).  Companion: the rate-race
side of completeness is `holonomic_modulus.md`; this chapter is the *other*
mechanism and the functional that makes the degree itself a parameter.

## 1. Two mechanisms, one divide

A total cut modulus is a composition `N(m,k) = rate⁻¹(distance(m,k))`.  The
repo now holds both ways of paying for the distance:

- **The rate race** (transcendental regime): the cross-determinant `W` must
  stay below the denominator's growth quantum (`Htel`, `holonomic_modulus.md`).
  Presentation-dependent — proved sharply by ζ(3): the Apéry recurrence,
  factorial-cleared to an exact ℕ orbit (`Zeta3Cut.aperyOrbit_exact`, growth
  invariant `(m+1)³·xₘ ≤ xₘ₊₁` from one seed condition), generates the genuine
  convergents with closed-form Casoratian `aperyCasDet m = 6·(m!)⁶`
  (`zeta3_cross_det`) and bracket `601/500 < ζ(3) ≤ 1203/1000` — yet
  `zeta3_presentation_overtakes` shows this presentation's `W` overtakes the
  denominator quantum at layer 9: rate-free, modulus stays a hypothesis (the
  π-posture).  The rate-carrying reduced presentation costs exactly the
  classical Apéry arithmetic (frontier board).
- **The form margin** (algebraic regime): a degree-`s` integer form vanishing
  at the real makes the side-decision against any probe `m/k` an all-additive
  comparison `ε_i·k^s < d_i^s`, with `|F(m,k)| ≥ 1` arriving for free as `Nat`
  strictness.  Presentation-robust: *any* presentation with a slack rate
  completes.  Degree-2 instance: φ (`masterCut`; `FibCassiniNat.qb_lt_pk`'s
  `4k² < b²`).  Degree-3 instance, closed end-to-end: ∛2.

## 2. ∛2 (`CubeRootTwoCut`)

Dyadic bisection on the cube bracket (`cbrtNum i / 2^i`, invariant
`a³ ≤ 2d³ < (a+1)³`, pure case analysis) gives cube-slack `ε_i ≤ 24·4^i`
against `d³ = 8^i`, so the comparison is won at `i ≈ 3k`:

> **`cbrtCauchySeq`** *(∅-axiom)*: total modulus `N(m,k) = 3k+5`.  ∛2 joins
> φ, e, Liouville in the unconditional class — the first degree-3 member, by
> the form, not the rate.

> **`cbrt_limit_eq_form`** *(∅-axiom)*: the completed fold **equals** the
> frozen closed-form cut `decide (2k³ ≤ m³)` — the degree-3 analog of
> `cs_eq_phiCut`.  Bracket `5/4 < ∛2 ≤ 13/10`.

The algebraic degree enters as the **probe exponent `k^s` in the schedule**;
the true (Roth) exponent 2 is receipt-less — the gap between them is the
constructive content of effectivity.

## 3. The degree slot opened (`ModulusComposition`)

`powSched c B k = ⌈k^{p/2^k}⌉`, with `p = dyUp c B k` the dyadic upper
numerator read off an **exponent cut** `c` (sound from an integer witness +
forward doubling, `dyUp_true`; `rootCeil` the exact integer root ceiling,
sound + least).  Closed facts:

- **Calibration** (`powSched_rat`): an integer exponent `s` returns exactly
  `k^s` — the functional extends the polynomial ladder.
- **Instances**: degree ∛2 — `cbrtPow_at_two : powSched cbrt2Cut 2 2 = 3`
  (`⌈2^{3/2}⌉`; the ladder consumes its own degree-3 brick as an exponent);
  degree e — `ePow_at_two : powSched eulerModCut 3 2 = 7` (`⌈2^{11/4}⌉`),
  where `eulerModCut` reads e through `eulerCauchySeq.N`: the kernel runs
  **e's constructed modulus inside the schedule**.  Receipts take receipts as
  arguments; the ladder is a call tree of folds.
- **Cascade rung 1**: `reschedule` (limit-preserving modulus weakening) +
  `eSelfScheduled` — e carrying a modulus that queries e's own modulus.
- **Degree order ⟹ schedule order** (`powSched_mono`, via `dyUp_mono`):
  exponent-cut order transports to schedule order.  This is the backbone of
  *degree-as-a-cut*: the predicate "a degree-τ schedule suffices for `x`" is
  monotone in τ, so the exact degree of a real is a cut one level up — and
  the decidability of that threshold is precisely the effective-measure
  question (frontier board).

## 4. The reading

The fold/residue correction refines into a filtration: modulus degree counts
the receipts a pointing carries — 0 (the form is the cut), 1 (the rate is its
own receipt), composed (receipt-of-receipt), no finite degree (toward
reached-by-none).  This grades *pointings*, not the residue: the residue sits
in no rung (`object1_not_surjective`); the ladder classifies the ways of
pointing at it.
