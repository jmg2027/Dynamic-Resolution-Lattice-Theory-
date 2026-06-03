# G184 — the Garrabrant–Pak mod-2 obstruction is subsumed (for its witnesses) by the zero-run + two-continuation criteria

**Tier 1 (volatile).**  Outcome of attempting the heavy "third axis" (the Garrabrant–Pak mod-2
forbidden-factor obstruction, flagged in `G175`).  The disciplined finding: **for its concrete
witnesses, GP is already caught by the two ∅-axiom criteria we have — no 2-adic valuation
infrastructure is needed.**  So the heavy GP build is low-ROI; what remains genuinely heavy and
open is stated precisely at the end.

## What was added this leg (∅-axiom)

  - `ZeroRunNonHolonomic.FiniteRecurrence a := HomogRec a ∨ AutoRec a` — the unified
    finite-state-machine class (time-varying homogeneous P-recursive **or** time-invariant
    autonomous).
  - `ZeroRunNonHolonomic.distinct_next_equal_window_not_autoRec` — the **general Myhill–Nerode**
    obstruction: two positions with *equal* length-`k` windows but *different* next-values ⟹
    `¬ AutoRec` (the all-zero `two_continuations_not_autoRec` is the special case).
  - `ZeroRunNonHolonomicWitness.chi_not_finiteRecurrence : ¬ FiniteRecurrence χ` — the
    powers-of-two indicator escapes **both** machine classes in one statement.

(`ZeroRunNonHolonomic` 7 PURE, `ZeroRunNonHolonomicWitness` 21 PURE.)

## The finding — GP's witnesses fall to the existing criteria

GP Lemma 1.2.1 (arXiv:1505.06508): a P-recursive integer sequence's mod-2 word omits some
finite factor; contrapositive — a **factor-universal** mod-2 sequence (Champernowne) is
non-holonomic.  The proof uses 2-adic valuation.  But the canonical witness is caught without
any of that:

  - **Champernowne contains `0^k` for every `k`** (the all-zero string of every length is one of
    the concatenated blocks).  So it has **arbitrarily long zero-runs at arbitrarily large
    positions** and infinitely many `1`s ⟹ `zero_run_not_homogRec` gives `¬ HomogRec`
    (no time-varying homogeneous P-recursive recurrence) — *exactly the GP conclusion*, with no
    valuation.
  - Factor-universality ⟹ the all-zero `k`-window is followed by both `0` (inside `0^{k+1}`) and
    `1` (in `0^k 1`) ⟹ `two_continuations_not_autoRec` gives `¬ AutoRec`.
  - Hence `¬ FiniteRecurrence` — both machine classes — by the same elementary route that
    handles `χ`.

So the 2-adic GP machinery is **unnecessary for factor-universal / long-zero-run witnesses**:
the zero-run criterion (for the linear class) and the Myhill–Nerode criterion (for the
autonomous class) already certify them.  This is why no GP infrastructure was built — it would
duplicate, on its concrete witnesses, results already ∅-axiom (repo-first / assume-nothing).

## Honest scope — what GP is strictly more general about, and what stays heavy/open

  - **Full GP (structural)** is strictly stronger than "zero-runs": it asserts *every*
    P-recursive integer sequence omits *some* mod-2 factor, including time-varying P-recursive
    sequences with **no** long zero-runs and **consistent** window-continuations (which neither
    `zero_run_not_homogRec` nor the Myhill–Nerode criterion detects).  Catching *those* corner
    cases is what the 2-adic valuation argument is for — a genuine but lower-ROI heavy target
    (no natural witness needs it that the existing criteria miss).
  - **Dense aperiodic sequences with no long zero-runs** (Thue–Morse, Sturmian) are *not* caught
    by the zero-run criterion, and the autonomous-class escape for them needs the **Morse–Hedlund
    direction** (bounded factor-complexity ⟹ eventually periodic) for *all* `k` — a real
    classical theorem, the genuinely heavy still-open ∅-axiom target on this axis.
  - **π itself** — classically OPEN, not ∅-axiom-closable (FGS analytic shape obstruction, no
    constructive shadow, bottoms out at unproven Gauss–Kuzmin normality of π).

## Net

The "third machine-class axis" turned out, for every concrete witness, to be **the same two
criteria already proven**.  The marathon's ∅-axiom reach on non-holonomicity is therefore: two
machine classes (`HomogRec`, `AutoRec`), their union (`FiniteRecurrence`), two escape criteria
(zero-run, Myhill–Nerode), and witnesses escaping both (`(n!)ⁿ` by growth, `χ` by sparseness).
The remaining heavy targets (full-GP corner, Morse–Hedlund for dense, π) are stated above;
none is forced by a witness the current tools miss.
