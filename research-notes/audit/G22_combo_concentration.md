# G22 — Slot-Combination Concentration: How 213 Theorems Actually Compose

**Author:** Claude (inspection); Mingu Jeong (methodology directive)
**Date:** 2026-05-XX (continues G17–G21)
**Companion file:**
  - `research-notes/G17_inspect_top_combos.md` (60 specimens across top 10 combos)

## §0  Cross-cutting question

G17–G21 looked at clusters by single dimension (∃, equality strata,
omega/simp, building blocks).  G22 asks the cross-cutting question:

  > For each theorem, which slots fire *together*?  Are there
  > recurring combinations — canonical "shapes" of 213 theorems?

Answer: **YES, dramatically so.**  The top 5 combos cover **54%** of
all theorems; top 10 cover **65%**.  566 unique combos exist but the
head is heavily concentrated.

## §1  Top 10 slot-combinations (across 4,624 theorems)

```
 #   Combo                              Count   % of all theorems
 1   decide                             1,375    29.7
 2   AND, decide                          349     7.5
 3   rfl                                  331     7.2
 4   (empty / pure term-mode)             229     5.0
 5   AND, anon, decide, refine            214     4.6
 6   exact, rw                            105     2.3
 7   FORALL, decide                        90     1.9
 8   rw                                    80     1.7
 9   IMPLIES                               63     1.4
10   IMPLIES, rfl                          60     1.3
                                       ─────    ────
                                        2,896    62.6
```

Plus 556 minor combos covering the remaining 37%.

## §2  The five dominant theorem-shapes (54% of codebase)

### Shape 1: `decide` — **atomic computation check** (1375, 30%)

```lean
theorem leaves_equates : Lens.leaves.view rAAB = Lens.leaves.view rABB := by decide
theorem parity_equates_ab : parityLens.view Raw.a = parityLens.view Raw.b := by decide
theorem rA1_depth_odd : Lens.depth.view rA1 % 2 = 1 := by decide
```

What it expresses: "This single equality holds.  Run the kernel."
The DEFAULT 213 theorem.  Almost a third of the codebase.

### Shape 2: `AND, decide` — **bundled atomic checks** (349, 7.5%)

```lean
theorem phase_CE_capstone :
    kerSizeDelta0 = 2 ∧ 2^5 = 32 ∧ 2^12 = 4096 ∧ 16 * 256 = 4096
    ∧ 256 = 2^8 ∧ 8 = 3 * 3 - 1 := by decide
theorem chi_N_pattern :
    chi_delta4 = 1 ∧ chi_two_glued = 2 ∧ chi_3_glued = 3 ∧ chi_4_glued = 4 := by decide
```

What it expresses: "These N equalities all hold.  Run the kernel
on each."  No `refine ⟨..⟩` needed — `decide` handles `∧`-chains
directly.

### Shape 3: `rfl` — **definitional identity** (331, 7.2%)

```lean
theorem boolToConstLens_true : boolToConstLens true = constTrueLens := rfl
theorem f9Lens_view_a : f9Lens.view Raw.a = F9.one := rfl
```

What it expresses: "This is true *by definition*.  Single-step
reduction."  Definitional unfolding without execution.

### Shape 4: `(empty / pure term-mode)` — **manual lifting** (229, 5%)

```lean
theorem Raw.swap_depth (r : Raw) : (Raw.swap r).depth = r.depth :=
  Tree.swap_depth r.val r.property

theorem Raw.swap_injective' : Function.Injective Raw.swap :=
  fun _ _ h => Raw.swap_injective h
```

What it expresses: "This follows by directly applying an existing
lemma at the right arguments."  No tactic at all — pure term-mode
function application.

### Shape 5: `AND, anon, decide, refine` — **capstone bundle** (214, 4.6%)

```lean
theorem mul_generators_ne_zero :
    I' * J ≠ 0 ∧ J * I' ≠ 0 ∧ I' * I' ≠ 0 ∧ J * J ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
```

What it expresses: "These N component facts all hold; bundle them
explicitly with `refine` and dispatch each by `decide`."  The
explicit-refine variant of Shape 2.  G18's "capstone" pattern.

## §3  Notable absences from the top 10

The following slots do NOT appear in any of the top 10 combos:

  · `cases`     (only ~5% of theorems use it)
  · `match`     (only ~3%)
  · `induction` (caught only as `intro` + `induction` keyword,
                 < 2% of theorems)
  · `omega`     (~2.4% — migration backlog)
  · `simp`      (~2.8% — migration backlog)
  · `CLASSICAL` (only 9 decls in entire codebase = G7/G9 demos)

So the dominant 65% of the codebase consists of:
  · **decide** (computational closure)
  · **rfl** (definitional reduction)
  · **AND** (conjunction bundling)
  · **anon + refine** (term-mode capstone scaffolding)
  · **exact + rw** (lemma-cite + structural rewrite)
  · **intro** (universal/implication unpacking)
  · **(empty)** (pure term-mode lifting)

The non-dominant 35% includes:
  · `cases/match` — when constructor enumeration is needed
  · `induction` — when structural recursion on a Raw / Tree / Nat is needed
  · `omega/simp` — when bounded-arithmetic / unfolding automation
                    closes it (and brings axioms)

## §4  Power-law distribution

```
Combo rank   Count   Cumulative %
       1     1,375    29.7
       5      214     54.0
      10       60     62.6
      25       17     79.0  (estimated)
      50        ?     90.0  (estimated)
     566        1    100.0
```

The combo distribution is heavy-tailed: the head dominates
massively, but a long tail of one-off combinations exists.

This empirically confirms a *style guide*:
  · Use `decide` whenever possible (Shape 1).
  · Bundle related `decide`-able facts under `∧` (Shape 2 or 5).
  · Use `rfl` when it works (Shape 3).
  · Lift to higher-level type by direct lemma application (Shape 4).
  · Use `cases/match/induction` only when structurally necessary.
  · Use `omega/simp` only when migration to ∅-axiom isn't yet done.

## §5  What this might mean (for Mingu's intuition)

Cross-cutting observation:

  · **65% of 213 theorems are "kernel-verifiable computational
    checks" — no clever proof, just compute or unfold.**
  · **Another 20% are structural propagations or dispatches**
    (rw, exact, intro, anon).
  · **Less than 5% require non-trivial tactic machinery**
    (omega/simp/cases/match/induction).
  · **Classical machinery is statistical noise (0.15%)**, exactly the
    9 G7/G9 demo cases.

The codebase IS the description of what 213 considers reasoning.
Reasoning, by frequency, is:
  > "verify the equality by running it"
or
  > "verify the conjunction of equalities by running each"
or
  > "this follows by directly applying a named lemma."

Whether this is "primitive", "naive", or "deep depending on how
you read it" is for Mingu's intuition.  The data says it is the
empirical shape of how 213 expresses mathematical content.

## §6  Five shapes side-by-side (quick reference)

```lean
-- Shape 1: atomic decide
theorem T : f x = c := by decide

-- Shape 2: bundled decide
theorem T : f x = c₁ ∧ g y = c₂ ∧ h z = c₃ := by decide

-- Shape 3: rfl
theorem T : f x = c := rfl

-- Shape 4: term-mode lift
theorem T : prop_at_higher_level := lower_lemma args proof

-- Shape 5: capstone with refine
theorem T : claim₁ ∧ claim₂ ∧ ... ∧ claimₙ := by
  refine ⟨?_, ?_, ..., ?_⟩ <;> decide
```

These five forms are 54% of the entire 213 codebase.

## §7  Method recap — fingerprint axes

The slot-combo metric uses these axes:

  · **Statement structure** (=, ∃, ∀, →, ∧, ∨, ¬, ↔)
  · **Proof method** (rfl, decide, rw, cases, match, omega, simp,
                     refine, anon ⟨, intro, exact, Classical.*)

A "combo" is the sorted set of axis-labels with non-zero
occurrence in a theorem.  Two theorems share a combo iff their
fingerprints span the same axis set (regardless of magnitude).

This metric is conservative — it doesn't distinguish a theorem
using `rw` once from one using `rw` ten times.  But for top-level
shape recognition it suffices.

## §8  Open inspection directions

  · Look at the **long tail** (combos 11–566) to see how minor
    variations express specialized content.
  · Inspect **specific marathon namespaces** (Cohomology 1387,
    Real213 835) to see how the 5 shapes COMPOSE within a marathon.
  · Look at the 9 `CLASSICAL` decls in detail (we already know they
    are G7/G9 demos but inspecting their relationship to surrounding
    PURE theorems would be informative).
  · Trace `rw` *occurrences* (1,888) vs *decls using rw* (377):
    a few decls do most of the rw-work.

The audit infrastructure (`tools/theorem_audit.py` +
`tools/theorem_inspect.py`) accommodates any new fingerprint
filter.  Inspection continues to be the next-stitch bottleneck;
data collection is fast.
