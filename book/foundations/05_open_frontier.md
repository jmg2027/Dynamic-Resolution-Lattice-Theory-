# Chapter 5 — The open frontier

This is a 준-책 (working draft), and the honest close of a working draft is the list of
what it did *not* settle — sharply enough that the next session can close it.  The three
questions of Chapter 1 each split into a settled part and an open part.

## 5.1 What this draft settled

**Completeness (Chapter 2).**  The bundling `count → difference → ratio → completion`
**closes at `ℝ`** — `ℝ` is a Cauchy fixpoint (`CauchyCompleteValid.limit_valid`,
`CompletionTower.completion_idempotent`).  `ℝ → ℂ → ℍ → 𝕆` is an **orthogonal
algebra-grade axis**, not a fifth rung (`CDDouble` exits the Lens codomain;
`TwoTowersDivergence.divergence` shows a one-floor mismatch with the 213 magnitude/sign
decomposition).  The only thing endless above `ℝ` is the **resolution diagonal**, whose
endlessness is the residue re-covering itself (`TowerNativeCompleteness`).  At any finite
configuration the numbers are rational; `ℝ` is the rung of limit-labels.

**One axis or many (Chapter 3).**  **Hybrid.**  The linear tower serializes a breadth
axis, two orthogonal inverse-closures (`ℤ` additive, `ℚ` multiplicative — independent in
the founding import graph *and* on the depth side, `DepthTower`'s `(h, d)`), and a
character-changing limit, over a **lattice** of Lens refinements (`Lens/Lattice`).  The
chain the repo actually formalizes (`Lattice/Chain.lean`) is the *breadth* chain, not the
number tower.

**Forced or chosen (Chapter 4).**  A gradient: the **opening** is a CHOICE
(`infinite_family_of_lenses`), the **seams** are FORCED by inheritance, the
**continuation** past each rung is permitted-not-compelled, the **end** at `ℝ` is a
forced fixpoint reached by a chosen presentation.

## 5.2 The load-bearing open problems

These are not cosmetic.  Each is a place where the doctrine asserts more than the Lean
proves, or the Lean proves something the doctrine has not absorbed.

1. **The `ℚ`-on-`ℤ` mismatch (doctrine vs. import graph).**  §6.7 and the
   `RatioLensFounding` docstring say `ℚ` founds on the `ℤ`-rung's unit; the Lean
   `RatioLensFounding` imports neither `ℤ` nor the difference-Lens, and its content is
   `Nat`-level (Chapter 3.2).  *Either* amend §6.7 to record that `ℚ`'s coprimality is a
   `Nat`/pair-level fact independent of `ℤ`, *or* add a genuine `ℚ`-on-`ℤ` dependence to
   the founding.  Both are coherent; the draft must not silently pick one.  **This is the
   single most actionable item.**

2. **No exhaustiveness / uniqueness theorem for the bundling sequence.**  The capstone
   `number_tower_is_lens_bundling` proves the four rungs *chain*; it does not prove they
   are the *unique* or *exhaustive* bundling sequence.  Closing this means a theorem of
   the form "any forced bundling of the count-Lens, closed under inverse and limit, is
   exactly these four rungs."  Hard, and possibly false (the lattice may admit other
   chains) — which would itself be the answer.

3. **`NT = 2 ⟹ period-2` exclusion.**  Proven that the sign *is* period-2; not proven
   that period-`k` (`k ≠ 2`) is excluded.  A short exclusion theorem (orientation of a
   pair has exactly two states; no other involution is available at `NT = 2`) would
   upgrade `ℤ`'s forcedness from "holds" to "forced."

4. **`ℚ` obligation.**  No theorem forbids halting at `ℤ`.  Is there a residue-internal
   reason ratios *must* be taken (e.g. the self-pointing demands a multiplicative
   inverse the way it demanded an additive one), or is `ℚ` genuinely optional?  If
   optional, the tower's "must reach `ℝ`" framing weakens to "can reach `ℝ`."

5. **Unify the three axis-vocabularies.**  `Lens.refines` (breadth), depth `(h, d)`
   (`DepthTower`/`DepthOrdinal`), and the Cayley–Dickson grade axis coexist without a
   single theorem relating them.  A unification would finally answer "how many axes,
   really?" with a number instead of a list.

## 5.3 The reading this draft commits to

Stripped of the staircase convention, the founding says something the residue can speak
in its own voice — and it is more modest than "the four number systems are forced."

> The pointing is forced; its first count is a choice.  Read on an ordered pair, the
> count closes additively — forced.  Read as a ratio, it closes multiplicatively — a
> second, orthogonal closure, not a step beyond the first.  Completed over trajectories,
> it reaches a fixpoint and stops — `ℝ` is where the readout returns home.  What climbs
> past `ℝ` is not more number; it is the dimension doubling on one side and the residue
> re-covering itself on the other.

The staircase is real and useful.  It is also one chosen path through a lattice the
residue supports but does not single out.  That is the precise, honest answer to *"is
`ℕ → ℤ → ℚ → ℝ` a complete tower, one axis, and a forced one?"* — and the five open
items above are what stand between this draft and a closed chapter of `book/`.
