import E213.Lib.Math.Foundations.UniverseChain.RawRecurrence
import E213.Theory.Raw.API

/-!
# The census reading of the `RawNat` spine — `2,3,5,12,…` as a second Lens on one object (∅-axiom)

`RawNat` (`Theory/Raw/RawNat`) is the `slash`-successor spine of `Raw`, read by `depth` as the linear
naturals `0,1,2,3,…`.  The *same* spine carries a **second, wider reading**: the level *population*
`rawCount n = 2 + C(rawCount (n−1), 2)` = `2,3,5,12,68,…` (`RawRecurrence`, Mingu's discovered
recurrence — canonical Raws of depth ≤ n).  This file ties the two: `census` is the count reading of a
`RawNat` rung, and the recurrence is re-indexed by `RawNat`'s **own** successor, so the count-spine is
a function on the generated naturals, not an external `Nat` sequence.

  * `census x = rawCount (toNat x)` — the population at the level `x` names.
  * `census_zero`, `census_succ` — the recurrence indexed by `RawNat.succ`.
  * `two_readings` — `depth` (linear `toNat`) and `census` (population) are two Lens readings of the
    one spine; concretely `census (depth-2 rung) = 5 = |canonical Raws of depth ≤ 2|`.

∅-axiom.
-/

namespace E213.Lib.Math.Foundations.UniverseChain.RawNatCensus

open E213.Lib.Math.Foundations.UniverseChain.RawRecurrence (choose2 rawCount rawCount_succ)
open E213.Theory.Raw.RawNat.RawNat (zero succ toNat toNat_zero toNat_succ)

/-- The **count reading** of a `RawNat` rung: how many canonical `Raw`s sit at or below its depth.
    `depth` reads the spine *linearly* (`toNat`); `census` reads its *population*. -/
def census (x : E213.Theory.Raw.RawNat.RawNat) : Nat := rawCount (toNat x)

/-- The seed level holds the two atoms. -/
theorem census_zero : census zero = 2 := by
  show rawCount (toNat zero) = 2
  rw [toNat_zero]; decide

/-- ★ **The recurrence, re-indexed by `RawNat`'s own successor.**  `census (succ x) = 2 + C(census x,
    2)` — Mingu's recurrence as a function on the generated naturals: one more distinguishing adds the
    unordered distinct pairs of the previous level. -/
theorem census_succ (x : E213.Theory.Raw.RawNat.RawNat) :
    census (succ x) = 2 + choose2 (census x) := by
  show rawCount (toNat (succ x)) = 2 + choose2 (rawCount (toNat x))
  rw [toNat_succ, rawCount_succ]

/-- ★★ **Two Lens readings of one spine.**  The single `RawNat` spine reads two ways: `depth` =
    `toNat` (the linear index `0,1,2,…`) and `census` (the population `2,3,5,12,…`).  They are distinct
    readings of the *same* object — at the depth-2 rung the linear reading is `2` while the population
    reading is `5` (the five canonical Raws of depth ≤ 2). -/
theorem two_readings :
    toNat (succ (succ zero)) = 2 ∧ census (succ (succ zero)) = 5
    ∧ census zero = 2 ∧ census (succ zero) = 3
    ∧ census (succ (succ (succ zero))) = 12 := by
  refine ⟨?_, ?_, census_zero, ?_, ?_⟩
  · rw [toNat_succ, toNat_succ, toNat_zero]
  · rw [census_succ, census_succ, census_zero]; decide
  · rw [census_succ, census_zero]; decide
  · rw [census_succ, census_succ, census_succ, census_zero]; decide

end E213.Lib.Math.Foundations.UniverseChain.RawNatCensus
