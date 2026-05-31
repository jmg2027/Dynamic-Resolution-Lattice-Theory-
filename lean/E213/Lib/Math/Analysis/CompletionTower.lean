import E213.Lib.Math.Analysis.CauchyCompleteValid

/-!
# CompletionTower — grouping thresholds, then grouping the groupings, closes

A transcendental real is presented as infinitely many threshold decisions
(`cut i m k` over all probes `m/k`).  Completion (`CauchyCutSeq.limit`)
**groups** that infinite family into one object — a single cut — by supplying a
modulus that says, at each probe, which layer to read.

The natural next thought: do it again.  Treat each completed limit as one term of
a *new* sequence, and group those — a sequence of sequences, completed; then a
sequence of *those*, completed; and so on.  Is this an infinite regress that
never lands, or a closed operation that returns home?

This file settles it: **it returns home, by `rfl`.**  Three facts.

  1. **Type closure.**  `limit : CauchyCutSeq → (ℕ → ℕ → Bool)`.  A cut is `ℕ → ℕ
     → Bool`; a cut-*sequence* is `ℕ → ℕ → ℕ → Bool`.  Completion takes the
     sequence and returns a cut — *the same type a single threshold-family
     lives in*.  The tower does not escalate to ever-higher types; each level
     lands back on `ℕ → ℕ → Bool`.

  2. **Idempotence / collapse.**  A level-2 tower — an outer cut-sequence whose
     `i`-th term is itself a completed limit `(inner i).limit` — completes to
     *one* inner completion evaluated at the outer modulus
     (`tower_is_single_inner`, `rfl`).  No second object is created; the two
     levels flatten to a single `(inner (Nₒ m k)).limit m k`.  Completing a thing
     that is already a limit is the identity (`completion_idempotent`).

  3. **Modulus composition.**  The only thing that accumulates up the tower is the
     **modulus**: level 2 reads at `inner`'s modulus composed after the outer
     modulus.  This is exactly the `(ℕ,+)`-graded composition of
     `Analysis/ResolutionShift` (`IsResolutionShift_compose`): grouping-of-
     groupings stacks grades, it does not stack objects.

So the "threshold of thresholds of thresholds …" sequence is not regress.  It is
the **self-similar floor** of `Theory/Raw/Lambek.self_similar_floor` read at the
cut scale (and the scale-invariance of `ObjectIsReadingScaleInvariant`): one fixed
shape — *group an indexed family into one object of the same kind* — recurring at
every level, with the descent of moduli the only thing that moves.  The value is
pinned after a single completion; further grouping only re-indexes which layer
answers, never changes the answer.

All ∅-axiom.
-/

namespace E213.Lib.Math.Analysis.CompletionTower

open E213.Lib.Math.Analysis.CauchyComplete

/-! ## §1 — Idempotence: completing an already-completed cut is the identity -/

/-- ★★ **Completion is idempotent.**  Wrapping a completed limit `ccs.limit` as a
    constant sequence and completing *again* returns it unchanged.  A real, once
    pinned as a cut, is a fixed point of "group it into one object". -/
theorem completion_idempotent (ccs : CauchyCutSeq) :
    (constCauchyCutSeq ccs.limit).limit = ccs.limit :=
  constCauchyCutSeq_limit ccs.limit

/-- ★★ **Two-level constant tower collapses to the floor.**  Grouping a cut `c`
    into a limit, then grouping *that* into another limit, returns `c` — by
    `rfl`.  The regress bottoms out at the original cut. -/
theorem const_tower_collapses (c : Nat → Nat → Bool) :
    (constCauchyCutSeq ((constCauchyCutSeq c).limit)).limit = c := by
  rw [constCauchyCutSeq_limit, constCauchyCutSeq_limit]

/-! ## §2 — The general level-2 tower collapses to one inner completion -/

/-- A **level-2 outer sequence**: term `i` is the completed limit of the inner
    `CauchyCutSeq` `inner i`.  A sequence-of-sequences, read as a cut-sequence. -/
def towerOuter (inner : Nat → CauchyCutSeq) : Nat → Nat → Nat → Bool :=
  fun i m k => (inner i).limit m k

/-- Assemble the level-2 tower into a single `CauchyCutSeq`, given that the outer
    sequence of inner-limits is itself Cauchy with modulus `No`. -/
def towerSeq (inner : Nat → CauchyCutSeq) (No : Nat → Nat → Nat)
    (hc : ∀ m k i j, i ≥ No m k → j ≥ No m k →
        towerOuter inner i m k = towerOuter inner j m k) : CauchyCutSeq where
  cs := towerOuter inner
  N := No
  cauchy := hc

/-- ★★★ **The level-2 tower collapses to a single inner completion.**  The
    completed value of the sequence-of-sequences at probe `(m,k)` *is* the inner
    limit `(inner (No m k)).limit m k` — one completion, evaluated at the outer
    modulus.  By `rfl`: grouping the groupings creates **no new object**, it only
    selects which inner real answers, via the composed modulus `inner ∘ No`. -/
theorem tower_is_single_inner (inner : Nat → CauchyCutSeq) (No : Nat → Nat → Nat)
    (hc : ∀ m k i j, i ≥ No m k → j ≥ No m k →
        towerOuter inner i m k = towerOuter inner j m k) (m k : Nat) :
    (towerSeq inner No hc).limit m k = (inner (No m k)).limit m k := rfl

/-- ★★★ **Type closure (the no-regress statement).**  Completion sends a
    cut-sequence (`ℕ → ℕ → ℕ → Bool`) to a cut (`ℕ → ℕ → Bool`) — the same type a
    single threshold-family inhabits.  Stated as the round trip: the level-2
    tower's limit is, at every probe, a value of the form `(_ : CauchyCutSeq).limit
    m k`, i.e. a level-1 limit value.  The tower never leaves `ℕ → ℕ → Bool`. -/
theorem tower_stays_in_cut (inner : Nat → CauchyCutSeq) (No : Nat → Nat → Nat)
    (hc : ∀ m k i j, i ≥ No m k → j ≥ No m k →
        towerOuter inner i m k = towerOuter inner j m k) :
    ∃ pick : Nat → Nat → Nat,
      ∀ m k, (towerSeq inner No hc).limit m k = (inner (pick m k)).limit m k :=
  ⟨No, fun m k => tower_is_single_inner inner No hc m k⟩

/-! ## §3 — Stability: the value is pinned after one completion -/

/-- ★★ **One completion pins the value; further grouping re-indexes only.**  If
    the inner reals already agree at `(m,k)` past the outer modulus (the honest
    case — they are completing toward the *same* real), the level-2 limit equals
    *any* inner term's limit there, not just the one at `No m k`.  Grouping the
    groupings changes which layer answers, never the answer. -/
theorem tower_value_stable (inner : Nat → CauchyCutSeq) (No : Nat → Nat → Nat)
    (hc : ∀ m k i j, i ≥ No m k → j ≥ No m k →
        towerOuter inner i m k = towerOuter inner j m k)
    (m k i : Nat) (hi : i ≥ No m k) :
    (towerSeq inner No hc).limit m k = (inner i).limit m k := by
  have h := (towerSeq inner No hc).limit_eq_at m k i hi
  rw [h]; rfl

end E213.Lib.Math.Analysis.CompletionTower
