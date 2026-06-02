import E213.Theory.Raw.API
import E213.Lib.Math.Cauchy.DepthOverflowDuality

/-!
# ReentryUnit — the foundational descent step and the tower overflow share the `Nat` unit

The self-applying re-entry has two faces, proven separately: the **foundational** descent
(`Theory.Raw.Lambek`, peeling a Raw drops `depth`, well-founded → converges) and the
**tower** overflow (`Cauchy.DepthOverflowDuality`, a value exceeds its bound, top-less →
escapes).  The load-bearing link this file makes is one fact: a peel, restated through the
tower's own `Overflow` predicate, reduces to the **same** unit surplus `+1` the tower uses
(`peel_overflow_is_unit`, via the shared `overflow_is_unit_surplus`).  That is the one place
two `1`s from different files are identified as the same `Nat` successor.

The two supporting observations are lighter:

  * **The slash depth matches the minimal-overflow shape.**  `(x / y).depth = max(x.depth,
    y.depth) + 1` and `minOverflow bound = bound + 1` are both `(·) + 1`, so they agree
    modulo `add_comm` (`slash_depth_is_minOverflow`) — a shared `+1` shape, not a deep fact.

  * **Each peel is an overflow.**  `IsPart c p → c.depth < p.depth` is, by definition of
    `Overflow`, an overflow of `p.depth` over `c.depth` (`part_is_overflow`) — `part_depth_lt`
    read through the tower predicate.

So the converging (well-founded) and escaping (top-less) readings move by the same `Nat`
unit `1`; well-foundedness is what distinguishes the direction.  This does **not** force the
two acts (peel on `Raw`, overflow on `Nat → Nat`) into one operator — the only shared object
is the `Nat` unit, and only `peel_overflow_is_unit` proves they are the same one.

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.ReentryUnit

open E213.Theory (Raw)
open E213.Theory.Raw.Lambek (IsPart part_depth_lt part_depth_succ_le)
open E213.Lib.Math.Cauchy.DepthOverflowDuality (Overflow minOverflow overflow_is_unit_surplus)

/-! ## §1 — the slash depth matches the minimal-overflow shape -/

/-- **The slash depth has the minimal-overflow shape.**  `(x / y).depth = max(x.depth,
    y.depth) + 1` and `minOverflow bound = bound + 1` are both `(·) + 1`; over the constant
    bound `max(x.depth, y.depth)` they agree modulo `add_comm`.  A shared `+1` shape — the
    content is only that both definitions are a successor. -/
theorem slash_depth_is_minOverflow (x y : Raw) (h : x ≠ y) :
    (Raw.slash x y h).depth = minOverflow (fun _ => max x.depth y.depth) 0 := by
  rw [Raw.depth_slash]
  -- `minOverflow bound 0 = bound 0 + 1`; goal `1 + max .. = max .. + 1`.
  show 1 + max x.depth y.depth = max x.depth y.depth + 1
  exact Nat.add_comm 1 _

/-! ## §2 — each peel is an overflow, by the unit -/

/-- **Each peel is an overflow.**  If `c` peels from `p` (`IsPart c p`), then `p`'s depth
    overflows `c`'s depth in the `DepthOverflowDuality` sense — the same predicate the tower
    uses for the escaping diagonal, here for the foundational descent. -/
theorem part_is_overflow (c p : Raw) (h : IsPart c p) (i : Nat) :
    Overflow (fun _ => c.depth) (fun _ => p.depth) i :=
  part_depth_lt c p h

/-- **The peel-overflow is the unit surplus.**  The overflow of `p` over its part `c` is, by
    `Nat`, exactly `c.depth + 1 ≤ p.depth` — the irreducible unit `1`, the same surplus
    `overflow_is_unit_surplus` reads at the tower scale. -/
theorem peel_overflow_is_unit (c p : Raw) (i : Nat) :
    Overflow (fun _ => c.depth) (fun _ => p.depth) i ↔ c.depth + 1 ≤ p.depth :=
  overflow_is_unit_surplus _ _ i

/-! ## §3 — the shared unit, bundled -/

/-- ★★ **The peel and the overflow share the `Nat` unit.**  The load-bearing fact is the
    third conjunct: a peel from `x / y`, read through the tower's `Overflow` predicate,
    reduces to the unit surplus `c.depth + 1 ≤ (x / y).depth` — the *same* `+1` the tower
    uses, via the shared `overflow_is_unit_surplus`.  Conjuncts 1–2 are the lighter
    supporting shape-matches (`slash_depth_is_minOverflow` is `add_comm`; `part_is_overflow`
    is `part_depth_lt` read through `Overflow`).  No operator is forced across the two types
    (peel on `Raw`, overflow on `Nat → Nat`); only the `Nat` unit is shared, and only the
    third conjunct proves two such units the same. -/
theorem reentry_unit_across_scales (x y : Raw) (h : x ≠ y) :
    ((Raw.slash x y h).depth = minOverflow (fun _ => max x.depth y.depth) 0)
    ∧ (∀ (c : Raw) (i : Nat), IsPart c (Raw.slash x y h) →
        Overflow (fun _ => c.depth) (fun _ => (Raw.slash x y h).depth) i)
    ∧ (∀ (c : Raw) (i : Nat), Overflow (fun _ => c.depth) (fun _ => (Raw.slash x y h).depth) i
        ↔ c.depth + 1 ≤ (Raw.slash x y h).depth) :=
  ⟨slash_depth_is_minOverflow x y h,
   fun c i hc => part_is_overflow c _ hc i,
   fun c i => peel_overflow_is_unit c _ i⟩

end E213.Lib.Math.Cauchy.ReentryUnit
