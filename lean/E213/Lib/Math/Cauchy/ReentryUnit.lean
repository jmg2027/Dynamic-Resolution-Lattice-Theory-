import E213.Theory.Raw.API
import E213.Lib.Math.Cauchy.DepthOverflowDuality

/-!
# ReentryUnit — the foundational descent unit IS the tower overflow unit

The self-applying re-entry has two faces, proven separately: the **foundational** descent
(`Theory.Raw.Lambek`, peeling a Raw drops `depth` by the unit, well-founded → converges)
and the **tower** overflow (`Cauchy.DepthOverflowDuality`, a value exceeds its bound by the
unit, top-less → escapes).  This file states the one fact behind both: the unit is the
*same* `Nat` surplus `1`, the count-Lens residue of one distinguishing.

  * **The slash constructor realizes the minimal overflow.**  `(x / y).depth =
    max(x.depth, y.depth) + 1` is exactly `minOverflow` (the pointwise-least overflow,
    `bound + 1`) over the parts' depths (`slash_depth_is_minOverflow`).  The act of pointing
    (parenting two distinct Raws) adds precisely the irreducible unit on top of the deeper
    part — the foundational pointing step *is* the tower's minimal overflow.

  * **Each peel is an overflow.**  A part's depth is overflowed by its whole's depth
    (`part_is_overflow`: `IsPart c p → Overflow (const c.depth) (const p.depth)`), and that
    overflow is, by `Nat`, the unit surplus `c.depth + 1 ≤ p.depth`
    (`peel_overflow_is_unit`).

So the downward (converging, well-founded) and upward (escaping, top-less) readings move by
the identical unit `1`; well-foundedness is the only thing that distinguishes which way the
unit is read.  This is the precise, cross-scale form of the engine's first property — *the
step is the irreducible unit* — without forcing the two acts (peel on `Raw`, overflow on
`Nat → Nat`) into one operator: the shared object is the `Nat` unit they both move by.

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.ReentryUnit

open E213.Theory (Raw)
open E213.Theory.Raw.Lambek (IsPart part_depth_lt part_depth_succ_le)
open E213.Lib.Math.Cauchy.DepthOverflowDuality (Overflow minOverflow overflow_is_unit_surplus)

/-! ## §1 — the slash constructor is the minimal overflow over its parts -/

/-- ★★ **The pointing step is the minimal overflow.**  `(x / y).depth = max(x.depth,
    y.depth) + 1`, which is exactly `minOverflow` (the least overflow, `bound + 1`) of the
    constant bound `max(x.depth, y.depth)`.  Parenting two distinct Raws adds precisely the
    irreducible unit above the deeper part — the foundational step realizes the tower's
    minimal-overflow generator. -/
theorem slash_depth_is_minOverflow (x y : Raw) (h : x ≠ y) (i : Nat) :
    (Raw.slash x y h).depth = minOverflow (fun _ => max x.depth y.depth) i := by
  rw [Raw.depth_slash]
  -- `minOverflow bound i = bound i + 1`; goal `1 + max .. = max .. + 1`.
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

/-! ## §3 — the cross-scale unit, bundled -/

/-- ★★★ **One unit, two scales.**  For the pointing step `x / y`:

    1. its depth is the minimal overflow over its parts (`slash_depth_is_minOverflow`) — the
       foundational step *is* the tower's least overflow;
    2. every peel from it is an overflow (`part_is_overflow`);
    3. that overflow is exactly the unit surplus `+1` (`peel_overflow_is_unit`).

    The foundational descent (`Lambek`, converging) and the tower overflow
    (`DepthOverflowDuality`, escaping) move by the identical `Nat` unit `1`; only
    well-foundedness distinguishes the direction.  No operator is forced across the two
    types — the shared object is the unit they both step by. -/
theorem reentry_unit_across_scales (x y : Raw) (h : x ≠ y) :
    (∀ i : Nat, (Raw.slash x y h).depth = minOverflow (fun _ => max x.depth y.depth) i)
    ∧ (∀ (c : Raw) (i : Nat), IsPart c (Raw.slash x y h) →
        Overflow (fun _ => c.depth) (fun _ => (Raw.slash x y h).depth) i)
    ∧ (∀ (c : Raw) (i : Nat), Overflow (fun _ => c.depth) (fun _ => (Raw.slash x y h).depth) i
        ↔ c.depth + 1 ≤ (Raw.slash x y h).depth) :=
  ⟨fun i => slash_depth_is_minOverflow x y h i,
   fun c i hc => part_is_overflow c _ hc i,
   fun c i => peel_overflow_is_unit c _ i⟩

end E213.Lib.Math.Cauchy.ReentryUnit
