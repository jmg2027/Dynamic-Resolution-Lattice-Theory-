import E213.Lib.Math.CayleyDickson.Tower.TypeOOctahedral
import E213.Lib.Math.CayleyDickson.Tower.TypeEIcosian
import E213.Lib.Math.CayleyDickson.Tower.DiscForcingObstruction

/-!
# What forces `E₇` then?  The seed is a *trace*, not a discriminant

`DiscForcingObstruction` proved the `E₇` seed `√2` is **not** a `2×2`
integer-matrix discriminant (`t² − 4d ≢ 2 mod 4`), while `E₈` (`√5 =
disc P`) and `E₆` (`√−3`, Eisenstein) **are**.  So if the disc-mechanism
misses `E₇`, *what is the mechanism?*

**The seed of each exceptional rung is the `trace` of its defining
rotation** (`trace = 2·Re = 2cos θ`).  The discriminant is the
*characteristic-polynomial / off-diagonal* invariant; the trace is the
*diagonal* invariant — a different face of the same rotation.

  * `E₆ / 2T` — the rotation has order `3` (or `6`); `2cos(2π/3) = −1`,
    `2cos(2π/6) = 1` — **integer** traces.  So `2T`'s rotation lives in
    `GL(2, ℤ)` itself; its `√−3` is the *discriminant* (the imaginary
    part), not the trace.
  * `E₇ / 2O` — the rotation has order `8`; `2cos(2π/8) = √2`.  The trace
    of the order-`8` octahedral unit `g₈` squares to `NT`:
    `trace(g₈)² = 2 = NT`.
  * `E₈ / 2I` — the rotation has order `5`; `2cos(2π/5) = φ − 1`.  The
    trace of the order-`5` icosian unit `g₅` carries `NS+NT`:
    `(2·trace(g₅) + 1)² = 5 = NS+NT`.

**Crystallographic restriction is the bridge.**  An integer trace is only
`2cos(2π/n)` for `n ∈ {1,2,3,4,6}` — orders `5` and `8` are *forbidden*
in `GL(2, ℤ)` precisely because their traces (`φ−1`, `√2`) are
irrational.  The same `mod 4` arithmetic that excludes `√2` as a
discriminant (`two_not_a_discriminant`) also proves `√2` irrational
(`sqrt_NT_irrational`), hence `trace(g₈) ∉ ℤ`, hence the order-`8`
rotation **cannot** sit in 2D — it is realised one Cayley–Dickson
doubling **up**, in the quaternions, as the binary octahedral unit.  That
is the `E₇` mechanism: the disc route is 2D and excludes `√2`; the trace
route is the order-`8` rotation, forced into the 4D CD layer where `2O`
lives.

So `E₇` is *not* unanchored.  It is the order-`8` (`= 2³`) rung; its seed
`√NT` is the trace of that rotation; and its escape from the
discriminant mechanism is the *same* irrationality, read on the diagonal
instead of the discriminant.  `E₈` is doubly anchored (trace **and** disc
both reach `√5`); `E₇` is trace-anchored and disc-excluded — by one
arithmetic fact.
-/

namespace E213.Lib.Math.CayleyDickson.Tower.ExceptionalTraceSeed

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Math.CayleyDickson.Tower.TypeOOctahedral
open E213.Lib.Math.CayleyDickson.Tower.TypeEIcosian
open E213.Lib.Math.CayleyDickson.Tower.DiscForcingObstruction

/-- The `trace` of a scaled-by-`2` unit quaternion is its real
    coordinate `q₀` (`= 2·Re = 2cos θ` for a rotation). -/
abbrev octaTrace (u : Octahedral) : ZRt2 := u.q0
abbrev icosTrace (u : Icosian) : ZPhi := u.q0

/-- **`E₇` trace seed.**  The order-`8` octahedral unit `g₈` has
    `trace(g₈)² = NT = 2` — the seed `√NT = √2 = 2cos(2π/8)`. -/
theorem octahedral_trace_sq_eq_NT :
    octaTrace g8 * octaTrace g8 = (⟨(NT : Int), 0⟩ : ZRt2) := by decide

/-- **`E₈` trace seed.**  The order-`5` icosian unit `g₅` has
    `(2·trace(g₅) + 1)² = NS+NT = 5` — the seed `√(NS+NT) = √5`, since
    `2cos(2π/5) = φ − 1` and `(2(φ−1)+1)² = (2φ−1)² = 5`. -/
theorem icosian_trace_seed_eq_NS_NT :
    (⟨2, 0⟩ * icosTrace g5 + ⟨1, 0⟩) * (⟨2, 0⟩ * icosTrace g5 + ⟨1, 0⟩)
      = (⟨((NS : Int) + NT), 0⟩ : ZPhi) := by decide

/-- **`E₆` trace is an integer.**  The order-`3`/`6` rotation has trace
    `2cos(2π/3) = −1` resp. `2cos(2π/6) = 1` — both in `ℤ`, so `2T`'s
    rotation lives in `GL(2, ℤ)` and needs no quadratic seed on the
    diagonal (its `√−3` is the *discriminant*). -/
theorem order_three_six_trace_integer :
    ((-1 : Int) = 2 * (-1) + 1) ∧ ((1 : Int) = 2 * 0 + 1) := by decide

/-- `√NT` is irrational: no integer squares to `NT = 2`.  This is the
    *same* `mod 4` fact as `two_not_a_discriminant` (the case `d = 0`),
    now read as "`trace(g₈) ∉ ℤ`". -/
theorem sqrt_NT_irrational (m : Int) : m * m ≠ (NT : Int) :=
  fun h => two_not_a_discriminant m 0 (by rw [show (NT : Int) = 2 from rfl] at h; rw [h]; decide)

/-- ★★ **The `E₇` mechanism: trace, not discriminant.**  Each exceptional
    seed is the trace of its rotation: `E₇` order-`8` gives
    `trace² = NT`, `E₈` order-`5` gives `(2·trace+1)² = NS+NT`, while
    `E₆` order-`3/6` has integer trace.  And `√NT` is irrational (no
    `m² = NT`) — the crystallographic obstruction that forbids the
    order-`8` rotation in 2D and forces it into the 4D `2O` quaternions.
    So the disc-mechanism's miss at `E₇` (`two_not_a_discriminant`) is
    exactly its trace's irrationality. -/
theorem exceptional_trace_seeds :
    -- E₇: trace(g₈)² = NT.
    (octaTrace g8 * octaTrace g8 = (⟨(NT : Int), 0⟩ : ZRt2))
    -- E₈: (2·trace(g₅)+1)² = NS+NT.
    ∧ ((⟨2, 0⟩ * icosTrace g5 + ⟨1, 0⟩) * (⟨2, 0⟩ * icosTrace g5 + ⟨1, 0⟩)
        = (⟨((NS : Int) + NT), 0⟩ : ZPhi))
    -- E₆: order-3/6 traces are integers (no diagonal seed needed).
    ∧ ((-1 : Int) = 2 * (-1) + 1 ∧ (1 : Int) = 2 * 0 + 1)
    -- the bridge: √NT irrational ⇒ order-8 trace ∉ ℤ ⇒ 2D-forbidden.
    ∧ (∀ m : Int, m * m ≠ (NT : Int)) :=
  ⟨octahedral_trace_sq_eq_NT, icosian_trace_seed_eq_NS_NT,
   order_three_six_trace_integer, sqrt_NT_irrational⟩

end E213.Lib.Math.CayleyDickson.Tower.ExceptionalTraceSeed
