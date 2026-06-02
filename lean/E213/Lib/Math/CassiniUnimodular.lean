import E213.Lib.Math.Mobius213.Px.CharPolySelf
import E213.Meta.Int213.Core

/-!
# CassiniUnimodular — period-2 oscillation and the golden Cassini are one unimodular law

The marathon left the link between the **Bool oscillation** (period exactly 2,
`not(not r) = r`) and the **golden Cassini** surplus as a *thematic* connection.  Here it is
a theorem.  Both are 2nd-order `Int` orbits, and the Cassini determinant
`D(n) = s(n)·s(n+2) − s(n+1)²` of such an orbit is governed by one quantity — the orbit's
**multiplier** `q` (the determinant of its shift):

  * **Golden / Pell** orbit (`s(n+2) = NS·s(n+1) − s(n)`, multiplier `q = 1` = det of the
    shift `[[2,1],[1,1]]`): `D` is **conserved** — `det_golden` (`= d` at every `n`,
    recovering `cassini_general`).
  * **Bool oscillation** (`s(n+2) = s(n)`, the period-2 recurrence `not(not r) = r`,
    multiplier `q = −1` = det of the swap `[[0,1],[1,0]]`): `D` **alternates** sign —
    `det_period2_alternates` (`D(n+1) = −D(n)`); its magnitude is conserved, and on the
    concrete oscillation value-sequence (`toggle`, the `{1,0}` swap orbit) it is the unit
    `D = ±1` (`toggle_det_unit`).

So the period-2 oscillation and the conserved Cassini are the **same law at the two
unimodular multipliers** `q = ±1`: the *period* is set by the trace (`p = NS = 3`
hyperbolic vs `p = 0` reflection), the *conservation of `|D|`* by `|q| = 1`.  The "period-2
vs +1" reading is exactly `q = −1` vs `q = +1` — both unimodular.
`cassini_unimodular_dichotomy` bundles the two.

(The `toggle` sequence `1,0,1,0,…` is the `boolValue` readout of the swap orbit
`r, not r, not(not r), …`; the layer discipline keeps the `Bool213` dependency out of this
`Lib/Math` file, but `toggle (n+2) = toggle n` is the same period-2 fact as `not_not`.)

All zero-axiom.
-/

namespace E213.Lib.Math.CassiniUnimodular

open E213.Lib.Math.Mobius213.Px.POrbitClosure (L)
open E213.Lib.Math.Mobius213.Px.CharPolySelf (cassini_general)
open E213.Lib.Physics.Simplex.Counts (d)

/-- `-(a − b) = b − a`, ∅-axiom via the `Int213` primitives (no core `Int.neg_sub`,
    which is not available propext-free here). -/
private theorem neg_sub_pure (a b : Int) : -(a - b) = b - a := by
  show -(a + (-b)) = b + (-a)
  rw [E213.Meta.Int213.neg_add a (-b), Int.neg_neg b,
      E213.Meta.Int213.add_comm (-a) b]

/-- The **Cassini determinant** of a sequence, in the `det = s(n)·s(n+2) − s(n+1)²`
    orientation (matching `cassini_general`): the conserved `2×2` determinant of the
    consecutive orbit window. -/
def det (s : Nat → Int) (n : Nat) : Int :=
  s n * s (n + 2) - s (n + 1) * s (n + 1)

/-! ## §1 — golden reading (q = 1): the determinant is conserved -/

/-- ★ **Golden Cassini is conserved at `d`** (`q = 1`).  The `L`-orbit's multiplier is `1`
    (det of `[[2,1],[1,1]]`), so its Cassini determinant is the constant `d = NS + NT = 5`
    at every layer — this is exactly `cassini_general`. -/
theorem det_golden (n : Nat) : det L n = (d : Int) := cassini_general n

/-! ## §2 — oscillation reading (q = −1): the determinant alternates -/

/-- ★★ **Period-2 Cassini alternates** (`q = −1`).  A period-2 orbit (`s(n+2) = s(n)`, the
    oscillation recurrence `not(not r) = r`) has multiplier `−1` (det of the swap), so its
    Cassini determinant flips sign each step: `D(n+1) = −D(n)`.  The magnitude is conserved
    (no `ring` needed — `p = 0`, so there are no cross terms; just `neg_sub`). -/
theorem det_period2_alternates (s : Nat → Int) (hp : ∀ m, s (m + 2) = s m) (n : Nat) :
    det s (n + 1) = - det s n := by
  unfold det
  rw [hp (n + 1), hp n]
  exact (neg_sub_pure _ _).symm

/-! ## §3 — the concrete oscillation toggle: the unit determinant -/

/-- The `{1,0}` toggle — the `boolValue` readout of the swap orbit `r, not r, …`, period 2
    by construction. -/
def toggle : Nat → Int
  | 0 => 1
  | 1 => 0
  | (n + 2) => toggle n

/-- `toggle` has period 2 (the `not_not` fact, here definitional). -/
theorem toggle_period2 (n : Nat) : toggle (n + 2) = toggle n := rfl

/-- ★★ **The oscillation's Cassini determinant is the unit.**  `det toggle 0 = 1`, and by
    `det_period2_alternates` it stays `±1` at every step — the oscillation's conserved
    `|Cassini|` is exactly the unit `1`. -/
theorem toggle_det_unit : det toggle 0 = 1 := rfl

/-! ## §4 — the unimodular dichotomy -/

/-- ★★★ **The period-2 oscillation and the golden Cassini are one unimodular law.**  Two
    readings of the Cassini multiplier at `q = ±1`:

    1. **golden** (`q = 1`, det of `[[2,1],[1,1]]`): the determinant is *conserved* —
       `det L (n+1) = det L n` (both `= d`);
    2. **oscillation** (`q = −1`, det of the swap): the determinant *alternates* —
       `det s (n+1) = −det s n` for every period-2 orbit.

    Both shifts are **unimodular** (`|q| = 1`), so both conserve `|Cassini|`; the difference
    — conserved vs alternating, period ∞ vs 2 — is the *trace* (`p = NS` vs `p = 0`), not the
    determinant.  The marathon's "period-2 ↔ Cassini +1" thematic link is this: the two
    unimodular multipliers `q = ±1`. -/
theorem cassini_unimodular_dichotomy :
    (∀ n : Nat, det L (n + 1) = det L n)
    ∧ (∀ (s : Nat → Int), (∀ m, s (m + 2) = s m) → ∀ n, det s (n + 1) = - det s n) :=
  ⟨fun n => by rw [det_golden, det_golden], det_period2_alternates⟩

end E213.Lib.Math.CassiniUnimodular
