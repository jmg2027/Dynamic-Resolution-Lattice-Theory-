import E213.Lib.Math.Mobius213.Px.CharPolySelf
import E213.Meta.Int213.Core
import E213.Meta.Int213.PolyIntMTactic

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
open E213.Lib.Math.Mobius213.Px.CharPolySelf (cassini_general L_rec)
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

/-! ## §5 — the parametric Cassini law: `det` multiplies by the orbit's `q` each step

The two readings above (`det_golden` `q=1`, `det_period2_alternates` `q=−1`) are instances of
**one** law: for *any* 2nd-order `Int` recurrence `s(n+2) = p·s(n+1) − q·s(n)`, the Cassini
determinant multiplies by the shift's determinant `q` at every step — `det s (n+1) = q·det s n`
— hence `det s n = qⁿ·det s 0`.  No `q² = 1` is needed for the step (unimodularity only makes
`|det|` *constant*); the multiplier is the orbit's own `q`, whatever it is. -/

/-- ★★★ **The Cassini multiplier law (parametric).**  For any `Int` orbit obeying the 2nd-order
    recurrence `s(n+2) = p·s(n+1) − q·s(n)`, one Cassini step multiplies the determinant by the
    shift determinant `q`: `det s (n+1) = q · det s n`.  (The discrete-Wronskian / Abel identity:
    `D(n+1) = q·D(n)`, by one `ring_intZ` after expanding `s(n+2)`, `s(n+3)` via the
    recurrence.)  `det_golden` is `q=1`; `det_period2_alternates` is `p=0, q=−1`. -/
theorem det_step (p q : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 2) = p * s (n + 1) - q * s n) (n : Nat) :
    det s (n + 1) = q * det s n := by
  have h2 : s (n + 2) = p * s (n + 1) - q * s n := hrec n
  have h3 : s (n + 3) = p * s (n + 2) - q * s (n + 1) := hrec (n + 1)
  show s (n + 1) * s (n + 3) - s (n + 2) * s (n + 2)
       = q * (s n * s (n + 2) - s (n + 1) * s (n + 1))
  rw [h3, h2]
  ring_intZ

/-- The multiplier power `qⁿ`, recursively (a propext-free `Int` power — Mathlib-free Lean lacks
    the `pow_zero`/`pow_succ` lemmas for `Int`). -/
def qpow (q : Int) : Nat → Int
  | 0     => 1
  | n + 1 => q * qpow q n

/-- ★★ **The closed form: `det s n = qⁿ · det s 0`.**  Iterating `det_step`: the Cassini
    determinant of the orbit at layer `n` is its initial value scaled by the `n`-th power of the
    multiplier `q`.  (`q=1`: constant `det s 0`; `q=−1`: alternating `±det s 0`.) -/
theorem det_closed (p q : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 2) = p * s (n + 1) - q * s n) (n : Nat) :
    det s n = qpow q n * det s 0 := by
  induction n with
  | zero => show det s 0 = 1 * det s 0; ring_intZ
  | succ k ih =>
      show det s (k + 1) = q * qpow q k * det s 0
      rw [det_step p q s hrec k, ih]; ring_intZ

/-- The period-2 recurrence `s(n+2) = s n` is the `p=0, q=−1` shape `s(n+2) = 0·s(n+1) − (−1)·s n`. -/
private theorem zero_sub_negone_mul (a b : Int) : (0 : Int) * a - (-1) * b = b := by
  rw [E213.Meta.Int213.zero_mul, E213.Meta.Int213.neg_mul, Int.one_mul]
  show (0 : Int) + -(-b) = b
  rw [Int.neg_neg, E213.Meta.Int213.zero_add]

/-- ★★★ **The dichotomy is one law at two multipliers — both branches factor through `det_step`.**
    The golden orbit (`s(n+2) = 3·s(n+1) − 1·s(n)`, `q=1`, conserved) and *every* period-2 orbit
    (`s(n+2) = s n`, rewritten `s(n+2) = 0·s(n+1) − (−1)·s(n)`, `q=−1`, alternating) are both
    *instances of the single parametric `det_step`* — here enacted, not narrated: the q=−1 branch
    is `det_step 0 (-1)`, not the standalone `det_period2_alternates`.  "Period-2 vs Cassini +1"
    is exactly: same law, different `q`. -/
theorem cassini_law_one_at_two_multipliers :
    (∀ n, det L (n + 1) = 1 * det L n)
    ∧ (∀ (s : Nat → Int), (∀ m, s (m + 2) = s m) → ∀ n, det s (n + 1) = (-1) * det s n) :=
  ⟨det_step 3 1 L (fun n => by rw [Int.one_mul]; exact L_rec n),
   fun s hp => det_step 0 (-1) s (fun n => by rw [zero_sub_negone_mul]; exact hp n)⟩

end E213.Lib.Math.CassiniUnimodular
