import E213.Lib.Math.CassiniUnimodular
import E213.Lib.Math.Cauchy.NewtonGregory
import E213.Lib.Math.Cauchy.DepthCharacterization

/-!
# Cauchy.CassiniDepthFloor — a conserved (`q = 1`, `SL₂`) orbit sits at depth-0 Cassini

`CassiniUnimodular.det_step` showed the Cassini determinant of any 2nd-order `Int` recurrence
`s(n+2) = p·s(n+1) − q·s(n)` multiplies by `q` each step.  When `q = 1` (the shift is in `SL₂`,
e.g. the golden/Lucas/Pell orbit) the determinant is **conserved** — a *constant* sequence —
hence sits at **divergence depth 0** (`polyDepthZ 0`).

This is the *sufficiency* direction `q = 1 ⟹ depth 0`, the structural floor behind
`DepthResidueFloor.floor_polyDepth0` (the φ/`W` instance).  Honest scope:

  * only `q = 1` is covered — **not** all of unimodular `|q| = 1`: the `q = −1` (period-2) case
    *alternates* (`det_period2_alternates`), so it is depth-0 only when `det s 0 = 0`, otherwise
    genuinely non-constant.  The floor is the `SL₂` (`q = 1`) case, a proper subset of unimodular;
  * this is one-directional — the **converse** (depth-0 Cassini ⟹ `q = 1`) is *false* without a
    non-degeneracy hypothesis (`det s 0 = 0` gives `det s n = qⁿ·0 = 0`, constant for *every*
    `q`), so it is not a biconditional;
  * the reading "the e/ζ(2)/ζ(3) divergence ladder is the *degree of departure* from this `q = 1`
    floor (each rung an `n`-dependent-coefficient drift from the constant-coefficient shift)" is a
    **conjectural interpretation**, NOT formalized here — this file only proves `q = 1 ⟹ depth 0`.
-/

namespace E213.Lib.Math.Cauchy.CassiniDepthFloor

open E213.Lib.Math.CassiniUnimodular (det det_step det_closed qpow)
open E213.Lib.Math.Cauchy.NewtonGregory (polyDepthZ isConstZ newtonZ diffZ)
open E213.Lib.Math.Cauchy.DepthCharacterization (finite_depthZ_iff)
open E213.Lib.Math.Mobius213.Px.POrbitClosure (L)
open E213.Lib.Math.Mobius213.Px.CharPolySelf (L_rec)

/-- ★★★ **A conserved (`q = 1`) orbit's Cassini sits at depth 0.**  For any 2nd-order `Int`
    recurrence with shift determinant `q = 1` (`s(n+2) = p·s(n+1) − 1·s(n)`), the Cassini
    determinant `det s` is *constant* (`det_step` with `q = 1` gives `det s (n+1) = det s n`),
    hence `polyDepthZ 0 (det s)`: the `SL₂` orbit is the **divergence-ladder floor**.  (Sufficiency
    only — `q = 1 ⟹ depth 0`; the converse fails for degenerate `det s 0 = 0`.) -/
theorem cassini_conserved_depth0 (p : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 2) = p * s (n + 1) - 1 * s n) :
    polyDepthZ 0 (det s) := by
  show ∀ n, det s n = det s 0
  intro n
  induction n with
  | zero => rfl
  | succ k ih => rw [det_step p 1 s hrec k, Int.one_mul]; exact ih

/-- ★★ **The golden/Lucas Cassini is a depth-0 floor.**  The `L`-orbit (`L(n+2) = 3·L(n+1) −
    1·L(n)`, shift `[[2,1],[1,1]]`, `det = q = 1`) has a *constant* Cassini (`= d = 5`), hence
    `polyDepthZ 0 (det L)` — an instance of `cassini_conserved_depth0`. -/
theorem golden_cassini_depth0 : polyDepthZ 0 (det L) :=
  cassini_conserved_depth0 3 L (fun n => by rw [Int.one_mul]; exact L_rec n)

/-- ★★ **`q = 1` ⟹ depth 0 (the `SL₂` Cassini floor).**  Bundle of the *sufficiency*: every
    `q = 1` (det-of-shift `= 1`, `SL₂`) 2nd-order orbit has a constant Cassini at depth 0
    (`cassini_conserved_depth0`), and the golden/Lucas orbit is such a floor
    (`golden_cassini_depth0`, `det L = d = 5`).  One-directional — **not** a biconditional, and
    the `SL₂` (`q = 1`) floor is a proper subset of unimodular (`q = −1` period-2 alternates). -/
theorem sl2_cassini_floor :
    (∀ (p : Int) (s : Nat → Int), (∀ n, s (n + 2) = p * s (n + 1) - 1 * s n) →
        polyDepthZ 0 (det s))
    ∧ polyDepthZ 0 (det L) :=
  ⟨cassini_conserved_depth0, golden_cassini_depth0⟩

/-! ## §2 — the conserved unit is the residue: an SL₂ orbit never reaches its frozen fixed point

The **frozen fixed point** of a 2nd-order orbit is the *degenerate* window `det s n = 0` (where
`s(n)·s(n+2) = s(n+1)²`, the homogeneous relation a convergent ratio would satisfy *exactly*).
For an `SL₂` (`q=1`) orbit the Cassini determinant is the conserved constant `det s 0`; if that
is non-zero, the orbit **never** lands on the degenerate relation — the dynamic approaches but
never reaches the frozen.  So the **conserved Cassini unit is the residue**, for *every* such
orbit — generalising the φ-specific `FibCassiniNat.convergent_never_frozen`. -/

/-- ★★★ **A non-degenerate SL₂ orbit never reaches its frozen fixed point.**  For a `q=1` orbit
    with non-zero initial Cassini (`det s 0 ≠ 0`), the determinant stays that constant
    (`cassini_conserved_depth0`), so `det s n ≠ 0` at *every* layer: the orbit never satisfies the
    degenerate (frozen) relation `s(n)·s(n+2) = s(n+1)²`.  The conserved Cassini unit is exactly
    the residue between the dynamic orbit and its frozen fixed point — the general law behind
    `convergent_never_frozen` (the φ instance, where `det = 1`). -/
theorem conserved_never_degenerate (p : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 2) = p * s (n + 1) - 1 * s n) (h0 : det s 0 ≠ 0) (n : Nat) :
    det s n ≠ 0 := by
  have hconst : det s n = det s 0 := cassini_conserved_depth0 p s hrec n
  rw [hconst]; exact h0

/-- ★★ **The golden orbit never reaches its frozen fixed point.**  `det L n = d = 5 ≠ 0` at every
    layer (`conserved_never_degenerate` with `det L 0 = 5`): the Lucas/golden orbit never
    satisfies the degenerate relation — the φ/`d` residue, as an instance of the general law. -/
theorem golden_never_degenerate (n : Nat) : det L n ≠ 0 :=
  conserved_never_degenerate 3 L (fun m => by rw [Int.one_mul]; exact L_rec m)
    (by decide) n

/-! ## §3 — the Cassini is a depth-collapsing invariant (bridge to the orbit-dimension ladder)

`DepthCharacterization.finite_depthZ_iff` proves **finite divergence depth ⟺ polynomial**, and
the orbit-dimension ladder (`G183_above_the_polynomials`) places constant-coefficient (C-finite)
recurrences — exactly the `s(n+2) = p·s(n+1) − q·s(n)` orbits here — *above* the polynomials
(divergence depth `∞`, e.g. Fibonacci/Lucas grow like `φⁿ`).  Yet the **Cassini determinant** of
such an orbit lands on the *bottom* rung (depth 0, `cassini_conserved_depth0`): the quadratic
Cassini map collapses a depth-`∞` C-finite orbit to a depth-`0` polynomial. -/

/-- ★★★ **The Cassini of an SL₂ orbit is a degree-0 polynomial (the bottom rung).**  Via the
    depth characterization `finite_depthZ_iff`: since `det s` is depth-0 (`cassini_conserved_depth0`,
    `q=1`), it is a degree-`≤0` polynomial in the Newton basis — `∃ c, ∀ n, det s n = newtonZ c 0 n`.
    So the Cassini quadratic invariant maps the (generally above-polynomial, C-finite) orbit `s`
    onto the polynomial bottom rung of the divergence-depth ladder — a *depth-collapsing* invariant. -/
theorem cassini_is_polynomial (p : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 2) = p * s (n + 1) - 1 * s n) :
    ∃ c : Nat → Int, ∀ n, det s n = newtonZ c 0 n :=
  finite_depthZ_iff.mp (cassini_conserved_depth0 p s hrec)

/-! ## §4 — the orbit is C-finite: the Δ-orbit closes at dimension ≤ 2 (the middle rung)

Where §3 puts the *Cassini* on the polynomial bottom rung, the *orbit itself* sits on the
**C-finite** middle rung of the orbit-dimension ladder (`G183_above_the_polynomials`): a 2nd-order
constant-coefficient recurrence makes the difference-orbit `⟨s, Δs, Δ²s, …⟩` close at dimension
`≤ 2` — the **second difference is a constant-coefficient combination of `s` and `Δs`** (the
"Cayley–Hamilton for `Δ`").  This is finite-`Δ`-orbit-over-`ℚ` for order 2, the witness that the
orbit is C-finite (and, generically, divergence-depth `∞` — above the polynomials, even as its
Cassini collapses to depth 0). -/

/-- ★★★ **The Δ-orbit closes at dimension ≤ 2 (C-finite witness).**  For a 2nd-order
    constant-coefficient orbit `s(n+2) = p·s(n+1) − q·s(n)`, the second difference is a *constant*
    -coefficient combination of `s` and `Δs`: `Δ²s n = (p − q − 1)·s n + (p − 2)·Δs n`.  So the
    difference-orbit `⟨s, Δs, Δ²s, …⟩` is spanned by `{s, Δs}` over `ℚ` — the orbit is C-finite
    (orbit dimension `≤ 2`), the middle rung of the divergence-depth ladder. -/
theorem second_diff_closure (p q : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 2) = p * s (n + 1) - q * s n) (n : Nat) :
    diffZ (diffZ s) n = (p - q - 1) * s n + (p - 2) * diffZ s n := by
  show (s (n + 2) - s (n + 1)) - (s (n + 1) - s n)
       = (p - q - 1) * s n + (p - 2) * (s (n + 1) - s n)
  rw [hrec n]
  ring_intZ

/-- ★★★ **The orbit on the ladder: order-2 C-finite, Cassini drops it by one order.**  For a
    2nd-order constant-coefficient orbit, two complementary structures:

    1. **additive / middle rung** — the orbit is C-finite, `Δ²s = (p−q−1)·s + (p−2)·Δs`
       (`second_diff_closure`): the difference-orbit closes at dimension `≤ 2`;
    2. **multiplicative / order-drop** — its Cassini determinant is *geometric* (order-1 C-finite),
       `det s n = qⁿ · det s 0` (`det_closed`): the quadratic Cassini invariant **drops the order
       by one** — from the order-2 orbit to an order-1 geometric sequence (and, when `q = 1`, to
       the order-0 constant of the polynomial bottom rung, `cassini_is_polynomial`).

    So the Cassini map is a one-step descent of the orbit-dimension ladder: order-2 C-finite ↦
    order-1 geometric ↦ (at `q=1`) order-0 polynomial. -/
theorem cfinite_orbit_ladder_placement (p q : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 2) = p * s (n + 1) - q * s n) :
    (∀ n, diffZ (diffZ s) n = (p - q - 1) * s n + (p - 2) * diffZ s n)
    ∧ (∀ n, det s n = qpow q n * det s 0) :=
  ⟨second_diff_closure p q s hrec, det_closed p q s hrec⟩

/-! ## §5 — the orbit lies on a conic (genus 0), not (yet) an elliptic curve

Geometric reading of the conserved Cassini.  The consecutive triple `(s n, s(n+1), s(n+2))` of
an `SL₂` (`q=1`) order-2 orbit lies on a **fixed conic** `X·Z − Y² = c` (the Cassini/Pell quadric):
the "circle" the two-orbit traces.  The shift (the `P`-step / Möbius) is the conic's `SL₂`
automorphism — and that `SL₂(ℤ)` Möbius action is the **modular group** (`Real213.ModularElliptic`:
`PSL(2,ℤ) = ℤ/2 * ℤ/3`, elliptic generators of orders `4, 6` — the rotations).

Honest scope (against over-reading): a conic is **genus 0**, *not* an elliptic curve (genus 1).
The orbit at this depth (order 2, quadratic) is a conic; a genus-1 *elliptic curve* is the
*cubic* object that would appear **one depth up** (order 3 — the ζ(3)-Apéry level), where the
Apéry↔modular-form connection (Beukers) lives.  That higher-depth elliptic/modular step is a
**conjecture** for the 213 ladder, not proved here — what *is* proved is the genus-0 conic. -/

/-- ★★★ **The order-2 SL₂ orbit lies on a fixed conic.**  For `q=1`, every consecutive triple
    `(s n, s(n+1), s(n+2))` satisfies the *same* conic equation `X·Z − Y² = s 0·s 2 − s 1²` — the
    Cassini/Pell quadric (genus 0).  This is the orbit's "circle": the two-orbit traces a conic,
    conserved by the `SL₂` (Möbius / modular) shift.  (A restatement of `cassini_conserved_depth0`
    in conic-geometry form.) -/
theorem orbit_on_conic (p : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 2) = p * s (n + 1) - 1 * s n) (n : Nat) :
    s n * s (n + 2) - s (n + 1) * s (n + 1) = s 0 * s 2 - s 1 * s 1 :=
  cassini_conserved_depth0 p s hrec n

end E213.Lib.Math.Cauchy.CassiniDepthFloor
