import E213.Meta.Int213.PolyIntMTactic
import E213.Lib.Math.Cauchy.NewtonGregory

/-!
# Cauchy.SecondCasoratian — the order-3 Casorati determinant multiplies by `c` each step

The honest generalisation of `CassiniUnimodular.det_step` (order 2, the `2×2` Hankel/Cassini
determinant `s(n)·s(n+2) − s(n+1)²`, multiplier `q`) to **order 3**: the `3×3` Hankel determinant

  `W₃(n) = det [[s n, s(n+1), s(n+2)], [s(n+1), s(n+2), s(n+3)], [s(n+2), s(n+3), s(n+4)]]`

of a constant-coefficient order-3 recurrence `s(n+3) = a·s(n+2) + b·s(n+1) + c·s(n)` obeys the
**same multiplier law** — `W₃(n+1) = c · W₃(n)` — where `c` (the constant coefficient) is the
determinant of the order-3 companion shift `[[0,1,0],[0,0,1],[c,b,a]]`.

This is the **determinantal / arithmetic** ascent of the depth ladder: order-`k` ↦ the `k×k`
Casorati determinant, multiplier = `det(shift)`.  It is **all genus 0** (a linear-recurrence orbit
is a toric / companion-matrix object at every order) — *not* a "genus climbs / order-3 ↦ elliptic
curve" ascent (a category error: a `k×k` Hankel determinant is a singular determinantal variety,
never a smooth plane curve; the degree of a many-variable form is not the genus of a curve).  So
`second_casoratian` is the real order-3 rung, and the conservation case (`c = 1`, the shift in
`SL₃`) is the order-3 analogue of the `SL₂` conic-conservation floor.

**Honest scope (two adversarial findings, both numerically verified, recorded to prevent
over-reach):**

  * **No conserved *cubic form* exists** on order-3 orbit triples `(s n, s(n+1), s(n+2))`.  The
    space of cubic forms `F(x,y,z)` constant along the orbit has nullity 0 beyond the trivial
    constant (checked numerically) — so there is **no** genus-1 "elliptic curve" the order-3 orbit
    lies on.  The conserved order-3 object is the `3×3` Casoratian `hankel3` (a 5-window
    determinant, multiplier `c`), **not** a single-window cubic.  This is *why* the "order-3 ↦
    elliptic / genus 1" reading is a category error, not a conjecture.
  * **The Apéry-number Hankel determinants have no ∅-axiom closed form** (`48, 1896, 321048,
    94396224, …` carry large primes `79, 641, …`).  Beukers' Apéry↔modular-form connection is
    genuine transcendental number theory (a K3-surface / weight-4 / Picard–Fuchs phenomenon),
    **out of ∅-axiom reach** — and the Apéry recurrence is order-2 *holonomic*, not order-3
    const-coeff, so it is not even on this ladder.  No modularity is claimed here.
-/

namespace E213.Lib.Math.Cauchy.SecondCasoratian

open E213.Lib.Math.Cauchy.NewtonGregory (diffZ)

/-- The `3×3` Hankel (Casorati) determinant of a sequence, expanded along the first row. -/
def hankel3 (s : Nat → Int) (n : Nat) : Int :=
  s n * (s (n + 2) * s (n + 4) - s (n + 3) * s (n + 3))
  - s (n + 1) * (s (n + 1) * s (n + 4) - s (n + 3) * s (n + 2))
  + s (n + 2) * (s (n + 1) * s (n + 3) - s (n + 2) * s (n + 2))

/-- ★★★ **The order-3 Casorati determinant multiplies by `c` each step.**  For any
    constant-coefficient order-3 recurrence `s(n+3) = a·s(n+2) + b·s(n+1) + c·s(n)`, the `3×3`
    Hankel determinant obeys `W₃(n+1) = c · W₃(n)` — the order-3 Abel/Casorati identity, with `c`
    (the constant coefficient) = `det` of the companion shift.  The honest order-3 rung of the
    *determinantal* ladder (all genus 0); the order-2 `det_step` (multiplier `q`) is the `k=2`
    case.  (Proved by one `ring_intZ` after expanding `s(n+3), s(n+4), s(n+5)` via the recurrence.) -/
theorem second_casoratian (a b c : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 3) = a * s (n + 2) + b * s (n + 1) + c * s n) (n : Nat) :
    hankel3 s (n + 1) = c * hankel3 s n := by
  have h3 : s (n + 3) = a * s (n + 2) + b * s (n + 1) + c * s n := hrec n
  have h4 : s (n + 4) = a * s (n + 3) + b * s (n + 2) + c * s (n + 1) := hrec (n + 1)
  have h5 : s (n + 5) = a * s (n + 4) + b * s (n + 3) + c * s (n + 2) := hrec (n + 2)
  show s (n + 1) * (s (n + 3) * s (n + 5) - s (n + 4) * s (n + 4))
        - s (n + 2) * (s (n + 2) * s (n + 5) - s (n + 4) * s (n + 3))
        + s (n + 3) * (s (n + 2) * s (n + 4) - s (n + 3) * s (n + 3))
      = c * (s n * (s (n + 2) * s (n + 4) - s (n + 3) * s (n + 3))
        - s (n + 1) * (s (n + 1) * s (n + 4) - s (n + 3) * s (n + 2))
        + s (n + 2) * (s (n + 1) * s (n + 3) - s (n + 2) * s (n + 2)))
  rw [h5, h4, h3]
  ring_intZ

/-- ★★ **`SL₃` (`c=1`) order-3 floor: the Casorati determinant is conserved.**  When the
    companion shift is in `SL₃` (`c = 1`), `W₃` is constant — `W₃(n) = W₃(0)` — the order-3
    analogue of the `q=1` conic-conservation floor (`cassini_conserved_depth0`), still genus 0. -/
theorem sl3_hankel_conserved (a b : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 3) = a * s (n + 2) + b * s (n + 1) + 1 * s n) (n : Nat) :
    hankel3 s n = hankel3 s 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [second_casoratian a b 1 s hrec k, Int.one_mul]; exact ih

/-- ★★★ **Order-3 C-finite closure: `Δ³s` is a constant-coefficient combination of `s, Δs, Δ²s`.**
    For `s(n+3) = a·s(n+2) + b·s(n+1) + c·s(n)`, the third difference closes with *constant*
    coefficients: `Δ³s n = (a+b+c−1)·s n + (2a+b−3)·Δs n + (a−3)·Δ²s n` (the Cayley–Hamilton-for-`Δ`
    of the order-3 companion).  So the difference-orbit `⟨s, Δs, Δ²s, Δ³s, …⟩` closes at dimension
    `≤ 3` — the order-3 orbit is C-finite, the order-3 rung of the orbit-dimension ladder (one up
    from `second_diff_closure`).  Still genus 0 — a linear-algebraic (companion) object. -/
theorem third_diff_closure (a b c : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 3) = a * s (n + 2) + b * s (n + 1) + c * s n) (n : Nat) :
    diffZ (diffZ (diffZ s)) n
      = (a + b + c - 1) * s n + (2 * a + b - 3) * diffZ s n + (a - 3) * diffZ (diffZ s) n := by
  show (s (n + 3) - s (n + 2) - (s (n + 2) - s (n + 1)))
        - ((s (n + 2) - s (n + 1)) - (s (n + 1) - s n))
      = (a + b + c - 1) * s n + (2 * a + b - 3) * (s (n + 1) - s n)
        + (a - 3) * ((s (n + 2) - s (n + 1)) - (s (n + 1) - s n))
  rw [hrec n]
  ring_intZ

end E213.Lib.Math.Cauchy.SecondCasoratian
