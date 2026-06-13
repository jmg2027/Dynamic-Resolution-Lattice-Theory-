# Chapter 3 — The Readout Layer: the Cassini

With the tower fixed, we can say exactly what the orbit/disc machinery *is*: it is the
difference-Lens (rung three) applied to quadratic readings (rung two) of the iterated self-pointing.
This chapter develops that machinery on its own terms — it is genuine, original mathematics — and
then records the one place the development went wrong and was corrected, because the correction is
the method of the book in miniature.

## 3.1 The conserved determinant and its multiplier law

Let `s` be any order-2 constant-coefficient orbit, `s(n+2) = p·s(n+1) − q·s(n)` — the self-pointing
read as a recurrence. Its Cassini determinant `det s n = s(n)·s(n+2) − s(n+1)²`
(`CassiniUnimodular.det`) obeys a single, fully general law:

> **The Cassini multiplies by the shift's determinant each step.**
> `det s (n+1) = q · det s n`  —  `CassiniUnimodular.det_step`,
> hence `det s n = qⁿ · det s 0`  —  `CassiniUnimodular.det_closed`.

No unimodularity is assumed; the multiplier is the orbit's own `q`. This is the discrete
Abel/Wronskian identity, and it is the load-bearing original result of the whole cluster — it holds
of any order-2 orbit and depends on nothing imported. The two classical-looking regimes are its two
unimodular instances: `q = 1` (the golden orbit, determinant conserved) and `q = −1` (the period-2
oscillation, determinant alternating) are *one law at two multipliers*
(`CassiniUnimodular.cassini_law_one_at_two_multipliers`).

## 3.2 The conic and the floor

Read the conserved case geometrically. For `q = 1` the determinant is constant, so every
consecutive triple `(s(n), s(n+1), s(n+2))` lies on the **same fixed conic**

```
X·Z − Y² = s0·s2 − s1²    —    CassiniDepthFloor.orbit_on_conic.
```

This is the "circle" the two-orbit traces. Being a constant sequence, the determinant sits at
divergence depth `0` (`CassiniDepthFloor.cassini_conserved_depth0`): the conserved orbit is the
floor of the divergence ladder. And the residue is visible here directly: if the initial Cassini is
nonzero, the determinant never vanishes —

> **A non-degenerate `SL₂` orbit never reaches its frozen fixed point.**
> `det s 0 ≠ 0 ⟹ ∀ n, det s n ≠ 0`  —  `CassiniDepthFloor.conserved_never_degenerate`.

The orbit approaches the fixed point (the conic's special locus) and never lands on it; the
conserved unit `det s 0` is exactly the gap. This is the source-without-enclosure of the residue
essays, read at the orbit's determinant.

## 3.3 The Casoratian ladder, all of one height

The order-2 Cassini generalizes. For an order-3 orbit `s(n+3) = a·s(n+2) + b·s(n+1) + c·s(n)`, the
`3×3` Hankel/Casorati determinant obeys the *same* shape:

> `W₃(n+1) = c · W₃(n)`  —  `SecondCasoratian.second_casoratian`,

with `c` the constant coefficient (the order-3 companion determinant). The conserved case `c = 1`
gives a constant `W₃` (`SecondCasoratian.sl3_hankel_conserved`); the order-3 orbit is itself
"C-finite," its third difference closing with constant coefficients
(`SecondCasoratian.third_diff_closure`). This is a genuine *determinantal* ladder, one rung per
order.

## 3.4 The category-error, and its correction

Here the development first overreached, and the correction is worth stating plainly because it is
the discipline at work.

The order-2 orbit lies on a conic — genus `0`. The conic is *quadratic*. So the seductive
extrapolation: order-3 → a *cubic* invariant → genus `1` → an elliptic curve → modularity; "climbing
a depth raises the genus." Every word of that is a stereotype match, and it is **false**, not merely
unproven:

- A constant-coefficient linear recurrence's orbit is genus `0` at *every* order — it is a
  companion-matrix (toric) object. The genus does not climb.
- The `k×k` Hankel determinant is a *singular, reducible* determinantal variety, never a smooth
  plane curve. The degree of a many-variable form is not the genus of a curve.
- There is **no** conserved cubic form on order-3 orbit triples; the conserved order-3 object is the
  `3×3` Casoratian, not a single-window cubic.

The honest statement of "what changes going up a depth" is therefore not a genus, but a determinant
size:

> On the order-3 Tribonacci orbit, the order-2 Cassini is *not* conserved (it is `0` at `n=0` and
> `−1` at `n=1`), while the order-3 `3×3` Casoratian *is* conserved.
> `SecondCasoratian.conserved_invariant_grows_with_order`.

Climbing a depth grows the *size* of the conserved determinant — order `k` ↦ a `k×k` determinant
with multiplier `det(shift)` — and the geometry stays genus `0`. The honest ladder is determinantal,
not a genus ascent. (The Apéry/ζ(3) connection that the "modular elliptic" reading reached for is a
different category entirely — order-2 *holonomic*, a K3/weight-4 phenomenon — and its own Hankel
determinants carry large primes with no closed form. It is not on this ladder.)

This is the book's method in one episode: a structure looked like famous mathematics; descending into
it dissolved the resemblance and left a smaller, genuine, native object — here the determinantal
multiplier law `det(n+1) = q·det(n)`.

## 3.5 Where the Cassini sits

Every object in this chapter is built from products (rung two) and a difference (rung three). By
Chapter 2's accounting the Cassini is at least three Lens-steps above the residue. It is **readout-
layer mathematics** — genuine, original, `∅`-axiom, and *not* foundational. The determinant law is
the difference-Lens doing precisely the job §6.7 assigns it: iterated differencing, closing in `ℤ`.
The next two chapters trace the readout back down to the ground.
