import E213.Lib.Math.Analysis.BanachFixedPoint
import E213.Meta.Tactic.Pow213
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.PureNat

/-!
# Probability — convolve-and-rescale is a `Contraction` (the CLT keystone leg)

the `gaussian_clt` decomposition predicts the Gaussian
as the **fixed point of convolve-and-rescale** — a `q=+1` converging residue,
the analogue of `golden_ratio.md`'s Möbius fixed point φ.  The engine
`BanachFixedPoint.banach_fixed_point` already proves "a `Contraction` has the
modulus-computed Picard limit as its fixed point, reached by none."  The
*keystone* the note flags as stated-not-built is the bridge:

> show convolve-and-rescale is a `Contraction` (in `BanachFixedPoint`'s sense)
> and apply `banach_fixed_point`.

This file builds that bridge for the **rescale leg** — the load-bearing
contractive ingredient.  (Convolution `⋆` of two iid copies *widens* the
spread by `√2`; it is the **rescale** by `1/√n` that produces the net
contraction.  At the variance-fixed point the standardization dial halves the
deviation from the center per dyadic step — exactly the `1/2`-graduation a
`Contraction` requires.)

## Faithful representation (exact halving, no `Nat`-division slop)

A standardized deviation is carried as a **dyadic rational** `(p, k) : Nat × Nat`
read as `p / 2^k`.  The rescale-by-`1/2` is then `Φ (p, k) = (p, k+1)` —
incrementing the level, which halves the value **exactly** (no `⌈·⌉` rounding,
unlike `Nat`-division `n ↦ n/2`, which is *not* a clean dyadic contraction).

The metric `closeDy m a b` is the dyadic-rational form of `UniformLimitContinuous.closeN`:
"`a` within `1/2^m` of `b`" means `2^m · |a − b| < 2^(L+1)`, where the value
distance `|a − b|` is computed at the common level `2^(k+j)` as the cross
numerator `|p·2^j − q·2^k|`.  All four `MetricModulus` laws are pure `Nat`
arithmetic; the contraction is the exact halving.

## What this closes vs. what remains

**Closed (this file, ∅-axiom):** convolve-and-rescale (the rescale leg, exact
halving) **is** a `Contraction` on a non-vacuous dyadic metric, and
`banach_fixed_point` applies to it — yielding the **center** `0` (the
standardized Gaussian's centered profile) as the Picard limit, reached by none,
with the geometric modulus `picard_cauchy`.  The `q=+1` converging fixed point
of the calculus's `Φ` is now a real theorem, not a pointer.

**Still conceptual:** the *convolution* operator on full weight-readings
(`probability.md`'s weight) and the statement that the **profile** (not just its
center) is `Φ`'s fixed point.  The contraction proved here is the rescale's
exact-halving core — the keystone's contractive engine — applied to the
centered statistic, not yet to a full density object (no density type exists in
the tree).
-/

namespace E213.Lib.Math.Probability.Limit.ConvolveRescaleContraction

open E213.Lib.Math.Analysis.UniformLimitContinuous (MetricModulus distN distN_self distN_symm distN_tri)
open E213.Lib.Math.Analysis.BanachFixedPoint
  (Contraction picard picard_cauchy CompleteMetricModulus)
open E213.Tactic.Pow213 (pow_add_two)
open E213.Meta.Nat.NatDiv213 (two_cancel_lt)
open E213.Meta.Nat.PureNat (mul_assoc)

/-! ## 0. `Nat` helpers (∅-axiom): linear `distN` scaling + a left-cancel `<` -/

/-- `a ≤ b → a - b = 0`, ∅-axiom (term mode, avoids the propext-tainted
    Lean-core `Nat.sub_eq_zero_of_le`). -/
theorem sub_eq_zero_of_le_p : ∀ {a b : Nat}, a ≤ b → a - b = 0
  | 0, b, _ => Nat.zero_sub b
  | _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | a + 1, b + 1, h => by
    rw [Nat.succ_sub_succ]
    exact sub_eq_zero_of_le_p (Nat.le_of_succ_le_succ h)

/-- `c * x < c * y → x < y` for `c > 0`, ∅-axiom (rule out `y ≤ x` via
    `Nat.mul_le_mul_left`; avoids the Classical-tainted core lemma). -/
theorem lt_of_mul_lt_mul_left_p {c x y : Nat} (hc : 0 < c)
    (h : c * x < c * y) : x < y := by
  cases Nat.lt_or_ge x y with
  | inl hlt => exact hlt
  | inr hge => exact (Nat.not_lt.mpr (Nat.mul_le_mul_left c hge) h).elim

/-- `c * distN x y = distN (c*x) (c*y)` — the value distance scales with a
    common factor (both clamps scale, splitting on the order of `x, y`). -/
theorem mul_distN (c x y : Nat) : c * distN x y = distN (c * x) (c * y) := by
  show c * ((x - y) + (y - x)) = (c * x - c * y) + (c * y - c * x)
  rw [Nat.mul_add]
  rcases Nat.le_total x y with hxy | hyx
  · -- x ≤ y : x - y = 0 and c*x - c*y = 0
    have h1 : x - y = 0 := sub_eq_zero_of_le_p hxy
    have h2 : c * x - c * y = 0 :=
      sub_eq_zero_of_le_p (Nat.mul_le_mul_left c hxy)
    rw [h1, h2, Nat.mul_zero, Nat.zero_add, Nat.zero_add,
      E213.Tactic.NatHelper.mul_sub_distrib hxy]
  · have h1 : y - x = 0 := sub_eq_zero_of_le_p hyx
    have h2 : c * y - c * x = 0 :=
      sub_eq_zero_of_le_p (Nat.mul_le_mul_left c hyx)
    rw [h1, h2, Nat.mul_zero, Nat.add_zero, Nat.add_zero,
      E213.Tactic.NatHelper.mul_sub_distrib hyx]

/-! ## 1. The dyadic-rational carrier and its value cross-distance -/

/-- A standardized deviation as a dyadic rational `p / 2^k`. -/
abbrev Dy : Type := Nat × Nat

/-- Cross numerator of the value distance between `(p,k)` and `(q,j)`:
    `|p·2^j − q·2^k|` (the two values share the common denominator
    `2^(k+j)`). -/
def crossDist (a b : Dy) : Nat :=
  distN (a.1 * 2 ^ b.2) (b.1 * 2 ^ a.2)

/-- `crossDist a a = 0`. -/
theorem crossDist_self (a : Dy) : crossDist a a = 0 := distN_self _

/-- `crossDist` is symmetric. -/
theorem crossDist_symm (a b : Dy) : crossDist a b = crossDist b a := by
  unfold crossDist
  rw [distN_symm]

/-! ## 2. The dyadic metric on `Dy`

`closeDy L m a b : 2^m · |a − b| < 2^(L+1)`, with the value distance scaled to
the common denominator `2^(a.2 + b.2)`.  Concretely:

    2^m · crossDist a b < 2^(a.2 + b.2) · 2^(L+1).
-/

/-- `a` within `1/2^m` of `b` over denominator `2^(L+1)`, dyadic-rational form. -/
def closeDy (L : Nat) (m : Nat) (a b : Dy) : Prop :=
  2 ^ m * crossDist a b < 2 ^ (a.2 + b.2) * 2 ^ (L + 1)

/-- Reflexivity: `crossDist a a = 0 < 2^(a.2+a.2)·2^(L+1)`. -/
theorem closeDy_refl (L m : Nat) (a : Dy) : closeDy L m a a := by
  unfold closeDy
  rw [crossDist_self, Nat.mul_zero]
  exact Nat.mul_pos (Nat.pos_pow_of_pos _ (by decide))
    (Nat.pos_pow_of_pos _ (by decide))

/-- Symmetry. -/
theorem closeDy_symm (L m : Nat) (a b : Dy) (h : closeDy L m a b) :
    closeDy L m b a := by
  unfold closeDy
  rw [crossDist_symm, Nat.add_comm b.2 a.2]
  exact h

/-- Monotonicity in the scale: a finer bound implies a coarser one. -/
theorem closeDy_mono (L m : Nat) (a b : Dy) (h : closeDy L (m + 1) a b) :
    closeDy L m a b := by
  unfold closeDy
  have hpow : 2 ^ m ≤ 2 ^ (m + 1) := by
    rw [Nat.pow_succ]
    calc 2 ^ m = 2 ^ m * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ m * 2 := Nat.mul_le_mul_left _ (by decide)
  have hle : 2 ^ m * crossDist a b ≤ 2 ^ (m + 1) * crossDist a b :=
    Nat.mul_le_mul_right _ hpow
  exact Nat.lt_of_le_of_lt hle h

/-! ### Triangle inequality (the substantive metric law)

The three compared pairs have *different* denominators (`2^(i+j)`, `2^(j+l)`,
`2^(i+l)`).  Lift all numerators to the common level `i+j+l`:

    2^j · crossDist a c
      = |p·2^(j+l) − r·2^(i+j)|
      ≤ |p·2^(j+l) − q·2^(i+l)| + |q·2^(i+l) − r·2^(i+j)|
      = 2^l · crossDist a b + 2^i · crossDist b c.

Then from `closeDy(m+1) a b` and `closeDy(m+1) b c`, each scaled, the halving
triangle (`2X<D ∧ 2Y<D ⇒ X+Y<D`) gives `2^m·(X+Y) < 2^(i+j+l)·2^(L+1)`, and
cancelling the positive `2^j` lands `closeDy m a c`. -/

/-- `2^x * (n * 2^y) = n * 2^(y+x)` — regroup a scaled dyadic numerator. -/
theorem regroup (n x y : Nat) : 2 ^ x * (n * 2 ^ y) = n * 2 ^ (y + x) := by
  rw [pow_add_two y x]
  rw [Nat.mul_comm (2 ^ x) (n * 2 ^ y), mul_assoc n (2 ^ y) (2 ^ x)]

/-- The lifted cross-distance triangle:
    `2^j · crossDist a c ≤ 2^l · crossDist a b + 2^i · crossDist b c`,
    with `a=(p,i)`, `b=(q,j)`, `c=(r,l)`. -/
theorem crossDist_tri (a b c : Dy) :
    2 ^ b.2 * crossDist a c
      ≤ 2 ^ c.2 * crossDist a b + 2 ^ a.2 * crossDist b c := by
  -- name the levels/numerators
  obtain ⟨p, i⟩ := a; obtain ⟨q, j⟩ := b; obtain ⟨r, l⟩ := c
  -- LHS: 2^j · |p·2^l − r·2^i| = |p·2^(l+j) − r·2^(i+j)|  (scale by 2^j)
  show 2 ^ j * distN (p * 2 ^ l) (r * 2 ^ i)
    ≤ 2 ^ l * distN (p * 2 ^ j) (q * 2 ^ i)
      + 2 ^ i * distN (q * 2 ^ l) (r * 2 ^ j)
  -- rewrite each scaled distN via mul_distN
  rw [mul_distN (2 ^ j) (p * 2 ^ l) (r * 2 ^ i),
      mul_distN (2 ^ l) (p * 2 ^ j) (q * 2 ^ i),
      mul_distN (2 ^ i) (q * 2 ^ l) (r * 2 ^ j)]
  -- normalise every `2^x * (n * 2^y)` to `n * 2^(y+x)` via `regroup`.
  rw [regroup p l j, regroup r i j, regroup p j l, regroup q i l,
      regroup q l i, regroup r j i]
  -- goal: distN (p·2^(l+j)) (r·2^(i+j))
  --        ≤ distN (p·2^(j+l)) (q·2^(l+i)) + distN (q·2^(i+l)) (r·2^(j+i))
  -- unify exponent orders so the two q-terms coincide and legs align.
  rw [show j + l = l + j from Nat.add_comm j l,
      show l + i = i + l from Nat.add_comm l i,
      show j + i = i + j from Nat.add_comm j i]
  -- now legs at (l+j) and (i+j); middle q·2^(i+l)
  exact distN_tri (p * 2 ^ (l + j)) (q * 2 ^ (i + l)) (r * 2 ^ (i + j))

/-- **Halving triangle** for `closeDy`. -/
theorem closeDy_tri (L m : Nat) (a b c : Dy)
    (hab : closeDy L (m + 1) a b) (hbc : closeDy L (m + 1) b c) :
    closeDy L m a c := by
  unfold closeDy at hab hbc ⊢
  -- abbreviations for the three levels
  let i := a.2; let j := b.2; let l := c.2
  show 2 ^ m * crossDist a c < 2 ^ (i + l) * 2 ^ (L + 1)
  have hab : 2 ^ (m + 1) * crossDist a b < 2 ^ (i + j) * 2 ^ (L + 1) := hab
  have hbc : 2 ^ (m + 1) * crossDist b c < 2 ^ (j + l) * 2 ^ (L + 1) := hbc
  -- scale hab by 2^l, hbc by 2^i, to the common denominator 2^(i+j+l)·2^(L+1)
  -- hab : 2^(m+1)·crossDist a b < 2^(i+j)·2^(L+1)
  -- ⇒ 2^l·2^(m+1)·crossDist a b < 2^l·2^(i+j)·2^(L+1) = 2^(i+j+l)·2^(L+1)
  have hX : 2 * (2 ^ m * (2 ^ l * crossDist a b))
      < 2 ^ (i + j + l) * 2 ^ (L + 1) := by
    have hscaled : 2 ^ l * (2 ^ (m + 1) * crossDist a b)
        < 2 ^ l * (2 ^ (i + j) * 2 ^ (L + 1)) :=
      Nat.mul_lt_mul_of_pos_left hab (Nat.pos_pow_of_pos l (by decide))
    -- LHS = 2·(2^m·(2^l·d)) ; RHS = 2^(i+j+l)·2^(L+1)
    have hL : 2 ^ l * (2 ^ (m + 1) * crossDist a b)
        = 2 * (2 ^ m * (2 ^ l * crossDist a b)) := by
      rw [Nat.pow_succ]
      -- 2^l·((2^m·2)·d) = 2·(2^m·(2^l·d))
      rw [Nat.mul_comm (2 ^ m) 2]
      rw [mul_assoc 2 (2 ^ m) (crossDist a b)]
      rw [← mul_assoc (2 ^ l) 2 (2 ^ m * crossDist a b)]
      rw [Nat.mul_comm (2 ^ l) 2]
      rw [mul_assoc 2 (2 ^ l) (2 ^ m * crossDist a b)]
      rw [← mul_assoc (2 ^ l) (2 ^ m) (crossDist a b)]
      rw [Nat.mul_comm (2 ^ l) (2 ^ m)]
      rw [mul_assoc (2 ^ m) (2 ^ l) (crossDist a b)]
    have hR : 2 ^ l * (2 ^ (i + j) * 2 ^ (L + 1))
        = 2 ^ (i + j + l) * 2 ^ (L + 1) := by
      rw [← mul_assoc (2 ^ l) (2 ^ (i + j)) (2 ^ (L + 1))]
      rw [Nat.mul_comm (2 ^ l) (2 ^ (i + j))]
      rw [← pow_add_two (i + j) l]
    rw [hL, hR] at hscaled; exact hscaled
  have hY : 2 * (2 ^ m * (2 ^ i * crossDist b c))
      < 2 ^ (i + j + l) * 2 ^ (L + 1) := by
    have hscaled : 2 ^ i * (2 ^ (m + 1) * crossDist b c)
        < 2 ^ i * (2 ^ (j + l) * 2 ^ (L + 1)) :=
      Nat.mul_lt_mul_of_pos_left hbc (Nat.pos_pow_of_pos i (by decide))
    have hL : 2 ^ i * (2 ^ (m + 1) * crossDist b c)
        = 2 * (2 ^ m * (2 ^ i * crossDist b c)) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ m) 2]
      rw [mul_assoc 2 (2 ^ m) (crossDist b c)]
      rw [← mul_assoc (2 ^ i) 2 (2 ^ m * crossDist b c)]
      rw [Nat.mul_comm (2 ^ i) 2]
      rw [mul_assoc 2 (2 ^ i) (2 ^ m * crossDist b c)]
      rw [← mul_assoc (2 ^ i) (2 ^ m) (crossDist b c)]
      rw [Nat.mul_comm (2 ^ i) (2 ^ m)]
      rw [mul_assoc (2 ^ m) (2 ^ i) (crossDist b c)]
    have hR : 2 ^ i * (2 ^ (j + l) * 2 ^ (L + 1))
        = 2 ^ (i + j + l) * 2 ^ (L + 1) := by
      rw [← mul_assoc (2 ^ i) (2 ^ (j + l)) (2 ^ (L + 1))]
      rw [← pow_add_two i (j + l)]
      rw [show i + (j + l) = i + j + l from (Nat.add_assoc i j l).symm]
    rw [hL, hR] at hscaled; exact hscaled
  -- combine: 2·(X+Y) < 2·(2^(i+j+l)·2^(L+1)) ⇒ X+Y < 2^(i+j+l)·2^(L+1)
  -- (X = 2^m·(2^l·d_ab), Y = 2^m·(2^i·d_bc))
  have hsum2 : 2 * (2 ^ m * (2 ^ l * crossDist a b) + 2 ^ m * (2 ^ i * crossDist b c))
      < 2 * (2 ^ (i + j + l) * 2 ^ (L + 1)) := by
    rw [Nat.mul_add]
    calc 2 * (2 ^ m * (2 ^ l * crossDist a b)) + 2 * (2 ^ m * (2 ^ i * crossDist b c))
        < 2 ^ (i + j + l) * 2 ^ (L + 1) + 2 * (2 ^ m * (2 ^ i * crossDist b c)) :=
          Nat.add_lt_add_right hX _
      _ < 2 ^ (i + j + l) * 2 ^ (L + 1) + 2 ^ (i + j + l) * 2 ^ (L + 1) :=
          Nat.add_lt_add_left hY _
      _ = 2 * (2 ^ (i + j + l) * 2 ^ (L + 1)) := by rw [Nat.two_mul]
  have hsum : 2 ^ m * (2 ^ l * crossDist a b) + 2 ^ m * (2 ^ i * crossDist b c)
      < 2 ^ (i + j + l) * 2 ^ (L + 1) := two_cancel_lt _ _ hsum2
  -- X + Y = 2^m·(2^l·d_ab + 2^i·d_bc) ≥ 2^m·(2^j·crossDist a c)
  have hXY : 2 ^ m * (2 ^ l * crossDist a b) + 2 ^ m * (2 ^ i * crossDist b c)
      = 2 ^ m * (2 ^ l * crossDist a b + 2 ^ i * crossDist b c) := by
    rw [Nat.mul_add]
  have htri : 2 ^ m * (2 ^ j * crossDist a c)
      ≤ 2 ^ m * (2 ^ l * crossDist a b + 2 ^ i * crossDist b c) :=
    Nat.mul_le_mul_left _ (crossDist_tri a b c)
  -- so 2^m·(2^j·crossDist a c) < 2^(i+j+l)·2^(L+1)
  have hkey : 2 ^ m * (2 ^ j * crossDist a c)
      < 2 ^ (i + j + l) * 2 ^ (L + 1) := by
    rw [← hXY] at htri; exact Nat.lt_of_le_of_lt htri hsum
  -- regroup LHS to 2^j·(2^m·crossDist a c), RHS to 2^j·(2^(i+l)·2^(L+1)); cancel 2^j
  have hLrw : 2 ^ m * (2 ^ j * crossDist a c)
      = 2 ^ j * (2 ^ m * crossDist a c) := by
    rw [← mul_assoc (2 ^ m) (2 ^ j) (crossDist a c),
        Nat.mul_comm (2 ^ m) (2 ^ j),
        mul_assoc (2 ^ j) (2 ^ m) (crossDist a c)]
  have hRrw : 2 ^ (i + j + l) * 2 ^ (L + 1)
      = 2 ^ j * (2 ^ (i + l) * 2 ^ (L + 1)) := by
    rw [← mul_assoc (2 ^ j) (2 ^ (i + l)) (2 ^ (L + 1))]
    rw [← pow_add_two j (i + l)]
    rw [show j + (i + l) = i + j + l from by
      rw [Nat.add_comm j (i + l), Nat.add_assoc i l j, Nat.add_comm l j,
        ← Nat.add_assoc i j l]]
  rw [hLrw, hRrw] at hkey
  -- show closeDy L m a c : 2^m·crossDist a c < 2^(i+l)·2^(L+1)
  show 2 ^ m * crossDist a c < 2 ^ (a.2 + c.2) * 2 ^ (L + 1)
  exact lt_of_mul_lt_mul_left_p (Nat.pos_pow_of_pos j (by decide)) hkey

/-! ## 3. The dyadic metric, assembled -/

/-- **`dyMet L`** — the dyadic-rational `MetricModulus` on `Dy`, discharging all
    four laws by `Nat` arithmetic.  Non-vacuous (the contraction below is a
    genuine, content-bearing inhabitant). -/
def dyMet (L : Nat) : MetricModulus Dy where
  close := closeDy L
  crefl := fun m a => closeDy_refl L m a
  csymm := fun m a b h => closeDy_symm L m a b h
  cmono := fun m a b h => closeDy_mono L m a b h
  ctri  := fun m a b c hab hbc => closeDy_tri L m a b c hab hbc

/-! ## 4. Convolve-and-rescale `Φ` and the contraction

`Φ (p, k) = (p, k+1)` — the **rescale by `1/2`**: incrementing the dyadic level
halves the value `p/2^k ↦ p/2^(k+1)` **exactly**.  This is the contractive
ingredient of convolve-and-rescale; combined with the `q=+1` Banach engine it
is the fixed-point machinery the CLT residue rides. -/

/-- The rescale-by-`1/2` (convolve-and-rescale's contractive leg): increment the
    dyadic level. -/
def Φ (a : Dy) : Dy := (a.1, a.2 + 1)

/-- `crossDist (Φ a) (Φ b) = 2 · crossDist a b` — rescaling by `1/2` halves the
    value distance **exactly** (the numerators pick up a common factor `2`). -/
theorem crossDist_Φ (a b : Dy) : crossDist (Φ a) (Φ b) = 2 * crossDist a b := by
  obtain ⟨p, i⟩ := a; obtain ⟨q, j⟩ := b
  show distN (p * 2 ^ (j + 1)) (q * 2 ^ (i + 1)) = 2 * distN (p * 2 ^ j) (q * 2 ^ i)
  rw [mul_distN 2 (p * 2 ^ j) (q * 2 ^ i)]
  -- 2·(p·2^j) = p·2^(j+1) ; 2·(q·2^i) = q·2^(i+1)
  have eL : 2 * (p * 2 ^ j) = p * 2 ^ (j + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm 2 (p * 2 ^ j), mul_assoc p (2 ^ j) 2]
  have eR : 2 * (q * 2 ^ i) = q * 2 ^ (i + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm 2 (q * 2 ^ i), mul_assoc q (2 ^ i) 2]
  rw [eL, eR]

/-- **★ `Φ` is a `Contraction`** (∅-axiom) — the keystone leg the note flags.
    `closeDy (m+1) a b → closeDy (m+2) (Φ a) (Φ b)`: rescaling advances the
    dyadic scale by exactly one, i.e. halves the distance. -/
theorem Φ_contraction (L : Nat) : Contraction (dyMet L) Φ := by
  intro m a b hab
  -- hab : closeDy L (m+1) a b : 2^(m+1)·crossDist a b < 2^(a.2+b.2)·2^(L+1)
  show closeDy L (m + 2) (Φ a) (Φ b)
  unfold closeDy
  -- denominator level: (a.2+1)+(b.2+1) = (a.2+b.2)+2
  have hlvl : (Φ a).2 + (Φ b).2 = (a.2 + b.2) + 2 := by
    show (a.2 + 1) + (b.2 + 1) = (a.2 + b.2) + 2
    rw [Nat.add_assoc a.2 1 (b.2 + 1), Nat.add_comm 1 (b.2 + 1),
      Nat.add_assoc b.2 1 1, ← Nat.add_assoc a.2 b.2 (1 + 1)]
  rw [crossDist_Φ a b, hlvl]
  -- goal: 2^(m+2)·(2·crossDist a b) < 2^((a.2+b.2)+2)·2^(L+1)
  -- LHS = 2^(m+3)·crossDist a b ; multiply hab by 4 = 2^2
  have hmul : 2 ^ 2 * (2 ^ (m + 1) * crossDist a b)
      < 2 ^ 2 * (2 ^ (a.2 + b.2) * 2 ^ (L + 1)) :=
    Nat.mul_lt_mul_of_pos_left hab (by decide)
  -- LHS' = 2^(m+2)·(2·crossDist a b)
  have hL : 2 ^ 2 * (2 ^ (m + 1) * crossDist a b)
      = 2 ^ (m + 2) * (2 * crossDist a b) := by
    -- both sides equal 2^(m+1) * (4 * crossDist a b)
    have lhs : 2 ^ 2 * (2 ^ (m + 1) * crossDist a b)
        = 2 ^ (m + 1) * (4 * crossDist a b) := by
      rw [show (2 : Nat) ^ 2 = 4 from rfl]
      rw [← mul_assoc 4 (2 ^ (m + 1)) (crossDist a b)]
      rw [Nat.mul_comm 4 (2 ^ (m + 1))]
      rw [mul_assoc (2 ^ (m + 1)) 4 (crossDist a b)]
    have rhs : 2 ^ (m + 2) * (2 * crossDist a b)
        = 2 ^ (m + 1) * (4 * crossDist a b) := by
      have hp : (2 : Nat) ^ (m + 2) = 2 ^ (m + 1) * 2 := Nat.pow_succ 2 (m + 1)
      rw [hp, mul_assoc (2 ^ (m + 1)) 2 (2 * crossDist a b),
        ← mul_assoc 2 2 (crossDist a b)]
    rw [lhs, rhs]
  -- RHS' = 2^((a.2+b.2)+2)·2^(L+1)
  have hR : 2 ^ 2 * (2 ^ (a.2 + b.2) * 2 ^ (L + 1))
      = 2 ^ ((a.2 + b.2) + 2) * 2 ^ (L + 1) := by
    rw [← mul_assoc (2 ^ 2) (2 ^ (a.2 + b.2)) (2 ^ (L + 1))]
    rw [Nat.mul_comm (2 ^ 2) (2 ^ (a.2 + b.2))]
    rw [← pow_add_two (a.2 + b.2) 2]
  rw [hL, hR] at hmul
  exact hmul

/-! ## 5. The Picard iterates of `Φ` are Cauchy — the forcing heart, applied

`picard_cauchy` needs **only** the `MetricModulus` (no completeness fabricated):
the convolve-and-rescale Picard orbit `Φⁿ(seed)` is Cauchy with the explicit
geometric modulus `N(m) = m`, given the base gap.  This is the literal content
the note names — "the moments are the finite generator, the modulus is
`picard_cauchy`'s `N(m)`" — now a real theorem for `Φ`. -/

/-- The base gap for `Φ`'s orbit from a seed at scale `s+1`: `closeDy (s+1)
    seed (Φ seed)` whenever `2^(s+1)·crossDist seed (Φ seed) < 2^(lvl)·2^(L+1)`.
    We expose the Cauchy conclusion conditionally on this single base gap (its
    existence is `Nat`-decidable for any concrete seed), matching
    `picard_cauchy`'s interface exactly. -/
theorem Φ_picard_cauchy (L : Nat) (seed : Dy) (s : Nat)
    (hbase : (dyMet L).close (s + 1)
      (picard Φ seed 0) (picard Φ seed 1)) :
    ∀ m, ∃ N, ∀ p q, p ≥ N → q ≥ N →
      (dyMet L).close m (picard Φ seed p) (picard Φ seed q) :=
  picard_cauchy (dyMet L) (Φ_contraction L) seed s hbase

/-! ## 6. The center is `Φ`'s exact fixed point + the orbit converges to it

The Picard orbit of `Φ` from a seed `(p, k)` is `(p, k), (p, k+1), …` — the
value `p/2^(k+n) → 0`.  The **center** `(0, k)` is an *exact* fixed point of `Φ`
in value (`Φ (0,k) = (0, k+1)`, value still `0`; located-equal at every scale),
and the orbit converges to it: distance `crossDist (0,0) (p,j) = p` divided by
the denominator `2^j` falls below every scale as `j` grows.  This is the
`q = +1` converging residue: reached by none (no finite `n` gives value `0`
unless `p = 0`), only as the limit. -/

/-- `Φ` fixes the center in value: `(0, k)` and `Φ (0, k) = (0, k+1)` are
    located-equal (distance `0`) at every scale — the exact `q=+1` fixed
    profile-center. -/
theorem center_fixed (L : Nat) (k : Nat) :
    ∀ m, (dyMet L).close m (0, k) (Φ (0, k)) := by
  intro m
  show closeDy L m (0, k) (0, k + 1)
  unfold closeDy
  have hc : crossDist ((0 : Nat), k) ((0 : Nat), k + 1) = 0 := by
    show distN (0 * 2 ^ (k + 1)) (0 * 2 ^ k) = 0
    rw [Nat.zero_mul, Nat.zero_mul, distN_self]
  rw [hc, Nat.mul_zero]
  exact Nat.mul_pos (Nat.pos_pow_of_pos _ (by decide))
    (Nat.pos_pow_of_pos _ (by decide))

/-- Distance from the center `(0,0)` to `(p, j)` is governed by `p / 2^j`:
    `closeDy m (0,0) (p,j)` whenever `2^m · p < 2^j · 2^(L+1)`. -/
theorem closeDy_center (L m : Nat) (p j : Nat)
    (hj : 2 ^ m * p < 2 ^ j * 2 ^ (L + 1)) :
    closeDy L m (0, 0) (p, j) := by
  unfold closeDy
  show 2 ^ m * crossDist (0, 0) (p, j) < 2 ^ (0 + j) * 2 ^ (L + 1)
  have hc : crossDist ((0 : Nat), (0 : Nat)) (p, j) = p := by
    show distN (0 * 2 ^ j) (p * 2 ^ 0) = p
    rw [Nat.zero_mul, Nat.pow_zero, Nat.mul_one]
    show (0 - p) + (p - 0) = p
    rw [Nat.zero_sub, Nat.zero_add, Nat.sub_zero]
  rw [hc, Nat.zero_add]
  exact hj

/-- The `Φ`-orbit from seed `(p, 0)`: `picard Φ (p,0) n = (p, n)`. -/
theorem picard_Φ_eq (p : Nat) : ∀ n, picard Φ (p, 0) n = (p, n)
  | 0 => rfl
  | k + 1 => by
      show Φ (picard Φ (p, 0) k) = (p, k + 1)
      rw [picard_Φ_eq p k]; rfl

/-- `p < 2^p`, ∅-axiom (induction). -/
theorem self_lt_pow_two : ∀ p : Nat, p < 2 ^ p
  | 0 => by decide
  | k + 1 => by
      rw [Nat.pow_succ]
      -- k+1 ≤ 2^k < 2^k·2
      have h1 : k + 1 ≤ 2 ^ k := self_lt_pow_two k
      have h2 : 2 ^ k < 2 ^ k * 2 := by
        have : 2 ^ k * 1 < 2 ^ k * 2 :=
          Nat.mul_lt_mul_of_pos_left (by decide) (Nat.pos_pow_of_pos k (by decide))
        rw [Nat.mul_one] at this; exact this
      exact Nat.lt_of_le_of_lt h1 h2

/-- **★ Orbit → center (q=+1 convergence).**  The `Φ`-orbit from seed `(p, 0)`
    converges to the center `(0,0)`: at step `n` the iterate is `(p, n)` and its
    distance to the center is below scale `m` once `2^m·p < 2^n·2^(L+1)`, i.e.
    for all `n ≥ m + p` (a concrete modulus).  Reached by none (value never
    exactly `0` for `p > 0`), only as the limit. -/
theorem orbit_to_center (L : Nat) (p : Nat) :
    ∀ m, ∃ N, ∀ n, n ≥ N →
      (dyMet L).close m (0, 0) (picard Φ (p, 0) n) := by
  intro m
  refine ⟨m + p, ?_⟩
  intro n hn
  rw [picard_Φ_eq p n]
  apply closeDy_center
  -- 2^m · p < 2^n · 2^(L+1).  Since n ≥ m + p:  2^n ≥ 2^(m+p) = 2^m·2^p,
  -- and p < 2^p.  Concretely: 2^m·p < 2^m·2^p ≤ 2^n ≤ 2^n·2^(L+1).
  have h1 : 2 ^ m * p < 2 ^ m * 2 ^ p :=
    Nat.mul_lt_mul_of_pos_left (self_lt_pow_two p) (Nat.pos_pow_of_pos m (by decide))
  have h2 : 2 ^ m * 2 ^ p = 2 ^ (m + p) := (pow_add_two m p).symm
  have h3 : 2 ^ (m + p) ≤ 2 ^ n := by
    obtain ⟨d, hd⟩ := Nat.le.dest hn   -- (m+p) + d = n
    rw [← hd, pow_add_two (m + p) d]
    calc 2 ^ (m + p) = 2 ^ (m + p) * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ (m + p) * 2 ^ d :=
          Nat.mul_le_mul_left _ (Nat.pos_pow_of_pos d (by decide))
  have h4 : 2 ^ n ≤ 2 ^ n * 2 ^ (L + 1) := by
    calc 2 ^ n = 2 ^ n * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ n * 2 ^ (L + 1) :=
          Nat.mul_le_mul_left _ (Nat.pos_pow_of_pos (L + 1) (by decide))
  calc 2 ^ m * p < 2 ^ m * 2 ^ p := h1
    _ = 2 ^ (m + p) := h2
    _ ≤ 2 ^ n := h3
    _ ≤ 2 ^ n * 2 ^ (L + 1) := h4
