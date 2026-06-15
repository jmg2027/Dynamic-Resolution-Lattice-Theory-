import E213.Lib.Math.NumberTheory.PrimeValuation
import E213.Lib.Math.NumberTheory.GcdLcmLattice
import E213.Meta.Nat.VpSeparation

/-!
# (ℕ, gcd, lcm) is a *distributive* lattice (∅-axiom)

`GcdLcmLattice` established the lattice axioms (absorption + idempotence); this
file completes the structure with the **distributive law** (the L4 item left open
there), upgrading `(ℕ, gcd, lcm)` to a verified distributive lattice:

  ★ **`gcd_lcm_distrib`** (`a,b,c > 0`): `gcd(a, lcm(b,c)) = lcm(gcd(a,b), gcd(a,c))`
  * **`lcm_gcd_distrib`** (dual): `lcm(a, gcd(b,c)) = gcd(lcm(a,b), lcm(a,c))`

Route — the prime-valuation bridge.  `vp_separation` (FTA uniqueness:
`(∀ prime p, vp p m = vp p n) → m = n`) reduces each identity to a per-prime
equality; `vp_gcd_min`/`vp_lcm_max` expand `vp(gcd)=min`, `vp(lcm)=max`; and the
underlying **(ℕ, min, max) lattice distributivity** (`min_max_distrib`,
`max_min_distrib` — also new here) closes it.  The only missing ingredient was
that min/max distributivity; all the valuation infra (`vp_gcd_min`, `vp_lcm_max`,
`vp_separation`) was already present and PURE.

`min213`/`max213` are explicit `if`-forms (matching the valuation lemmas; the
`Nat.min`/`Nat.max` simp lemmas carry `propext`).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.GcdLcmDistributive

open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213 vp_gcd_min vp_lcm_max)
open E213.Lib.Math.NumberTheory.Lcm213 (lcm213 gcd_pos lcm_pos)
open E213.Meta.Nat.VpMul (IsPrime213)
open E213.Meta.Nat.VpSeparation (vp_separation)
open E213.Meta.Nat.Valuation (vp)
open E213.Tactic.NatHelper (gcd213)

/-! ## §1 — min/max as explicit `if` (matching the valuation lemmas) -/

/-- `min` as explicit `if` — avoids the `propext`-carrying `Nat.min_*` lemmas. -/
def min213 (a b : Nat) : Nat := if a ≤ b then a else b

/-- `max` as explicit `if`. -/
def max213 (a b : Nat) : Nat := if a ≤ b then b else a

theorem min213_eq_left {a b : Nat} (h : a ≤ b) : min213 a b = a := by
  unfold min213; rw [if_pos h]

theorem min213_eq_right {a b : Nat} (h : ¬ a ≤ b) : min213 a b = b := by
  unfold min213; rw [if_neg h]

theorem max213_eq_right {a b : Nat} (h : a ≤ b) : max213 a b = b := by
  unfold max213; rw [if_pos h]

theorem max213_eq_left {a b : Nat} (h : ¬ a ≤ b) : max213 a b = a := by
  unfold max213; rw [if_neg h]

/-- `min213 m x = x` whenever `x ≤ m`. -/
theorem min213_right_of_ge {m x : Nat} (h : x ≤ m) : min213 m x = x := by
  by_cases hmx : m ≤ x
  · rw [min213_eq_left hmx]; exact Nat.le_antisymm hmx h
  · rw [min213_eq_right hmx]

/-- `max213 m x = m` whenever `x ≤ m`. -/
theorem max213_left_of_ge {m x : Nat} (h : x ≤ m) : max213 m x = m := by
  by_cases hmx : m ≤ x
  · rw [max213_eq_right hmx]; exact (Nat.le_antisymm hmx h).symm
  · rw [max213_eq_left hmx]

/-! ## §2 — lattice distributivity of (ℕ, min, max), PURE by case analysis -/

/-- ★ **min/max distributivity** (the (ℕ, min, max) lattice law):
    `min x (max y z) = max (min x y) (min x z)`. -/
theorem min_max_distrib (x y z : Nat) :
    min213 x (max213 y z) = max213 (min213 x y) (min213 x z) := by
  by_cases hyz : y ≤ z
  · rw [max213_eq_right hyz]
    by_cases hxy : x ≤ y
    · have hxz : x ≤ z := Nat.le_trans hxy hyz
      rw [min213_eq_left hxz, min213_eq_left hxy, max213_eq_right (Nat.le_refl x)]
    · rw [min213_eq_right hxy]
      by_cases hxz : x ≤ z
      · have hyx : y ≤ x := Nat.le_of_lt (Nat.lt_of_not_le hxy)
        rw [min213_eq_left hxz, max213_eq_right hyx]
      · rw [min213_eq_right hxz, max213_eq_right hyz]
  · rw [max213_eq_left hyz]
    have hzy : z ≤ y := Nat.le_of_lt (Nat.lt_of_not_le hyz)
    by_cases hxz : x ≤ z
    · have hxy : x ≤ y := Nat.le_trans hxz hzy
      rw [min213_eq_left hxy, min213_eq_left hxz, max213_eq_right (Nat.le_refl x)]
    · rw [min213_eq_right hxz]
      by_cases hxy : x ≤ y
      · rw [min213_eq_left hxy, max213_eq_left hxz]
      · rw [min213_eq_right hxy, max213_eq_left hyz]

/-- ★ **max/min distributivity** (dual lattice law):
    `max x (min y z) = min (max x y) (max x z)`. -/
theorem max_min_distrib (x y z : Nat) :
    max213 x (min213 y z) = min213 (max213 x y) (max213 x z) := by
  by_cases hyz : y ≤ z
  · rw [min213_eq_left hyz]
    by_cases hxy : x ≤ y
    · have hxz : x ≤ z := Nat.le_trans hxy hyz
      rw [max213_eq_right hxy, max213_eq_right hxz, min213_eq_left hyz]
    · rw [max213_eq_left hxy]
      by_cases hxz : x ≤ z
      · rw [max213_eq_right hxz, min213_eq_left hxz]
      · rw [max213_eq_left hxz, min213_eq_left (Nat.le_refl x)]
  · rw [min213_eq_right hyz]
    have hzy : z ≤ y := Nat.le_of_lt (Nat.lt_of_not_le hyz)
    by_cases hxz : x ≤ z
    · have hxy : x ≤ y := Nat.le_trans hxz hzy
      rw [max213_eq_right hxy, max213_eq_right hxz, min213_eq_right hyz]
    · rw [max213_eq_left hxz]
      by_cases hxy : x ≤ y
      · rw [max213_eq_right hxy, min213_right_of_ge hxy]
      · rw [max213_eq_left hxy, min213_eq_left (Nat.le_refl x)]

/-! ## §3 — `vp` of gcd / lcm in `min213` / `max213` form -/

theorem vp_gcd_min213 {p a b : Nat} (hp : Prime213 p) (ha : 0 < a) (hb : 0 < b) :
    vp p (gcd213 a b) = min213 (vp p a) (vp p b) :=
  vp_gcd_min hp ha hb

theorem vp_lcm_max213 {p a b : Nat} (hp : Prime213 p) (ha : 0 < a) (hb : 0 < b) :
    vp p (lcm213 a b) = max213 (vp p a) (vp p b) :=
  vp_lcm_max hp ha hb

/-! ## §4 — the full distributive law -/

/-- ★★★ **Distributive law for the (ℕ, gcd, lcm) lattice** (`a,b,c > 0`):
    `gcd(a, lcm(b,c)) = lcm(gcd(a,b), gcd(a,c))`.

    `vp_separation` reduces to "equal at every prime"; at prime `p` both sides
    are `vp`-expanded to `min (vp a) (max (vp b) (vp c))` resp.
    `max (min (vp a) (vp b)) (min (vp a) (vp c))`, equal by `min_max_distrib`.
    Completes the L4 item left open in `GcdLcmLattice`. -/
theorem gcd_lcm_distrib {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    gcd213 a (lcm213 b c) = lcm213 (gcd213 a b) (gcd213 a c) := by
  have hlbc : 0 < lcm213 b c := lcm_pos b c hb hc
  have hgab : 0 < gcd213 a b := gcd_pos a b ha
  have hgac : 0 < gcd213 a c := gcd_pos a c ha
  have hL : 0 < gcd213 a (lcm213 b c) := gcd_pos a (lcm213 b c) ha
  have hR : 0 < lcm213 (gcd213 a b) (gcd213 a c) := lcm_pos _ _ hgab hgac
  refine vp_separation hL hR (fun p hp => ?_)
  -- `IsPrime213 p` and `Prime213 p` are the same predicate (identical body).
  have hp' : Prime213 p := hp
  have hLHS : vp p (gcd213 a (lcm213 b c))
      = min213 (vp p a) (max213 (vp p b) (vp p c)) := by
    rw [vp_gcd_min213 hp' ha hlbc, vp_lcm_max213 hp' hb hc]
  have hRHS : vp p (lcm213 (gcd213 a b) (gcd213 a c))
      = max213 (min213 (vp p a) (vp p b)) (min213 (vp p a) (vp p c)) := by
    rw [vp_lcm_max213 hp' hgab hgac, vp_gcd_min213 hp' ha hb, vp_gcd_min213 hp' ha hc]
  rw [hLHS, hRHS]
  exact min_max_distrib (vp p a) (vp p b) (vp p c)

/-- Dual distributive law (`a,b,c > 0`):
    `lcm(a, gcd(b,c)) = gcd(lcm(a,b), lcm(a,c))`, via `max_min_distrib`. -/
theorem lcm_gcd_distrib {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    lcm213 a (gcd213 b c) = gcd213 (lcm213 a b) (lcm213 a c) := by
  have hgbc : 0 < gcd213 b c := gcd_pos b c hb
  have hlab : 0 < lcm213 a b := lcm_pos a b ha hb
  have hlac : 0 < lcm213 a c := lcm_pos a c ha hc
  have hL : 0 < lcm213 a (gcd213 b c) := lcm_pos a (gcd213 b c) ha hgbc
  have hR : 0 < gcd213 (lcm213 a b) (lcm213 a c) := gcd_pos _ _ hlab
  refine vp_separation hL hR (fun p hp => ?_)
  have hp' : Prime213 p := hp
  have hLHS : vp p (lcm213 a (gcd213 b c))
      = max213 (vp p a) (min213 (vp p b) (vp p c)) := by
    rw [vp_lcm_max213 hp' ha hgbc, vp_gcd_min213 hp' hb hc]
  have hRHS : vp p (gcd213 (lcm213 a b) (lcm213 a c))
      = min213 (max213 (vp p a) (vp p b)) (max213 (vp p a) (vp p c)) := by
    rw [vp_gcd_min213 hp' hlab hlac, vp_lcm_max213 hp' ha hb, vp_lcm_max213 hp' ha hc]
  rw [hLHS, hRHS]
  exact max_min_distrib (vp p a) (vp p b) (vp p c)

end E213.Lib.Math.NumberTheory.GcdLcmDistributive
