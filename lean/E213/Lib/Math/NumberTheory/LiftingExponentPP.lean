import E213.Meta.Nat
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum

/-!
# Prime-power lifting for LTE — foundations (∅-axiom)

Toward the lifting-the-exponent kernel `v_p(aᵖ − bᵖ) = v_p(a − b) + 1` (p odd prime, p∣a−b, p∤b).
The route is binomial: `aᵖ − bᵖ = (b+d)ᵖ − bᵖ = p·b^{p−1}·d + Σ_{k≥2} C(p,k) b^{p−k} dᵏ` with `d = a−b`,
where the first term has `v_p = v_p(d)+1` and every later term has `v_p ≥ v_p(d)+2`.  The result then
follows from the **strict-minimum (ultrametric) valuation law**: a sum whose terms have a unique
minimal `v_p` inherits that minimum.

This module starts with that law (`vp_add_eq_min`), a general reusable `vp` tool.  The remaining
binomial-tail bound + assembly are the next rungs (see `HANDOFF.md` LTE roadmap).
-/

namespace E213.Lib.Math.NumberTheory.LiftingExponentPP

open E213.Meta.Nat.Valuation (vp pow_vp_dvd vp_not_dvd_succ le_vp_iff)
open E213.Meta.Nat.Gcd213 (dvd_add_213 dvd_sub_213)
open E213.Meta.Nat.NatRing213 (nat_add_sub_self_right)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)

/-- ★★★ **Strict-minimum valuation law** (ultrametric, the `<` case):
    if `v_p(x) < v_p(y)` then `v_p(x + y) = v_p(x)`.

    `pᵃ` (`a = v_p x`) divides both `x` and `y`, hence `x+y`; but `p^{a+1}` divides `y` and not `x`,
    so it cannot divide `x+y = (x+y)` — were it to, it would divide `(x+y)−y = x`.  Hence the
    valuation of the sum is pinned to the strictly-smaller `a`.  A general `vp` tool. -/
theorem vp_add_eq_min {p x y : Nat} (hp : 2 ≤ p) (hx : 0 < x) (hy : 0 < y)
    (hlt : vp p x < vp p y) : vp p (x + y) = vp p x := by
  have hxy : 0 < x + y := Nat.lt_of_lt_of_le hx (Nat.le_add_right x y)
  have hax : p ^ (vp p x) ∣ x := pow_vp_dvd p x
  have hay : p ^ (vp p x) ∣ y := (le_vp_iff p y (vp p x) hp hy).mpr (Nat.le_of_lt hlt)
  have haxy : p ^ (vp p x) ∣ (x + y) := dvd_add_213 _ _ _ hax hay
  have hle : vp p x ≤ vp p (x + y) := (le_vp_iff p (x + y) (vp p x) hp hxy).mp haxy
  have hay1 : p ^ (vp p x + 1) ∣ y := (le_vp_iff p y (vp p x + 1) hp hy).mpr hlt
  have hnax1 : ¬ p ^ (vp p x + 1) ∣ x := vp_not_dvd_succ p x hp hx
  have hnaxy1 : ¬ p ^ (vp p x + 1) ∣ (x + y) := by
    intro hd
    have hsub : p ^ (vp p x + 1) ∣ ((x + y) - y) :=
      dvd_sub_213 y (x + y) (p ^ (vp p x + 1)) (Nat.le_add_left y x) hay1 hd
    rw [nat_add_sub_self_right x y] at hsub
    exact hnax1 hsub
  have hlt2 : vp p (x + y) < vp p x + 1 := by
    rcases Nat.lt_or_ge (vp p (x + y)) (vp p x + 1) with h | h
    · exact h
    · exact absurd ((le_vp_iff p (x + y) (vp p x + 1) hp hxy).mpr h) hnaxy1
  exact Nat.le_antisymm (Nat.le_of_lt_succ hlt2) hle

/-- Symmetric form: if `v_p(y) < v_p(x)` then `v_p(x + y) = v_p(y)` (add commutes). -/
theorem vp_add_eq_min' {p x y : Nat} (hp : 2 ≤ p) (hx : 0 < x) (hy : 0 < y)
    (hlt : vp p y < vp p x) : vp p (x + y) = vp p y := by
  rw [Nat.add_comm]; exact vp_add_eq_min hp hy hx hlt

/-- ★★ **Sum divisibility**: if `g` divides every term `f k` (`k < n`), it divides `Σ_{k<n} f k`.
    The other half of the ultrametric package — used to lower-bound the valuation of the binomial
    tail `Σ_{k≥2} C(p,k) b^{p−k} dᵏ`. -/
theorem dvd_sumTo (g : Nat) (f : Nat → Nat) :
    ∀ n, (∀ k, k < n → g ∣ f k) → g ∣ sumTo n f
  | 0, _ => ⟨0, by rw [Nat.mul_zero]; rfl⟩
  | n + 1, h => by
      rw [sumTo_succ]
      exact dvd_add_213 g (sumTo n f) (f n)
        (dvd_sumTo g f n (fun k hk => h k (Nat.lt_succ_of_lt hk)))
        (h n (Nat.lt_succ_self n))

/-- ★★ **Sum valuation lower bound**: if `pᵐ ∣ f k` for every term, then `m ≤ v_p(Σ f)`
    (for a positive sum). -/
theorem le_vp_sumTo {p m n : Nat} (f : Nat → Nat) (hp : 2 ≤ p) (hpos : 0 < sumTo n f)
    (h : ∀ k, k < n → p ^ m ∣ f k) : m ≤ vp p (sumTo n f) :=
  (le_vp_iff p (sumTo n f) m hp hpos).mp (dvd_sumTo (p ^ m) f n h)

end E213.Lib.Math.NumberTheory.LiftingExponentPP
