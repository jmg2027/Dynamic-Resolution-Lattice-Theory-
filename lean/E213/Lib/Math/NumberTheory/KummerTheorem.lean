import E213.Lib.Math.NumberTheory.LegendreDePolignac
import E213.Lib.Math.Combinatorics.BollobasSetPair
import E213.Lib.Math.Combinatorics.Sperner
import E213.Lib.Math.NumberTheory.PrimeValuation
import E213.Meta.Nat.PolyNatMTactic
import E213.Meta.Nat.NatRing213

/-!
# Kummer's theorem — digit-sum / carry form (∅-axiom)

A clean consequence of the de Polignac digit-sum formula
`(p−1)·vₚ(n!) + s_p(n) = n` (`LegendreDePolignac.de_polignac`).

  ★★★ **Kummer (digit-sum form)** — for prime `p`:
        `(p−1)·vₚ(C(m+n,m)) + s_p(m+n) = s_p(m) + s_p(n)`
      The subtraction-free statement of `(p−1)·vₚ(C(m+n,m)) = s_p(m)+s_p(n)−s_p(m+n)`;
      the RHS `/(p−1)` is the number of base-`p` carries in adding `m+n`.

Proof: `binom (m+n) m · (m!·n!) = (m+n)!` (`BollobasSetPair.binom_ab`); apply `vₚ`,
use additivity `vp_mul`, multiply by `(p−1)`, substitute de Polignac three times, the
linear `m, n, m+n` terms cancel (`m+n = m+n`).  All additive — no Nat subtraction.

`de_polignac` uses `CutFactorial.factorial`; `binom_ab` uses `Permutations.fact`.  The two
have identical defining equations, bridged here by `factorial_eq_fact` (induction).
-/

namespace E213.Lib.Math.NumberTheory.KummerTheorem

open E213.Meta.Nat.Valuation (vp)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213 vp_mul)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial factorial_succ
  factorial_pos)
open E213.Lib.Math.Combinatorics.Permutations (fact)
open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Combinatorics.BollobasSetPair (binom_ab)
open E213.Lib.Math.Combinatorics.Sperner (binom_pos)
open E213.Lib.Math.NumberTheory.LegendreDePolignac (de_polignac sDigit)
open E213.Meta.Nat.NatRing213 (nat_add_right_cancel)

/-! ## §1 — factorial / fact bridge

`CutFactorial.factorial` and `Permutations.fact` share the recursion
`f 0 = 1`, `f (k+1) = (k+1)·f k`.  Equal by induction. -/

/-- `CutFactorial.factorial n = Permutations.fact n` (identical recursion). -/
theorem factorial_eq_fact : ∀ n, factorial n = fact n
  | 0 => rfl
  | n + 1 => by
    rw [factorial_succ n, factorial_eq_fact n]
    rfl

/-! ## §2 — the valuation identity from `binom_ab` -/

/-- `vₚ(C(m+n,m)) + vₚ(m!) + vₚ(n!) = vₚ((m+n)!)` (`p` prime), the `vₚ`-image of
    `binom_ab` via valuation additivity. -/
theorem vp_binom_split {p : Nat} (hp : Prime213 p) (m n : Nat) :
    vp p (binom (m + n) m) + vp p (factorial m) + vp p (factorial n)
      = vp p (factorial (m + n)) := by
  have hbpos : 0 < binom (m + n) m := binom_pos (Nat.le_add_right m n)
  have hmpos : 0 < fact m := factorial_pos m |> fun h => by
    rw [factorial_eq_fact m] at h; exact h
  have hnpos : 0 < fact n := factorial_pos n |> fun h => by
    rw [factorial_eq_fact n] at h; exact h
  -- vₚ(C·(m!·n!)) = vₚ((m+n)!)
  have heq : binom (m + n) m * (fact m * fact n) = fact (m + n) := binom_ab m n
  have hkey : vp p (binom (m + n) m * (fact m * fact n)) = vp p (fact (m + n)) := by
    rw [heq]
  rw [vp_mul hp hbpos (Nat.mul_pos hmpos hnpos),
      vp_mul hp hmpos hnpos] at hkey
  -- transfer fact → factorial
  rw [factorial_eq_fact m, factorial_eq_fact n, factorial_eq_fact (m + n)]
  rw [← Nat.add_assoc] at hkey
  exact hkey

/-! ## §3 — Kummer's theorem (digit-sum form) -/

/-- ★★★ **Kummer's theorem (digit-sum / carry form)** — for prime `p`:
    `(p−1)·vₚ(C(m+n,m)) + s_p(m+n) = s_p(m) + s_p(n)`.
    Subtraction-free form of `(p−1)·vₚ(C(m+n,m)) = s_p(m)+s_p(n)−s_p(m+n)`; the RHS
    `/(p−1)` counts the base-`p` carries when adding `m+n`. -/
theorem kummer {p : Nat} (hp : Prime213 p) (m n : Nat) :
    (p - 1) * vp p (binom (m + n) m) + sDigit p (m + n)
      = sDigit p m + sDigit p n := by
  -- the three de Polignac instances
  have hm : (p - 1) * vp p (factorial m) + sDigit p m = m := de_polignac hp m
  have hn : (p - 1) * vp p (factorial n) + sDigit p n = n := de_polignac hp n
  have hmn : (p - 1) * vp p (factorial (m + n)) + sDigit p (m + n) = m + n :=
    de_polignac hp (m + n)
  -- the valuation split, times (p−1)
  have hsplit := vp_binom_split hp m n
  -- abstract the opaque terms so ring_nat sees plain Nat variables
  generalize hC : vp p (binom (m + n) m) = C at *
  generalize hvm : vp p (factorial m) = vm at *
  generalize hvn : vp p (factorial n) = vn at *
  generalize hvmn : vp p (factorial (m + n)) = vmn at *
  generalize hsm : sDigit p m = sm at *
  generalize hsn : sDigit p n = sn at *
  generalize hsmn : sDigit p (m + n) = smn at *
  generalize hq : p - 1 = q at *
  -- hsplit : C + vm + vn = vmn
  -- hm : q*vm + sm = m, hn : q*vn + sn = n, hmn : q*vmn + smn = m+n
  -- goal : q*C + smn = sm + sn
  -- Multiply hsplit by q: q*C + q*vm + q*vn = q*vmn.
  have hmul : q * C + q * vm + q * vn = q * vmn := by
    rw [← Nat.mul_add, ← Nat.mul_add, hsplit]
  -- Add sm + sn + smn to both sides of hmul, then substitute the three de Polignac instances.
  have hbig : (q * C + q * vm + q * vn) + (sm + sn + smn)
      = q * vmn + (sm + sn + smn) := by rw [hmul]
  -- LHS regroups to (q*C + smn) + (q*vm + sm) + (q*vn + sn);
  -- RHS regroups to (q*vmn + smn) + sm + sn.
  have hL : (q * C + q * vm + q * vn) + (sm + sn + smn)
      = (q * C + smn) + (q * vm + sm) + (q * vn + sn) := by ring_nat
  have hR : q * vmn + (sm + sn + smn) = (q * vmn + smn) + sm + sn := by ring_nat
  rw [hL, hR, hm, hn, hmn] at hbig
  -- hbig : (q*C + smn) + m + n = (m+n) + sm + sn ; cancel m + n.
  have hcancel : (q * C + smn) + (m + n) = (sm + sn) + (m + n) := by
    have e : (q * C + smn) + m + n = (q * C + smn) + (m + n) := by ring_nat
    have e2 : (m + n) + sm + sn = (sm + sn) + (m + n) := by ring_nat
    rw [e, e2] at hbig; exact hbig
  exact nat_add_right_cancel hcancel

/-! ## §4 — concrete smokes (closed numeric, axiom-clean) -/

/-- `vp 2 (C(4,2)) = vp 2 6 = 1`. -/
theorem smoke_vp2_binom42 : vp 2 (binom 4 2) = 1 := by decide
/-- `s₂(2)+s₂(2)−s₂(4) = 1+1−1 = 1` (additive: `(2−1)·1 + s₂(4) = s₂(2)+s₂(2)`). -/
theorem smoke_kummer2 :
    (2 - 1) * vp 2 (binom (2 + 2) 2) + sDigit 2 (2 + 2) = sDigit 2 2 + sDigit 2 2 := by
  decide
/-- `p = 3`, `m = n = 1`: `C(2,1) = 2`, `vp 3 2 = 0`, `s₃(1)+s₃(1) = 2`, `s₃(2) = 2`. -/
theorem smoke_kummer3 :
    (3 - 1) * vp 3 (binom (1 + 1) 1) + sDigit 3 (1 + 1) = sDigit 3 1 + sDigit 3 1 := by
  decide
/-- `p = 3`, `m = 1, n = 2`: `C(3,1) = 3`, `vp 3 3 = 1`; one carry adding `1+2` in base 3.
    `s₃(1)+s₃(2) = 1+2 = 3`, `s₃(3) = 1`; `(3−1)·1 + 1 = 3`. -/
theorem smoke_kummer3b :
    (3 - 1) * vp 3 (binom (1 + 2) 1) + sDigit 3 (1 + 2) = sDigit 3 1 + sDigit 3 2 := by
  decide

end E213.Lib.Math.NumberTheory.KummerTheorem
