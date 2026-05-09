import E213.Lib.Math.CayleyDickson.ZI
import E213.Lib.Math.CayleyDickson.ZIDomain
import E213.Theory.Internal.Int213


import E213.Lib.Math.CayleyDickson.ZIDomain

/-!
# ZI ring-arithmetic supplement

Adds `Neg`, `Add`, `Sub` instances on `ZI` needed for the
Cayley–Dickson doubling (`Research.CDDouble`).  Core Lean 4
only, componentwise on `Int`.

∅-axiom — `omega` calls replaced with `Int213.{add_comm, neg_add}`
+ Lean-core PURE Int lemmas (`Int.add_zero`, `Int.neg_neg`,
`Int.sub_eq_add_neg`).
-/

namespace E213.Lib.Math.CayleyDickson.ZI.ZI

open E213.Theory.Internal.Int213 (add_comm neg_add)

instance : Add ZI := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance : Neg ZI := ⟨fun u => ⟨-u.re, -u.im⟩⟩
instance : Sub ZI := ⟨fun u v => u + (-v)⟩

theorem add_re (u v : ZI) : (u + v).re = u.re + v.re := rfl
theorem add_im (u v : ZI) : (u + v).im = u.im + v.im := rfl
theorem neg_re (u : ZI) : (-u).re = -u.re := rfl
theorem neg_im (u : ZI) : (-u).im = -u.im := rfl

theorem sub_re (u v : ZI) : (u - v).re = u.re - v.re := by
  show (u + (-v)).re = u.re - v.re
  rw [add_re, neg_re, ← Int.sub_eq_add_neg]

theorem sub_im (u v : ZI) : (u - v).im = u.im - v.im := by
  show (u + (-v)).im = u.im - v.im
  rw [add_im, neg_im, ← Int.sub_eq_add_neg]

theorem conj_neg (u : ZI) : (-u).conj = -(u.conj) := by
  apply ext
  · show -u.re = -u.re; rfl
  · show -(-u.im) = -(-u.im); rfl

theorem conj_zero : ZI.conj 0 = 0 := by
  apply ext
  · show (0 : Int) = 0; rfl
  · show -(0 : Int) = 0; rfl

theorem add_zero (u : ZI) : u + 0 = u := by
  apply ext
  · show u.re + 0 = u.re; exact Int.add_zero _
  · show u.im + 0 = u.im; exact Int.add_zero _

theorem zero_add (u : ZI) : 0 + u = u := by
  apply ext
  · show 0 + u.re = u.re
    rw [add_comm 0 u.re]; exact Int.add_zero _
  · show 0 + u.im = u.im
    rw [add_comm 0 u.im]; exact Int.add_zero _

theorem add_comm (u v : ZI) : u + v = v + u := by
  apply ext
  · show u.re + v.re = v.re + u.re; exact E213.Theory.Internal.Int213.add_comm _ _
  · show u.im + v.im = v.im + u.im; exact E213.Theory.Internal.Int213.add_comm _ _

-- Conj compatibility with add/sub.

theorem conj_add (u v : ZI) : (u + v).conj = u.conj + v.conj := by
  apply ext
  · show u.re + v.re = u.re + v.re; rfl
  · show -(u.im + v.im) = -u.im + -v.im; exact neg_add _ _

theorem conj_sub (u v : ZI) : (u - v).conj = u.conj - v.conj := by
  apply ext
  · show u.re - v.re = u.re - v.re; rfl
  · show -(u.im - v.im) = -u.im - -v.im
    -- Both sides reduce to -u.im + v.im
    have hL : -(u.im - v.im) = -u.im + v.im := by
      rw [Int.sub_eq_add_neg, neg_add, Int.neg_neg]
    have hR : -u.im - -v.im = -u.im + v.im := by
      rw [Int.sub_eq_add_neg, Int.neg_neg]
    exact hL.trans hR.symm

-- ZI neg/mul distributivity (needed in CD proof).

theorem neg_mul (u v : ZI) : (-u) * v = -(u * v) := by
  apply ext
  · show -u.re * v.re - -u.im * v.im = -(u.re * v.re - u.im * v.im)
    rw [Int.neg_mul, Int.neg_mul]
    have hL : -(u.re * v.re) - -(u.im * v.im) = -(u.re * v.re) + u.im * v.im := by
      rw [Int.sub_eq_add_neg, Int.neg_neg]
    have hR : -(u.re * v.re - u.im * v.im) = -(u.re * v.re) + u.im * v.im := by
      rw [Int.sub_eq_add_neg, neg_add, Int.neg_neg]
    exact hL.trans hR.symm
  · show -u.re * v.im + -u.im * v.re = -(u.re * v.im + u.im * v.re)
    rw [Int.neg_mul, Int.neg_mul, ← neg_add]

theorem mul_neg (u v : ZI) : u * (-v) = -(u * v) := by
  rw [mul_comm, neg_mul, mul_comm v u]

theorem neg_neg (u : ZI) : -(-u) = u := by
  apply ext
  · show -(-u.re) = u.re; exact Int.neg_neg _
  · show -(-u.im) = u.im; exact Int.neg_neg _

theorem sub_neg_neg (u v : ZI) : u - (-(-v)) = u - v := by
  rw [neg_neg]

open E213.Tactic

/-- **ZI multiplication is associative.**  Polynomial identity
    in 6 Int variables, closed by `quad_norm`. -/
theorem mul_assoc (u v w : ZI) : (u * v) * w = u * (v * w) := by
  apply ext
  · show (u.re * v.re - u.im * v.im) * w.re - (u.re * v.im + u.im * v.re) * w.im
       = u.re * (v.re * w.re - v.im * w.im) - u.im * (v.re * w.im + v.im * w.re)
    quad_norm
  · show (u.re * v.re - u.im * v.im) * w.im + (u.re * v.im + u.im * v.re) * w.re
       = u.re * (v.re * w.im + v.im * w.re) + u.im * (v.re * w.re - v.im * w.im)
    quad_norm

-- ═══ Projection simp lemmas for tactic (hurwitz_ring) ═══

theorem mul_re (u v : ZI) :
    (u * v).re = u.re * v.re - u.im * v.im := rfl

theorem mul_im (u v : ZI) :
    (u * v).im = u.re * v.im + u.im * v.re := rfl

theorem conj_re (u : ZI) : u.conj.re = u.re := rfl
theorem conj_im (u : ZI) : u.conj.im = -u.im := rfl

theorem I_re : (ZI.I).re = 0 := rfl
theorem I_im : (ZI.I).im = 1 := rfl
theorem negI_re : (ZI.negI).re = 0 := rfl
theorem negI_im : (ZI.negI).im = -1 := rfl

end E213.Lib.Math.CayleyDickson.ZI.ZI
