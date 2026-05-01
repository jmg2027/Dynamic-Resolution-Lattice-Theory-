import E213.Research.CayleyDickson.ZI
import E213.Research.CayleyDickson.ZIDomain

/-!
# Research: ZI ring-arithmetic supplement

Adds `Neg`, `Add`, `Sub` instances on `ZI` needed for the
Cayley–Dickson doubling (`Research.CDDouble`).  Core Lean 4
only, componentwise on `Int`.
-/

namespace E213.Research.CayleyDickson.ZIArith

instance : Add ZI := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance : Neg ZI := ⟨fun u => ⟨-u.re, -u.im⟩⟩
instance : Sub ZI := ⟨fun u v => u + (-v)⟩

theorem add_re (u v : ZI) : (u + v).re = u.re + v.re := rfl
theorem add_im (u v : ZI) : (u + v).im = u.im + v.im := rfl
theorem neg_re (u : ZI) : (-u).re = -u.re := rfl
theorem neg_im (u : ZI) : (-u).im = -u.im := rfl

theorem sub_re (u v : ZI) : (u - v).re = u.re - v.re := by
  show (u + (-v)).re = u.re - v.re
  rw [add_re, neg_re]; omega

theorem sub_im (u v : ZI) : (u - v).im = u.im - v.im := by
  show (u + (-v)).im = u.im - v.im
  rw [add_im, neg_im]; omega

theorem conj_neg (u : ZI) : (-u).conj = -(u.conj) := by
  apply ext
  · show -u.re = -u.re
    rfl
  · show -(-u.im) = -(-u.im)
    rfl

theorem conj_zero : ZI.conj 0 = 0 := by
  apply ext
  · show (0 : Int) = 0; rfl
  · show -(0 : Int) = 0; rfl

theorem add_zero (u : ZI) : u + 0 = u := by
  apply ext
  · show u.re + 0 = u.re; omega
  · show u.im + 0 = u.im; omega

theorem zero_add (u : ZI) : 0 + u = u := by
  apply ext
  · show 0 + u.re = u.re; omega
  · show 0 + u.im = u.im; omega

theorem add_comm (u v : ZI) : u + v = v + u := by
  apply ext
  · show u.re + v.re = v.re + u.re; omega
  · show u.im + v.im = v.im + u.im; omega

end E213.Research.CayleyDickson.ZIArith

namespace E213.Research.CayleyDickson.ZIArith

-- Conj compatibility with add/sub.

theorem conj_add (u v : ZI) : (u + v).conj = u.conj + v.conj := by
  apply ext
  · show u.re + v.re = u.re + v.re; rfl
  · show -(u.im + v.im) = -u.im + -v.im; omega

theorem conj_sub (u v : ZI) : (u - v).conj = u.conj - v.conj := by
  apply ext
  · show u.re - v.re = u.re - v.re; rfl
  · show -(u.im - v.im) = -u.im - -v.im; omega

-- ZI neg/mul distributivity (needed in CD proof).

theorem neg_mul (u v : ZI) : (-u) * v = -(u * v) := by
  apply ext
  · show -u.re * v.re - -u.im * v.im = -(u.re * v.re - u.im * v.im)
    rw [Int.neg_mul, Int.neg_mul]; omega
  · show -u.re * v.im + -u.im * v.re = -(u.re * v.im + u.im * v.re)
    rw [Int.neg_mul, Int.neg_mul]; omega

theorem mul_neg (u v : ZI) : u * (-v) = -(u * v) := by
  rw [mul_comm, neg_mul, mul_comm v u]

theorem neg_neg (u : ZI) : -(-u) = u := by
  apply ext
  · show -(-u.re) = u.re; omega
  · show -(-u.im) = u.im; omega

theorem sub_neg_neg (u v : ZI) : u - (-(-v)) = u - v := by
  rw [neg_neg]

end E213.Research.CayleyDickson.ZIArith

namespace E213.Research.CayleyDickson.ZIArith

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

end E213.Research.CayleyDickson.ZIArith

namespace E213.Research.CayleyDickson.ZIArith

-- ═══ Projection simp lemmas for tactic (hurwitz_ring) ═══

/-- `.re` projection of `ZI` multiplication. -/
theorem mul_re (u v : ZI) :
    (u * v).re = u.re * v.re - u.im * v.im := rfl

/-- `.im` projection of `ZI` multiplication. -/
theorem mul_im (u v : ZI) :
    (u * v).im = u.re * v.im + u.im * v.re := rfl

/-- `.re` projection of ZI conjugation. -/
theorem conj_re (u : ZI) : u.conj.re = u.re := rfl

/-- `.im` projection of ZI conjugation. -/
theorem conj_im (u : ZI) : u.conj.im = -u.im := rfl

/-- `.re` of `ZI.I`. -/
theorem I_re : (ZI.I).re = 0 := rfl

/-- `.im` of `ZI.I`. -/
theorem I_im : (ZI.I).im = 1 := rfl

/-- `.re` of `ZI.negI`. -/
theorem negI_re : (ZI.negI).re = 0 := rfl

/-- `.im` of `ZI.negI`. -/
theorem negI_im : (ZI.negI).im = -1 := rfl

end E213.Research.CayleyDickson.ZIArith
