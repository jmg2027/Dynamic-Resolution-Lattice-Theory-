import E213.Research.ZI
import E213.Research.ZIDomain

/-!
# Research: ZI ring-arithmetic supplement

Adds `Neg`, `Add`, `Sub` instances on `ZI` needed for the
Cayley–Dickson doubling (`Research.CDDouble`).  Core Lean 4
only, componentwise on `Int`.
-/

namespace E213.Research.ZI

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

end E213.Research.ZI
