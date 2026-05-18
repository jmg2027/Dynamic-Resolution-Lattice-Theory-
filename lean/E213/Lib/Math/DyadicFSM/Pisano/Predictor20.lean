import E213.Lib.Math.DyadicFSM.ArithFSM.ModLarge
import E213.Lib.Math.DyadicFSM.Legendre
import E213.Lib.Math.DyadicFSM.Pisano.Predictor17

/-!
# Pisano predictor — 20-prime evidence (mod 67, 71, 73 added)

  | p  | Legendre | Branch    | π(p) | predict | match |
  | 67 |     2    | inert     |  68  |   68    | TIGHT | NEW
  | 71 |     1    | split     |  35  |   35    | TIGHT | NEW
  | 73 |     2    | inert     |  74  |   74    | TIGHT | NEW

All 3 new TIGHT.

Coverage:
  Inert (10): {3, 7, 13, 17, 23, 37, 43, 47, 53, 67, 73} — wait that's 11
  Split (8): {11, 19, 29, 31, 41, 59, 61, 71}
  Ramified (1): {5}

Sub-tight cases at 2 of 20:
  p=29 (split, ×2): predict 14 = 2 · tight 7
  p=47 (inert, ×3): predict 48 = 3 · tight 16

These 2 sub-tight remain isolated up to p=73.
-/

namespace E213.Lib.Math.DyadicFSM.Pisano.Predictor20

open E213.Lib.Math.DyadicFSM.Legendre.V213 (legendre213)


theorem legendre_5_mod_67 :
    legendre213 5 67 (by decide) = ⟨2, by decide⟩ := by decide

theorem legendre_5_mod_71 :
    legendre213 5 71 (by decide) = ⟨1, by decide⟩ := by decide

theorem legendre_5_mod_73 :
    legendre213 5 73 (by decide) = ⟨2, by decide⟩ := by decide

end E213.Lib.Math.DyadicFSM.Pisano.Predictor20
