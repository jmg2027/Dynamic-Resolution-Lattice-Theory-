import E213.Research.CayleyDickson.Sedenion

/-!
# Research: Cayley–Dickson layer 4 — integer trigintaduonions

`Trigintaduonion = Sedenion × Sedenion` via CD doubling.
32-dimensional (64 Int coordinates per element).  Inherits
structural failure modes of Sedenion (non-alt, zero divs)
and adds more.
-/

namespace E213.Research.CayleyDickson.Trigintaduonion

/-- CD layer 4: the 32-dim trigintaduonions. -/
structure Trigintaduonion where
  re : Sedenion
  im : Sedenion
  deriving DecidableEq

namespace Trigintaduonion

instance : Zero Trigintaduonion := ⟨⟨0, 0⟩⟩

theorem ext {u v : Trigintaduonion} (hr : u.re = v.re)
    (hi : u.im = v.im) : u = v := by cases u; cases v; congr

/-- CD multiplication (same formula, lifted once more). -/
def mul (u v : Trigintaduonion) : Trigintaduonion :=
  ⟨u.re * v.re - v.im.conj * u.im,
   v.im * u.re + u.im * v.re.conj⟩

instance : Mul Trigintaduonion := ⟨mul⟩

instance : Add Trigintaduonion := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance : Neg Trigintaduonion := ⟨fun u => ⟨-u.re, -u.im⟩⟩
instance : Sub Trigintaduonion := ⟨fun u v => u + (-v)⟩

/-- CD conjugation. -/
def conj (u : Trigintaduonion) : Trigintaduonion := ⟨u.re.conj, -u.im⟩

-- ═══ Projection lemmas ═══

theorem mul_re (u v : Trigintaduonion) :
    (u * v).re = u.re * v.re - v.im.conj * u.im := rfl

theorem mul_im (u v : Trigintaduonion) :
    (u * v).im = v.im * u.re + u.im * v.re.conj := rfl

theorem conj_re (u : Trigintaduonion) : (conj u).re = u.re.conj := rfl
theorem conj_im (u : Trigintaduonion) : (conj u).im = -u.im := rfl

theorem add_re (u v : Trigintaduonion) : (u + v).re = u.re + v.re := rfl
theorem add_im (u v : Trigintaduonion) : (u + v).im = u.im + v.im := rfl
theorem neg_re (u : Trigintaduonion) : (-u).re = -u.re := rfl
theorem neg_im (u : Trigintaduonion) : (-u).im = -u.im := rfl
theorem sub_re (u v : Trigintaduonion) : (u - v).re = u.re - v.re := rfl
theorem sub_im (u v : Trigintaduonion) : (u - v).im = u.im - v.im := rfl
theorem zero_re : (0 : Trigintaduonion).re = 0 := rfl
theorem zero_im : (0 : Trigintaduonion).im = 0 := rfl

end Trigintaduonion

end E213.Research.CayleyDickson.Trigintaduonion
