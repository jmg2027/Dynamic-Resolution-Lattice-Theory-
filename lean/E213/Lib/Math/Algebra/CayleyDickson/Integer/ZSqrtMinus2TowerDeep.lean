import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtMinus2Tower
import E213.Lib.Math.Algebra.CayleyDickson.Tower.Order4Monopoly_L6T

/-!
# ZSqrt[-2] tower — deeper layers L7, L8, L9 (structural shells)

Continues `ZSqrtMinus2Tower` (which provides L3T through L6T) with
three additional CD-doubling layers.  Each layer follows the
identical CD-doubling template:

```
structure L<N>T where
  re : L<N-1>T
  im : L<N-1>T

def mul, normSq, conj, add, neg, sub
def L<N>T_left, L<N>T_right : L<N-1>T → L<N>T
def L<N>T_units := (L<N-1>T_units.map left) ++ (L<N-1>T_units.map right)
theorem L<N>T_units_count : L<N>T_units.length = 2 * |L<N-1>T_units|
```

Unit cardinalities:
  · L4T:  8 units  (Lipschitz integers)
  · L5T: 16 units  (quaternion-like)
  · L6T: 32 units  (sedenion-like, past Moufang)
  · L7T: 64 units  (this file, §1)
  · L8T: 128 units (this file, §2)
  · L9T: 256 units (this file, §3)

The order distribution `(1, 1, 30, 0)` for orders `(1, 2, 4, 0)`
at L6T extends to each layer by the CD-doubling sign rule
(order-4 monopoly preserves under `(0, u) ↦ (-N(u), 0) = (-1, 0)`).
Full `decide` verification at L7+ exceeds practical heartbeat
budget and is left as future work; this file ships the structural
shells.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.ZSqrtMinus2

/-! ### §1 — L7T = CD-doubling of L6T (64 units) -/

/-- L7T = CD-doubling of L6T. -/
structure L7T where
  re : L6T
  im : L6T
  deriving DecidableEq, Repr

namespace L7T

instance : Zero L7T := ⟨⟨0, 0⟩⟩

/-- Cayley-Dickson multiplication at L7. -/
def mul (u v : L7T) : L7T :=
  ⟨u.re * v.re - (L6T.conj v.im) * u.im,
    v.im * u.re + u.im * (L6T.conj v.re)⟩

instance : Mul L7T := ⟨mul⟩

/-- L7T norm-squared. -/
def normSq (u : L7T) : Int :=
  L6T.normSq u.re + L6T.normSq u.im

instance : Add L7T := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance : Neg L7T := ⟨fun u => ⟨-u.re, -u.im⟩⟩
instance : Sub L7T := ⟨fun u v => u + (-v)⟩

/-- L7T conjugation. -/
def conj (u : L7T) : L7T := ⟨L6T.conj u.re, -u.im⟩

end L7T

/-- L6T zero element. -/
def L6T_zero : L6T := (⟨0, 0⟩ : L6T)

/-- L7T zero. -/
def L7T_zero : L7T := (⟨0, 0⟩ : L7T)

/-- Lift an L6T element to L7T via the re-axis. -/
def L7T_left (u : L6T) : L7T := ⟨u, L6T_zero⟩

/-- Lift an L6T element to L7T via the im-axis. -/
def L7T_right (u : L6T) : L7T := ⟨L6T_zero, u⟩

/-- L7T units: 64 elements (32 re-axis + 32 im-axis L6T liftings). -/
def L7T_units : List L7T :=
  (L6T_units.map L7T_left) ++ (L6T_units.map L7T_right)

/-- L7T unit count = 64 = 2 × 32. -/
theorem L7T_units_count : L7T_units.length = 64 := by decide

/-- L7T identity element. -/
def L7T_one : L7T := L7T_left L6T_one

/-- L7T `-1`. -/
def L7T_minus_one : L7T := L7T_left L6T_minus_one

/-- L7T deeper-layer capstone. -/
theorem L7T_deeper_layer_capstone :
    L7T_units.length = 64
    ∧ L7T_units.length = 2 * L6T_units.length := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ### §2 — L8T = CD-doubling of L7T (128 units) -/

/-- L8T = CD-doubling of L7T. -/
structure L8T where
  re : L7T
  im : L7T
  deriving DecidableEq, Repr

namespace L8T

instance : Zero L8T := ⟨⟨0, 0⟩⟩

/-- Cayley-Dickson multiplication at L8. -/
def mul (u v : L8T) : L8T :=
  ⟨u.re * v.re - (L7T.conj v.im) * u.im,
    v.im * u.re + u.im * (L7T.conj v.re)⟩

instance : Mul L8T := ⟨mul⟩

/-- L8T norm-squared. -/
def normSq (u : L8T) : Int :=
  L7T.normSq u.re + L7T.normSq u.im

instance : Add L8T := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance : Neg L8T := ⟨fun u => ⟨-u.re, -u.im⟩⟩
instance : Sub L8T := ⟨fun u v => u + (-v)⟩

/-- L8T conjugation. -/
def conj (u : L8T) : L8T := ⟨L7T.conj u.re, -u.im⟩

end L8T

/-- L7T zero (re-exported for L8T). -/
def L7T_zero' : L7T := (⟨0, 0⟩ : L7T)

/-- L8T zero. -/
def L8T_zero : L8T := (⟨0, 0⟩ : L8T)

/-- Lift L7T element via the re-axis. -/
def L8T_left (u : L7T) : L8T := ⟨u, L7T_zero'⟩

/-- Lift L7T element via the im-axis. -/
def L8T_right (u : L7T) : L8T := ⟨L7T_zero', u⟩

/-- L8T units: 128 elements. -/
def L8T_units : List L8T :=
  (L7T_units.map L8T_left) ++ (L7T_units.map L8T_right)

/-- L8T unit count = 128 = 2 × 64. -/
theorem L8T_units_count : L8T_units.length = 128 := by
  set_option maxRecDepth 1024 in decide

/-- L8T identity element. -/
def L8T_one : L8T := L8T_left L7T_one

/-- L8T `-1`. -/
def L8T_minus_one : L8T := L8T_left L7T_minus_one

/-- L8T deeper-layer capstone. -/
theorem L8T_deeper_layer_capstone :
    L8T_units.length = 128
    ∧ L8T_units.length = 2 * L7T_units.length := by
  refine ⟨?_, ?_⟩ <;> set_option maxRecDepth 1024 in decide

/-! ### §3 — L9T = CD-doubling of L8T (256 units) -/

/-- L9T = CD-doubling of L8T. -/
structure L9T where
  re : L8T
  im : L8T
  deriving DecidableEq, Repr

namespace L9T

instance : Zero L9T := ⟨⟨0, 0⟩⟩

/-- CD-multiplication at L9. -/
def mul (u v : L9T) : L9T :=
  ⟨u.re * v.re - (L8T.conj v.im) * u.im,
    v.im * u.re + u.im * (L8T.conj v.re)⟩

instance : Mul L9T := ⟨mul⟩

/-- L9T norm-squared. -/
def normSq (u : L9T) : Int :=
  L8T.normSq u.re + L8T.normSq u.im

instance : Add L9T := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance : Neg L9T := ⟨fun u => ⟨-u.re, -u.im⟩⟩
instance : Sub L9T := ⟨fun u v => u + (-v)⟩

/-- L9T conjugation. -/
def conj (u : L9T) : L9T := ⟨L8T.conj u.re, -u.im⟩

end L9T

/-- L8T zero (re-exported for L9T). -/
def L8T_zero' : L8T := (⟨0, 0⟩ : L8T)

/-- L9T zero. -/
def L9T_zero : L9T := (⟨0, 0⟩ : L9T)

/-- Lift L8T element via re-axis. -/
def L9T_left (u : L8T) : L9T := ⟨u, L8T_zero'⟩

/-- Lift L8T element via im-axis. -/
def L9T_right (u : L8T) : L9T := ⟨L8T_zero', u⟩

/-- L9T units: 256 elements (128 re + 128 im liftings). -/
def L9T_units : List L9T :=
  (L8T_units.map L9T_left) ++ (L8T_units.map L9T_right)

/-- L9T unit count = 256 = 2 × 128. -/
theorem L9T_units_count : L9T_units.length = 256 := by
  set_option maxRecDepth 2048 in decide

/-- L9T deeper-layer capstone. -/
theorem L9T_deeper_layer_capstone :
    L9T_units.length = 256
    ∧ L9T_units.length = 2 * L8T_units.length := by
  refine ⟨?_, ?_⟩ <;> set_option maxRecDepth 2048 in decide

end E213.Lib.Math.Algebra.CayleyDickson.ZSqrtMinus2
