import E213.Lib.Math.CayleyDickson.Integer.ZSqrtMinus2TowerL7
/-!
# ZSqrt[-2] tower at L8 — extends L7T

Extends `ZSqrtMinus2TowerL7` to **L8T**, the next CD-doubling.

  · L4T: 8 units (Lipschitz integers)
  · L5T: 16 units (quaternion-like)
  · L6T: 32 units (sedenion-like)
  · L7T: 64 units (this file's predecessor)
  · **L8T: 128 units** (this file)

The CD-doubling pattern continues uniformly past L7; the order
distribution `(1, 1, *, 0)` extends with `* = 126` at L8 (one
identity, one `-1`, all others order-4 by the right-imaginary
square-to-`-1` lemma).  Full `decide` verification at L8 exceeds
budget; structural shell only.

All declarations PURE.
-/

namespace E213.Lib.Math.CayleyDickson.ZSqrtMinus2

-- L8 (next CD-doubling past L7; 128 units)
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

/-- L8T norm-squared = `|re|² + |im|²`. -/
def normSq (u : L8T) : Int :=
  L7T.normSq u.re + L7T.normSq u.im

instance : Add L8T := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance : Neg L8T := ⟨fun u => ⟨-u.re, -u.im⟩⟩
instance : Sub L8T := ⟨fun u v => u + (-v)⟩

/-- L8T conjugation. -/
def conj (u : L8T) : L8T := ⟨L7T.conj u.re, -u.im⟩

end L8T

/-! ## §2 — L8T units (128 expected)

The unit set: 2-fold split between L8T_left and L8T_right liftings
of L7T units (64 each). -/

/-- L7T zero. -/
def L7T_zero' : L7T := (⟨0, 0⟩ : L7T)

/-- L8T zero. -/
def L8T_zero : L8T := (⟨0, 0⟩ : L8T)

/-- Lift L7T element via the re-axis. -/
def L8T_left (u : L7T) : L8T := ⟨u, L7T_zero'⟩

/-- Lift L7T element via the im-axis. -/
def L8T_right (u : L7T) : L8T := ⟨L7T_zero', u⟩

/-- L8T units = 128 elements: 64 re-axis + 64 im-axis liftings of L7T units. -/
def L8T_units : List L8T :=
  (L7T_units.map L8T_left) ++ (L7T_units.map L8T_right)

/-- ★ **L8T unit count** = 128 = 2 × 64. -/
theorem L8T_units_count : L8T_units.length = 128 := by
  set_option maxRecDepth 1024 in decide

/-! ## §3 — L8T identity -/

/-- L8T identity element. -/
def L8T_one : L8T := L8T_left L7T_one

/-- L8T `-1`. -/
def L8T_minus_one : L8T := L8T_left L7T_minus_one

/-! ## §4 — L8T capstone -/

/-- ★★★★ **L8T deeper-layer capstone**: structural shell for the
    8th CD-doubling layer in the ZSqrt[-2] tower.

    Bundles: (a) L8T type, (b) operations, (c) unit cardinality
    128 = 2 × 64, (d) doubling relation `|L8T_units| = 2 · |L7T_units|`. -/
theorem L8T_deeper_layer_capstone :
    L8T_units.length = 128
    ∧ L8T_units.length = 2 * L7T_units.length := by
  refine ⟨?_, ?_⟩ <;> set_option maxRecDepth 1024 in decide

end E213.Lib.Math.CayleyDickson.ZSqrtMinus2
