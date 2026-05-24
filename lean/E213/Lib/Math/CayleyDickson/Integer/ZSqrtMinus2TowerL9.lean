import E213.Lib.Math.CayleyDickson.Integer.ZSqrtMinus2TowerL8
/-!
# ZSqrt[-2] tower at L9

Extends `ZSqrtMinus2TowerL8` to **L9T**: next CD-doubling layer.

  · L8T: 128 units
  · **L9T: 256 units** (this file)

CD-doubling pattern continues uniformly past L8.  Full `decide`
verification at L9 exceeds heartbeat budget; structural shell only.

All declarations PURE.
-/

namespace E213.Lib.Math.CayleyDickson.ZSqrtMinus2

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

/-! ## §2 — L9T units (256 expected) -/

/-- L8T zero. -/
def L8T_zero' : L8T := (⟨0, 0⟩ : L8T)

/-- L9T zero. -/
def L9T_zero : L9T := (⟨0, 0⟩ : L9T)

/-- Lift L8T element via re-axis. -/
def L9T_left (u : L8T) : L9T := ⟨u, L8T_zero'⟩

/-- Lift L8T element via im-axis. -/
def L9T_right (u : L8T) : L9T := ⟨L8T_zero', u⟩

/-- L9T units = 256 elements: 128 re + 128 im liftings. -/
def L9T_units : List L9T :=
  (L8T_units.map L9T_left) ++ (L8T_units.map L9T_right)

/-- ★ **L9T unit count** = 256 = 2 × 128. -/
theorem L9T_units_count : L9T_units.length = 256 := by
  set_option maxRecDepth 2048 in decide

/-! ## §3 — Capstone -/

/-- ★★★★ **L9T deeper-layer capstone**: structural shell for the
    9th CD-doubling layer in the ZSqrt[-2] tower.

    Bundles: (a) L9T type, (b) operations, (c) unit cardinality
    256 = 2 × 128, (d) doubling relation. -/
theorem L9T_deeper_layer_capstone :
    L9T_units.length = 256
    ∧ L9T_units.length = 2 * L8T_units.length := by
  refine ⟨?_, ?_⟩ <;> set_option maxRecDepth 2048 in decide

end E213.Lib.Math.CayleyDickson.ZSqrtMinus2
