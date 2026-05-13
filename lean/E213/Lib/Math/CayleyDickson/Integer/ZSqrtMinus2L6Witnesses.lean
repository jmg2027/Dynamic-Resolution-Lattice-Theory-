import E213.Lib.Math.CayleyDickson.Integer.ZSqrtMinus2Tower

/-!
# L6 ZSqrt[-2] tower — explicit zero-divisor witness (Rust-discovered)

The Rust probe `algebra213-tower-probe` found that L6 ZSqrt[-2]
(32-dim, sedenion-position) has zero divisors:

  (e_1 + e_10) · (e_4 - e_15) = 0

where e_k is the k-th basis "real-slot" axis unit (positions 2, 8, 20, 30
in the 32-component flat array).  This file pins that fact as an
∅-axiom Lean theorem — the Rust→Lean discovery loop closing.

Notably L6 ZSqrt[-2] is NOT a sedenion-analogue: alt-L, alt-R, flex
all hold on basis units.  Yet zero divisors exist.  Novel structure.
-/

namespace E213.Lib.Math.CayleyDickson.ZSqrtMinus2

open E213.Lib.Math.CayleyDickson.Integer.ZSqrt

-- Zero builders at each layer
def Z2z : ZSqrt 2 := ⟨0, 0⟩
def L3z : L3T := ⟨Z2z, Z2z⟩
def L4z : L4T := ⟨L3z, L3z⟩
def L5z : L5T := ⟨L4z, L4z⟩
def L6z : L6T := ⟨L5z, L5z⟩

-- Basis units. Position-to-path encoding: 5-bit msb-first selector
-- (re=0, im=1) into nested L6T → ... → ZSqrt 2 → .re (always real-slot).
--
-- e_1  = pos 2  = 0b00010 = re re re im re
-- e_4  = pos 8  = 0b01000 = re im re re re
-- e_10 = pos 20 = 0b10100 = im re im re re
-- e_15 = pos 30 = 0b11110 = im im im im re

def e1  : L6T := ⟨⟨⟨⟨Z2z, ⟨1,0⟩⟩, L3z⟩, L4z⟩, L5z⟩
def e4  : L6T := ⟨⟨L4z, ⟨⟨⟨1,0⟩, Z2z⟩, L3z⟩⟩, L5z⟩
def e10 : L6T := ⟨L5z, ⟨⟨L3z, ⟨⟨1,0⟩, Z2z⟩⟩, L4z⟩⟩
def e15 : L6T := ⟨L5z, ⟨L4z, ⟨L3z, ⟨Z2z, ⟨1,0⟩⟩⟩⟩⟩

-- Witness sums
def zd_a : L6T := e1 + e10
def zd_b : L6T := e4 - e15

#eval (zd_a * zd_b = L6z : Bool)   -- should be true

/-- ★ ∅-axiom witness: L6 ZSqrt[-2] has a zero divisor. -/
theorem L6_zd_witness : zd_a * zd_b = L6z := by decide

end E213.Lib.Math.CayleyDickson.ZSqrtMinus2
