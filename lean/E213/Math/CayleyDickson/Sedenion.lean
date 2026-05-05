import E213.Math.CayleyDickson.Cayley

/-!
# Research: Cayley–Dickson layer 3 — integer sedenions

`Sedenion = Cayley × Cayley` with the same CD doubling formula.
Classically gives the 16-dimensional sedenions.

**Structural status**: at this layer, R3 (no zero divisors)
*fails* — the sedenions have explicit zero divisors.  This is
the algebraic boundary below which CD still preserves
"integral-domain-like" behaviour and above which it does not.

Non-commutativity and non-associativity are inherited.
-/

namespace E213.Math.CayleyDickson.Sedenion


open E213.Math.CayleyDickson.ZI
open E213.Math.CayleyDickson.ZI.ZI
open Cayley

/-- CD layer 3: the integer sedenions. -/
structure Sedenion where
  re : Cayley
  im : Cayley
  deriving DecidableEq

namespace Sedenion

instance : Zero Sedenion := ⟨⟨0, 0⟩⟩

theorem ext {u v : Sedenion} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr

end Sedenion

-- Cayley Add/Neg needed before we can define Sedenion.mul via CD.

namespace Cayley

instance : Add Cayley := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance : Neg Cayley := ⟨fun u => ⟨-u.re, -u.im⟩⟩
instance : Sub Cayley := ⟨fun u v => u + (-v)⟩

end Cayley

namespace Sedenion

open Cayley

/-- CD multiplication (same formula, lifted once more). -/
def mul (u v : Sedenion) : Sedenion :=
  ⟨u.re * v.re - v.im.conj * u.im,
   v.im * u.re + u.im * v.re.conj⟩

instance : Mul Sedenion := ⟨mul⟩

end Sedenion

end E213.Math.CayleyDickson.Sedenion

/-
**Classical fact (not yet formalised).**  Sedenions have
zero divisors; for instance

  (e_3 + e_10) · (e_6 - e_15) = 0

in the standard octonion-extended basis.  The product of two
non-zero sedenions can be zero — R3 (NonVanishing) fails for
the first time in the CD tower.

Formalising a specific witness in our CD encoding requires
mapping the e_k basis elements to the concrete Sedenion
constructors `⟨re, im⟩` with `re, im : Cayley`, unfolding
the CD multiplication through four levels of nesting, and
closing via `decide`.  Deferred to a future session.

Once formalised, this completes the R-condition failure
ladder across the first four CD layers:

  ZI         R2 ✓   R3 ✓   assoc ✓
  Lipschitz  R2 ✗   R3 ✓   assoc ✓
  Cayley     R2 ✗   R3 ✓   assoc ✗  (non_associative formal)
  Sedenion   R2 ✗   R3 ✗   assoc ✗  (R3 fail deferred)
-/

namespace E213.Math.CayleyDickson.Sedenion

open E213.Math.CayleyDickson.Cayley

instance : Add Sedenion := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance : Neg Sedenion := ⟨fun u => ⟨-u.re, -u.im⟩⟩
instance : Sub Sedenion := ⟨fun u v => u + (-v)⟩

-- Standard CD basis elements.  Encoding:
--   Bit 0 → ZI.im,  Bit 1 → Lipschitz.im outer,
--   Bit 2 → Cayley.im,  Bit 3 → Sedenion.im.

/-- `e_3 = ij` lifted three CD layers. -/
def e3  : Sedenion := ⟨⟨⟨0, ⟨0, 1⟩⟩, 0⟩, 0⟩

/-- `e_6`. -/
def e6  : Sedenion := ⟨⟨0, ⟨0, ⟨1, 0⟩⟩⟩, 0⟩

/-- `e_10`. -/
def e10 : Sedenion := ⟨0, ⟨⟨0, ⟨1, 0⟩⟩, 0⟩⟩

/-- `e_15`. -/
def e15 : Sedenion := ⟨0, ⟨0, ⟨0, ⟨0, 1⟩⟩⟩⟩

/-- `e_3 + e_10` — one side of a classical sedenion zero
    divisor pair. -/
def zd_left : Sedenion := e3 + e10

/-- `e_6 - e_15` — other side. -/
def zd_right : Sedenion := e6 - e15

open E213.Math.CayleyDickson.Cayley

/-- **Moreno's sedenion zero divisor** (1998).
    `(e_3 + e_10) · (e_6 - e_15) = 0` in the standard
    CD-basis encoding.  Closed by `decide` which unfolds
    the four-level CD multiplication on concrete basis
    vectors. -/
theorem zd_product_zero :
    zd_left * zd_right = (0 : Sedenion) := by decide

/-- `zd_left` is nonzero. -/
theorem zd_left_ne_zero : zd_left ≠ (0 : Sedenion) := by decide

/-- `zd_right` is nonzero. -/
theorem zd_right_ne_zero : zd_right ≠ (0 : Sedenion) := by decide

/-- **R3 (NonVanishing) FAILS on Sedenion.**  Explicit
    zero-divisor pair: `zd_left * zd_right = 0` with both
    factors non-zero. -/
theorem R3_fails_on_sedenion :
    ∃ u v : Sedenion, u ≠ 0 ∧ v ≠ 0 ∧ u * v = 0 :=
  ⟨zd_left, zd_right, zd_left_ne_zero, zd_right_ne_zero,
   zd_product_zero⟩

/-- Generators at sedenion level: Cayley generators lifted. -/
def Sedenion.I' : Sedenion := ⟨E213.Math.CayleyDickson.Cayley.I', 0⟩
def Sedenion.J' : Sedenion := ⟨E213.Math.CayleyDickson.Cayley.J', 0⟩
def Sedenion.L' : Sedenion := ⟨E213.Math.CayleyDickson.Cayley.L, 0⟩
/-- New generator at sedenion level (the "M" imaginary). -/
def M  : Sedenion := ⟨0, ⟨⟨⟨1, 0⟩, 0⟩, 0⟩⟩

/-- **Sedenion multiplication is not commutative**
    (inherited via Cayley Sedenion.I'/Sedenion.J'). -/
theorem mul_not_commutative :
    ∃ u v : Sedenion, u * v ≠ v * u := by
  refine ⟨Sedenion.I', Sedenion.J', ?_⟩; decide

/-- **Sedenion multiplication is not associative**
    (inherited via Cayley Sedenion.I', Sedenion.J', L). -/
theorem mul_not_associative :
    ∃ u v w : Sedenion, (u * v) * w ≠ u * (v * w) := by
  refine ⟨Sedenion.I', Sedenion.J', Sedenion.L', ?_⟩; decide

-- ═══ Alternativity failure at Sedenion level ═══
-- Octonions (CD layer 2) are classically alternative.
-- Sedenions (CD layer 3) are *not* — second structural
-- drop at layer 3 (along with R3 failure).

/-- Alternativity holds at basis `(e_3, e_3, e_6)`. -/
theorem alt_holds_at_basis :
    (e3 * e3) * e6 = e3 * (e3 * e6) := by decide

/-- **Alternativity FAILS at `(zd_left, zd_left, zd_right)`**.
    RHS = 0 since `zd_left · zd_right = 0`.  LHS non-zero;
    hence the two differ.  Closed by `decide`. -/
theorem alt_fails_at_zd :
    (zd_left * zd_left) * zd_right ≠ zd_left * (zd_left * zd_right) := by
  decide

/-- **Sedenion is NOT alternative.**  Existential wrap. -/
theorem not_alternative :
    ∃ a b : Sedenion, (a * a) * b ≠ a * (a * b) :=
  ⟨zd_left, zd_right, alt_fails_at_zd⟩

open E213.Math.CayleyDickson.Cayley

-- ═══ Conjugation at Sedenion level ═══

/-- CD conjugation for Sedenion. -/
def conj (u : Sedenion) : Sedenion := ⟨u.re.conj, -u.im⟩

-- ═══ Projection simp lemmas for hurwitz_ring ═══

theorem mul_re (u v : Sedenion) :
    (u * v).re = u.re * v.re - v.im.conj * u.im := rfl

theorem mul_im (u v : Sedenion) :
    (u * v).im = v.im * u.re + u.im * v.re.conj := rfl

theorem conj_re (u : Sedenion) : (conj u).re = u.re.conj := rfl
theorem conj_im (u : Sedenion) : (conj u).im = -u.im := rfl

theorem add_re (u v : Sedenion) : (u + v).re = u.re + v.re := rfl
theorem add_im (u v : Sedenion) : (u + v).im = u.im + v.im := rfl
theorem neg_re (u : Sedenion) : (-u).re = -u.re := rfl
theorem neg_im (u : Sedenion) : (-u).im = -u.im := rfl
theorem sub_re (u v : Sedenion) : (u - v).re = u.re - v.re := rfl
theorem sub_im (u v : Sedenion) : (u - v).im = u.im - v.im := rfl
theorem zero_re : (0 : Sedenion).re = 0 := rfl
theorem zero_im : (0 : Sedenion).im = 0 := rfl

end E213.Math.CayleyDickson.Sedenion
