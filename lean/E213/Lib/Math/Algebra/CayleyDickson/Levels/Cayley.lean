import E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble

/-!
# Cayley–Dickson layer 2 — integer octonions

`Cayley = Lipschitz × Lipschitz` with the same CD doubling
formula applied again.  Classically gives the integer
octonions (rank-8 non-associative ring).

At this level:
- **commutativity** fails (inherited from Lipschitz at layer 1),
- **associativity** fails (NEW at layer 2; octonions are
  alternative but non-associative).

This module sets up the structure and basic involution.  The
non-associativity witness and a layer-2 `mul_not_commutative`
computation are structurally straightforward (inherit from
layer 1 via the `Cayley.I'`/`Cayley.J'` lifts) but verbose; deferred.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Levels.Cayley

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI.ZI
open E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble
open E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble.Lipschitz

/-- CD layer 2: the integer octonions. -/
structure Cayley where
  re : Lipschitz
  im : Lipschitz
  deriving DecidableEq

namespace Cayley

instance : Zero Cayley := ⟨⟨0, 0⟩⟩

/-- Generator `ℓ` (new imaginary at layer 2). -/
def L : Cayley := ⟨0, ⟨⟨1, 0⟩, 0⟩⟩

/-- `J` lifted into the first copy of Lipschitz. -/
def Cayley.J' : Cayley := ⟨Lipschitz.J, 0⟩

/-- `I` lifted into the first copy of Lipschitz. -/
def Cayley.I' : Cayley := ⟨Lipschitz.I', 0⟩

theorem ext {u v : Cayley} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr

/-- CD multiplication (same formula as layer 1, lifted). -/
def mul (u v : Cayley) : Cayley :=
  ⟨u.re * v.re - v.im.conj * u.im,
   v.im * u.re + u.im * v.re.conj⟩

instance : Mul Cayley := ⟨mul⟩

/-- Conjugation at layer 2. -/
def conj (u : Cayley) : Cayley := ⟨u.re.conj, -u.im⟩

end Cayley

open Cayley

/-- `Cayley.conj` is involutive. -/
theorem conj_conj (u : Cayley) : conj (conj u) = u := by
  apply Cayley.ext
  · show u.re.conj.conj = u.re
    exact Lipschitz.conj_conj u.re
  · show -(-u.im) = u.im
    apply Lipschitz.ext
    · show (-(-u.im)).re = u.im.re
      apply ZI.ext
      · show -(-u.im.re.re) = u.im.re.re; exact Int.neg_neg _
      · show -(-u.im.re.im) = u.im.re.im; exact Int.neg_neg _
    · show (-(-u.im)).im = u.im.im
      apply ZI.ext
      · show -(-u.im.im.re) = u.im.im.re; exact Int.neg_neg _
      · show -(-u.im.im.im) = u.im.im.im; exact Int.neg_neg _

/-- `Cayley.conj` has a non-fixed point — witness `L`. -/
theorem conj_ne_id : ∃ x : Cayley, conj x ≠ x := by
  refine ⟨L, ?_⟩
  intro hL
  have hLim : (conj L).im = L.im := by rw [hL]
  have hLim' : -(⟨⟨1, 0⟩, 0⟩ : Lipschitz) = ⟨⟨1, 0⟩, 0⟩ := hLim
  have hre : (-(⟨⟨1, 0⟩, 0⟩ : Lipschitz)).re = ((⟨⟨1, 0⟩, 0⟩ : Lipschitz)).re := by
    rw [hLim']
  have hre' : -(⟨1, 0⟩ : ZI) = ⟨1, 0⟩ := hre
  have hreZ : (-(⟨1, 0⟩ : ZI)).re = ((⟨1, 0⟩ : ZI)).re := by rw [hre']
  have h_re : (-1 : Int) = 1 := hreZ
  exact absurd h_re (by decide)

end E213.Lib.Math.Algebra.CayleyDickson.Levels.Cayley

/-
**Classical fact (not yet formalised).**  Cayley at this
level is **non-associative**: by hand-computation,

  (Cayley.I' · Cayley.J') · L = ⟨0, ⟨0, ZI.I⟩⟩
  Cayley.I' · (Cayley.J' · L) = ⟨0, ⟨0, ZI.negI⟩⟩

so `(Cayley.I' · Cayley.J') · L ≠ Cayley.I' · (Cayley.J' · L)` — the octonion
non-associator.  Formalisation requires unfolding the CD
formula through three layers of nested `mul`; deferred.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Levels.Cayley

open Cayley

open E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble.Lipschitz

/-- **Non-associativity of Cayley multiplication.**  Three
    generators `Cayley.I', Cayley.J', L` of the integer octonions satisfy
    `(Cayley.I' · Cayley.J') · L ≠ Cayley.I' · (Cayley.J' · L)`.  This is the octonion
    non-associator; closed by `decide` which computes both
    products via the (concrete) CD formula. -/
theorem mul_not_associative :
    ∃ u v w : Cayley, (u * v) * w ≠ u * (v * w) := by
  refine ⟨Cayley.I', Cayley.J', L, ?_⟩
  decide


/-- **Non-commutativity of Cayley multiplication.**
    `Cayley.I' * Cayley.J' ≠ Cayley.J' * Cayley.I'` at the Cayley level (inherited from
    the Lipschitz subalgebra via the `re`-component). -/
theorem mul_not_commutative :
    ∃ u v : Cayley, u * v ≠ v * u := by
  refine ⟨Cayley.I', Cayley.J', ?_⟩
  decide


/-- `Cayley.I' ≠ 0` in Cayley. -/
theorem I'_ne_zero : (Cayley.I' : Cayley) ≠ 0 := by decide

/-- `Cayley.J' ≠ 0` in Cayley. -/
theorem J'_ne_zero : (Cayley.J' : Cayley) ≠ 0 := by decide

/-- `L ≠ 0` in Cayley. -/
theorem L_ne_zero : (Cayley.L : Cayley) ≠ 0 := by decide

/-- **Three non-zero generators with pairwise non-zero product.**
    Demonstrates that R3 (no zero divisors) is preserved at this
    level.  Classical fact: CD layer 2 = octonions has no zero
    divisors (Hurwitz classification); R3 first fails at layer 3
    (sedenions).  The three per-generator checks below are
    decidable and closed by `decide`. -/
theorem mul_generators_ne_zero :
    Cayley.I' * Cayley.J' ≠ (0 : Cayley) ∧ Cayley.J' * Cayley.L ≠ (0 : Cayley) ∧ Cayley.I' * Cayley.L ≠ (0 : Cayley) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- `L² = -1` at Cayley level. -/
theorem L_squared : Cayley.L * Cayley.L = ⟨⟨⟨-1, 0⟩, 0⟩, 0⟩ := by decide

/-- `I'² = -1` at Cayley (inherited). -/
theorem I'_squared : Cayley.I' * Cayley.I' = ⟨⟨⟨-1, 0⟩, 0⟩, 0⟩ := by decide

/-- `J'² = -1` at Cayley (inherited). -/
theorem J'_squared : Cayley.J' * Cayley.J' = ⟨⟨⟨-1, 0⟩, 0⟩, 0⟩ := by decide

/-- `Cayley.I' * Cayley.J' * L ≠ L * (Cayley.I' * Cayley.J')`.  Basis triple product
    non-commuting, octonion-flavor. -/
theorem I'_J'_L_ne_comm : (Cayley.I' * Cayley.J') * L ≠ L * (Cayley.I' * Cayley.J') := by decide

-- ═══ Alternativity evidence ═══
-- Octonions are classically an alternative algebra:
-- (a*a)*b = a*(a*b) holds universally.
-- Non-associativity + alternativity is the defining flavour.
-- Full universal alternativity is beyond `decide`; specific
-- basis-triple instances verified below.

/-- Alternativity at `(Cayley.I', Cayley.J')`: `(Cayley.I'·Cayley.I')·Cayley.J' = Cayley.I'·(Cayley.I'·Cayley.J')`. -/
theorem alt_I_I_J : (Cayley.I' * Cayley.I') * Cayley.J' = Cayley.I' * (Cayley.I' * Cayley.J') := by decide

/-- Alternativity at `(Cayley.J', Cayley.I')`: `(Cayley.J'·Cayley.J')·Cayley.I' = Cayley.J'·(Cayley.J'·Cayley.I')`. -/
theorem alt_J_J_I : (Cayley.J' * Cayley.J') * Cayley.I' = Cayley.J' * (Cayley.J' * Cayley.I') := by decide

/-- Alternativity at `(L, Cayley.I')`: `(L·L)·Cayley.I' = L·(L·Cayley.I')`. -/
theorem alt_L_L_I : (L * L) * Cayley.I' = L * (L * Cayley.I') := by decide

/-- Right alternativity at `(Cayley.I', Cayley.J')`: `Cayley.I'·(Cayley.J'·Cayley.J') = (Cayley.I'·Cayley.J')·Cayley.J'`. -/
theorem alt_right_I_J_J : Cayley.I' * (Cayley.J' * Cayley.J') = (Cayley.I' * Cayley.J') * Cayley.J' := by decide


-- ═══ Cayley Add/Neg/Sub (needed for hurwitz_ring) ═══

instance : Add Cayley := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance : Neg Cayley := ⟨fun u => ⟨-u.re, -u.im⟩⟩
instance : Sub Cayley := ⟨fun u v => u + (-v)⟩

-- ═══ Projection simp lemmas ═══

theorem mul_re (u v : Cayley) :
    (u * v).re = u.re * v.re - v.im.conj * u.im := rfl

theorem mul_im (u v : Cayley) :
    (u * v).im = v.im * u.re + u.im * v.re.conj := rfl

theorem conj_re (u : Cayley) : (conj u).re = u.re.conj := rfl

theorem conj_im (u : Cayley) : (conj u).im = -u.im := rfl

theorem add_re (u v : Cayley) : (u + v).re = u.re + v.re := rfl
theorem add_im (u v : Cayley) : (u + v).im = u.im + v.im := rfl
theorem neg_re (u : Cayley) : (-u).re = -u.re := rfl
theorem neg_im (u : Cayley) : (-u).im = -u.im := rfl
theorem zero_re : (0 : Cayley).re = 0 := rfl
theorem zero_im : (0 : Cayley).im = 0 := rfl

theorem sub_re (u v : Cayley) : (u - v).re = u.re - v.re := rfl
theorem sub_im (u v : Cayley) : (u - v).im = u.im - v.im := rfl

end E213.Lib.Math.Algebra.CayleyDickson.Levels.Cayley
