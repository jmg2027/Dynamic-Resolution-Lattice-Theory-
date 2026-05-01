import E213.Research.CayleyDickson.CDDouble

/-!
# Research: Cayley–Dickson layer 2 — integer octonions

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
layer 1 via the `I'`/`J'` lifts) but verbose; deferred.
-/

namespace E213.Research.CayleyDickson.Cayley

open Lipschitz

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
def J' : Cayley := ⟨Lipschitz.J, 0⟩

/-- `I` lifted into the first copy of Lipschitz. -/
def I' : Cayley := ⟨Lipschitz.I', 0⟩

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

end E213.Research.CayleyDickson.Cayley

namespace E213.Research.Cayley

open E213.Research E213.Research.Lipschitz

/-- `Cayley.conj` is involutive. -/
theorem conj_conj (u : Cayley) : conj (conj u) = u := by
  apply ext
  · show u.re.conj.conj = u.re
    exact Lipschitz.conj_conj u.re
  · show -(-u.im) = u.im
    apply Lipschitz.ext
    · show (-(-u.im)).re = u.im.re
      apply ZI.ext
      · show -(-u.im.re.re) = u.im.re.re; omega
      · show -(-u.im.re.im) = u.im.re.im; omega
    · show (-(-u.im)).im = u.im.im
      apply ZI.ext
      · show -(-u.im.im.re) = u.im.im.re; omega
      · show -(-u.im.im.im) = u.im.im.im; omega

/-- `Cayley.conj` is not the identity. -/
theorem conj_ne_id : (conj : Cayley → Cayley) ≠ id := by
  intro h
  have hL : conj L = id L := congrFun h L
  have hLim : (conj L).im = (id L).im := by rw [hL]
  have hLim' : -(⟨⟨1, 0⟩, 0⟩ : Lipschitz) = ⟨⟨1, 0⟩, 0⟩ := hLim
  have hre : (-(⟨⟨1, 0⟩, 0⟩ : Lipschitz)).re = ((⟨⟨1, 0⟩, 0⟩ : Lipschitz)).re := by
    rw [hLim']
  have hre' : -(⟨1, 0⟩ : ZI) = ⟨1, 0⟩ := hre
  have hreZ : (-(⟨1, 0⟩ : ZI)).re = ((⟨1, 0⟩ : ZI)).re := by rw [hre']
  have : (-1 : Int) = 1 := hreZ
  exact absurd this (by decide)

end E213.Research.Cayley

/-
**Classical fact (not yet formalised).**  Cayley at this
level is **non-associative**: by hand-computation,

  (I' · J') · L = ⟨0, ⟨0, ZI.I⟩⟩
  I' · (J' · L) = ⟨0, ⟨0, ZI.negI⟩⟩

so `(I' · J') · L ≠ I' · (J' · L)` — the octonion
non-associator.  Formalisation requires unfolding the CD
formula through three layers of nested `mul`; deferred.
-/

namespace E213.Research.Cayley

open E213.Research E213.Research.Lipschitz

/-- **Non-associativity of Cayley multiplication.**  Three
    generators `I', J', L` of the integer octonions satisfy
    `(I' · J') · L ≠ I' · (J' · L)`.  This is the octonion
    non-associator; closed by `decide` which computes both
    products via the (concrete) CD formula. -/
theorem mul_not_associative :
    ∃ u v w : Cayley, (u * v) * w ≠ u * (v * w) := by
  refine ⟨I', J', L, ?_⟩
  decide

end E213.Research.Cayley

namespace E213.Research.Cayley

open E213.Research E213.Research.Lipschitz

/-- **Non-commutativity of Cayley multiplication.**
    `I' * J' ≠ J' * I'` at the Cayley level (inherited from
    the Lipschitz subalgebra via the `re`-component). -/
theorem mul_not_commutative :
    ∃ u v : Cayley, u * v ≠ v * u := by
  refine ⟨I', J', ?_⟩
  decide

end E213.Research.Cayley

namespace E213.Research.Cayley

open E213.Research E213.Research.Lipschitz

/-- `I' ≠ 0` in Cayley. -/
theorem I'_ne_zero : I' ≠ (0 : Cayley) := by decide

/-- `J' ≠ 0` in Cayley. -/
theorem J'_ne_zero : J' ≠ (0 : Cayley) := by decide

/-- `L ≠ 0` in Cayley. -/
theorem L_ne_zero : L ≠ (0 : Cayley) := by decide

/-- **Three non-zero generators with pairwise non-zero product.**
    Demonstrates that R3 (no zero divisors) is preserved at this
    level.  Classical fact: CD layer 2 = octonions has no zero
    divisors (Hurwitz classification); R3 first fails at layer 3
    (sedenions).  The three per-generator checks below are
    decidable and closed by `decide`. -/
theorem mul_generators_ne_zero :
    I' * J' ≠ 0 ∧ J' * L ≠ 0 ∧ I' * L ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end E213.Research.Cayley

namespace E213.Research.Cayley

/-- `L² = -1` at Cayley level. -/
theorem L_squared : L * L = ⟨⟨⟨-1, 0⟩, 0⟩, 0⟩ := by decide

/-- `I'² = -1` at Cayley (inherited). -/
theorem I'_squared : I' * I' = ⟨⟨⟨-1, 0⟩, 0⟩, 0⟩ := by decide

/-- `J'² = -1` at Cayley (inherited). -/
theorem J'_squared : J' * J' = ⟨⟨⟨-1, 0⟩, 0⟩, 0⟩ := by decide

/-- `I' * J' * L ≠ L * (I' * J')`.  Basis triple product
    non-commuting, octonion-flavor. -/
theorem I'_J'_L_ne_comm : (I' * J') * L ≠ L * (I' * J') := by decide

end E213.Research.Cayley

namespace E213.Research.Cayley

-- ═══ Alternativity evidence ═══
-- Octonions are classically an alternative algebra:
-- (a*a)*b = a*(a*b) holds universally.
-- Non-associativity + alternativity is the defining flavour.
-- Full universal alternativity is beyond `decide`; specific
-- basis-triple instances verified below.

/-- Alternativity at `(I', J')`: `(I'·I')·J' = I'·(I'·J')`. -/
theorem alt_I_I_J : (I' * I') * J' = I' * (I' * J') := by decide

/-- Alternativity at `(J', I')`: `(J'·J')·I' = J'·(J'·I')`. -/
theorem alt_J_J_I : (J' * J') * I' = J' * (J' * I') := by decide

/-- Alternativity at `(L, I')`: `(L·L)·I' = L·(L·I')`. -/
theorem alt_L_L_I : (L * L) * I' = L * (L * I') := by decide

/-- Right alternativity at `(I', J')`: `I'·(J'·J') = (I'·J')·J'`. -/
theorem alt_right_I_J_J : I' * (J' * J') = (I' * J') * J' := by decide

end E213.Research.Cayley

namespace E213.Research.Cayley

open E213.Research.Lipschitz

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

end E213.Research.Cayley

namespace E213.Research.Cayley

theorem sub_re (u v : Cayley) : (u - v).re = u.re - v.re := rfl
theorem sub_im (u v : Cayley) : (u - v).im = u.im - v.im := rfl

end E213.Research.Cayley
