import E213.Research.CDDouble

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

namespace E213.Research

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

end E213.Research

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
