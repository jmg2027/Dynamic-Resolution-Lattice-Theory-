import E213.Research.Cayley

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

namespace E213.Research

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

end E213.Research

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
