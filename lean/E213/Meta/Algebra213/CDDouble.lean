import E213.Meta.Int213.Core
import E213.Meta.Algebra213.Core

/-!
# `CDDouble` functor — META-theorem: CD doubling lifts CommStarRing213 → StarRing213

Cayley-Dickson doubling as a typeclass-level functor:
  CDDouble : CommStarRing213 → StarRing213

Given any commutative *-ring α with conjugation, the structure α × α
with multiplication
  (a, b)·(c, d) = (a·c - d̄·b, d·a + b·c̄)
and conjugation (a, b)↦(ā, -b) is a (possibly non-commutative) *-ring.

Once specialized:
  CDDouble Int = ZI (Gaussian integers, with trivial Int-conj)
  CDDouble ZI  = Lipschitz (integer quaternions)
  CDDouble Lipschitz = Cayley-like (loses associativity!)

This meta-theorem captures the structural CD-construction once, so
each concrete instance no longer needs hand-written ring axioms.

Caveats:
  * Associativity preservation requires base to be COMMUTATIVE.
  * Beyond Lipschitz (i.e., when doubling a non-commutative base),
    associativity breaks; we get an "alternative" structure instead.
-/

namespace E213.Meta.Algebra213

/-- Combined commutative *-ring class for clean CD-double base. -/
class CommStarRing213 (α : Type) extends CommRing213 α, StarRing213 α

/-- Combined commutative integer-normed *-ring class.  Used as the
    base precondition for the abstract Cayley-Dickson Hurwitz
    extension `IntegerNormed213 (CDDouble α)` — avoids the typeclass
    diamond that arises when `[CommStarRing213 α]` and
    `[IntegerNormed213 α]` are inferred independently (the two
    `.toStarRing213` projections are syntactically distinct).
    All commutative base rings (ZI, ZOmega, ZSqrt[D]) satisfy this. -/
class CommIntegerNormed213 (α : Type) extends CommStarRing213 α, IntegerNormed213 α

/-- `CDDouble α` — pair structure. -/
structure CDDouble (α : Type) where
  re : α
  im : α
  deriving DecidableEq

namespace CDDouble

variable {α : Type}

instance [Zero α] : Zero (CDDouble α) := ⟨⟨0, 0⟩⟩
instance [Add α] : Add (CDDouble α) := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance [Neg α] : Neg (CDDouble α) := ⟨fun u => ⟨-u.re, -u.im⟩⟩

/-- CD multiplication: `(a, b)·(c, d) = (a·c - d̄·b, d·a + b·c̄)`. -/
instance [Add α] [Neg α] [Mul α] [StarRing213 α] : Mul (CDDouble α) :=
  ⟨fun u v => ⟨u.re * v.re + -(StarRing213.conj v.im * u.im),
                v.im * u.re + u.im * StarRing213.conj v.re⟩⟩

/-- CD conjugation: `(a, b) ↦ (ā, -b)`. -/
def conj [StarRing213 α] (u : CDDouble α) : CDDouble α :=
  ⟨StarRing213.conj u.re, -u.im⟩

theorem ext {u v : CDDouble α} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr

end CDDouble

end E213.Meta.Algebra213

namespace E213.Meta.Algebra213.CDDouble

variable {α : Type}

-- ═══ Componentwise add axioms (require only Ring213 α) ═══

private theorem add_assoc' [Ring213 α] (u v w : CDDouble α) :
    u + v + w = u + (v + w) := by
  apply ext
  · exact Ring213.add_assoc u.re v.re w.re
  · exact Ring213.add_assoc u.im v.im w.im

private theorem add_comm' [Ring213 α] (u v : CDDouble α) :
    u + v = v + u := by
  apply ext
  · exact Ring213.add_comm u.re v.re
  · exact Ring213.add_comm u.im v.im

private theorem add_zero' [Ring213 α] (u : CDDouble α) : u + 0 = u := by
  apply ext
  · exact Ring213.add_zero u.re
  · exact Ring213.add_zero u.im

private theorem add_left_neg' [Ring213 α] (u : CDDouble α) : -u + u = 0 := by
  apply ext
  · exact Ring213.add_left_neg u.re
  · exact Ring213.add_left_neg u.im

end E213.Meta.Algebra213.CDDouble

namespace E213.Meta.Algebra213.CDDouble

variable {α : Type}

-- ═══ Distributive axioms (require Ring213 + StarRing213) ═══

private theorem add_mul' [Ring213 α] [StarRing213 α] (u v w : CDDouble α) :
    (u + v) * w = u * w + v * w := by
  apply ext
  · -- ((u + v) * w).re = (u.re + v.re) * w.re + -(conj w.im * (u.im + v.im))
    show (u.re + v.re) * w.re + -(StarRing213.conj w.im * (u.im + v.im))
       = (u.re * w.re + -(StarRing213.conj w.im * u.im))
       + (v.re * w.re + -(StarRing213.conj w.im * v.im))
    rw [Ring213.add_mul u.re v.re w.re,
        Ring213.mul_add (StarRing213.conj w.im) u.im v.im]
    rw [Ring213.neg_add (StarRing213.conj w.im * u.im) (StarRing213.conj w.im * v.im)]
    exact Ring213.add_4_swap_mid _ _ _ _
  · show w.im * (u.re + v.re) + (u.im + v.im) * StarRing213.conj w.re
       = (w.im * u.re + u.im * StarRing213.conj w.re)
         + (w.im * v.re + v.im * StarRing213.conj w.re)
    rw [Ring213.mul_add w.im u.re v.re,
        Ring213.add_mul u.im v.im (StarRing213.conj w.re)]
    exact Ring213.add_4_swap_mid _ _ _ _

end E213.Meta.Algebra213.CDDouble
