import E213.Theory.Internal.Int213

/-!
# Algebra213 — abstract algebra layer over Int213

Hierarchical typeclass layer for Cayley-Dickson rings.  Generic
theorems (most importantly `normSq_mul` via the Hurwitz-style
`N(uv) = u(v · conj v)conj u` decomposition) are proved once at
the abstract `IntegerNormed213` level and inherited by every
instance — replaces the brute-force `hurwitz_ring` polynomial
expansion that times out at higher CD layers.

∅-axiom design constraints:
  * No `simp` tags on generic theorems (avoids simp's internal
    propext machinery).
  * No `Decidable` / `decide` on abstract types.
  * Class fields are `Eq`-typed (no `Iff`).
  * Generic proofs use only `rw`, `calc`, `exact`, projection.
-/

namespace E213.Theory.Internal.Algebra213

/-- Ring axioms (associative, distributive, with 0/neg).
    Note: omits `1` / `mul_one` / `one_mul` since they are not
    required for the Hurwitz-style `normSq_mul` derivation.
    Pure `Eq` fields; no `Decidable` / `simp` machinery. -/
class Ring213 (α : Type) extends Add α, Neg α, Mul α, Zero α where
  add_assoc    : ∀ a b c : α, a + b + c = a + (b + c)
  add_comm     : ∀ a b   : α, a + b = b + a
  add_zero     : ∀ a     : α, a + 0 = a
  add_left_neg : ∀ a     : α, -a + a = 0
  mul_assoc    : ∀ a b c : α, a * b * c = a * (b * c)
  add_mul      : ∀ a b c : α, (a + b) * c = a * c + b * c
  mul_add      : ∀ a b c : α, a * (b + c) = a * b + a * c

/-- Commutative ring (ZI, ZOmega, ZSqrt[D] base layer). -/
class CommRing213 (α : Type) extends Ring213 α where
  mul_comm : ∀ a b : α, a * b = b * a

/-- *-Ring with anti-involutive conjugation (`conj(uv) = conj v · conj u`).
    For commutative cases (CommRing213 + StarRing213) the same-order
    form `conj(uv) = conj u · conj v` follows via `mul_comm`. -/
class StarRing213 (α : Type) extends Ring213 α where
  conj      : α → α
  conj_conj : ∀ a   : α, conj (conj a) = a
  conj_add  : ∀ a b : α, conj (a + b) = conj a + conj b
  conj_mul  : ∀ a b : α, conj (a * b) = conj b * conj a

/-- Integer-normed *-Ring: norm lands in Int, lifted via `ofInt`,
    with `a · conj a = ofInt (normSq a)` (the central identity).
    `ofInt_central` says integer scalars commute with everything,
    `ofInt_inj` lifts equalities back to Int. -/
class IntegerNormed213 (α : Type) extends StarRing213 α where
  ofInt         : Int → α
  normSq        : α → Int
  self_mul_conj : ∀ a   : α, a * conj a = ofInt (normSq a)
  ofInt_mul     : ∀ a b : Int, ofInt a * ofInt b = ofInt (a * b)
  ofInt_central : ∀ (z : Int) (a : α), ofInt z * a = a * ofInt z
  ofInt_inj     : ∀ {a b : Int}, ofInt a = ofInt b → a = b

namespace IntegerNormed213

open Ring213 (mul_assoc)
open StarRing213 (conj conj_mul)

variable {α : Type} [IntegerNormed213 α]

/-- ★★★★★★★ Generic Hurwitz norm-multiplicativity:
    `|uv|² = |u|² · |v|²`.

    Proof entirely via ring algebra + conj anti-distributivity +
    self_mul_conj.  No polynomial expansion at the Int level —
    each layer's instance only needs to provide its 4-variable
    `self_mul_conj` lemma plus the ring axioms. -/
theorem normSq_mul {α : Type} [inst : IntegerNormed213 α] (u v : α) :
    inst.normSq (u * v) = inst.normSq u * inst.normSq v := by
  apply @IntegerNormed213.ofInt_inj α inst
  calc IntegerNormed213.ofInt (inst.normSq (u * v))
      = (u * v) * StarRing213.conj (u * v) :=
        (IntegerNormed213.self_mul_conj _).symm
    _ = (u * v) * (StarRing213.conj v * StarRing213.conj u) := by
        rw [StarRing213.conj_mul]
    _ = u * (v * (StarRing213.conj v * StarRing213.conj u)) :=
        Ring213.mul_assoc _ _ _
    _ = u * (v * StarRing213.conj v * StarRing213.conj u) := by
        rw [← Ring213.mul_assoc v]
    _ = u * (IntegerNormed213.ofInt (inst.normSq v) * StarRing213.conj u) := by
        rw [IntegerNormed213.self_mul_conj]
    _ = u * (StarRing213.conj u * IntegerNormed213.ofInt (inst.normSq v)) := by
        rw [IntegerNormed213.ofInt_central]
    _ = u * StarRing213.conj u * IntegerNormed213.ofInt (inst.normSq v) :=
        (Ring213.mul_assoc _ _ _).symm
    _ = IntegerNormed213.ofInt (inst.normSq u) * IntegerNormed213.ofInt (inst.normSq v) := by
        rw [IntegerNormed213.self_mul_conj]
    _ = IntegerNormed213.ofInt (inst.normSq u * inst.normSq v) :=
        IntegerNormed213.ofInt_mul _ _

end IntegerNormed213

namespace Ring213

variable {α : Type} [inst : Ring213 α]

/-- Generic Ring213 `add_left_comm`. -/
theorem add_left_comm (a b c : α) : a + (b + c) = b + (a + c) := by
  rw [← @Ring213.add_assoc α inst, @Ring213.add_comm α inst a b,
      @Ring213.add_assoc α inst]

/-- Generic Ring213 `add_right_comm`. -/
theorem add_right_comm (a b c : α) : a + b + c = a + c + b := by
  rw [@Ring213.add_assoc α inst, @Ring213.add_comm α inst b c,
      ← @Ring213.add_assoc α inst]

/-- Generic Ring213 `zero_add`. -/
theorem zero_add (a : α) : 0 + a = a := by
  rw [@Ring213.add_comm α inst, @Ring213.add_zero α inst]

/-- Generic Ring213 `add_4_swap_mid`: `A + X + (Y + Z) = A + Y + (X + Z)`. -/
theorem add_4_swap_mid (A X Y Z : α) :
    A + X + (Y + Z) = A + Y + (X + Z) := by
  rw [@Ring213.add_assoc α inst A X (Y + Z),
      add_left_comm X Y Z,
      ← @Ring213.add_assoc α inst A Y (X + Z)]

end Ring213

end E213.Theory.Internal.Algebra213
