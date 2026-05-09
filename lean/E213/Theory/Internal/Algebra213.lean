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
    `ofInt_inj` lifts equalities back to Int.
    `ofInt_add` is the additive ring-hom property — needed for
    norm-additivity at higher CD layers. -/
class IntegerNormed213 (α : Type) extends StarRing213 α where
  ofInt         : Int → α
  normSq        : α → Int
  self_mul_conj : ∀ a   : α, a * conj a = ofInt (normSq a)
  ofInt_mul     : ∀ a b : Int, ofInt a * ofInt b = ofInt (a * b)
  ofInt_add     : ∀ a b : Int, ofInt a + ofInt b = ofInt (a + b)
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

/-- Generic Ring213 `add_5_perm`: 5-term permutation
    `A + P + (Q + R + S) = A + Q + (R + P + S)`.  Used by ZOmega
    mul_assoc.re (Eisenstein -ab structure). -/
theorem add_5_perm (A P Q R S : α) :
    A + P + (Q + R + S) = A + Q + (R + P + S) := by
  rw [@Ring213.add_assoc α inst Q R S, @Ring213.add_assoc α inst R P S,
      @Ring213.add_assoc α inst A P (Q + (R + S)),
      @Ring213.add_assoc α inst A Q (R + (P + S))]
  congr 1
  rw [add_left_comm P Q (R + S), add_left_comm P R S]

/-- Generic Ring213 `zero_mul`: `0 * a = 0`. -/
theorem zero_mul (a : α) : (0 : α) * a = 0 := by
  have h1 : (0 : α) * a = (0 + 0) * a :=
    congrArg (· * a) (@Ring213.add_zero α inst 0).symm
  rw [@Ring213.add_mul α inst] at h1
  -- h1 : 0 * a = 0 * a + 0 * a
  -- Apply: -(0*a) + (0*a) = -(0*a) + (0*a + 0*a), so 0 = -(0*a) + (0*a + 0*a)
  -- = (-(0*a) + 0*a) + 0*a = 0 + 0*a = 0*a
  have h2 : -(0 * a) + (0 * a) = -(0 * a) + (0 * a + 0 * a) :=
    congrArg ((-(0*a)) + ·) h1
  rw [@Ring213.add_left_neg α inst, ← @Ring213.add_assoc α inst,
      @Ring213.add_left_neg α inst, zero_add] at h2
  exact h2.symm

/-- Generic Ring213 `mul_zero`: `a * 0 = 0`. -/
theorem mul_zero (a : α) : a * (0 : α) = 0 := by
  have h1 : a * (0 : α) = a * (0 + 0) :=
    congrArg (a * ·) (@Ring213.add_zero α inst 0).symm
  rw [@Ring213.mul_add α inst] at h1
  have h2 : -(a * 0) + (a * 0) = -(a * 0) + (a * 0 + a * 0) :=
    congrArg ((-(a*0)) + ·) h1
  rw [@Ring213.add_left_neg α inst, ← @Ring213.add_assoc α inst,
      @Ring213.add_left_neg α inst, zero_add] at h2
  exact h2.symm

/-- Generic Ring213 `neg_add_cancel_self`: `(-a) + a = 0`.  Just a re-export of `add_left_neg`. -/
theorem neg_add_cancel_self (a : α) : -a + a = 0 :=
  @Ring213.add_left_neg α inst a

/-- Generic Ring213 `neg_mul`: `(-a) * b = -(a * b)`.  Derived
    from `(-a) * b + a * b = (-a + a) * b = 0 * b = 0`,
    so `(-a) * b` is the additive inverse of `a * b`. -/
theorem neg_mul (a b : α) : (-a) * b = -(a * b) := by
  have h1 : (-a + a) * b = (0 : α) * b := by rw [@Ring213.add_left_neg α inst]
  rw [@Ring213.add_mul α inst, zero_mul] at h1
  have h2 : -(a * b) + ((-a) * b + a * b) = -(a * b) + 0 := by rw [h1]
  rw [← @Ring213.add_assoc α inst, @Ring213.add_comm α inst (-(a*b)) (-a*b),
      @Ring213.add_assoc α inst, @Ring213.add_left_neg α inst,
      @Ring213.add_zero α inst, @Ring213.add_zero α inst] at h2
  exact h2

/-- Generic Ring213 `mul_neg`: `a * (-b) = -(a * b)`.  Same shape
    as `neg_mul`, using `mul_add` instead. -/
theorem mul_neg (a b : α) : a * (-b) = -(a * b) := by
  have h1 : a * (-b + b) = a * (0 : α) := by rw [@Ring213.add_left_neg α inst]
  rw [@Ring213.mul_add α inst, mul_zero] at h1
  have h2 : -(a * b) + (a * (-b) + a * b) = -(a * b) + 0 := by rw [h1]
  rw [← @Ring213.add_assoc α inst, @Ring213.add_comm α inst (-(a*b)) (a*(-b)),
      @Ring213.add_assoc α inst, @Ring213.add_left_neg α inst,
      @Ring213.add_zero α inst, @Ring213.add_zero α inst] at h2
  exact h2

/-- Generic Ring213 `neg_neg`: `-(-a) = a`. -/
theorem neg_neg (a : α) : -(-a) = a := by
  have h1 : -(-a) + (-a) = 0 := @Ring213.add_left_neg α inst (-a)
  have h2 : -(-a) + (-a) + a = 0 + a := by rw [h1]
  rw [@Ring213.add_assoc α inst, @Ring213.add_left_neg α inst,
      @Ring213.add_zero α inst, zero_add] at h2
  exact h2

/-- Generic Ring213 `neg_add`: `-(a + b) = -a + -b`.  Derives via
    showing `(a+b) + (-b+-a) = 0`, then unique inverse + add_comm. -/
theorem neg_add (a b : α) : -(a + b) = -a + -b := by
  -- (a + b) + (-b + -a) = 0
  have h_inv : (a + b) + (-b + -a) = 0 := by
    rw [@Ring213.add_assoc α inst a b (-b + -a),
        ← @Ring213.add_assoc α inst b (-b) (-a),
        @Ring213.add_comm α inst b (-b),
        @Ring213.add_left_neg α inst b,
        zero_add,
        @Ring213.add_comm α inst a (-a),
        @Ring213.add_left_neg α inst a]
  -- From h_inv, -(a+b) = -b + -a (unique inverse)
  have h2 : -(a + b) + ((a + b) + (-b + -a)) = -(a + b) + 0 := by rw [h_inv]
  rw [← @Ring213.add_assoc α inst, @Ring213.add_left_neg α inst,
      zero_add, @Ring213.add_zero α inst] at h2
  -- h2 : -b + -a = -(a + b)
  rw [← h2, @Ring213.add_comm α inst (-b) (-a)]

end Ring213

end E213.Theory.Internal.Algebra213
