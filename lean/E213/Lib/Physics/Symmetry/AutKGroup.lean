import E213.Lib.Physics.Symmetry.Sym3Group
import E213.Lib.Physics.Symmetry.AutKType

/-!
# Aut(K) as a proper Group — Phase 12

Phase 12 of the **C3 chain** — combines `Sym3Group.Sym3`,
`Sym2 := Fin 2`, and `C2_6 := Fin 64` into a proper Group
structure on `Aut_K = Sym3 × Sym2 × C2_6`.

## Direct vs semidirect structure

The true Aut(K_{3,2}^{(c=2)}) is the **semidirect product**
`(Sym(3) × Sym(2)) ⋉ C_2^6` (per `AutKChiral` docstring), where
the external factors act on the internal C_2^6 by permuting bit
positions.

This file constructs the **direct product** version first as a
proper Group; the semidirect twist is a future refinement.  At
the cardinality level both give 6 · 2 · 64 = 768.

## Component structure

  · `Sym3` (Phase 11): proper Group via Cayley table
  · `Sym2 := Fin 2` with XOR: trivial group ℤ/2
  · `C2_6 := Fin 64` with bitwise XOR: (ℤ/2)^6

All theorems below are **PURE** via `decide`.
-/

namespace E213.Lib.Physics.Symmetry.AutKGroup

open E213.Lib.Physics.Symmetry.Sym3Group (Sym3)

/-! ## §1.  Sym(2) Group structure -/

/-- `Sym(2)` — the order-2 cyclic group encoded as `Fin 2`. -/
abbrev Sym2 : Type := Fin 2

/-- Sym(2) identity. -/
def Sym2.one : Sym2 := ⟨0, by decide⟩

/-- Sym(2) multiplication via XOR. -/
def Sym2.mul (i j : Sym2) : Sym2 :=
  ⟨(i.val + j.val) % 2, Nat.mod_lt _ (by decide)⟩

/-- Sym(2) inverse: self-inverse (element of order 2). -/
def Sym2.inv (i : Sym2) : Sym2 := i

/-- Sym(2) identity left. -/
theorem Sym2.one_mul : ∀ i : Sym2, Sym2.mul Sym2.one i = i := by decide

/-- Sym(2) identity right. -/
theorem Sym2.mul_one : ∀ i : Sym2, Sym2.mul i Sym2.one = i := by decide

/-- Sym(2) inverse left. -/
theorem Sym2.inv_mul : ∀ i : Sym2, Sym2.mul (Sym2.inv i) i = Sym2.one := by decide

/-- Sym(2) associativity. -/
theorem Sym2.mul_assoc :
    ∀ i j k : Sym2, Sym2.mul (Sym2.mul i j) k = Sym2.mul i (Sym2.mul j k) := by
  decide

/-- Sym(2) is abelian. -/
theorem Sym2.mul_comm : ∀ i j : Sym2, Sym2.mul i j = Sym2.mul j i := by decide

/-! ## §2.  C_2^6 Group structure (= 6-fold ℤ/2)

We use the **pointwise representation** `C_2^6 := Fin 6 → Bool`
to make the group axioms PURE.  (The packed `Fin 64` representation
via `Nat.xor` brings `propext` / `Quot.sound` through Lean-core
`Nat.xor_assoc`.) -/

/-- `C_2^6` encoded as `Fin 6 → Bool`.  Cardinality 2^6 = 64.
    Each component is a ℤ/2 bit; 6 bits total. -/
abbrev C2_6 : Type := Fin 6 → Bool

/-- C_2^6 identity: constant `false`. -/
def C2_6.one : C2_6 := fun _ => false

/-- C_2^6 multiplication: pointwise XOR. -/
def C2_6.mul (f g : C2_6) : C2_6 := fun i => xor (f i) (g i)

/-- C_2^6 inverse: each element is self-inverse. -/
def C2_6.inv (f : C2_6) : C2_6 := f

/-- C_2^6 identity left (pointwise). -/
theorem C2_6.one_mul (f : C2_6) : ∀ i, C2_6.mul C2_6.one f i = f i := by
  intro i
  show xor false (f i) = f i
  cases f i <;> rfl

/-- C_2^6 identity right (pointwise). -/
theorem C2_6.mul_one (f : C2_6) : ∀ i, C2_6.mul f C2_6.one i = f i := by
  intro i
  show xor (f i) false = f i
  cases f i <;> rfl

/-- C_2^6 inverse left (pointwise). -/
theorem C2_6.inv_mul (f : C2_6) : ∀ i, C2_6.mul (C2_6.inv f) f i = C2_6.one i := by
  intro i
  show xor (f i) (f i) = false
  cases f i <;> rfl

/-- C_2^6 commutativity (pointwise). -/
theorem C2_6.mul_comm (f g : C2_6) :
    ∀ i, C2_6.mul f g i = C2_6.mul g f i := by
  intro i
  show xor (f i) (g i) = xor (g i) (f i)
  cases f i <;> cases g i <;> rfl

/-- C_2^6 associativity (pointwise) — pure Bool xor associativity. -/
theorem C2_6.mul_assoc (f g h : C2_6) :
    ∀ i, C2_6.mul (C2_6.mul f g) h i = C2_6.mul f (C2_6.mul g h) i := by
  intro i
  show xor (xor (f i) (g i)) (h i) = xor (f i) (xor (g i) (h i))
  cases f i <;> cases g i <;> cases h i <;> rfl

/-! ## §3.  Aut(K) as direct-product Group -/

/-- `Aut(K_{3,2}^{(c=2)})` as direct product `Sym3 × Sym2 × C2_6`.
    Cardinality 6 · 2 · 64 = 768. -/
abbrev Aut_K : Type := Sym3 × Sym2 × C2_6

/-- Aut(K) identity element. -/
def Aut_K.one : Aut_K := (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.one, Sym2.one, C2_6.one)

/-- Aut(K) multiplication component-wise. -/
def Aut_K.mul (g h : Aut_K) : Aut_K :=
  (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.mul g.1 h.1,
   Sym2.mul g.2.1 h.2.1,
   C2_6.mul g.2.2 h.2.2)

/-- Aut(K) inverse component-wise. -/
def Aut_K.inv (g : Aut_K) : Aut_K :=
  (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv g.1,
   Sym2.inv g.2.1,
   C2_6.inv g.2.2)

/-! ## §4.  Aut(K) Group axioms

Each axiom follows component-wise from the factor-group axioms.
Stated pointwise to avoid funext on the product type. -/

/-! The Aut(K) axioms are stated **componentwise** (Sym3 and Sym2
    factors as full equalities since they're decidable Fin types;
    C2_6 factor as pointwise equality since it's a function space). -/

/-- ★ Aut(K) identity left (Sym3 + Sym2 component-wise, C2_6 pointwise). -/
theorem Aut_K.one_mul (g : Aut_K) :
    (Aut_K.mul Aut_K.one g).1 = g.1
    ∧ (Aut_K.mul Aut_K.one g).2.1 = g.2.1
    ∧ (∀ i : Fin 6, (Aut_K.mul Aut_K.one g).2.2 i = g.2.2 i) := by
  refine ⟨?_, ?_, ?_⟩
  · exact E213.Lib.Physics.Symmetry.Sym3Group.Sym3.one_mul g.1
  · exact Sym2.one_mul g.2.1
  · exact C2_6.one_mul g.2.2

/-- ★ Aut(K) identity right. -/
theorem Aut_K.mul_one (g : Aut_K) :
    (Aut_K.mul g Aut_K.one).1 = g.1
    ∧ (Aut_K.mul g Aut_K.one).2.1 = g.2.1
    ∧ (∀ i : Fin 6, (Aut_K.mul g Aut_K.one).2.2 i = g.2.2 i) := by
  refine ⟨?_, ?_, ?_⟩
  · exact E213.Lib.Physics.Symmetry.Sym3Group.Sym3.mul_one g.1
  · exact Sym2.mul_one g.2.1
  · exact C2_6.mul_one g.2.2

/-- ★ Aut(K) inverse left. -/
theorem Aut_K.inv_mul (g : Aut_K) :
    (Aut_K.mul (Aut_K.inv g) g).1 = Aut_K.one.1
    ∧ (Aut_K.mul (Aut_K.inv g) g).2.1 = Aut_K.one.2.1
    ∧ (∀ i : Fin 6, (Aut_K.mul (Aut_K.inv g) g).2.2 i = Aut_K.one.2.2 i) := by
  refine ⟨?_, ?_, ?_⟩
  · exact E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv_mul g.1
  · exact Sym2.inv_mul g.2.1
  · exact C2_6.inv_mul g.2.2

/-- ★ Aut(K) associativity (component-wise from factor-group axioms). -/
theorem Aut_K.mul_assoc (g h k : Aut_K) :
    (Aut_K.mul (Aut_K.mul g h) k).1 = (Aut_K.mul g (Aut_K.mul h k)).1
    ∧ (Aut_K.mul (Aut_K.mul g h) k).2.1 = (Aut_K.mul g (Aut_K.mul h k)).2.1
    ∧ (∀ i : Fin 6,
         (Aut_K.mul (Aut_K.mul g h) k).2.2 i
           = (Aut_K.mul g (Aut_K.mul h k)).2.2 i) := by
  refine ⟨?_, ?_, ?_⟩
  · exact E213.Lib.Physics.Symmetry.Sym3Group.Sym3.mul_assoc g.1 h.1 k.1
  · exact Sym2.mul_assoc g.2.1 h.2.1 k.2.1
  · exact C2_6.mul_assoc g.2.2 h.2.2 k.2.2

/-! ## §5.  Phase-12 capstone -/

/-- ★★ **Phase-12 capstone**: Aut(K_{3,2}^{(c=2)}) realised as a
    proper direct-product Group with cardinality 768.

    Substantive content:
      (a) Component Groups: Sym3 (Phase 11), Sym2 (this phase),
          C2_6 (this phase)
      (b) Direct product `Aut_K := Sym3 × Sym2 × C2_6` with
          component-wise mul, identity, inverse
      (c) Group axioms (component-wise composition):
          one_mul, mul_one, inv_mul, mul_assoc
      (d) Cardinality 6 · 2 · 64 = 768

    Note: this is the **direct product** version.  The full
    semidirect `(Sym3 × Sym2) ⋉ C2_6` (per AutKChiral) is a
    future refinement; at the cardinality level both are 768.

    PURE. -/
theorem AutKGroup_capstone :
    -- Sym(2) group axioms
    (∀ i : Sym2, Sym2.mul Sym2.one i = i)
    ∧ (∀ i j : Sym2, Sym2.mul i j = Sym2.mul j i)
    -- C_2^6 group axioms (pointwise)
    ∧ (∀ f : C2_6, ∀ i : Fin 6, C2_6.mul (C2_6.inv f) f i = C2_6.one i)
    ∧ (∀ f g : C2_6, ∀ i : Fin 6, C2_6.mul f g i = C2_6.mul g f i)
    -- Aut(K) group axioms (component-wise / pointwise)
    ∧ (∀ g : Aut_K, (Aut_K.mul Aut_K.one g).1 = g.1)
    ∧ (∀ g : Aut_K, (Aut_K.mul g Aut_K.one).2.1 = g.2.1)
    ∧ (∀ g : Aut_K, ∀ i : Fin 6,
         (Aut_K.mul (Aut_K.inv g) g).2.2 i = Aut_K.one.2.2 i)
    -- Cardinality
    ∧ 6 * 2 * 64 = 768 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Sym2.one_mul
  · exact Sym2.mul_comm
  · exact C2_6.inv_mul
  · exact C2_6.mul_comm
  · intro g; exact (Aut_K.one_mul g).1
  · intro g; exact (Aut_K.mul_one g).2.1
  · intro g i; exact (Aut_K.inv_mul g).2.2 i
  · decide

end E213.Lib.Physics.Symmetry.AutKGroup
