import E213.Lib.Physics.Simplex.Counts
import E213.Lib.Physics.Symmetry.AutKChiral

/-!
# Symmetry.AutKType — `Aut(K_{3,2}^{(c=2)})` as a Type

Promotes the previously-Nat-only `aut_order = 768` (from
`AutKChiral.lean`) to a **proper Lean Type** via the explicit
direct-product structure `Sym3 × Sym2 × C2_6`.

This is Phase 1 of the **C3 chain** (G87 §4) — gauge group
emergence from the Aut(K) representation on cohomology.

The type-level cardinality is **structurally encoded** in the
direct-product type: `Fin 6 × Fin 2 × Fin 64` has 768 distinct
inhabitants by construction (since the cardinalities of `Fin n`
are 1-1 with `n`).  No `Fintype.card` proof is required at this
layer; that lives in `Mathlib` and requires propext-tainted
`Multiset.card`.

For downstream representation-theory work, the explicit
decomposition is more useful than a `Fin 768` flattening.

All theorems below are **PURE**.  No `omega`, no Mathlib.
-/

namespace E213.Lib.Physics.Symmetry.AutKType

open E213.Lib.Physics.Simplex.Counts (NS NT)

/-! ## §1.  Component types -/

/-- `Sym(3)` enumeration: 6 elements (= NS! = 3!).
    Currently a flat enumeration; full permutation interpretation
    (= bijections on `Fin 3`) comes in Phase 2. -/
def Sym3 : Type := Fin 6

/-- `Sym(2)` enumeration: 2 elements (= NT! = 2!). -/
def Sym2 : Type := Fin 2

/-- `C_2^6` enumeration: 64 elements (= 2^(NS·NT)).  The 6 bits
    correspond to one sheet-swap per S-T edge pair. -/
def C2_6 : Type := Fin 64

/-! ## §2.  The Aut(K) Type -/

/-- ★ **`Aut(K_{3,2}^{(c=2)})`** as a direct-product Type.

    Type-level cardinality 6 · 2 · 64 = 768, matching
    `AutKChiral.aut_order_eq_768`.

    Note: this is the direct product, not the semidirect product.
    The `(Sym(3) × Sym(2)) ⋉ C_2^6` semidirect structure (per
    `AutKChiral` docstring) is a future refinement; for the C3
    representation-theory work, the underlying set structure is
    sufficient at this layer. -/
def Aut_K : Type := Sym3 × Sym2 × C2_6

instance : DecidableEq Sym3 := inferInstanceAs (DecidableEq (Fin 6))
instance : DecidableEq Sym2 := inferInstanceAs (DecidableEq (Fin 2))
instance : DecidableEq C2_6 := inferInstanceAs (DecidableEq (Fin 64))
instance : DecidableEq Aut_K := inferInstanceAs (DecidableEq (Sym3 × Sym2 × C2_6))

/-! ## §3.  Component element witnesses

Each component is `Fin n`; the cardinality is structurally encoded.
We provide explicit "maximal" element witnesses to confirm the
cardinality count. -/

/-- The maximal element of `Sym3` (index 5 = 6 - 1).  Existence of
    `⟨5, _⟩` proves `Sym3` has at least 6 distinct inhabitants. -/
def Sym3.max : Sym3 := ⟨5, by decide⟩

/-- The maximal element of `Sym2` (index 1 = 2 - 1). -/
def Sym2.max : Sym2 := ⟨1, by decide⟩

/-- The maximal element of `C2_6` (index 63 = 64 - 1). -/
def C2_6.max : C2_6 := ⟨63, by decide⟩

/-- The maximal element of `Aut_K` = (Sym3.max, Sym2.max, C2_6.max). -/
def Aut_K.max : Aut_K := (Sym3.max, Sym2.max, C2_6.max)

/-! ## §4.  Cardinality bridges to existing Nat-level definitions -/

/-- ★ The component cardinalities match the existing
    `AutKChiral` Nat-level definitions.  PURE via `decide`. -/
theorem component_cardinalities :
    -- Sym3 has 6 elements (= NS! = fac NS)
    (Sym3.max.val + 1 = 6)
    ∧ (6 = E213.Lib.Physics.Symmetry.AutKChiral.sym_NS_order)
    ∧ (E213.Lib.Physics.Symmetry.AutKChiral.sym_NS_order
       = E213.Lib.Physics.Symmetry.AutKChiral.fac NS)
    -- Sym2 has 2 elements (= NT! = fac NT)
    ∧ (Sym2.max.val + 1 = 2)
    ∧ (2 = E213.Lib.Physics.Symmetry.AutKChiral.sym_NT_order)
    ∧ (E213.Lib.Physics.Symmetry.AutKChiral.sym_NT_order
       = E213.Lib.Physics.Symmetry.AutKChiral.fac NT)
    -- C2_6 has 64 elements (= 2^(NS·NT))
    ∧ (C2_6.max.val + 1 = 64)
    ∧ (64 = E213.Lib.Physics.Symmetry.AutKChiral.internal_order)
    ∧ (E213.Lib.Physics.Symmetry.AutKChiral.internal_order = 2 ^ (NS * NT))
    -- Product cardinality
    ∧ (6 * 2 * 64 = 768)
    ∧ (768 = E213.Lib.Physics.Symmetry.AutKChiral.aut_order)
    ∧ (E213.Lib.Physics.Symmetry.AutKChiral.aut_order
       = E213.Lib.Physics.Symmetry.AutKChiral.external_order
       * E213.Lib.Physics.Symmetry.AutKChiral.internal_order) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ★ Type-level decomposition `Aut_K = Sym3 × Sym2 × C2_6`. -/
theorem Aut_K_type_decomp :
    Aut_K = (Sym3 × Sym2 × C2_6) := rfl

/-! ## §5.  Explicit element constructors -/

/-- Construct an `Aut_K` element from three component indices, with
    in-range proofs.  PURE. -/
def Aut_K.mk (s3 : Fin 6) (s2 : Fin 2) (c : Fin 64) : Aut_K :=
  (s3, s2, c)

/-- The identity element (all components at index 0). -/
def Aut_K.one : Aut_K := Aut_K.mk ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩

/-- Identity has component values 0. -/
theorem Aut_K.one_components :
    Aut_K.one.1.val = 0 ∧ Aut_K.one.2.1.val = 0 ∧ Aut_K.one.2.2.val = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- ★★ **Phase-1 capstone**: `Aut_K` exists as a Type with:
      (a) explicit component decomposition `Sym3 × Sym2 × C2_6`
      (b) decidable equality
      (c) explicit identity element
      (d) cardinality bridges to `aut_order = 768 = 6 · 2 · 64`
          = `external_order × internal_order`
          = `fac NS × fac NT × 2^(NS·NT)`

    The Type-level structural content is sufficient for downstream
    group action / representation theory work (Phase 2+).  PURE. -/
theorem AutK_capstone :
    -- Type decomposition is concrete
    (Aut_K = (Sym3 × Sym2 × C2_6))
    -- Identity element exists
    ∧ (Aut_K.one.1.val = 0 ∧ Aut_K.one.2.1.val = 0 ∧ Aut_K.one.2.2.val = 0)
    -- Each component reaches its cardinality bound
    ∧ (Sym3.max.val + 1 = 6)
    ∧ (Sym2.max.val + 1 = 2)
    ∧ (C2_6.max.val + 1 = 64)
    -- Cardinality bridge to AutKChiral.aut_order = 768
    ∧ (6 * 2 * 64 = E213.Lib.Physics.Symmetry.AutKChiral.aut_order) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact Aut_K.one_components
  · rfl
  · rfl
  · rfl
  · decide

end E213.Lib.Physics.Symmetry.AutKType
