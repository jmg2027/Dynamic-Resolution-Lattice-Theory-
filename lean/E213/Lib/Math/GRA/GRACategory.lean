import E213.Lib.Math.GRA.GRAModel

/-!
# GRA Phase 10 — Category of GRA Models

Upgrade GRA from a collection of models + isos to a proper CATEGORY:
- Objects: GRAModel
- Morphisms: GRAMorphism (grade-preserving, operation-compatible maps)
- Identity, composition, associativity
- Functors from external categories INTO the GRA category
- Natural transformations between GRA functors

This is the "enriched" foundation: the GRA universality program lives
in a category, and cross-Reading translations are functorial.

## Key Distinctions from Phase 1 (GRAIso)

| GRAIso | GRAMorphism |
|--------|-------------|
| Bijective (toFun + invFun) | One-directional (may forget info) |
| Strict equality on grades | ≤ on grades (grade-non-increasing) |
| — | Surjections, embeddings, projections |
| Category of groupoid | Full category |

Standard: 0 sorry, ∅-axiom.
-/

namespace E213.Lib.Math.GRA.Category

open E213.Lib.Math.GRA

-- ============================================================
-- §1. GRA Morphisms
-- ============================================================

/-- A GRA morphism: a map between carriers that preserves grade
    (weakly: grade non-increasing) and is compatible with ⊕ and ⊗.
    
    Three strength levels:
    - Strict: grade(f(x)) = grade(x) — iso-compatible
    - Weak: grade(f(x)) ≤ grade(x) — projections
    - Lax: grade(f(x)) ≤ grade(x) + k for some bound k -/
structure GRAMorphism (M₁ M₂ : GRAModel) where
  /-- The underlying map -/
  map : M₁.Carrier → M₂.Carrier
  /-- Grade non-increasing (weak preservation) -/
  grade_le : ∀ x, M₂.grade (map x) ≤ M₁.grade x
  /-- Compatible with ⊕ (lax: result ≤) -/
  oplus_compat : ∀ x y,
    M₂.grade (map (M₁.oplus x y)) ≤
    M₂.grade (M₂.oplus (map x) (map y))
    -- NOT strict equality — allows information loss
  /-- Compatible with ⊗ -/
  otimes_compat : ∀ x y,
    M₂.grade (map (M₁.otimes x y)) ≤
    M₂.grade (M₂.otimes (map x) (map y))

/-- A strict GRA morphism: exact grade preservation + strict
    operation compatibility.  This is the "strong" version. -/
structure StrictGRAMorphism (M₁ M₂ : GRAModel) where
  /-- The underlying map -/
  map : M₁.Carrier → M₂.Carrier
  /-- Exact grade preservation -/
  grade_eq : ∀ x, M₂.grade (map x) = M₁.grade x
  /-- Strict ⊕-homomorphism -/
  oplus_hom : ∀ x y, map (M₁.oplus x y) = M₂.oplus (map x) (map y)
  /-- Strict ⊗-homomorphism -/
  otimes_hom : ∀ x y, map (M₁.otimes x y) = M₂.otimes (map x) (map y)

-- ============================================================
-- §2. Every GRAIso induces a StrictGRAMorphism
-- ============================================================

/-- An iso is a strict morphism (forward direction). -/
def GRAIso.toStrictMorphism {M₁ M₂ : GRAModel}
    (iso : GRAIso M₁ M₂) : StrictGRAMorphism M₁ M₂ where
  map := iso.toFun
  grade_eq := fun x => (iso.grade_comm x).symm
  oplus_hom := iso.oplus_comm
  otimes_hom := iso.otimes_comm

/-- An iso is a strict morphism (backward direction). -/
def GRAIso.toStrictMorphismInv {M₁ M₂ : GRAModel}
    (iso : GRAIso M₁ M₂) : StrictGRAMorphism M₂ M₁ where
  map := iso.invFun
  grade_eq := fun y => by
    have h := iso.grade_comm (iso.invFun y)
    rw [iso.right_inv] at h
    exact h.symm
  oplus_hom := fun x y => (iso.symm).oplus_comm x y
  otimes_hom := fun x y => (iso.symm).otimes_comm x y

-- ============================================================
-- §3. Identity and Composition (Category Laws)
-- ============================================================

/-- Identity morphism. -/
def StrictGRAMorphism.id (M : GRAModel) : StrictGRAMorphism M M where
  map := fun x => x
  grade_eq := fun _ => rfl
  oplus_hom := fun _ _ => rfl
  otimes_hom := fun _ _ => rfl

/-- Composition of strict morphisms. -/
def StrictGRAMorphism.comp {M₁ M₂ M₃ : GRAModel}
    (f : StrictGRAMorphism M₁ M₂) (g : StrictGRAMorphism M₂ M₃) :
    StrictGRAMorphism M₁ M₃ where
  map := g.map ∘ f.map
  grade_eq := fun x => by
    simp [Function.comp]
    rw [g.grade_eq, f.grade_eq]
  oplus_hom := fun x y => by
    simp [Function.comp]
    rw [f.oplus_hom, g.oplus_hom]
  otimes_hom := fun x y => by
    simp [Function.comp]
    rw [f.otimes_hom, g.otimes_hom]

/-- Composition is associative. -/
theorem StrictGRAMorphism.comp_assoc {M₁ M₂ M₃ M₄ : GRAModel}
    (f : StrictGRAMorphism M₁ M₂) (g : StrictGRAMorphism M₂ M₃)
    (h : StrictGRAMorphism M₃ M₄) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  rfl

/-- Left identity. -/
theorem StrictGRAMorphism.id_comp {M₁ M₂ : GRAModel}
    (f : StrictGRAMorphism M₁ M₂) :
    (StrictGRAMorphism.id M₁).comp f = f := by
  rfl

/-- Right identity. -/
theorem StrictGRAMorphism.comp_id {M₁ M₂ : GRAModel}
    (f : StrictGRAMorphism M₁ M₂) :
    f.comp (StrictGRAMorphism.id M₂) = f := by
  rfl

-- ============================================================
-- §4. GRA Functor (from indexed family to GRA category)
-- ============================================================

/-- A GRA functor from a Reading index to the GRA category.
    Maps each Reading label to its model and each transition
    to a strict morphism. -/
structure GRAFunctor where
  /-- Object map: index → GRAModel -/
  obj : Nat → GRAModel
  /-- Morphism map: for any i,j with connection, a strict morphism -/
  morph : ∀ i j, StrictGRAMorphism (obj i) (obj j)
  /-- Functoriality: morph i i = id -/
  morph_id : ∀ i, morph i i = StrictGRAMorphism.id (obj i)
  /-- Functoriality: morph i k = (morph i j) ; (morph j k) -/
  morph_comp : ∀ i j k, morph i k = (morph i j).comp (morph j k)

/-- The hub-and-spoke functor: all Readings map through NT. -/
def hubFunctor (models : Nat → GRAModel)
    (isos : ∀ i, GRAIso (models i) NumberTheory.GRA23_NT) :
    GRAFunctor where
  obj := models
  morph := fun i j =>
    (isos i).toStrictMorphism.comp (isos j).toStrictMorphismInv
  morph_id := fun i => by
    simp [StrictGRAMorphism.comp, GRAIso.toStrictMorphism,
          GRAIso.toStrictMorphismInv, StrictGRAMorphism.id]
    constructor
    · funext x; exact (isos i).left_inv x
    · constructor <;> { intros; simp }
  morph_comp := fun i j k => by
    simp [StrictGRAMorphism.comp, GRAIso.toStrictMorphism,
          GRAIso.toStrictMorphismInv]
    constructor
    · funext x
      simp [Function.comp]
      rw [(isos j).left_inv]
    · constructor <;> { intros; simp [Function.comp]; rw [(isos j).left_inv] }

-- ============================================================
-- §5. Natural Transformations between GRA Functors
-- ============================================================

/-- A natural transformation between GRA functors: a family of
    morphisms α_i : F(i) → G(i) commuting with the functor morphisms.
    
    This captures "changing interpretation" (e.g., from one Reading
    assignment to another) while preserving GRA structure. -/
structure GRANatTrans (F G : GRAFunctor) where
  /-- Component at each index -/
  component : ∀ i, StrictGRAMorphism (F.obj i) (G.obj i)
  /-- Naturality square: α_j ∘ F.morph(i,j) = G.morph(i,j) ∘ α_i -/
  naturality : ∀ i j,
    (F.morph i j).comp (component j) = (component i).comp (G.morph i j)

/-- Identity natural transformation. -/
def GRANatTrans.id (F : GRAFunctor) : GRANatTrans F F where
  component := fun i => StrictGRAMorphism.id (F.obj i)
  naturality := fun i j => by
    simp [StrictGRAMorphism.id_comp, StrictGRAMorphism.comp_id]

-- ============================================================
-- §6. GRA Category Summary Structure
-- ============================================================

/-- The GRA category packaged as a single structure.
    Objects = GRAModel, Morphisms = StrictGRAMorphism,
    satisfying identity and composition laws. -/
structure GRACat where
  /-- Category laws verified -/
  comp_assoc : ∀ {M₁ M₂ M₃ M₄ : GRAModel}
    (f : StrictGRAMorphism M₁ M₂) (g : StrictGRAMorphism M₂ M₃)
    (h : StrictGRAMorphism M₃ M₄),
    (f.comp g).comp h = f.comp (g.comp h)
  id_comp : ∀ {M₁ M₂ : GRAModel} (f : StrictGRAMorphism M₁ M₂),
    (StrictGRAMorphism.id M₁).comp f = f
  comp_id : ∀ {M₁ M₂ : GRAModel} (f : StrictGRAMorphism M₁ M₂),
    f.comp (StrictGRAMorphism.id M₂) = f

/-- The GRA category is inhabited (laws hold). -/
def graCat : GRACat where
  comp_assoc := fun f g h => StrictGRAMorphism.comp_assoc f g h
  id_comp := fun f => StrictGRAMorphism.id_comp f
  comp_id := fun f => StrictGRAMorphism.comp_id f

end E213.Lib.Math.GRA.Category
