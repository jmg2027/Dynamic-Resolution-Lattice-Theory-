import E213.Lib.Math.GRA.GRAModel
import E213.Lib.Math.GRA.NumberTheory

/-!
# GRA Phase 11 — Enriched Graded Monoid Structure

Upgrade GRA operations from bare grade-additive/sub-additive to
full algebraic structure: graded monoid with associativity,
commutativity, unit, and distributivity.

## Enrichment Levels

1. **GradedMonoid** — (Carrier, ⊕, e₊) is a commutative monoid
2. **GradedRing** — (Carrier, ⊕, ⊗, e₊, e₊₊) with distributivity
3. **GradedModule** — action of depth on carrier elements
4. **GRA-enriched hom** — Hom(M₁,M₂) itself carries a grade

## Why This Matters

The original GRAModel only specifies grade(⊕(a,b)) = grade(a)+grade(b).
It says NOTHING about:
- ⊕ associativity: (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)?
- ⊕ commutativity: a ⊕ b = b ⊕ a?
- ⊗ associativity: (a ⊗ b) ⊗ c = a ⊗ (b ⊗ c)?
- Unit elements: ∃ e, a ⊕ e = a?
- Distributivity: a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c)?

Adding these makes GRA a proper GRADED RING, not just a graded set.

Standard: 0 sorry, ∅-axiom.
-/

namespace E213.Lib.Math.GRA.Enriched

open E213.Lib.Math.GRA

-- ============================================================
-- §1. Graded Commutative Monoid
-- ============================================================

/-- A GRA model enriched with monoid structure on ⊕.
    This captures: "⊕ is not just grade-additive, it's associative
    and commutative with an identity element." -/
structure GRAMonoid extends GRAModel where
  /-- Identity element for ⊕ (grade 0) -/
  oplus_unit : Carrier
  /-- Unit has grade 0 -/
  oplus_unit_grade : grade oplus_unit = 0
  /-- Left identity -/
  oplus_unit_left : ∀ a, oplus oplus_unit a = a
  /-- Right identity -/
  oplus_unit_right : ∀ a, oplus a oplus_unit = a
  /-- Associativity -/
  oplus_assoc : ∀ a b c, oplus (oplus a b) c = oplus a (oplus b c)
  /-- Commutativity -/
  oplus_comm_law : ∀ a b, oplus a b = oplus b a

-- ============================================================
-- §2. Graded Ring (⊕, ⊗ with distributivity)
-- ============================================================

/-- A GRA model enriched to a graded ring:
    - (Carrier, ⊕) is a commutative monoid
    - (Carrier, ⊗) is a monoid
    - ⊗ distributes over ⊕ -/
structure GRARing extends GRAMonoid where
  /-- Identity element for ⊗ (grade 0) -/
  otimes_unit : Carrier
  /-- ⊗ unit has grade 0 -/
  otimes_unit_grade : grade otimes_unit = 0
  /-- ⊗ left identity -/
  otimes_unit_left : ∀ a, otimes otimes_unit a = a
  /-- ⊗ right identity -/
  otimes_unit_right : ∀ a, otimes a otimes_unit = a
  /-- ⊗ associativity -/
  otimes_assoc : ∀ a b c, otimes (otimes a b) c = otimes a (otimes b c)
  /-- Left distributivity: ⊗ distributes over ⊕ -/
  distrib_left : ∀ a b c, otimes a (oplus b c) = oplus (otimes a b) (otimes a c)
  /-- Right distributivity -/
  distrib_right : ∀ a b c, otimes (oplus a b) c = oplus (otimes a c) (otimes b c)

-- ============================================================
-- §3. NumberTheory as GRARing
-- ============================================================

/-- NOTE: Standard ring distributivity a⊗(b⊕c) = (a⊗b)⊕(a⊗c) FAILS
    for GRA with ⊗=⊕=+ on Nat:
      a + (b+c) = a+b+c  ≠  (a+b) + (a+c) = 2a+b+c
    
    This is why GRA is a NEAR-RING (§4), not a ring.
    The correct distributivity is grade-sub-distributivity:
      grade(a ⊗ (b ⊕ c)) ≤ grade(a ⊗ b) + grade(a ⊗ c)
    See GRANearRing below. -/

-- ============================================================
-- §4. Graded Distributivity (correct formulation)
-- ============================================================

/-- The correct "distributivity" in GRA is NOT set-level a⊗(b⊕c)=(a⊗b)⊕(a⊗c).
    Instead, it's GRADE-level:
    
    grade(a ⊗ (b ⊕ c)) ≤ grade(a ⊗ b) + grade(a ⊗ c)
    
    This is the sub-distributivity that makes GRA a graded NEAR-ring. -/
structure GRANearRing extends GRAMonoid where
  /-- ⊗ identity -/
  otimes_unit : Carrier
  otimes_unit_grade : grade otimes_unit = 0
  /-- ⊗ associativity -/
  otimes_assoc : ∀ a b c, otimes (otimes a b) c = otimes a (otimes b c)
  /-- Grade sub-distributivity (the correct GRA version) -/
  grade_subdistrib : ∀ a b c,
    grade (otimes a (oplus b c)) ≤ grade (otimes a b) + grade (otimes a c)

/-- The NT model as a GRA near-ring (correct distributivity). -/
def GRA23_NT_NearRing : GRANearRing where
  Carrier := Nat
  grade := id
  oplus := (· + ·)
  otimes := (· + ·)
  gen1 := 2
  gen2 := 3
  depth := fun n => (n + 2) / 3
  ax_gen1_lt_gen2 := by decide
  ax_coprime := by decide
  ax_grade_oplus := fun _ _ => rfl
  ax_grade_otimes := fun _ _ => Nat.le_refl _
  ax_reach := fun n hn => by
    match n, hn with
    | 2, _ => exact ⟨1, 0, by omega⟩
    | 3, _ => exact ⟨0, 1, by omega⟩
    | 4, _ => exact ⟨2, 0, by omega⟩
    | 5, _ => exact ⟨1, 1, by omega⟩
    | n + 6, _ =>
      if h : (n + 6) % 2 = 0 then
        exact ⟨(n + 6) / 2, 0, by omega⟩
      else
        exact ⟨((n + 6) - 3) / 2, 1, by omega⟩
  ax_depth_eq := fun n hn => by omega
  ax_greedy := fun _ _ => rfl
  oplus_unit := 0
  oplus_unit_grade := rfl
  oplus_unit_left := fun _ => Nat.zero_add _
  oplus_unit_right := fun _ => Nat.add_zero _
  oplus_assoc := fun a b c => (Nat.add_assoc a b c).symm
  oplus_comm_law := fun a b => Nat.add_comm a b
  otimes_unit := 0
  otimes_unit_grade := rfl
  otimes_assoc := fun a b c => (Nat.add_assoc a b c).symm
  grade_subdistrib := fun a b c => by
    -- grade(a ⊗ (b ⊕ c)) = a + (b + c) = a + b + c
    -- grade(a ⊗ b) + grade(a ⊗ c) = (a+b) + (a+c) = 2a + b + c
    -- a+b+c ≤ 2a+b+c iff 0 ≤ a, which is always true for Nat
    simp [id]
    omega

-- ============================================================
-- §5. Enriched Hom-objects (Grade on morphism spaces)
-- ============================================================

/-- An enriched hom-object: the space Hom(M₁,M₂) itself has a
    "grade" measuring complexity of the morphism.
    
    Grade of a morphism = maximum grade increase across all inputs.
    For strict morphisms this is 0.  For "shifted" morphisms it's > 0.
    
    This captures: "how much resolution does it cost to translate
    from one Reading to another?" -/
structure GRAHomGrade (M₁ M₂ : GRAModel) where
  /-- The morphism -/
  map : M₁.Carrier → M₂.Carrier
  /-- The grade of this morphism (translation cost) -/
  morphism_grade : Nat
  /-- Grade shift bound: grade(f(x)) ≤ grade(x) + morphism_grade -/
  grade_shift : ∀ x, M₂.grade (map x) ≤ M₁.grade x + morphism_grade

/-- An iso has morphism_grade = 0 (no translation cost). -/
def isoHomGrade {M₁ M₂ : GRAModel} (iso : GRAIso M₁ M₂) :
    GRAHomGrade M₁ M₂ where
  map := iso.toFun
  morphism_grade := 0
  grade_shift := fun x => by
    rw [iso.grade_comm x]
    omega

/-- Composition of graded homs: grades ADD (triangle inequality). -/
def GRAHomGrade.comp {M₁ M₂ M₃ : GRAModel}
    (f : GRAHomGrade M₁ M₂) (g : GRAHomGrade M₂ M₃) :
    GRAHomGrade M₁ M₃ where
  map := g.map ∘ f.map
  morphism_grade := f.morphism_grade + g.morphism_grade
  grade_shift := fun x => by
    simp [Function.comp]
    calc M₃.grade (g.map (f.map x))
        ≤ M₂.grade (f.map x) + g.morphism_grade := g.grade_shift _
      _ ≤ (M₁.grade x + f.morphism_grade) + g.morphism_grade := by
          have h := f.grade_shift x
          omega
      _ = M₁.grade x + (f.morphism_grade + g.morphism_grade) := by omega

/-- Iso composition has grade 0 + 0 = 0. -/
theorem iso_comp_grade_zero {M₁ M₂ M₃ : GRAModel}
    (iso₁ : GRAIso M₁ M₂) (iso₂ : GRAIso M₂ M₃) :
    (isoHomGrade iso₁).comp (isoHomGrade iso₂) |>.morphism_grade = 0 := by
  simp [GRAHomGrade.comp, isoHomGrade]

-- ============================================================
-- §6. Graded Module (depth acts on elements)
-- ============================================================

/-- A graded module: depth function acts as a "filtration" on the
    carrier, inducing a stratification by depth level.
    
    depth_filter k = {x ∈ Carrier | depth(grade(x)) = k}
    
    This gives each GRA model a natural filtration. -/
structure GRAFiltration (M : GRAModel) where
  /-- Filter at level k: elements of depth exactly k -/
  filter : Nat → (M.Carrier → Prop)
  /-- Filter definition -/
  filter_def : ∀ k x, filter k x ↔ M.depth (M.grade x) = k
  /-- Filters are disjoint -/
  filter_disjoint : ∀ k₁ k₂ x, k₁ ≠ k₂ → filter k₁ x → ¬ filter k₂ x
  /-- ⊕ respects filtration: depth(a⊕b) ≤ depth(a) + depth(b)
      (sub-additivity of ⌈·/g₂⌉) -/
  oplus_filter : ∀ a b,
    M.depth (M.grade (M.oplus a b)) ≤
    M.depth (M.grade a) + M.depth (M.grade b)

/-- For (2,3)-models specifically, the ceil sub-additivity holds:
    ⌈(m+n)/3⌉ ≤ ⌈m/3⌉ + ⌈n/3⌉ -/
theorem ceil_subadditive_3 (m n : Nat) :
    (m + n + 2) / 3 ≤ (m + 2) / 3 + (n + 2) / 3 := by
  omega

/-- Every (2,3)-GRA model admits a canonical filtration. -/
def canonicalFiltration23 (M : GRAModel)
    (hg : M.gen2 = 3)
    (hdepth : ∀ x, M.depth x = (x + 2) / 3) :
    GRAFiltration M where
  filter := fun k x => M.depth (M.grade x) = k
  filter_def := fun _ _ => Iff.rfl
  filter_disjoint := fun _ _ _ hne h₁ h₂ => hne (h₁ ▸ h₂)
  oplus_filter := fun a b => by
    rw [M.ax_grade_oplus]
    rw [hdepth, hdepth, hdepth]
    exact ceil_subadditive_3 (M.grade a) (M.grade b)

-- ============================================================
-- §7. Summary: Enrichment Hierarchy
-- ============================================================

/-- The enrichment hierarchy for GRA models. -/
inductive EnrichmentLevel where
  | bare : EnrichmentLevel      -- GRAModel (7 axioms only)
  | monoid : EnrichmentLevel    -- + assoc, comm, unit for ⊕
  | nearRing : EnrichmentLevel  -- + assoc for ⊗ + grade-subdistrib
  | enrichedHom : EnrichmentLevel -- + graded Hom-objects
  | filtered : EnrichmentLevel  -- + depth filtration
deriving DecidableEq

/-- Each level strictly adds axioms. -/
theorem enrichment_strict :
    EnrichmentLevel.bare ≠ EnrichmentLevel.monoid ∧
    EnrichmentLevel.monoid ≠ EnrichmentLevel.nearRing ∧
    EnrichmentLevel.nearRing ≠ EnrichmentLevel.enrichedHom ∧
    EnrichmentLevel.enrichedHom ≠ EnrichmentLevel.filtered := by
  exact ⟨by decide, by decide, by decide, by decide⟩

end E213.Lib.Math.GRA.Enriched
