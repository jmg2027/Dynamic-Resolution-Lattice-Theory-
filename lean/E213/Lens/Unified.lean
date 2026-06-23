import E213.Lens.LensCore
import E213.Lens.Compose.Morphism
import E213.Lens.EqPW

/-!
# Unified — single concept for 213-native equivalence

Synthesis file: bundles the four classical concepts (equivalence
relation, equivalence class, isomorphism, homomorphism) under
the single Lens-arrow concept.  See `theory/lens/unified_equivalence.md`
for the synthesis chapter.

## Contents

  · `LensIso L M`     — bidirectional refinement (= kernel coincidence)
  · `LensFiber L a`   — the equivalence class as a subtype of Raw
  · refl / symm / trans for LensIso
  · `lensIso_iff_kernel_eq` — kernel-equality characterisation
  · `fibers_complete` — every Raw lies in some LensFiber
  · `morphism_is_arrow` — homomorphism → refinement arrow
  · `lensIso_of_eqPW` — DIRTY-recovery P1 (eqPW bridge → LensIso)
  · `lensIso_of_morphism_pair` — P2 (mutual morphism → LensIso)
  · `LensImage`, `LensImage.proj`, `LensImage.proj_val_eq_iff` —
    P3 (Σ-type substitute for `α / L.equiv`, no Quot.sound)

All declarations PURE (∅-axiom).  The reverse `slash-cong →
Lens-kernel` direction (sealed-DIRTY by `STRICT_ZERO_AXIOM.md`
category (b)) lives in `Lens/Universal/QuotLens.lean`.  The Möbius
P-orbit canonical form lives in `Lib/Math/NumberSystems/Real213/Mobius/Mobius213Equiv.lean`
and `Mobius213SternBrocot.lean`.
-/

namespace E213.Lens.Unified

open E213.Theory E213.Lens

/-- **Lens-isomorphism**: two Lenses sit at the same node of
    the `refines` preorder.  Equivalently: their kernels
    coincide.  This is the single 213-native concept of
    isomorphism — `Lens.equiv` agreement under both directions
    of refinement. -/
def LensIso {α β : Type} (L : Lens α) (M : Lens β) : Prop :=
  L.refines M ∧ M.refines L

/-- LensIso reflexivity. -/
theorem lensIso_refl {α : Type} (L : Lens α) : LensIso L L :=
  ⟨L.refines_refl, L.refines_refl⟩

/-- LensIso symmetry. -/
theorem lensIso_symm {α β : Type} {L : Lens α} {M : Lens β} :
    LensIso L M → LensIso M L := fun ⟨h1, h2⟩ => ⟨h2, h1⟩

/-- LensIso transitivity. -/
theorem lensIso_trans {α β γ : Type}
    {L : Lens α} {M : Lens β} {N : Lens γ} :
    LensIso L M → LensIso M N → LensIso L N := fun ⟨h1, h2⟩ ⟨h3, h4⟩ =>
  ⟨Lens.refines_trans h1 h3, Lens.refines_trans h4 h2⟩

/-- **Kernel-equality characterisation**: two Lenses are
    LensIso iff their kernels coincide on every Raw-pair.
    "Iso of equivalence relations" = "bidirectional
    refinement" = "kernel coincidence" — three readings of
    one fact. -/
theorem lensIso_iff_kernel_eq {α β : Type} (L : Lens α) (M : Lens β) :
    LensIso L M ↔ ∀ x y : Raw, L.equiv x y ↔ M.equiv x y := by
  constructor
  · rintro ⟨h1, h2⟩ x y
    exact ⟨h1 x y, h2 x y⟩
  · intro h
    exact ⟨fun x y hxy => (h x y).mp hxy,
           fun x y hxy => (h x y).mpr hxy⟩

/-- **Equivalence class** as a subtype: the fiber of `L.view`
    at a value `a : α`.  This is 213's representation of the
    quotient — no Quot.sound required, just the Raw subtype.
    The equivalence class of `r` is `LensFiber L (L.view r)`. -/
def LensFiber {α : Type} (L : Lens α) (a : α) : Type :=
  { r : Raw // L.view r = a }

/-- Every Raw is canonically a member of its own fiber. -/
def LensFiber.self {α : Type} (L : Lens α) (r : Raw) :
    LensFiber L (L.view r) := ⟨r, rfl⟩

/-- **Fibers cover Raw**: every `r : Raw` belongs to the fiber
    over `L.view r`.  Disjointness is automatic — distinct
    `α`-values cannot share a Raw by `Eq.trans` on `α`. -/
theorem fibers_complete {α : Type} (L : Lens α) (r : Raw) :
    ∃ a : α, Nonempty (LensFiber L a) :=
  ⟨L.view r, ⟨LensFiber.self L r⟩⟩

/-- **Morphism IS an arrow**: an L-M Lens morphism `h` (with
    both combines symmetric) realises the Lens-arrow `L.refines
    M`.  Restatement of `refines_of_morphism` at the unification
    layer.  The homomorphism IS the refinement-arrow witness;
    there is no separate "homomorphism" object — only this arrow. -/
theorem morphism_is_arrow {α β : Type} (L : Lens α) (M : Lens β)
    (h : α → β)
    (hLsym : ∀ u v : α, L.combine u v = L.combine v u)
    (hMsym : ∀ u v : β, M.combine u v = M.combine v u)
    (hmor : E213.Lens.Compose.Morphism.IsLensMorphism h L M) :
    L.refines M :=
  E213.Lens.Compose.Morphism.refines_of_morphism L M h hLsym hMsym hmor

/-! ## DIRTY-recovery helpers

Patterns for replacing DIRTY claims (function-level `Eq` on
Lens combine, classical quotient `Quot.sound`, ∃-quantified
morphism existence) with PURE Lens-arrow statements.  See
`theory/lens/dirty_recovery_patterns.md` for methodology +
worked examples. -/

/-- **P1** (Lens-Eq → LensIso): pointwise Lens equality
    (`Lens.eqPW`, the funext-free PURE substitute for
    `L = M : Lens α`) implies a Lens-isomorphism.  Replaces a
    Cat-1 DIRTY result of the form `L = M : Lens α` by a PURE
    LensIso claim. -/
theorem lensIso_of_eqPW {α : Type} {L M : Lens α}
    (h : L.eqPW M)
    (hLsym : ∀ u v : α, L.combine u v = L.combine v u) :
    LensIso L M := by
  have hview : ∀ r : Raw, L.view r = M.view r :=
    fun r => Lens.eqPW_view_of_sym h hLsym r
  refine ⟨?_, ?_⟩
  · intro x y hxy
    show M.view x = M.view y
    rw [← hview x, ← hview y]; exact hxy
  · intro x y hxy
    show L.view x = L.view y
    rw [hview x, hview y]; exact hxy

/-- **P2** (mutual morphism pair → LensIso): given forward and
    backward Lens-morphisms (each with respect to its
    source-symmetric combine), get LensIso PURE.  Replaces "L
    and M are isomorphic as Lens-algebras" — usually proved via
    function-equality with funext — by an arrow-level claim
    using only the morphism predicate. -/
theorem lensIso_of_morphism_pair {α β : Type}
    (L : Lens α) (M : Lens β) (h : α → β) (k : β → α)
    (hLsym : ∀ u v : α, L.combine u v = L.combine v u)
    (hMsym : ∀ u v : β, M.combine u v = M.combine v u)
    (hLM : E213.Lens.Compose.Morphism.IsLensMorphism h L M)
    (hML : E213.Lens.Compose.Morphism.IsLensMorphism k M L) :
    LensIso L M :=
  ⟨E213.Lens.Compose.Morphism.refines_of_morphism L M h hLsym hMsym hLM,
   E213.Lens.Compose.Morphism.refines_of_morphism M L k hMsym hLsym hML⟩

/-- **P3** (classical quotient → LensImage): the "quotient"
    `Raw / L.equiv` as a Σ-type — values reached by `L.view`
    together with a witness Raw.  No `Quot.sound` required.
    Use in place of `Quot L.equiv` when a quotient type is
    wanted. -/
def LensImage {α : Type} (L : Lens α) : Type :=
  { a : α // ∃ r : Raw, L.view r = a }

/-- Canonical projection `Raw → LensImage L`.  PURE substitute
    for `Quot.mk L.equiv`. -/
def LensImage.proj {α : Type} (L : Lens α) (r : Raw) :
    LensImage L := ⟨L.view r, r, rfl⟩

/-- **Projection-value characterisation**: `proj` values
    coincide iff the Raws share a Lens-kernel.  PURE substitute
    for the `Quot.sound`-based `Quot.mk` equality. -/
theorem LensImage.proj_val_eq_iff {α : Type} (L : Lens α) (x y : Raw) :
    (LensImage.proj L x).val = (LensImage.proj L y).val ↔
      L.equiv x y := Iff.rfl

end E213.Lens.Unified
