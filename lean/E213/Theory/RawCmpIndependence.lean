import E213.Theory.Raw.API

/-!
# CmpIndependence: Axiom-independence of the cmp choice

Meta-theorem: the choice of total order `Tree.cmp` for canonical
form is an *encoding* artifact, not part of the axiom.  Any
well-behaved comparison `cmp` (satisfying `CmpProps`) yields a
type `RawBy cmp` bijective with `RawBy Tree.cmp` via a Tree-level
transport.  Hence the 213 axiom is independent of the cmp choice.

## Justification for internal access

This file opens `E213.Term.Internal`.  An **explicit exception**
to the general CLAUDE.md rule ("no Internal open in user code") —
this file itself verifies the axiom-independence of the encoding
scaffolding (Tree, Tree.cmp).

## Contents

  * `CmpProps`                              — abstract well-behaved cmp
  * `Tree.cmp` / `cmpRev` satisfy CmpProps
  * `canonicalBy cmp`, `RawBy cmp`          — cmp-parametric type
  * `RawBy_Tree_cmp_iff`                    — agreement with `Raw`
  * `RawBy.{a, b, slash, slash_comm, rec}`  — polymorphic API
  * `transportTree`                         — Tree-level canonicalisation
  * `transportTree_roundtrip`               — g ∘ f = id on canonical input
  * `transportTree_canonical`               — preserves canonical-by-cmp
  * `transportRawBy` + `transportRawBy_roundtrip`
  * `RawBy_bijection`                       — final closure
-/

namespace E213.Theory.RawCmpIndependence

open E213.Theory
open E213.Term.Internal (Tree Bool.and_eq_true_to_pair)

/-- **CmpProps**: well-behaved order conditions for cmp. -/
structure CmpProps (cmp : Tree → Tree → Ordering) : Prop where
  eq_iff : ∀ x y, cmp x y = .eq ↔ x = y
  swap : ∀ x y, cmp x y = (cmp y x).swap

/-- Tree.cmp satisfies CmpProps. -/
theorem Tree_cmp_props : CmpProps Tree.cmp where
  eq_iff := Tree.cmp_eq_iff
  swap := Tree.cmp_swap

/-- Reverse of cmp: cmpRev x y := (cmp x y).swap. -/
def cmpRev (cmp : Tree → Tree → Ordering) (x y : Tree) : Ordering :=
  (cmp x y).swap

theorem Ordering_swap_swap (o : Ordering) : o.swap.swap = o := by
  cases o <;> rfl

/-- cmpRev also satisfies CmpProps (involutive). -/
theorem cmpRev_props (cmp : Tree → Tree → Ordering) (h : CmpProps cmp) :
    CmpProps (cmpRev cmp) where
  eq_iff := by
    intro x y
    unfold cmpRev
    constructor
    · intro hsw
      have : cmp x y = .eq := by
        cases hcmp : cmp x y with
        | eq => rfl
        | lt => rw [hcmp] at hsw; cases hsw
        | gt => rw [hcmp] at hsw; cases hsw
      exact (h.eq_iff x y).mp this
    · intro hxy
      rw [hxy]
      have : cmp y y = .eq := (h.eq_iff y y).mpr rfl
      rw [this]; rfl
  swap := by
    intro x y
    unfold cmpRev
    rw [h.swap x y, Ordering_swap_swap]

/-- **canonicalBy cmp**: Tree is cmp-canonical (the left child of
    slash is strictly less under cmp). -/
def canonicalBy (cmp : Tree → Tree → Ordering) : Tree → Bool
  | .a => true
  | .b => true
  | .slash x y =>
      canonicalBy cmp x && canonicalBy cmp y &&
      (match cmp x y with | .lt => true | _ => false)

/-- **RawBy cmp**: subtype of cmp-canonical Trees. -/
def RawBy (cmp : Tree → Tree → Ordering) : Type :=
  { t : Tree // canonicalBy cmp t = true }

/-- When using the original Tree.cmp, canonicalBy = Tree.canonical. -/
theorem canonicalBy_Tree_cmp (t : Tree) :
    canonicalBy Tree.cmp t = t.canonical := by
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      unfold canonicalBy Tree.canonical
      rw [ihx, ihy]
      rfl

/-- Therefore the underlying predicate of RawBy Tree.cmp = Tree.canonical. -/
theorem RawBy_Tree_cmp_iff (t : Tree) :
    canonicalBy Tree.cmp t = true ↔ t.canonical = true := by
  rw [canonicalBy_Tree_cmp]

/-- **Polymorphic constructors**: base and slash of RawBy cmp. -/
def RawBy.a (cmp : Tree → Tree → Ordering) : RawBy cmp := ⟨.a, rfl⟩
def RawBy.b (cmp : Tree → Tree → Ordering) : RawBy cmp := ⟨.b, rfl⟩

/-- **Polymorphic slash**: slash of RawBy cmp canonicalized by cmp.
    Generalization of the original Raw.slash. -/
def RawBy.slash (cmp : Tree → Tree → Ordering) (h : CmpProps cmp)
    (x y : RawBy cmp) (hxy : x ≠ y) : RawBy cmp :=
  match hc : cmp x.val y.val with
  | .lt => ⟨.slash x.val y.val, by
      unfold canonicalBy
      rw [x.property, y.property, hc]
      rfl⟩
  | .gt =>
      have hyx : cmp y.val x.val = .lt := by
        have := h.swap x.val y.val
        rw [hc] at this
        cases hyx_val : cmp y.val x.val with
        | lt => rfl
        | eq => rw [hyx_val] at this; cases this
        | gt => rw [hyx_val] at this; cases this
      ⟨.slash y.val x.val, by
        unfold canonicalBy
        rw [x.property, y.property, hyx]
        rfl⟩
  | .eq =>
      have hxy_val : x.val = y.val := (h.eq_iff x.val y.val).mp hc
      absurd (Subtype.ext hxy_val) hxy

/-- **Tree-level slash helper**: Tree slash canonicalized by cmp.
    A helper that extracts the underlying val of RawBy.slash. -/
def slashTree (cmp : Tree → Tree → Ordering) (x y : Tree) : Tree :=
  match cmp x y with
  | .lt => .slash x y
  | .gt => .slash y x
  | .eq => .slash x y

/-- slashTree is commutative (using only CmpProps). -/
theorem slashTree_comm (cmp : Tree → Tree → Ordering) (h : CmpProps cmp)
    (x y : Tree) (hxy : x ≠ y) :
    slashTree cmp x y = slashTree cmp y x := by
  have hsw := h.swap x y
  unfold slashTree
  cases hxy_cmp : cmp x y with
  | lt =>
      have hyx_cmp : cmp y x = .gt := by
        rw [hxy_cmp] at hsw
        cases hyx_val : cmp y x with
        | lt => rw [hyx_val] at hsw; cases hsw
        | eq => rw [hyx_val] at hsw; cases hsw
        | gt => rfl
      rw [hyx_cmp]
  | eq =>
      have hxy_val : x = y := (h.eq_iff x y).mp hxy_cmp
      exact absurd hxy_val hxy
  | gt =>
      have hyx_cmp : cmp y x = .lt := by
        rw [hxy_cmp] at hsw
        cases hyx_val : cmp y x with
        | lt => rfl
        | eq => rw [hyx_val] at hsw; cases hsw
        | gt => rw [hyx_val] at hsw; cases hsw
      rw [hyx_cmp]

/-- val of RawBy.slash = slashTree.  Tree-level equality — all cases. -/
theorem RawBy_slash_val (cmp : Tree → Tree → Ordering) (h : CmpProps cmp)
    (x y : RawBy cmp) (hxy : x ≠ y) :
    (RawBy.slash cmp h x y hxy).val = slashTree cmp x.val y.val := by
  unfold RawBy.slash slashTree
  split
  · rename_i hc
    show x.val.slash y.val = (match cmp x.val y.val with
      | .lt => x.val.slash y.val
      | .gt => y.val.slash x.val
      | .eq => x.val.slash y.val)
    rw [hc]
  · rename_i hc
    show y.val.slash x.val = (match cmp x.val y.val with
      | .lt => x.val.slash y.val
      | .gt => y.val.slash x.val
      | .eq => x.val.slash y.val)
    rw [hc]
  · rename_i hc
    have hxy_val : x.val = y.val := (h.eq_iff x.val y.val).mp hc
    exact absurd (Subtype.ext hxy_val) hxy

/-- **Polymorphic RawBy.slash_comm**: compare vals via Subtype.ext →
    apply slashTree_comm. -/
theorem RawBy.slash_comm (cmp : Tree → Tree → Ordering) (h : CmpProps cmp)
    (x y : RawBy cmp) (hxy : x ≠ y) :
    RawBy.slash cmp h x y hxy = RawBy.slash cmp h y x (Ne.symm hxy) := by
  apply Subtype.ext
  rw [RawBy_slash_val, RawBy_slash_val]
  exact slashTree_comm cmp h x.val y.val
    (fun heq => hxy (Subtype.ext heq))

/-- Extract lt from canonicalBy slash. -/
theorem canonicalBy_slash_lt {cmp : Tree → Tree → Ordering}
    {x y : Tree} (h : canonicalBy cmp (.slash x y) = true) :
    cmp x y = .lt := by
  unfold canonicalBy at h
  obtain ⟨_, hlt_raw⟩ := Bool.and_eq_true_to_pair h
  match hm : cmp x y with
  | .lt => rfl
  | .eq => rw [hm] at hlt_raw; cases hlt_raw
  | .gt => rw [hm] at hlt_raw; cases hlt_raw

/-- Decompose `canonicalBy cmp (.slash x y) = true`: both sub-trees
    are canonicalBy-cmp and `cmp x y = .lt`.  G107 §2 Sub-2 helper
    (canonicalBy variant). -/
theorem canonicalBy_slash_decompose {cmp : Tree → Tree → Ordering}
    {x y : Tree} (h : canonicalBy cmp (.slash x y) = true) :
    canonicalBy cmp x = true ∧ canonicalBy cmp y = true ∧ cmp x y = .lt := by
  have h' := h
  unfold canonicalBy at h'
  obtain ⟨hxy, _⟩ := Bool.and_eq_true_to_pair h'
  obtain ⟨hx, hy⟩ := Bool.and_eq_true_to_pair hxy
  exact ⟨hx, hy, canonicalBy_slash_lt h⟩

/-- **RawBy.recAux**: structural recursion on Tree, canonical
    form re-assembled via cmp-parameterized RawBy.slash. -/
private noncomputable def RawBy.recAux {cmp : Tree → Tree → Ordering}
    (hP : CmpProps cmp)
    {motive : RawBy cmp → Sort u}
    (a_case : motive (RawBy.a cmp))
    (b_case : motive (RawBy.b cmp))
    (slash_case : ∀ (x y : RawBy cmp) (hxy : x ≠ y),
                  motive x → motive y →
                  motive (RawBy.slash cmp hP x y hxy)) :
    ∀ (t : Tree) (hcanon : canonicalBy cmp t = true),
        motive ⟨t, hcanon⟩ := by
  intro t
  induction t with
  | a => intro _; exact a_case
  | b => intro _; exact b_case
  | slash x y ihx ihy =>
      intro hcanon
      have hc := hcanon
      unfold canonicalBy at hc
      obtain ⟨h_xy_and, _⟩ := Bool.and_eq_true_to_pair hc
      obtain ⟨hx, hy⟩ := Bool.and_eq_true_to_pair h_xy_and
      have hcmp := canonicalBy_slash_lt hcanon
      let x' : RawBy cmp := ⟨x, hx⟩
      let y' : RawBy cmp := ⟨y, hy⟩
      have hne : x' ≠ y' := by
        intro heq
        have hxy : x = y := congrArg Subtype.val heq
        rw [hxy] at hcmp
        rw [(hP.eq_iff y y).mpr rfl] at hcmp
        cases hcmp
      have heq : (⟨.slash x y, hcanon⟩ : RawBy cmp) =
                  RawBy.slash cmp hP x' y' hne := by
        apply Subtype.ext
        rw [RawBy_slash_val]
        unfold slashTree
        rw [hcmp]
      rw [heq]
      exact slash_case x' y' hne (ihx hx) (ihy hy)

/-- **Custom RawBy eliminator** (cmp-parameterized). -/
@[elab_as_elim]
noncomputable def RawBy.rec {cmp : Tree → Tree → Ordering}
    (hP : CmpProps cmp)
    {motive : RawBy cmp → Sort u}
    (a_case : motive (RawBy.a cmp))
    (b_case : motive (RawBy.b cmp))
    (slash_case : ∀ (x y : RawBy cmp) (hxy : x ≠ y),
                  motive x → motive y →
                  motive (RawBy.slash cmp hP x y hxy))
    (r : RawBy cmp) : motive r :=
  RawBy.recAux hP a_case b_case slash_case r.val r.property

/-- DecidableEq on RawBy. -/
instance (cmp : Tree → Tree → Ordering) : DecidableEq (RawBy cmp) :=
  fun x y => by
    rcases decEq x.val y.val with hne | heq
    · exact .isFalse (fun h => hne (congrArg Subtype.val h))
    · exact .isTrue (Subtype.ext heq)

/-- **Transport**: RawBy cmp1 → RawBy cmp2 via RawBy.rec.
    The transformation itself is a Lens — a fold using cmp2's
    constructors for base + slash. -/
noncomputable def transport (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2)
    (r : RawBy cmp1) : RawBy cmp2 :=
  RawBy.rec h1 (motive := fun _ => RawBy cmp2)
    (RawBy.a cmp2)
    (RawBy.b cmp2)
    (fun _ _ _ ih_x ih_y =>
      if hne : ih_x ≠ ih_y then RawBy.slash cmp2 h2 ih_x ih_y hne
      else RawBy.a cmp2)
    r

/-- transport of RawBy.a. -/
theorem transport_a (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2) :
    transport cmp1 cmp2 h1 h2 (RawBy.a cmp1) = RawBy.a cmp2 := rfl

/-- transport of RawBy.b. -/
theorem transport_b (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2) :
    transport cmp1 cmp2 h1 h2 (RawBy.b cmp1) = RawBy.b cmp2 := rfl

/-- **Tree-level transport**: canonicalize Tree under cmp2.
    Computable, inductively defined on Tree.

    A direct Tree-level transport sidesteps the reduction obstacles of
    the noncomputable `RawBy.rec` (universe constraints, match-branch
    `.val` projections, `Eq.mpr` cleanup from rewrites). -/
def transportTree (cmp2 : Tree → Tree → Ordering) : Tree → Tree
  | .a => .a
  | .b => .b
  | .slash x y => slashTree cmp2 (transportTree cmp2 x) (transportTree cmp2 y)

/-- transportTree reductions (computable, automatic). -/
theorem transportTree_a (cmp2 : Tree → Tree → Ordering) :
    transportTree cmp2 .a = .a := rfl

theorem transportTree_b (cmp2 : Tree → Tree → Ordering) :
    transportTree cmp2 .b = .b := rfl

theorem transportTree_slash (cmp2 : Tree → Tree → Ordering) (x y : Tree) :
    transportTree cmp2 (.slash x y)
      = slashTree cmp2 (transportTree cmp2 x) (transportTree cmp2 y) := rfl

/-- Key consequence of slashTree commutativity: result for canonical input. -/
theorem slashTree_canonical_input {cmp : Tree → Tree → Ordering}
    (h : CmpProps cmp) (s u : Tree) (hsu : cmp s u = .lt) :
    slashTree cmp s u = .slash s u := by
  unfold slashTree; rw [hsu]

/-- slashTree of {a, b} = canonical .slash result. -/
theorem slashTree_of_pair_eq {cmp : Tree → Tree → Ordering}
    (h : CmpProps cmp) (s u p q : Tree) (hsu : cmp s u = .lt)
    (hpair : (p = s ∧ q = u) ∨ (p = u ∧ q = s)) :
    slashTree cmp p q = .slash s u := by
  rcases hpair with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [hp, hq]; exact slashTree_canonical_input h s u hsu
  · rw [hp, hq]
    have hus : cmp u s = .gt := by
      have hsw := h.swap s u
      rw [hsu] at hsw
      cases hus_val : cmp u s with
      | lt => rw [hus_val] at hsw; cases hsw
      | eq => rw [hus_val] at hsw; cases hsw
      | gt => rfl
    unfold slashTree
    rw [hus]

/-- **Round-trip on canonical**: f(g(t)) = t for canonical-by-cmp2 t.
    f := transportTree cmp2, g := transportTree cmp1. -/
theorem transportTree_roundtrip
    (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2)
    (t : Tree) (hcanon : canonicalBy cmp2 t = true) :
    transportTree cmp2 (transportTree cmp1 t) = t := by
  induction t with
  | a => rfl
  | b => rfl
  | slash s u ihs ihu =>
      obtain ⟨hcs, hcu, hsu⟩ := canonicalBy_slash_decompose hcanon
      have ihs' := ihs hcs
      have ihu' := ihu hcu
      rw [transportTree_slash]
      cases hcmp1 : cmp1 (transportTree cmp1 s) (transportTree cmp1 u) with
      | lt =>
          have h_st : slashTree cmp1 (transportTree cmp1 s)
                        (transportTree cmp1 u)
                    = .slash (transportTree cmp1 s) (transportTree cmp1 u) := by
            unfold slashTree; rw [hcmp1]
          rw [h_st, transportTree_slash, ihs', ihu']
          unfold slashTree; rw [hsu]
      | gt =>
          have h_st : slashTree cmp1 (transportTree cmp1 s)
                        (transportTree cmp1 u)
                    = .slash (transportTree cmp1 u) (transportTree cmp1 s) := by
            unfold slashTree; rw [hcmp1]
          rw [h_st, transportTree_slash, ihs', ihu']
          have hus : cmp2 u s = .gt := by
            have hsw := h2.swap s u
            rw [hsu] at hsw
            cases hus_val : cmp2 u s with
            | lt => rw [hus_val] at hsw; cases hsw
            | eq => rw [hus_val] at hsw; cases hsw
            | gt => rfl
          unfold slashTree; rw [hus]
      | eq =>
          have hpq : transportTree cmp1 s = transportTree cmp1 u :=
            (h1.eq_iff _ _).mp hcmp1
          have hsu_eq : s = u := by
            have := ihs'
            rw [hpq] at this
            rw [ihu'] at this
            exact this.symm
          rw [hsu_eq] at hsu
          rw [(h2.eq_iff u u).mpr rfl] at hsu
          cases hsu

/-- transportTree maps canonical-by-cmp1 → canonical-by-cmp2.
    Injectivity derived via symmetric application of g∘f = id. -/
theorem transportTree_canonical
    (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2)
    (t : Tree) (hcanon1 : canonicalBy cmp1 t = true) :
    canonicalBy cmp2 (transportTree cmp2 t) = true := by
  induction t with
  | a => rfl
  | b => rfl
  | slash s u ihs ihu =>
      obtain ⟨hcs, hcu, hsu1⟩ := canonicalBy_slash_decompose hcanon1
      have ihs' := ihs hcs
      have ihu' := ihu hcu
      -- transportTree cmp2 s, u canonical-by-cmp2 (IH).
      -- f s ≠ f u: by g∘f = id.
      have hsu_ne : s ≠ u := by
        intro heq
        rw [heq] at hsu1
        rw [(h1.eq_iff u u).mpr rfl] at hsu1
        cases hsu1
      have hfs_ne : transportTree cmp2 s ≠ transportTree cmp2 u := by
        intro hfeq
        -- By transportTree_roundtrip cmp2 cmp1: g(f s) = s, g(f u) = u.
        have hgs := transportTree_roundtrip cmp2 cmp1 h2 h1 s hcs
        have hgu := transportTree_roundtrip cmp2 cmp1 h2 h1 u hcu
        rw [hfeq] at hgs
        rw [hgu] at hgs
        exact hsu_ne hgs.symm
      rw [transportTree_slash]
      -- slashTree cmp2 (f s) (f u) canonical (children canonical, order from cmp2).
      unfold slashTree
      cases hcmp2 : cmp2 (transportTree cmp2 s) (transportTree cmp2 u) with
      | lt =>
          unfold canonicalBy
          rw [ihs', ihu', hcmp2]
          rfl
      | eq =>
          have : transportTree cmp2 s = transportTree cmp2 u :=
            (h2.eq_iff _ _).mp hcmp2
          exact absurd this hfs_ne
      | gt =>
          unfold canonicalBy
          rw [ihs', ihu']
          have hus : cmp2 (transportTree cmp2 u) (transportTree cmp2 s) = .lt := by
            have hsw := h2.swap (transportTree cmp2 s) (transportTree cmp2 u)
            rw [hcmp2] at hsw
            cases hus_val : cmp2 (transportTree cmp2 u) (transportTree cmp2 s) with
            | lt => rfl
            | eq => rw [hus_val] at hsw; cases hsw
            | gt => rw [hus_val] at hsw; cases hsw
          rw [hus]
          rfl

/-- **Forward bijection**: RawBy cmp1 → RawBy cmp2 via transportTree. -/
def transportRawBy (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2)
    (r : RawBy cmp1) : RawBy cmp2 :=
  ⟨transportTree cmp2 r.val,
   transportTree_canonical cmp1 cmp2 h1 h2 r.val r.property⟩

/-- **Bijection theorem**: transportRawBy is a bijection with inverse.
    f∘g = id, g∘f = id. -/
theorem transportRawBy_roundtrip
    (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2)
    (r : RawBy cmp2) :
    transportRawBy cmp1 cmp2 h1 h2
      (transportRawBy cmp2 cmp1 h2 h1 r) = r := by
  apply Subtype.ext
  show transportTree cmp2 (transportTree cmp1 r.val) = r.val
  exact transportTree_roundtrip cmp1 cmp2 h1 h2 r.val r.property

/-- **Final**: RawBy cmp1 ≃ RawBy cmp2 (inverse via roundtrip).
    Formal closing of the cmp-independence meta theorem. -/
theorem RawBy_bijection (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2) :
    ∀ (r : RawBy cmp2),
        transportRawBy cmp1 cmp2 h1 h2
          (transportRawBy cmp2 cmp1 h2 h1 r) = r :=
  transportRawBy_roundtrip cmp1 cmp2 h1 h2

end E213.Theory.RawCmpIndependence
