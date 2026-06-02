import E213.Theory.Raw.Rec
import E213.Theory.Raw.Slash
import E213.Theory.Raw.Levels

/-!
# Theory.Raw.Lambek — the pointing act closes as a fixed point (Lambek), and
well-foundedness selects which one

Two distinct closures meet at Raw, and this file separates them:

  1. **Self-fixed-point (Lambek)** — the *pointing act*: Raw is a fixed point
     of its own constructor shape `F(X) = {a} ⊎ {b} ⊎ {x/y : x ≠ y}`.
     `decompose` (Raw → its constructor) and the constructors (build : F → Raw)
     are mutual inverses.  This is the act meeting itself — it holds for *any*
     fixed point of `F`, finite or not.

  2. **Well-founded (μ)** — the *pointed-AT* things: each `slash` is strictly
     deeper than its parts (`depth` drops), so every Raw bottoms out at the
     atoms.  This is the extra fact that picks the *least* fixed point μF out
     of the Lambek fixed points (it excludes any non-well-founded νF inhabitant
     — there is no infinite descent).

So the "1" carries **two** closures, not one: Lambek gives the rotation-shape
(structure = its own image), well-foundedness gives the finite bottom.  Neither
implies the other (Lambek alone holds for νF too); together they pin Raw = μF.
This is the ∅-axiom form of the question "one closure or two?": **two, mutually
supporting.**  See `research-notes/G152_residue_self_covering.md` for the
discussion.

§5 makes the well-foundedness of §2 a *theorem about the descent re-entry*, not only a
per-step measure: the peel relation `IsPart` (a Raw is one of the two parts of a slash) is
**well-founded** (`isPart_wf`) — every chain of peels terminates at an atom, the atoms
being the terminal points (`no_part_of_atom`).  Peeling re-enters the structure at a
strictly shallower part (`part_depth_lt`) and the re-entry **converges** at the floor.
This is the convergence dual of `Lens.ResidueReentry.residue_reentry_never_closes`: the
*same* self-applying re-entry, read on the atomic/Nat-Lens side, closes at the atoms; read
on the predicate/residue side, never closes — two faces of one self-pointing (cf.
`Lens.Bool213.SelfReferenceForms.self_reference_two_forms`).
-/

namespace E213.Theory.Raw.Lambek

open E213.Theory

/-! ## 1. Lambek — Raw is a fixed point of its constructor shape -/

/-- **Exhaustive decomposition** (the forward Lambek map `Raw → F(Raw)`): every
    Raw is an atom or a slash of two distinct Raws.  The "act of pointing" has
    exactly these shapes; nothing else inhabits Raw. -/
theorem decompose (r : Raw) :
    r = Raw.a ∨ r = Raw.b ∨ ∃ (x y : Raw) (h : x ≠ y), r = Raw.slash x y h := by
  induction r using Raw.rec with
  | a => exact Or.inl rfl
  | b => exact Or.inr (Or.inl rfl)
  | slash x y h _ _ => exact Or.inr (Or.inr ⟨x, y, h, rfl⟩)

/-- A slash is never an atom — the slash branch of the constructor is disjoint
    from the atom branches. -/
theorem slash_ne_atoms (x y : Raw) (h : x ≠ y) :
    Raw.slash x y h ≠ Raw.a ∧ Raw.slash x y h ≠ Raw.b :=
  ⟨Raw.slash_ne_a x y h, Raw.slash_ne_b x y h⟩

/-- **Lambek round-trip** (`build ∘ decompose = id`): decomposing a Raw and
    rebuilding with the same constructor returns it.  The witness of
    `decompose` rebuilds `r` (`decompose ∘ build = id` is the `rfl` inside each
    branch).  This is the self-fixed-point: the pointing act applied to its own
    readout is the identity. -/
theorem rebuild (r : Raw) :
    (r = Raw.a) ∨ (r = Raw.b) ∨
    (∃ (x y : Raw) (h : x ≠ y), r = Raw.slash x y h ∧
      Raw.slash x y h = r) := by
  rcases decompose r with ha | hb | ⟨x, y, h, hr⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr ⟨x, y, h, hr, hr.symm⟩)

/-! ## 2. Well-foundedness — the extra fact that selects μF

Lambek (above) holds for any fixed point of the constructor shape, including
non-well-founded ones.  The following strict-descent facts are what exclude
infinite descent and pin Raw to the *least* fixed point. -/

/-- Each `slash` is strictly deeper than either part: `depth` drops on the way
    down.  This is the well-founded measure — there is no infinite descent. -/
theorem depth_drops (x y : Raw) (h : x ≠ y) :
    x.depth < (Raw.slash x y h).depth ∧ y.depth < (Raw.slash x y h).depth := by
  rw [Raw.depth_slash x y h]
  -- `1 + m = m + 1 = m.succ`, and `k ≤ m → k < m.succ`.
  have hlt : ∀ m : Nat, m < 1 + m := by
    intro m; rw [Nat.add_comm]; exact Nat.lt_succ_self m
  -- `NatHelper.le_max_{left,right}` are the propext-free replacements for
  -- `Nat.le_max_{left,right}` (which pull propext).
  constructor
  · calc x.depth ≤ max x.depth y.depth :=
          E213.Tactic.NatHelper.le_max_left _ _
      _ < 1 + max x.depth y.depth := hlt _
  · calc y.depth ≤ max x.depth y.depth :=
          E213.Tactic.NatHelper.le_max_right _ _
      _ < 1 + max x.depth y.depth := hlt _

/-- The atoms are the floor: `depth = 0`.  Combined with `depth_drops`, every
    descent terminates at an atom — Raw is well-founded (= μF). -/
theorem atoms_are_floor : Raw.a.depth = 0 ∧ Raw.b.depth = 0 := ⟨rfl, rfl⟩

/-! ## 3. The two closures, named together -/

/-- ★★ **Two closures, mutually supporting.**  The pointing structure carries
    BOTH a Lambek self-fixed-point (`decompose`: Raw is its own constructor
    image) AND a well-founded floor (`depth_drops` + `atoms_are_floor`: every
    descent terminates).  Lambek alone does not force the floor (it holds for
    non-well-founded fixed points too); the floor is the independent fact that
    selects the least fixed point.  Answer to "one closure or two?": **two** —
    the act's self-coincidence and the finiteness of pointing are distinct, and
    Raw = μF is exactly their conjunction. -/
theorem two_closures :
    -- Lambek: self-fixed-point (exhaustive self-decomposition)
    (∀ r : Raw, r = Raw.a ∨ r = Raw.b ∨
        ∃ (x y : Raw) (h : x ≠ y), r = Raw.slash x y h)
    ∧ -- well-founded: strict descent + atomic floor
    (∀ (x y : Raw) (h : x ≠ y),
        x.depth < (Raw.slash x y h).depth ∧
        y.depth < (Raw.slash x y h).depth)
    ∧ (Raw.a.depth = 0 ∧ Raw.b.depth = 0) :=
  ⟨decompose, depth_drops, atoms_are_floor⟩

/-! ## 4. Self-similar floor — same shape under refinement, descent terminating

The floor is not where the regress stops (it does not stop "by fiat") but what
**keeps the same shape under label-refinement**: peeling one layer off a
non-atom yields two parts that *each again satisfy `decompose`* (same shape),
while their depth strictly drops (the refinement makes progress).  Iterating,
the shape is invariant and the descent terminates only at the atoms.  This is
the formal reading of "what stays the same shape as you descend is the floor." -/

/-- **Self-similar peel.**  A non-atom Raw refines into two parts; each part
    again satisfies `decompose` (the same atom-or-slash shape — *self-similar*),
    and each part is strictly shallower (refinement descends).  "Same shape,
    smaller depth." -/
theorem self_similar_peel (x y : Raw) (h : x ≠ y) :
    -- each part has the same decompose-shape (self-similar)
    ( (x = Raw.a ∨ x = Raw.b ∨ ∃ (u v : Raw) (hu : u ≠ v), x = Raw.slash u v hu)
      ∧ (y = Raw.a ∨ y = Raw.b ∨ ∃ (u v : Raw) (hv : u ≠ v), y = Raw.slash u v hv) )
    ∧ -- and the refinement strictly descends in depth
    ( x.depth < (Raw.slash x y h).depth ∧ y.depth < (Raw.slash x y h).depth ) :=
  ⟨⟨decompose x, decompose y⟩, depth_drops x y h⟩

/-- ★★ **Self-similar floor.**  Bundles the shape-invariance and the terminating
    descent: the decompose-shape `atom ∨ slash` recurs at *every* depth
    (`decompose` holds for all Raw, including the peeled parts), the depth
    strictly drops at each peel (`depth_drops`), and the descent bottoms out at
    the atoms (`atoms_are_floor`).  The "floor" is exactly this fixed shape under
    refinement — invariant form, terminating descent — not a stipulated stop. -/
theorem self_similar_floor :
    -- the decompose-shape is invariant: it holds at every Raw (every depth)
    (∀ r : Raw, r = Raw.a ∨ r = Raw.b ∨
        ∃ (u v : Raw) (h : u ≠ v), r = Raw.slash u v h)
    ∧ -- refinement strictly descends
    (∀ (x y : Raw) (h : x ≠ y),
        x.depth < (Raw.slash x y h).depth ∧ y.depth < (Raw.slash x y h).depth)
    ∧ -- and bottoms out at the atoms (the shape's fixed points: depth 0)
    (Raw.a.depth = 0 ∧ Raw.b.depth = 0) :=
  ⟨decompose, depth_drops, atoms_are_floor⟩

/-! ## 5. The descent re-entry converges — well-foundedness as a theorem

§2 gave well-foundedness as a per-step *measure* (`depth_drops`).  Here it is the actual
**well-foundedness of the peel relation**: peeling a non-atom re-enters the structure at
one of its two strictly-shallower parts, and every such re-entry chain terminates at an
atom.  This is the convergence face of the self-applying re-entry — the dual of the
predicate-side `Lens.ResidueReentry.residue_reentry_never_closes` (which never closes). -/

/-- The **peel (descent) relation**: `c` is a *part* of `p` — `p` is a slash and `c` is
    one of its two parts.  One peel re-enters the structure at a part. -/
def IsPart (c p : Raw) : Prop :=
  ∃ (x y : Raw) (h : x ≠ y), p = Raw.slash x y h ∧ (c = x ∨ c = y)

/-- The atoms are **terminal**: nothing is a part of an atom (atoms do not peel — they are
    the floor where the descent re-entry stops). -/
theorem no_part_of_atom (c : Raw) : ¬ IsPart c Raw.a ∧ ¬ IsPart c Raw.b := by
  refine ⟨?_, ?_⟩
  · rintro ⟨x, y, h, hp, _⟩
    exact (Raw.slash_ne_a x y h) hp.symm
  · rintro ⟨x, y, h, hp, _⟩
    exact (Raw.slash_ne_b x y h) hp.symm

/-- A peel re-enters strictly **shallower**: every part has smaller depth than its whole.
    The re-entry descends — this is the measure behind well-foundedness. -/
theorem part_depth_lt (c p : Raw) (hcp : IsPart c p) : c.depth < p.depth := by
  obtain ⟨x, y, h, hp, hc⟩ := hcp
  subst hp
  rcases hc with hc | hc
  · rw [hc]; exact (depth_drops x y h).1
  · rw [hc]; exact (depth_drops x y h).2

/-- ★★ **The peel relation is well-founded** — every descent re-entry terminates.
    `IsPart` strictly drops the `depth` measure (`part_depth_lt`), so there is no infinite
    descent: each Raw is accessible (reached by finitely many peels from the atoms).  The
    floor is reached in finitely many steps.  Proof: strong induction on a `depth` bound —
    a part is shallower than its bound, so accessibility lifts one layer. -/
theorem isPart_wf : WellFounded IsPart := by
  -- `key n`: every Raw with depth `< n` is accessible.
  have key : ∀ n : Nat, ∀ r : Raw, r.depth < n → Acc IsPart r := by
    intro n
    induction n with
    | zero => intro r hr; exact absurd hr (Nat.not_lt_zero _)
    | succ k ih =>
        intro r hr
        refine Acc.intro r (fun c hc => ?_)
        have hlt : c.depth < r.depth := part_depth_lt c r hc
        exact ih c (Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ hr))
  exact WellFounded.intro (fun r => key (r.depth + 1) r (Nat.lt_succ_self _))

/-- ★★★ **The descent re-entry converges** (the Lambek / Nat-Lens face).  Three facts of
    one downward re-entry:

    1. the atoms are terminal — nothing peels from an atom (`no_part_of_atom`);
    2. every peel re-enters strictly shallower (`part_depth_lt`);
    3. the peel relation is well-founded — every descent chain terminates at the atomic
       floor (`isPart_wf`).

    This is the convergence dual of `Lens.ResidueReentry.residue_reentry_never_closes`: the
    *same* self-applying re-entry, read on the atomic side (peeling toward the floor),
    **closes** at the atoms; read on the predicate/residue side (re-pointing the encoded
    residue), **never closes**.  Two faces of one Raw self-pointing — the bounded,
    terminating descent and the unbounded, escaping ascent. -/
theorem descent_reentry_converges :
    (∀ c : Raw, ¬ IsPart c Raw.a ∧ ¬ IsPart c Raw.b)
    ∧ (∀ c p : Raw, IsPart c p → c.depth < p.depth)
    ∧ WellFounded IsPart :=
  ⟨no_part_of_atom, part_depth_lt, isPart_wf⟩

end E213.Theory.Raw.Lambek
