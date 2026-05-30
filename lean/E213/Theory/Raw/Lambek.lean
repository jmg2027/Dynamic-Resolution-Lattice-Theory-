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

end E213.Theory.Raw.Lambek
