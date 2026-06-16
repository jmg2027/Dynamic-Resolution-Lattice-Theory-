/-!
# The full Tarski theorem: the fixed-point set is a complete lattice (∅-axiom)

Beyond Knaster–Tarski (`Order/KnasterTarski.lean`): for a monotone `f` on a
complete lattice, ANY set `S` of fixed points has a *least fixed point above
it* (`fixJoin`, the join in the fixed-point lattice) and dually a *greatest
fixed point below it* (`fixMeet`).  This is the Tarski content that makes the
fixed points a complete lattice in their own right.

Construction (the join): let `u = lub S`.  The pre-fixed points that lie
`≥ u`, i.e. `{y | le u y ∧ le (f y) y}`, have a glb `j`.  We show `j` is a
fixed point (constrained Knaster argument: `f` carries the interval `[u,⊤]`
into itself), an upper bound of `S`, and the least fixed upper bound.

Pure order-chase: `refl`/`trans`/`antisymm`/`mono`/`glb_lb`/`glb_glb`/
`lub_ub`/`lub_lub`.  No arithmetic, no `funext`, no `Classical`.  The
predicate argument to `glb` is `fun y => le u y ∧ le (f y) y`; the membership
obligations are `And` and are supplied directly.
-/

namespace E213.Lib.Math.Order.TarskiLattice

section Tarski

variable {α : Type}
variable {le : α → α → Prop}
variable {f : α → α}

/-- The **join of a set of fixed points** `S` in the fixed-point lattice:
    with `u = lub S`, the glb of the pre-fixed points lying `≥ u`. -/
def fixJoin (le : α → α → Prop) (glb lub : (α → Prop) → α) (f : α → α)
    (S : α → Prop) : α :=
  glb (fun y => le (lub S) y ∧ le (f y) y)

/-- **`le u (f z)` whenever `le u z`** (here `u = lub S`).  `f` carries the
    interval `[u,⊤]` into itself: each `x ∈ S` is a fixed point with
    `le x u ≤ z`, so `le x (f z)` (mono + `f x = x`), hence `le u (f z)`
    by `lub_lub`. -/
theorem interval_closed
    (lub : (α → Prop) → α)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (lub_ub : ∀ (S : α → Prop) a, S a → le a (lub S))
    (lub_lub : ∀ (S : α → Prop) a, (∀ x, S x → le x a) → le (lub S) a)
    (mono : ∀ a b, le a b → le (f a) (f b))
    (S : α → Prop) (hS : ∀ x, S x → f x = x)
    (z : α) (hz : le (lub S) z) :
    le (lub S) (f z) :=
  lub_lub S (f z)
    (fun x (hx : S x) =>
      have hxu : le x (lub S) := lub_ub S x hx
      have hxz : le x z := trans _ _ _ hxu hz
      have hfxz : le (f x) (f z) := mono _ _ hxz
      -- f x = x, so le x (f z)
      (hS x hx) ▸ hfxz)

/-- **`u ≤ fixJoin S`** (`u = lub S`): every member `y` of the constrained
    pre-fixed set satisfies `le u y` (first conjunct), so `glb_glb`. -/
theorem fixJoin_above_lub
    (glb lub : (α → Prop) → α)
    (glb_glb : ∀ (S : α → Prop) a, (∀ x, S x → le a x) → le a (glb S))
    (S : α → Prop) :
    le (lub S) (fixJoin le glb lub f S) :=
  glb_glb (fun y => le (lub S) y ∧ le (f y) y) (lub S)
    (fun _ hy => hy.1)

/-- **`le (f (fixJoin S)) (fixJoin S)`** — `fixJoin` is pre-fixed.
    For any constrained pre-fixed `y`: `le j y` (glb_lb) ⟹ `le (f j) (f y)`
    (mono) ⟹ `le (f j) y` (trans with `le (f y) y`). -/
theorem fixJoin_prefixed
    (glb lub : (α → Prop) → α)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (glb_lb : ∀ (S : α → Prop) a, S a → le (glb S) a)
    (glb_glb : ∀ (S : α → Prop) a, (∀ x, S x → le a x) → le a (glb S))
    (mono : ∀ a b, le a b → le (f a) (f b))
    (S : α → Prop) :
    le (f (fixJoin le glb lub f S)) (fixJoin le glb lub f S) :=
  glb_glb (fun y => le (lub S) y ∧ le (f y) y)
    (f (fixJoin le glb lub f S))
    (fun y (hy : le (lub S) y ∧ le (f y) y) =>
      have h1 : le (fixJoin le glb lub f S) y :=
        glb_lb (fun y => le (lub S) y ∧ le (f y) y) y hy
      have h2 : le (f (fixJoin le glb lub f S)) (f y) := mono _ _ h1
      trans _ _ _ h2 hy.2)

/-- ★★★ **`f (fixJoin S) = fixJoin S`** — the join of fixed points is itself
    a fixed point.  `(1)` `le (f j) j` is `fixJoin_prefixed`.  `(2)` `le j
    (f j)`: `f j` again lies in the constrained pre-fixed set — `le u (f j)`
    by `interval_closed` (since `le u j`), and `le (f (f j)) (f j)` by mono
    on `(1)` — so `glb_lb` gives `le j (f j)`.  antisymm closes. -/
theorem fixJoin_is_fixed
    (glb lub : (α → Prop) → α)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (antisymm : ∀ a b, le a b → le b a → a = b)
    (lub_ub : ∀ (S : α → Prop) a, S a → le a (lub S))
    (lub_lub : ∀ (S : α → Prop) a, (∀ x, S x → le x a) → le (lub S) a)
    (glb_lb : ∀ (S : α → Prop) a, S a → le (glb S) a)
    (glb_glb : ∀ (S : α → Prop) a, (∀ x, S x → le a x) → le a (glb S))
    (mono : ∀ a b, le a b → le (f a) (f b))
    (S : α → Prop) (hS : ∀ x, S x → f x = x) :
    f (fixJoin le glb lub f S) = fixJoin le glb lub f S :=
  have hpre : le (f (fixJoin le glb lub f S)) (fixJoin le glb lub f S) :=
    fixJoin_prefixed glb lub trans glb_lb glb_glb mono S
  have hu : le (lub S) (fixJoin le glb lub f S) :=
    fixJoin_above_lub glb lub glb_glb S
  -- f j is in the constrained pre-fixed set
  have hu' : le (lub S) (f (fixJoin le glb lub f S)) :=
    interval_closed lub trans lub_ub lub_lub mono S hS
      (fixJoin le glb lub f S) hu
  have hpre' : le (f (f (fixJoin le glb lub f S))) (f (fixJoin le glb lub f S)) :=
    mono _ _ hpre
  have hge : le (fixJoin le glb lub f S) (f (fixJoin le glb lub f S)) :=
    glb_lb (fun y => le (lub S) y ∧ le (f y) y)
      (f (fixJoin le glb lub f S)) ⟨hu', hpre'⟩
  antisymm _ _ hpre hge

/-- ★★★ **`fixJoin S` is an upper bound of `S`**: `le x u ≤ fixJoin S`. -/
theorem fixJoin_ub
    (glb lub : (α → Prop) → α)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (lub_ub : ∀ (S : α → Prop) a, S a → le a (lub S))
    (glb_glb : ∀ (S : α → Prop) a, (∀ x, S x → le a x) → le a (glb S))
    (S : α → Prop)
    (x : α) (hx : S x) :
    le x (fixJoin le glb lub f S) :=
  trans _ _ _ (lub_ub S x hx) (fixJoin_above_lub glb lub glb_glb S)

/-- ★★★ **`fixJoin S` is the LEAST fixed upper bound of `S`**: any fixed
    point `y` above all of `S` has `le (fixJoin S) y`.  `y` lies in the
    constrained pre-fixed set (`le u y` by `lub_lub`; `le (f y) y` from
    `f y = y` + refl), so `glb_lb`. -/
theorem fixJoin_least
    (glb lub : (α → Prop) → α)
    (refl : ∀ a, le a a)
    (lub_lub : ∀ (S : α → Prop) a, (∀ x, S x → le x a) → le (lub S) a)
    (glb_lb : ∀ (S : α → Prop) a, S a → le (glb S) a)
    (S : α → Prop)
    (y : α) (hfy : f y = y) (hub : ∀ x, S x → le x y) :
    le (fixJoin le glb lub f S) y :=
  have hu : le (lub S) y := lub_lub S y hub
  have hfy' : le (f y) y := by show le (f y) y; rw [hfy]; exact refl y
  glb_lb (fun y => le (lub S) y ∧ le (f y) y) y ⟨hu, hfy'⟩

end Tarski

/-! ## Dual: `fixMeet`, the meet of a set of fixed points

With `v = glb S`, the post-fixed points lying `≤ v`, i.e.
`{y | le y (glb S) ∧ le y (f y)}`, have a lub `m`.  `m` is a fixed point, a
lower bound of `S`, and the greatest fixed lower bound.  Dual order-chases. -/

section TarskiDual

variable {α : Type}
variable {le : α → α → Prop}
variable {f : α → α}

/-- The **meet of a set of fixed points** `S`: with `v = glb S`, the lub of
    the post-fixed points lying `≤ v`. -/
def fixMeet (le : α → α → Prop) (glb lub : (α → Prop) → α) (f : α → α)
    (S : α → Prop) : α :=
  lub (fun y => le y (glb S) ∧ le y (f y))

/-- Dual of `interval_closed`: `le (f z) v` whenever `le z v` (`v = glb S`). -/
theorem interval_closed_dual
    (glb : (α → Prop) → α)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (glb_lb : ∀ (S : α → Prop) a, S a → le (glb S) a)
    (glb_glb : ∀ (S : α → Prop) a, (∀ x, S x → le a x) → le a (glb S))
    (mono : ∀ a b, le a b → le (f a) (f b))
    (S : α → Prop) (hS : ∀ x, S x → f x = x)
    (z : α) (hz : le z (glb S)) :
    le (f z) (glb S) :=
  glb_glb S (f z)
    (fun x (hx : S x) =>
      have hvx : le (glb S) x := glb_lb S x hx
      have hzx : le z x := trans _ _ _ hz hvx
      have hfzx : le (f z) (f x) := mono _ _ hzx
      (hS x hx) ▸ hfzx)

/-- Dual of `fixJoin_above_lub`: `fixMeet S ≤ v` (`v = glb S`). -/
theorem fixMeet_below_glb
    (glb lub : (α → Prop) → α)
    (lub_lub : ∀ (S : α → Prop) a, (∀ x, S x → le x a) → le (lub S) a)
    (S : α → Prop) :
    le (fixMeet le glb lub f S) (glb S) :=
  lub_lub (fun y => le y (glb S) ∧ le y (f y)) (glb S)
    (fun _ hy => hy.1)

/-- Dual of `fixJoin_prefixed`: `fixMeet` is post-fixed. -/
theorem fixMeet_postfixed
    (glb lub : (α → Prop) → α)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (lub_ub : ∀ (S : α → Prop) a, S a → le a (lub S))
    (lub_lub : ∀ (S : α → Prop) a, (∀ x, S x → le x a) → le (lub S) a)
    (mono : ∀ a b, le a b → le (f a) (f b))
    (S : α → Prop) :
    le (fixMeet le glb lub f S) (f (fixMeet le glb lub f S)) :=
  lub_lub (fun y => le y (glb S) ∧ le y (f y))
    (f (fixMeet le glb lub f S))
    (fun y (hy : le y (glb S) ∧ le y (f y)) =>
      have h1 : le y (fixMeet le glb lub f S) :=
        lub_ub (fun y => le y (glb S) ∧ le y (f y)) y hy
      have h2 : le (f y) (f (fixMeet le glb lub f S)) := mono _ _ h1
      trans _ _ _ hy.2 h2)

/-- ★★ **`f (fixMeet S) = fixMeet S`** — the meet is a fixed point. -/
theorem fixMeet_is_fixed
    (glb lub : (α → Prop) → α)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (antisymm : ∀ a b, le a b → le b a → a = b)
    (glb_lb : ∀ (S : α → Prop) a, S a → le (glb S) a)
    (glb_glb : ∀ (S : α → Prop) a, (∀ x, S x → le a x) → le a (glb S))
    (lub_ub : ∀ (S : α → Prop) a, S a → le a (lub S))
    (lub_lub : ∀ (S : α → Prop) a, (∀ x, S x → le x a) → le (lub S) a)
    (mono : ∀ a b, le a b → le (f a) (f b))
    (S : α → Prop) (hS : ∀ x, S x → f x = x) :
    f (fixMeet le glb lub f S) = fixMeet le glb lub f S :=
  have hpost : le (fixMeet le glb lub f S) (f (fixMeet le glb lub f S)) :=
    fixMeet_postfixed glb lub trans lub_ub lub_lub mono S
  have hv : le (fixMeet le glb lub f S) (glb S) :=
    fixMeet_below_glb glb lub lub_lub S
  have hv' : le (f (fixMeet le glb lub f S)) (glb S) :=
    interval_closed_dual glb trans glb_lb glb_glb mono S hS
      (fixMeet le glb lub f S) hv
  have hpost' : le (f (fixMeet le glb lub f S)) (f (f (fixMeet le glb lub f S))) :=
    mono _ _ hpost
  have hle : le (f (fixMeet le glb lub f S)) (fixMeet le glb lub f S) :=
    lub_ub (fun y => le y (glb S) ∧ le y (f y))
      (f (fixMeet le glb lub f S)) ⟨hv', hpost'⟩
  antisymm _ _ hle hpost

/-- ★★ **`fixMeet S` is a lower bound of `S`**. -/
theorem fixMeet_lb
    (glb lub : (α → Prop) → α)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (glb_lb : ∀ (S : α → Prop) a, S a → le (glb S) a)
    (lub_lub : ∀ (S : α → Prop) a, (∀ x, S x → le x a) → le (lub S) a)
    (S : α → Prop)
    (x : α) (hx : S x) :
    le (fixMeet le glb lub f S) x :=
  trans _ _ _ (fixMeet_below_glb glb lub lub_lub S) (glb_lb S x hx)

/-- ★★ **`fixMeet S` is the GREATEST fixed lower bound of `S`**. -/
theorem fixMeet_greatest
    (glb lub : (α → Prop) → α)
    (refl : ∀ a, le a a)
    (glb_glb : ∀ (S : α → Prop) a, (∀ x, S x → le a x) → le a (glb S))
    (lub_ub : ∀ (S : α → Prop) a, S a → le a (lub S))
    (S : α → Prop)
    (y : α) (hfy : f y = y) (hlb : ∀ x, S x → le y x) :
    le y (fixMeet le glb lub f S) :=
  have hv : le y (glb S) := glb_glb S y hlb
  have hfy' : le y (f y) := by show le y (f y); rw [hfy]; exact refl y
  lub_ub (fun y => le y (glb S) ∧ le y (f y)) y ⟨hv, hfy'⟩

end TarskiDual

/-! ## Concrete instance: the one-point lattice `α = Unit`

Inhabits the full hypothesis bundle at zero axiom cost (cf. KnasterTarski). -/

section UnitInstance

def uLe : Unit → Unit → Prop := fun _ _ => True
def uGlb : (Unit → Prop) → Unit := fun _ => ()
def uLub : (Unit → Prop) → Unit := fun _ => ()

theorem uLe_refl : ∀ a, uLe a a := fun _ => True.intro
theorem uLe_trans : ∀ a b c, uLe a b → uLe b c → uLe a c :=
  fun _ _ _ _ _ => True.intro
theorem uLe_antisymm : ∀ a b, uLe a b → uLe b a → a = b :=
  fun a b _ _ => by cases a; cases b; rfl
theorem uGlb_lb : ∀ (S : Unit → Prop) a, S a → uLe (uGlb S) a :=
  fun _ _ _ => True.intro
theorem uGlb_glb : ∀ (S : Unit → Prop) a, (∀ x, S x → uLe a x) → uLe a (uGlb S) :=
  fun _ _ _ => True.intro
theorem uLub_ub : ∀ (S : Unit → Prop) a, S a → uLe a (uLub S) :=
  fun _ _ _ => True.intro
theorem uLub_lub : ∀ (S : Unit → Prop) a, (∀ x, S x → uLe x a) → uLe (uLub S) a :=
  fun _ _ _ => True.intro
theorem uMono : ∀ a b, uLe a b → uLe (id a) (id b) :=
  fun _ _ _ => True.intro

/-- Smoke: `fixJoin` is a fixed point at the one-point lattice. -/
theorem unit_fixJoin_is_fixed (S : Unit → Prop) (hS : ∀ x, S x → id x = x) :
    id (fixJoin uLe uGlb uLub id S) = fixJoin uLe uGlb uLub id S :=
  fixJoin_is_fixed (le := uLe) (f := id) uGlb uLub
    uLe_trans uLe_antisymm uLub_ub uLub_lub uGlb_lb uGlb_glb uMono S hS

/-- Smoke: `fixMeet` is a fixed point at the one-point lattice. -/
theorem unit_fixMeet_is_fixed (S : Unit → Prop) (hS : ∀ x, S x → id x = x) :
    id (fixMeet uLe uGlb uLub id S) = fixMeet uLe uGlb uLub id S :=
  fixMeet_is_fixed (le := uLe) (f := id) uGlb uLub
    uLe_trans uLe_antisymm uGlb_lb uGlb_glb uLub_ub uLub_lub uMono S hS

end UnitInstance

end E213.Lib.Math.Order.TarskiLattice
