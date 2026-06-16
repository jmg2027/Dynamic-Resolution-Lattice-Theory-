/-!
# Knaster–Tarski fixed-point theorem (parametrized, ∅-axiom)

A monotone map `f` on a complete lattice has a **least fixed point**, the
greatest-lower-bound of its pre-fixed points `{x | f x ≤ x}`.

The complete lattice is given by an *explicit* relation parameter `le`
with its order axioms plus a set-indexed infimum `glb : (α → Prop) → α`
(the greatest lower bound of the predicate-defined set), with its two
defining properties.  No typeclass, no bundled structure, no Mathlib —
the same idiom as the sibling `Order/{GaloisConnection,BooleanAlgebra}`.

Everything below is a pure order-chase using only
`refl`/`trans`/`antisymm`/`mono`/`glb_lb`/`glb_glb`.  No arithmetic, no
`funext`, no `Classical`.  The predicate-set argument to `glb` is
`(fun x => le (f x) x)`; `glb_lb`/`glb_glb` applied at this predicate use
that `S a` for `S = fun x => le (f x) x` is `le (f a) a` *definitionally*
(beta), so the membership obligations are supplied directly.
-/

namespace E213.Lib.Math.Order.KnasterTarski

section KnasterTarski

variable {α : Type}
variable {le : α → α → Prop}
variable {f : α → α}

/-- The **least fixed point**: the glb of the pre-fixed points
    `{x | le (f x) x}`. -/
def lfp (le : α → α → Prop) (glb : (α → Prop) → α) (f : α → α) : α :=
  glb (fun x => le (f x) x)

/-- **`f lfp ≤ lfp`** — `f lfp` is a lower bound of the pre-fixed points.

    For any pre-fixed point `x` (`le (f x) x`): `le lfp x` (glb_lb) ⟹
    `le (f lfp) (f x)` (mono) ⟹ `le (f lfp) x` (trans).  So `f lfp` is a
    lower bound of all pre-fixed points ⟹ `le (f lfp) lfp` (glb_glb). -/
theorem lfp_prefixed
    (glb : (α → Prop) → α)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (glb_lb : ∀ (S : α → Prop) a, S a → le (glb S) a)
    (glb_glb : ∀ (S : α → Prop) a, (∀ x, S x → le a x) → le a (glb S))
    (mono : ∀ a b, le a b → le (f a) (f b)) :
    le (f (lfp le glb f)) (lfp le glb f) :=
  glb_glb (fun x => le (f x) x) (f (lfp le glb f))
    (fun x (hx : le (f x) x) =>
      -- lfp ≤ x  (x is a pre-fixed point)
      have h1 : le (lfp le glb f) x := glb_lb (fun x => le (f x) x) x hx
      -- f lfp ≤ f x
      have h2 : le (f (lfp le glb f)) (f x) := mono _ _ h1
      -- f lfp ≤ x  (compose with hx : f x ≤ x)
      trans _ _ _ h2 hx)

/-- ★★★ **`f lfp = lfp`** — `lfp` IS a fixed point.

    (1) `le (f lfp) lfp` is `lfp_prefixed`.  (2) `le lfp (f lfp)`: from (1)
    + mono, `le (f (f lfp)) (f lfp)`, so `f lfp` is itself a pre-fixed
    point ⟹ `le lfp (f lfp)` (glb_lb).  antisymm closes it. -/
theorem lfp_fixed
    (glb : (α → Prop) → α)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (antisymm : ∀ a b, le a b → le b a → a = b)
    (glb_lb : ∀ (S : α → Prop) a, S a → le (glb S) a)
    (glb_glb : ∀ (S : α → Prop) a, (∀ x, S x → le a x) → le a (glb S))
    (mono : ∀ a b, le a b → le (f a) (f b)) :
    f (lfp le glb f) = lfp le glb f :=
  have h1 : le (f (lfp le glb f)) (lfp le glb f) :=
    lfp_prefixed glb trans glb_lb glb_glb mono
  -- f lfp is a pre-fixed point: f (f lfp) ≤ f lfp
  have h2 : le (f (f (lfp le glb f))) (f (lfp le glb f)) := mono _ _ h1
  -- so lfp ≤ f lfp by glb_lb at the pre-fixed-point predicate
  have h3 : le (lfp le glb f) (f (lfp le glb f)) :=
    glb_lb (fun x => le (f x) x) (f (lfp le glb f)) h2
  antisymm _ _ h1 h3

/-- ★★ **`lfp ≤` every PRE-fixed point**.  Directly `glb_lb`. -/
theorem lfp_least_prefixed
    (glb : (α → Prop) → α)
    (glb_lb : ∀ (S : α → Prop) a, S a → le (glb S) a)
    (a : α) (h : le (f a) a) :
    le (lfp le glb f) a :=
  glb_lb (fun x => le (f x) x) a h

/-- ★★★ **`lfp ≤` every fixed point** — `lfp` is the LEAST fixed point.

    A fixed point is a pre-fixed point: `f a = a ⟹ le (f a) a` by `refl`
    (rewriting the goal `le (f a) a` to `le a a`).  Then `glb_lb`. -/
theorem lfp_least
    (glb : (α → Prop) → α)
    (refl : ∀ a, le a a)
    (glb_lb : ∀ (S : α → Prop) a, S a → le (glb S) a)
    (a : α) (h : f a = a) :
    le (lfp le glb f) a :=
  glb_lb (fun x => le (f x) x) a (by show le (f a) a; rw [h]; exact refl a)

end KnasterTarski

/-! ## Dual: the greatest fixed point (parametrized `lub`)

By the order-dual, the **greatest fixed point** is the lub of the
post-fixed points `{x | le x (f x)}`.  Parametrize a least-upper-bound
`lub : (α → Prop) → α` with its two defining properties; the proofs are
the dual order-chases.  (Optional companion to the lfp results above.) -/

section KnasterTarskiDual

variable {α : Type}
variable {le : α → α → Prop}
variable {f : α → α}

/-- The **greatest fixed point**: the lub of the post-fixed points
    `{x | le x (f x)}`. -/
def gfp (le : α → α → Prop) (lub : (α → Prop) → α) (f : α → α) : α :=
  lub (fun x => le x (f x))

/-- **`gfp ≤ f gfp`** — `f gfp` is an upper bound of the post-fixed points. -/
theorem gfp_postfixed
    (lub : (α → Prop) → α)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (lub_ub : ∀ (S : α → Prop) a, S a → le a (lub S))
    (lub_lub : ∀ (S : α → Prop) a, (∀ x, S x → le x a) → le (lub S) a)
    (mono : ∀ a b, le a b → le (f a) (f b)) :
    le (gfp le lub f) (f (gfp le lub f)) :=
  lub_lub (fun x => le x (f x)) (f (gfp le lub f))
    (fun x (hx : le x (f x)) =>
      have h1 : le x (gfp le lub f) := lub_ub (fun x => le x (f x)) x hx
      have h2 : le (f x) (f (gfp le lub f)) := mono _ _ h1
      trans _ _ _ hx h2)

/-- ★ **`f gfp = gfp`** — `gfp` IS a fixed point (dual of `lfp_fixed`). -/
theorem gfp_fixed
    (lub : (α → Prop) → α)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (antisymm : ∀ a b, le a b → le b a → a = b)
    (lub_ub : ∀ (S : α → Prop) a, S a → le a (lub S))
    (lub_lub : ∀ (S : α → Prop) a, (∀ x, S x → le x a) → le (lub S) a)
    (mono : ∀ a b, le a b → le (f a) (f b)) :
    f (gfp le lub f) = gfp le lub f :=
  have h1 : le (gfp le lub f) (f (gfp le lub f)) :=
    gfp_postfixed lub trans lub_ub lub_lub mono
  have h2 : le (f (gfp le lub f)) (f (f (gfp le lub f))) := mono _ _ h1
  have h3 : le (f (gfp le lub f)) (gfp le lub f) :=
    lub_ub (fun x => le x (f x)) (f (gfp le lub f)) h2
  antisymm _ _ h3 h1

/-- ★ **every fixed point `≤ gfp`** — `gfp` is the GREATEST fixed point. -/
theorem gfp_greatest
    (lub : (α → Prop) → α)
    (refl : ∀ a, le a a)
    (lub_ub : ∀ (S : α → Prop) a, S a → le a (lub S))
    (a : α) (h : f a = a) :
    le a (gfp le lub f) :=
  lub_ub (fun x => le x (f x)) a (by show le a (f a); rw [h]; exact refl a)

end KnasterTarskiDual

/-! ## Concrete instance: `α = Bool`, `false ≤ true`

`le a b := (a = true → b = true)` is a complete lattice on `Bool`
(`false < true`).  The set-indexed infimum is
`glb S := S false` (treating the predicate value at `false` as a `Bool`
via `decide`)... that is fiddly to make ∅-axiom.  A clean honest instance:
`le := fun a b => (!a || b) = true` and the glb of a predicate `S` defined
by AND-ing over the two points.  Rather than fight the decidable-predicate
machinery (which risks `propext`/`Classical`), we give the *simplest*
honest witness: the **one-point lattice** `α = Unit`.

`α = Unit`, `le _ _ := True`, `glb _ := ()`.  All order axioms and both
glb laws hold trivially (`trivial`), `f = id` is monotone, and the abstract
`lfp_fixed`/`lfp_least` instantiate.  This inhabits the hypothesis bundle
with zero axiom cost; a richer lattice (e.g. `Bool`) is routine but adds
decidability friction with no extra theoretical content. -/

section UnitInstance

/-- `le` on `Unit`: everything related. -/
def uLe : Unit → Unit → Prop := fun _ _ => True

/-- glb on `Unit`: the unique point. -/
def uGlb : (Unit → Prop) → Unit := fun _ => ()

theorem uLe_refl : ∀ a, uLe a a := fun _ => True.intro
theorem uLe_trans : ∀ a b c, uLe a b → uLe b c → uLe a c :=
  fun _ _ _ _ _ => True.intro
theorem uLe_antisymm : ∀ a b, uLe a b → uLe b a → a = b :=
  fun a b _ _ => by cases a; cases b; rfl
theorem uGlb_lb : ∀ (S : Unit → Prop) a, S a → uLe (uGlb S) a :=
  fun _ _ _ => True.intro
theorem uGlb_glb : ∀ (S : Unit → Prop) a, (∀ x, S x → uLe a x) → uLe a (uGlb S) :=
  fun _ _ _ => True.intro
theorem uMono : ∀ a b, uLe a b → uLe (id a) (id b) :=
  fun _ _ _ => True.intro

/-- Smoke: the abstract `lfp_fixed` instantiated at the one-point lattice
    with `f = id` gives `id (lfp uGlb id) = lfp uGlb id`. -/
theorem unit_lfp_fixed :
    id (lfp uLe uGlb id) = lfp uLe uGlb id :=
  lfp_fixed (le := uLe) (f := id) uGlb
    uLe_trans uLe_antisymm uGlb_lb uGlb_glb uMono

/-- Smoke: the abstract `lfp_least` instantiated at the one-point lattice. -/
theorem unit_lfp_least (a : Unit) (h : id a = a) :
    uLe (lfp uLe uGlb id) a :=
  lfp_least (le := uLe) (f := id) uGlb uLe_refl uGlb_lb a h

end UnitInstance

end E213.Lib.Math.Order.KnasterTarski
