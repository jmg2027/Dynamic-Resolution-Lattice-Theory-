import E213.Lib.Math.Order.GaloisConnection

/-!
# Fenchel–Moreau biconjugate as a Galois closure (antitone self-adjoint, ∅-axiom)

`Order/GaloisConnection.lean` builds the **monotone** Galois closure
`clo = g ∘ f`.  The Legendre–Fenchel transform `(·)*` is *order-reversing*
(antitone): `f ≤ g  ⟹  g* ≤ f*`, and it is its own adjoint in the antitone
sense

    star (star)  self-adjunction :   leA y (star x)  ↔  leA x (star y)

(`y ≤ g*  ⟺  g ≤ y*` — the conjugation pairing, symmetric in the two
arguments).  An order-reversing self-adjoint map's **square** `star ∘ star`
is therefore a closure operator (extensive, monotone, idempotent), and this
is exactly the **Fenchel–Moreau biconjugate** `f** = clo f` — the closed
convex hull, as `research-notes/decomposition/practice/convex_duality.md`
predicts (and `galois.md`'s order-reversing leg names).

This file proves the **abstract antitone-self-adjoint ⟹ closure** theorem
(the ∅-axiom content; an actual `sup_x (p·x − f x)` Legendre transform over
the reals would additionally need `Real213`).  Headlines:

* `biconjugate_eq_clo` — `star (star x) = cloAntitone star x` (definitional
  weld: the biconjugate **is** the antitone closure).
* `cloAntitone_extensive` — weak duality / the unit: `x ≤ star (star x)`
  **always**.  This is the duality-gap-as-residue: the gap `cloAntitone x`
  vs `x` is the residue, tagged `q=+1` (it *settles*, by idempotence).
* `cloAntitone_monotone`, `cloAntitone_idempotent` — closure laws.
* `star_triple` (`f*** = f*`) and `biconj_idempotent` (`f**** = f**`) —
  Fenchel–Moreau: the closed elements are the fixed points.
* `closed_iff_fixed` — strong duality: `x = star (star x)` iff `x` is closed
  (the residue *vanishes* exactly on the closure-fixed locus, q=+1).

All derivations are pure order-chases (`reflA`/`transA`/`antisymmA`, `.mp`/
`.mpr`, `congrArg`) — no `funext`, no `propext`, no Mathlib.

A concrete witness is order-reversal on the 3-element chain `Fin 3`
(`star = (2 - ·)`), an order-reversing involution whose square is the
identity closure.
-/

namespace E213.Lib.Math.Order.FenchelMoreau

section AntitoneSelfAdjoint

variable {α : Type}

/-- The **antitone closure** induced by an order-reversing self-adjoint
    `star`: `cloAntitone star x = star (star x)` — the **biconjugate**
    `x ↦ x**`.  (Definitionally `star (star x)`; the lemmas below show it is
    a genuine closure operator.) -/
def cloAntitone (star : α → α) (x : α) : α := star (star x)

/-- **The biconjugate is the antitone closure** (definitional weld):
    `star (star x) = cloAntitone star x`.  This is the named target —
    `f** = clo f` — read as a Galois closure of the order-reversing
    conjugation `star`. -/
theorem biconjugate_eq_clo (star : α → α) (x : α) :
    star (star x) = cloAntitone star x := rfl

/-- **Extensive / weak duality / the unit.**  For an antitone self-adjoint
    `star`, `x ≤ star (star x)` **always**.

    From `gc x (star x) : leA (star x) (star x) ↔ leA x (star (star x))`,
    applied `.mp` to reflexivity `leA (star x) (star x)`.

    This is the *over-shoot* direction `a ≤ g (f a)`: the duality gap
    `cloAntitone x` vs `x` is the residue.  `f** ≤ f` in the function-lattice
    sign convention; here the order is the abstract `leA` and the closure
    over-shoots upward. -/
theorem cloAntitone_extensive
    {leA : α → α → Prop} (reflA : ∀ a, leA a a)
    {star : α → α} (gc : ∀ x y, leA y (star x) ↔ leA x (star y))
    (x : α) : leA x (cloAntitone star x) :=
  (gc x (star x)).mp (reflA (star x))

/-- **`star` is antitone (order-reversing).**  If `x ≤ y` then
    `star y ≤ star x`.

    From `x ≤ y` and the unit `y ≤ star (star y)` we get
    `x ≤ star (star y)` by transitivity; then
    `gc x (star y) : leA (star y) (star x) ↔ leA x (star (star y))`
    closes it via `.mpr`. -/
theorem star_antitone
    {leA : α → α → Prop} (reflA : ∀ a, leA a a)
    (transA : ∀ a b c, leA a b → leA b c → leA a c)
    {star : α → α} (gc : ∀ x y, leA y (star x) ↔ leA x (star y))
    (x y : α) (h : leA x y) : leA (star y) (star x) :=
  (gc x (star y)).mpr
    (transA x y (star (star y)) h (cloAntitone_extensive reflA gc y))

/-- **The closure is monotone.**  `x ≤ y ⟹ star (star x) ≤ star (star y)`
    — antitone twice. -/
theorem cloAntitone_monotone
    {leA : α → α → Prop} (reflA : ∀ a, leA a a)
    (transA : ∀ a b c, leA a b → leA b c → leA a c)
    {star : α → α} (gc : ∀ x y, leA y (star x) ↔ leA x (star y))
    (x y : α) (h : leA x y) : leA (cloAntitone star x) (cloAntitone star y) :=
  star_antitone reflA transA gc (star y) (star x)
    (star_antitone reflA transA gc x y h)

/-- **Triangle identity `f*** = f*`.**  `star (star (star x)) = star x`.

    `≤`: apply `star_antitone` to the unit `x ≤ star (star x)` —
        `star (star (star x)) ≤ star x`.
    `≥`: the unit at `star x` — `star x ≤ star (star (star x))`.
    Antisymmetry of `leA` closes it. -/
theorem star_triple
    {leA : α → α → Prop} (reflA : ∀ a, leA a a)
    (transA : ∀ a b c, leA a b → leA b c → leA a c)
    (antisymmA : ∀ a b, leA a b → leA b a → a = b)
    {star : α → α} (gc : ∀ x y, leA y (star x) ↔ leA x (star y))
    (x : α) : star (star (star x)) = star x :=
  antisymmA (star (star (star x))) (star x)
    (star_antitone reflA transA gc x (star (star x))
      (cloAntitone_extensive reflA gc x))
    (cloAntitone_extensive reflA gc (star x))

/-- **The closure is idempotent** (`clo (clo x) = clo x`, pointwise).
    `star (star (star (star x))) = star (star x)` by `congrArg star` on the
    triangle identity `star (star (star x)) = star x`. -/
theorem cloAntitone_idempotent
    {leA : α → α → Prop} (reflA : ∀ a, leA a a)
    (transA : ∀ a b c, leA a b → leA b c → leA a c)
    (antisymmA : ∀ a b, leA a b → leA b a → a = b)
    {star : α → α} (gc : ∀ x y, leA y (star x) ↔ leA x (star y))
    (x : α) : cloAntitone star (cloAntitone star x) = cloAntitone star x :=
  congrArg star (star_triple reflA transA antisymmA gc x)

/-- **Fenchel–Moreau idempotence `f**** = f**`.**  The fourfold conjugate
    equals the twofold — the closed convex hull is itself closed.  This is
    `cloAntitone_idempotent` spelled in raw `star`-iterates. -/
theorem biconj_idempotent
    {leA : α → α → Prop} (reflA : ∀ a, leA a a)
    (transA : ∀ a b c, leA a b → leA b c → leA a c)
    (antisymmA : ∀ a b, leA a b → leA b a → a = b)
    {star : α → α} (gc : ∀ x y, leA y (star x) ↔ leA x (star y))
    (x : α) : star (star (star (star x))) = star (star x) :=
  cloAntitone_idempotent reflA transA antisymmA gc x

/-! ## Strong duality = closure-fixed locus (the residue vanishing, q=+1) -/

/-- **Strong duality / the closed elements.**  `x` is closure-fixed
    (`x = star (star x)`) iff it is a single conjugate `x = star b` for some
    `b` (here `b = star x`).  On this locus the duality gap is zero — the
    residue vanishes.

    `⟹`: witness `b = star x`, directly from `h`.
    `⟸`: from `x = star b`, `star (star x) = star (star (star b)) = star b = x`
    by the triangle identity `star_triple`. -/
theorem closed_iff_fixed
    {leA : α → α → Prop} (reflA : ∀ a, leA a a)
    (transA : ∀ a b c, leA a b → leA b c → leA a c)
    (antisymmA : ∀ a b, leA a b → leA b a → a = b)
    {star : α → α} (gc : ∀ x y, leA y (star x) ↔ leA x (star y))
    (x : α) : x = cloAntitone star x ↔ ∃ b, x = star b :=
  Iff.intro
    (fun h => ⟨star x, h⟩)
    (fun h => by
      obtain ⟨b, hb⟩ := h
      -- x = star b ⟹ star (star x) = star (star (star b)) = star b = x
      calc x = star b := hb
        _ = star (star (star b)) := (star_triple reflA transA antisymmA gc b).symm
        _ = cloAntitone star x := by rw [← hb]; rfl)

/-! ## Reduction to the monotone Galois closure (the explicit weld)

The antitone self-adjoint `star` is a Galois connection between `α` (ordered
by `leA`) and `α` carried with the **opposite** order `leA' x y := leA y x`.
With `f := star`, `g := star`, the antitone adjunction
`leA y (star x) ↔ leA x (star y)` is exactly the monotone-shaped
`leA' (f x) y ↔ leA x (g y)` for `leA' := flip leA`, so `cloAntitone star`
**is** `GaloisConnection.clo star star`. -/

/-- The antitone self-adjunction, re-read as a *monotone* Galois connection
    `star ⊣ star` between `(α, leA)` and `(α, flip leA)`:
    `(flip leA) (star x) y ↔ leA x (star y)`. -/
theorem star_as_monotone_gc
    {leA : α → α → Prop}
    {star : α → α} (gc : ∀ x y, leA y (star x) ↔ leA x (star y))
    (x y : α) : (fun a b => leA b a) (star x) y ↔ leA x (star y) :=
  gc x y

/-- The antitone closure **is** the monotone Galois closure `clo star star`
    (definitional). -/
theorem cloAntitone_eq_gc_clo (star : α → α) (x : α) :
    cloAntitone star x = E213.Lib.Math.Order.GaloisConnection.clo star star x :=
  rfl

end AntitoneSelfAdjoint

/-! ## Concrete witness: order-reversal on `Bool`

`star = not` is an order-reversing involution on `Bool` ordered by
`ble a b := (!a || b) = true` (`false ≤ true`).  Its antitone
self-adjunction `bool_self_adjoint` holds; being an involution
(`Bool.not_not`), the closure `star ∘ star` is the **identity** — every
element is closed, the fully convex / `f** = f` corner.

The order is taken **`Bool`-valued** (an `Eq` to `true`) so every fact is a
`∀`-over-`Bool` equality, proved `decide`-pure exactly like the sibling
`BooleanAlgebra.bool_*` witnesses — no `Fin`/subtype `Quot`, no `propext`. -/

section BoolWitness

/-- `Bool` order: `bleBool a b` iff `(!a || b) = true` (i.e. `false ≤ true`). -/
def bleBool (a b : Bool) : Prop := (!a || b) = true

/-- `bleBool` is reflexive (`∀ a, (!a || a) = true`). -/
theorem bleBool_refl (a : Bool) : bleBool a a := by
  unfold bleBool; revert a; decide

/-- The order-reversal pairing as a **Bool equality** (commutativity of `||`):
    `(!y || !x) = (!x || !y)`.  This is the load-bearing decidable fact. -/
theorem bool_swap_eq (x y : Bool) : (!y || !x) = (!x || !y) := by
  revert x y; decide

/-- `not` is an **antitone self-adjoint** for `bleBool`:
    `bleBool y (not x) ↔ bleBool x (not y)`.  Both sides are
    `(!_ || !_) = true`; the underlying Bool expressions are equal by
    `bool_swap_eq`, so the `Iff` is `Eq`-rewriting only (no `propext`). -/
theorem bool_self_adjoint (x y : Bool) :
    bleBool y (!x) ↔ bleBool x (!y) := by
  unfold bleBool
  rw [bool_swap_eq]

/-- `not` is an **involution**: `not (not x) = x` (`Bool.not_not`). -/
theorem bool_not_involution (x : Bool) : (!(!x)) = x := by
  revert x; decide

/-- Smoke: the abstract `cloAntitone_extensive` at `star = not` gives the
    unit `bleBool x (not (not x))`, which collapses to `bleBool x x`. -/
theorem bool_unit (x : Bool) : bleBool x (cloAntitone Bool.not x) :=
  cloAntitone_extensive (leA := bleBool)
    bleBool_refl (star := Bool.not)
    (fun a b => bool_self_adjoint a b) x

/-- Smoke: the biconjugate is the identity on `Bool` (the fully closed /
    `f** = f` case) — `cloAntitone not x = x`. -/
theorem bool_biconj_id (x : Bool) : cloAntitone Bool.not x = x :=
  bool_not_involution x

end BoolWitness

end E213.Lib.Math.Order.FenchelMoreau
