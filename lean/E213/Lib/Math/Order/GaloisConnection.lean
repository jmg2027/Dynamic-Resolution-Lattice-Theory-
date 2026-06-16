import E213.Meta.Nat.AddMod213

/-!
# Galois connections (parametrized order, ∅-axiom)

A Galois connection between two ordered types is a pair of maps
`f : α → β`, `g : β → α` satisfying the adjunction

    leB (f a) b  ↔  leA a (g b)

The order is given as *explicit* relation parameters plus their
reflexivity / transitivity / antisymmetry witnesses — no typeclasses,
no Mathlib.  Everything below is a pure order-chase using only
`reflA/reflB/transA/transB/antisymmA/antisymmB` and `.mp/.mpr` of the
adjunction (`Iff` elimination is propext-free; we never `rw` on the
`Iff`).

Results: unit, counit, monotonicity of both adjoints, the triangle
identities `f∘g∘f = f` / `g∘f∘g = g` (stated **pointwise** to avoid
`funext`/`Quot.sound`), and the induced closure operator `c = g ∘ f`
(extensive, monotone, idempotent).

A concrete witness is the multiply/divide adjunction
`y*p ≤ a ↔ y ≤ a/p` on `Nat` (`AddMod213.le_div_iff_mul_le`).

Hypotheses are taken as explicit binders on each theorem (rather than a
bundled `structure`) to keep the order-chase transparent and avoid
projection friction.
-/

namespace E213.Lib.Math.Order.GaloisConnection

section GaloisConnection

variable {α β : Type}

/-! ## Unit and counit -/

/-- The **unit**: `a ≤ g (f a)`.  From `gc` applied to `leB (f a) (f a)`
    (reflexivity of `leB`). -/
theorem gc_unit
    {leA : α → α → Prop} {leB : β → β → Prop} (reflB : ∀ b, leB b b)
    {f : α → β} {g : β → α} (gc : ∀ a b, leB (f a) b ↔ leA a (g b))
    (a : α) : leA a (g (f a)) :=
  (gc a (f a)).mp (reflB (f a))

/-- The **counit**: `f (g b) ≤ b`.  From `gc` applied to `leA (g b) (g b)`
    (reflexivity of `leA`). -/
theorem gc_counit
    {leA : α → α → Prop} {leB : β → β → Prop} (reflA : ∀ a, leA a a)
    {f : α → β} {g : β → α} (gc : ∀ a b, leB (f a) b ↔ leA a (g b))
    (b : β) : leB (f (g b)) b :=
  (gc (g b) b).mpr (reflA (g b))

/-! ## Monotonicity of the adjoints -/

/-- `f` is monotone.  If `a ≤ a'` then `a ≤ g (f a')` (compose with the
    unit), hence `f a ≤ f a'` by the adjunction. -/
theorem gc_monotone_f
    {leA : α → α → Prop} {leB : β → β → Prop}
    (transA : ∀ a b c, leA a b → leA b c → leA a c) (reflB : ∀ b, leB b b)
    {f : α → β} {g : β → α} (gc : ∀ a b, leB (f a) b ↔ leA a (g b))
    (a a' : α) (h : leA a a') : leB (f a) (f a') :=
  (gc a (f a')).mpr (transA a a' (g (f a')) h (gc_unit reflB gc a'))

/-- `g` is monotone.  If `b ≤ b'` then `f (g b) ≤ b'` (compose counit with
    `h`), hence `g b ≤ g b'` by the adjunction. -/
theorem gc_monotone_g
    {leA : α → α → Prop} {leB : β → β → Prop}
    (transB : ∀ a b c, leB a b → leB b c → leB a c) (reflA : ∀ a, leA a a)
    {f : α → β} {g : β → α} (gc : ∀ a b, leB (f a) b ↔ leA a (g b))
    (b b' : β) (h : leB b b') : leA (g b) (g b') :=
  (gc (g b) b').mp (transB (f (g b)) b b' (gc_counit reflA gc b) h)

/-! ## Triangle identities (pointwise — no `funext`) -/

/-- `f (g (f a)) = f a`.  `≤`: counit at `f a`.  `≥`: monotone `f` on the
    unit `a ≤ g (f a)`.  Antisymmetry of `leB` closes it. -/
theorem gc_fgf
    {leA : α → α → Prop} {leB : β → β → Prop}
    (transA : ∀ a b c, leA a b → leA b c → leA a c) (reflA : ∀ a, leA a a)
    (reflB : ∀ b, leB b b) (antisymmB : ∀ a b, leB a b → leB b a → a = b)
    {f : α → β} {g : β → α} (gc : ∀ a b, leB (f a) b ↔ leA a (g b))
    (a : α) : f (g (f a)) = f a :=
  antisymmB (f (g (f a))) (f a)
    (gc_counit reflA gc (f a))
    (gc_monotone_f transA reflB gc a (g (f a)) (gc_unit reflB gc a))

/-- `g (f (g b)) = g b`.  `≥`: unit applied through `g`.  `≤`: monotone `g`
    on the counit `f (g b) ≤ b`.  Antisymmetry of `leA` closes it. -/
theorem gc_gfg
    {leA : α → α → Prop} {leB : β → β → Prop}
    (transB : ∀ a b c, leB a b → leB b c → leB a c) (reflA : ∀ a, leA a a)
    (reflB : ∀ b, leB b b) (antisymmA : ∀ a b, leA a b → leA b a → a = b)
    {f : α → β} {g : β → α} (gc : ∀ a b, leB (f a) b ↔ leA a (g b))
    (b : β) : g (f (g b)) = g b :=
  antisymmA (g (f (g b))) (g b)
    (gc_monotone_g transB reflA gc (f (g b)) b (gc_counit reflA gc b))
    (gc_unit reflB gc (g b))

/-! ## Induced closure operator `c = g ∘ f` -/

/-- The closure operator `c a = g (f a)`. -/
def clo (f : α → β) (g : β → α) (a : α) : α := g (f a)

/-- `c` is **extensive**: `a ≤ c a` (this is exactly the unit). -/
theorem clo_extensive
    {leA : α → α → Prop} {leB : β → β → Prop} (reflB : ∀ b, leB b b)
    {f : α → β} {g : β → α} (gc : ∀ a b, leB (f a) b ↔ leA a (g b))
    (a : α) : leA a (clo f g a) :=
  gc_unit reflB gc a

/-- `c` is **monotone**. -/
theorem clo_monotone
    {leA : α → α → Prop} {leB : β → β → Prop}
    (transA : ∀ a b c, leA a b → leA b c → leA a c)
    (transB : ∀ a b c, leB a b → leB b c → leB a c)
    (reflA : ∀ a, leA a a) (reflB : ∀ b, leB b b)
    {f : α → β} {g : β → α} (gc : ∀ a b, leB (f a) b ↔ leA a (g b))
    (a a' : α) (h : leA a a') : leA (clo f g a) (clo f g a') :=
  gc_monotone_g transB reflA gc (f a) (f a')
    (gc_monotone_f transA reflB gc a a' h)

/-- `c` is **idempotent**: `c (c a) = c a` (pointwise).
    `c (c a) = g (f (g (f a))) = g (f a) = c a` by `gc_gfg` at `f a`. -/
theorem clo_idempotent
    {leA : α → α → Prop} {leB : β → β → Prop}
    (transB : ∀ a b c, leB a b → leB b c → leB a c) (reflA : ∀ a, leA a a)
    (reflB : ∀ b, leB b b) (antisymmA : ∀ a b, leA a b → leA b a → a = b)
    {f : α → β} {g : β → α} (gc : ∀ a b, leB (f a) b ↔ leA a (g b))
    (a : α) : clo f g (clo f g a) = clo f g a :=
  gc_gfg transB reflA reflB antisymmA gc (f a)

/-! ## Uniqueness of the right adjoint -/

/-- The right adjoint is **unique**: any two `g₁, g₂` adjoint to the same
    `f` agree pointwise.  `leA (g₁ b) (g₂ b)` comes from `gc₂.mp` on the
    counit of `gc₁` (`leB (f (g₁ b)) b`, from `reflA`); the reverse is
    symmetric.  Antisymmetry of `leA` closes it. -/
theorem gc_unique_right
    {leA : α → α → Prop} {leB : β → β → Prop}
    (reflA : ∀ a, leA a a)
    (antisymmA : ∀ a b, leA a b → leA b a → a = b)
    {f : α → β} {g₁ g₂ : β → α}
    (gc₁ : ∀ a b, leB (f a) b ↔ leA a (g₁ b))
    (gc₂ : ∀ a b, leB (f a) b ↔ leA a (g₂ b))
    (b : β) : g₁ b = g₂ b :=
  antisymmA (g₁ b) (g₂ b)
    ((gc₂ (g₁ b) b).mp (gc_counit reflA gc₁ b))
    ((gc₁ (g₂ b) b).mp (gc_counit reflA gc₂ b))

end GaloisConnection

/-! ## Concrete instance: the multiply/divide adjunction on `Nat`

`f y = y * p`, `g a = a / p` (for `p > 0`) form a Galois connection:
`y * p ≤ a ↔ y ≤ a / p` is `AddMod213.le_div_iff_mul_le`.
The order on both sides is `Nat.le`.  This is a genuine (non-trivial)
Galois connection — the closure operator `c y = (y * p) / p` is the
identity here, but `f` and `g` are not mutually inverse. -/

section NatInstance

open E213.Meta.Nat

/-- The adjunction `(· * p) ⊣ (· / p)` on `Nat`, for `p > 0`:
    `leB (f y) a ↔ leA y (g a)` with `f y = y*p`, `g a = a/p`. -/
theorem mulDiv_gc {p : Nat} (hp : 0 < p) (y a : Nat) :
    (y * p) ≤ a ↔ y ≤ a / p :=
  AddMod213.le_div_iff_mul_le hp y a |>.symm

/-- Smoke: the abstract `gc_unit` instantiated at the multiply/divide
    adjunction gives `y ≤ (y * p) / p`. -/
theorem mulDiv_unit {p : Nat} (hp : 0 < p) (y : Nat) : y ≤ (y * p) / p :=
  gc_unit (leA := Nat.le) (leB := Nat.le) Nat.le_refl
    (f := fun y => y * p) (g := fun a => a / p) (fun y a => mulDiv_gc hp y a) y

/-- Smoke: the abstract `gc_counit` gives `((a / p) * p) ≤ a`. -/
theorem mulDiv_counit {p : Nat} (hp : 0 < p) (a : Nat) : ((a / p) * p) ≤ a :=
  gc_counit (leA := Nat.le) (leB := Nat.le) Nat.le_refl
    (f := fun y => y * p) (g := fun a => a / p) (fun y a => mulDiv_gc hp y a) a

/-- Trivial instance: `id ⊣ id` on `Nat`, witnessing inhabitation of the
    Galois-connection hypotheses directly. -/
theorem id_gc (a b : Nat) : (id a) ≤ b ↔ a ≤ (id b) := Iff.rfl

end NatInstance

end E213.Lib.Math.Order.GaloisConnection
