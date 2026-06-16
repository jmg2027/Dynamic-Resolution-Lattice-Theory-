import E213.Lib.Math.Order.GaloisConnection

/-!
# Galois connections: composition + closed elements (∅-axiom)

Two capstone facts extending `Order/GaloisConnection.lean`:

* **Composition** `gc_comp`: Galois connections compose.  `(f'∘f, g∘g')`
  is a Galois connection between `A` and `C`.  Pure adjunction
  transitivity (`Iff.trans`) — no order axioms.
* **Closed elements = image of `g`**: for the closure `c a = g (f a)`,
  the fixed points of `c` are exactly the elements of the form `g b`.
  `closed_of_image` is the triangle identity `gc_gfg`; `image_of_closed`
  is the trivial `a = c a`.  `closed_iff_image` packages both directions.

Same parametrized idiom as the sibling file: explicit relation
parameters with refl/trans/antisymm witnesses, `Iff` only via
`.mp/.mpr/.trans`, no `funext`, no Mathlib.
-/

namespace E213.Lib.Math.Order.GaloisConnectionComposition

open E213.Lib.Math.Order.GaloisConnection

section Composition

variable {α β γ : Type}

/-- **Composition of Galois connections.**  Given `(f,g) : A ⊣ B` and
    `(f',g') : B ⊣ C`, the composite `(f'∘f, g∘g')` is a Galois
    connection `A ⊣ C`:

        leC (f' (f a)) c  ↔  leB (f a) (g' c)   [gcBC at `f a, c`]
                          ↔  leA a (g (g' c))    [gcAB at `a, g' c`]

    Pure `Iff.trans` — needs no order axioms whatsoever. -/
theorem gc_comp
    {leA : α → α → Prop} {leB : β → β → Prop} {leC : γ → γ → Prop}
    {f : α → β} {g : β → α} {f' : β → γ} {g' : γ → β}
    (gcAB : ∀ a b, leB (f a) b ↔ leA a (g b))
    (gcBC : ∀ b c, leC (f' b) c ↔ leB b (g' c))
    (a : α) (c : γ) : leC (f' (f a)) c ↔ leA a (g (g' c)) :=
  Iff.trans (gcBC (f a) c) (gcAB a (g' c))

end Composition

section ClosedElements

variable {α β : Type}

/-- The closure operator `c a = g (f a)` (the same `clo` as the sibling
    file, re-abbreviated locally for readability). -/
local notation "c[" f ", " g "]" => clo f g

/-- **Every `g b` is closed.**  `c (g b) = g (f (g b)) = g b` is exactly
    the triangle identity `gc_gfg` at `b`. -/
theorem closed_of_image
    {leA : α → α → Prop} {leB : β → β → Prop}
    (transB : ∀ a b c, leB a b → leB b c → leB a c) (reflA : ∀ a, leA a a)
    (reflB : ∀ b, leB b b) (antisymmA : ∀ a b, leA a b → leA b a → a = b)
    {f : α → β} {g : β → α} (gc : ∀ a b, leB (f a) b ↔ leA a (g b))
    (b : β) : clo f g (g b) = g b :=
  gc_gfg transB reflA reflB antisymmA gc b

/-- **Every closed element is in the image of `g`.**  If `c a = a` then
    `a = g (f a)` — `a` equals `g` of the witness `f a`.  Purely the
    fixed-point hypothesis read backwards (no order axioms). -/
theorem image_of_closed
    {f : α → β} {g : β → α}
    (a : α) (h : clo f g a = a) : a = g (f a) :=
  Eq.symm h

/-- **Characterization** (⟸): if `a = g b` for some `b`, then `a` is
    closed.  Rewrite through `closed_of_image`. -/
theorem closed_of_exists_image
    {leA : α → α → Prop} {leB : β → β → Prop}
    (transB : ∀ a b c, leB a b → leB b c → leB a c) (reflA : ∀ a, leA a a)
    (reflB : ∀ b, leB b b) (antisymmA : ∀ a b, leA a b → leA b a → a = b)
    {f : α → β} {g : β → α} (gc : ∀ a b, leB (f a) b ↔ leA a (g b))
    (a : α) (h : ∃ b, a = g b) : clo f g a = a := by
  obtain ⟨b, hb⟩ := h
  rw [hb]
  exact closed_of_image transB reflA reflB antisymmA gc b

/-- **Closed ⟺ in the image of `g`.**  `a` is a fixed point of the
    closure operator iff `a = g b` for some `b`.

    `⟹` witness `b = f a` (`image_of_closed`); `⟸` via
    `closed_of_exists_image`. -/
theorem closed_iff_image
    {leA : α → α → Prop} {leB : β → β → Prop}
    (transB : ∀ a b c, leB a b → leB b c → leB a c) (reflA : ∀ a, leA a a)
    (reflB : ∀ b, leB b b) (antisymmA : ∀ a b, leA a b → leA b a → a = b)
    {f : α → β} {g : β → α} (gc : ∀ a b, leB (f a) b ↔ leA a (g b))
    (a : α) : clo f g a = a ↔ ∃ b, a = g b :=
  Iff.intro
    (fun h => ⟨f a, image_of_closed a h⟩)
    (fun h => closed_of_exists_image transB reflA reflB antisymmA gc a h)

/-! ## Idempotent closure + universal property (clean bonus) -/

/-- `c (c a) = c a` — the closure is idempotent.  This is the sibling
    file's `clo_idempotent`, re-exported here for completeness. -/
theorem gc_idempotent_closure
    {leA : α → α → Prop} {leB : β → β → Prop}
    (transB : ∀ a b c, leB a b → leB b c → leB a c) (reflA : ∀ a, leA a a)
    (reflB : ∀ b, leB b b) (antisymmA : ∀ a b, leA a b → leA b a → a = b)
    {f : α → β} {g : β → α} (gc : ∀ a b, leB (f a) b ↔ leA a (g b))
    (a : α) : clo f g (clo f g a) = clo f g a :=
  clo_idempotent transB reflA reflB antisymmA gc a

/-- **Universal property of the closure.**  A closed element `g b` sees
    `a` only through its closure: `leA a (g b) ↔ leA (c a) (g b)`.

    `⟸`: `a ≤ c a` (unit) then transitivity.
    `⟹`: `a ≤ g b` gives `c a = g (f a) ≤ g (g (f a) … )`; concretely
    `f a ≤ b` (adjunction) hence `g (f a) ≤ g b` (`gc_monotone_g`). -/
theorem gc_le_closed
    {leA : α → α → Prop} {leB : β → β → Prop}
    (transA : ∀ a b c, leA a b → leA b c → leA a c)
    (transB : ∀ a b c, leB a b → leB b c → leB a c)
    (reflA : ∀ a, leA a a) (reflB : ∀ b, leB b b)
    {f : α → β} {g : β → α} (gc : ∀ a b, leB (f a) b ↔ leA a (g b))
    (a : α) (b : β) : leA a (g b) ↔ leA (clo f g a) (g b) :=
  Iff.intro
    (fun h =>
      -- a ≤ g b  ⟹  f a ≤ b  ⟹  g (f a) ≤ g b
      gc_monotone_g transB reflA gc (f a) b ((gc a b).mpr h))
    (fun h =>
      -- a ≤ c a ≤ g b
      transA a (clo f g a) (g b) (clo_extensive reflB gc a) h)

end ClosedElements

/-! ## Concrete smoke: composing `id ⊣ id` with itself -/

section Smoke

/-- Composing the trivial `id ⊣ id` Galois connection with itself yields
    again `id ⊣ id` (shape `leC (f'(f a)) c ↔ leA a (g(g' c))` with all
    maps `id`).  Witnesses inhabitation of `gc_comp`. -/
theorem id_comp_gc (a c : Nat) :
    (id (id a)) ≤ c ↔ a ≤ (id (id c)) :=
  gc_comp (leA := Nat.le) (leB := Nat.le) (leC := Nat.le)
    (f := id) (g := id) (f' := id) (g' := id)
    (fun a b => Iff.rfl) (fun b c => Iff.rfl) a c

/-- Numeric smoke: the composite at concrete values is decidable and
    axiom-clean. -/
theorem id_comp_gc_smoke : ((id (id 2)) ≤ 5 ↔ 2 ≤ (id (id 5))) :=
  id_comp_gc 2 5

end Smoke

end E213.Lib.Math.Order.GaloisConnectionComposition
