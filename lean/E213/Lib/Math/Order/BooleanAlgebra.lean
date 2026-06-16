/-!
# Abstract Boolean algebra (parametrized, ∅-axiom)

A Boolean algebra over a type `α` is given by two binary operations
`inf sup : α → α → α`, a unary complement `cmpl : α → α`, and two
constants `bot top : α`, satisfying the standard (lattice + distributive
+ complemented) axiom set, supplied as *explicit* per-theorem hypotheses
(no typeclass, no bundled structure, no Mathlib — same idiom as the
sibling `Order/GaloisConnection.lean`).

Everything below is pure equational rewriting with the axiom hypotheses
(`rw`/`calc` on `Eq`s only — propext-free), deriving the fundamental
Boolean laws: idempotence, boundedness, **uniqueness of complement**,
**double complement**, and **both De Morgan laws**.

A concrete witness is `α = Bool` with `and / or / not / false / true`;
the axioms hold by `decide` (closed `∀`-over-`Bool`, axiom-clean).
-/

namespace E213.Lib.Math.Order.BooleanAlgebra

section BooleanAlgebra

variable {α : Type}
variable {inf sup : α → α → α} {cmpl : α → α} {bot top : α}

/-! ## Idempotence (from absorption + identities) -/

/-- `inf a a = a`.  `inf a a = inf a (sup a bot) = a` by `sup_bot` then
    `inf_absorb`. -/
theorem idem_inf
    (sup_bot : ∀ a, sup a bot = a)
    (inf_absorb : ∀ a b, inf a (sup a b) = a)
    (a : α) : inf a a = a :=
  calc inf a a = inf a (sup a bot) := by rw [sup_bot]
    _ = a := inf_absorb a bot

/-- `sup a a = a`.  `sup a a = sup a (inf a top) = a` by `inf_top` then
    `sup_absorb`. -/
theorem idem_sup
    (inf_top : ∀ a, inf a top = a)
    (sup_absorb : ∀ a b, sup a (inf a b) = a)
    (a : α) : sup a a = a :=
  calc sup a a = sup a (inf a top) := by rw [inf_top]
    _ = a := sup_absorb a top

/-! ## Boundedness -/

/-- `inf a bot = bot`.  Using `bot = inf a (cmpl a)`, associativity and
    `inf`-idempotence. -/
theorem inf_bot
    (inf_assoc : ∀ a b c, inf (inf a b) c = inf a (inf b c))
    (sup_bot : ∀ a, sup a bot = a)
    (inf_absorb : ∀ a b, inf a (sup a b) = a)
    (inf_cmpl : ∀ a, inf a (cmpl a) = bot)
    (a : α) : inf a bot = bot :=
  calc inf a bot = inf a (inf a (cmpl a)) := by rw [inf_cmpl]
    _ = inf (inf a a) (cmpl a) := (inf_assoc a a (cmpl a)).symm
    _ = inf a (cmpl a) := by rw [idem_inf sup_bot inf_absorb]
    _ = bot := inf_cmpl a

/-- `sup a top = top`.  Dual of `inf_bot`. -/
theorem sup_top
    (sup_assoc : ∀ a b c, sup (sup a b) c = sup a (sup b c))
    (inf_top : ∀ a, inf a top = a)
    (sup_absorb : ∀ a b, sup a (inf a b) = a)
    (sup_cmpl : ∀ a, sup a (cmpl a) = top)
    (a : α) : sup a top = top :=
  calc sup a top = sup a (sup a (cmpl a)) := by rw [sup_cmpl]
    _ = sup (sup a a) (cmpl a) := (sup_assoc a a (cmpl a)).symm
    _ = sup a (cmpl a) := by rw [idem_sup inf_top sup_absorb]
    _ = top := sup_cmpl a

/-! ## Uniqueness of complement (the key lemma) -/

/-- The complement is **unique**: if `b` is a complement of `a`
    (`sup a b = top` and `inf a b = bot`), then `b = cmpl a`.

    Standard proof: both `b` and `cmpl a` equal the meet `inf (cmpl a) b`. -/
theorem cmpl_unique
    (inf_comm : ∀ a b, inf a b = inf b a)
    (sup_comm : ∀ a b, sup a b = sup b a)
    (inf_top : ∀ a, inf a top = a)
    (sup_bot : ∀ a, sup a bot = a)
    (inf_distrib : ∀ a b c, inf a (sup b c) = sup (inf a b) (inf a c))
    (inf_cmpl : ∀ a, inf a (cmpl a) = bot)
    (sup_cmpl : ∀ a, sup a (cmpl a) = top)
    (a b : α) (h1 : sup a b = top) (h2 : inf a b = bot) : b = cmpl a :=
  have hb : b = inf (cmpl a) b :=
    calc b = inf b top := (inf_top b).symm
      _ = inf b (sup a (cmpl a)) := by rw [sup_cmpl]
      _ = sup (inf b a) (inf b (cmpl a)) := inf_distrib b a (cmpl a)
      _ = sup (inf a b) (inf b (cmpl a)) := by rw [inf_comm b a]
      _ = sup bot (inf b (cmpl a)) := by rw [h2]
      _ = sup (inf b (cmpl a)) bot := sup_comm bot (inf b (cmpl a))
      _ = inf b (cmpl a) := sup_bot (inf b (cmpl a))
      _ = inf (cmpl a) b := inf_comm b (cmpl a)
  have hc : cmpl a = inf (cmpl a) b :=
    calc cmpl a = inf (cmpl a) top := (inf_top (cmpl a)).symm
      _ = inf (cmpl a) (sup a b) := by rw [h1]
      _ = sup (inf (cmpl a) a) (inf (cmpl a) b) := inf_distrib (cmpl a) a b
      _ = sup (inf a (cmpl a)) (inf (cmpl a) b) := by rw [inf_comm (cmpl a) a]
      _ = sup bot (inf (cmpl a) b) := by rw [inf_cmpl]
      _ = sup (inf (cmpl a) b) bot := sup_comm bot (inf (cmpl a) b)
      _ = inf (cmpl a) b := sup_bot (inf (cmpl a) b)
  hb.trans hc.symm

/-! ## Double complement -/

/-- `cmpl (cmpl a) = a`.  `a` is a complement of `cmpl a`, so by
    `cmpl_unique` `a = cmpl (cmpl a)`. -/
theorem cmpl_cmpl
    (inf_comm : ∀ a b, inf a b = inf b a)
    (sup_comm : ∀ a b, sup a b = sup b a)
    (inf_top : ∀ a, inf a top = a)
    (sup_bot : ∀ a, sup a bot = a)
    (inf_distrib : ∀ a b c, inf a (sup b c) = sup (inf a b) (inf a c))
    (inf_cmpl : ∀ a, inf a (cmpl a) = bot)
    (sup_cmpl : ∀ a, sup a (cmpl a) = top)
    (a : α) : cmpl (cmpl a) = a :=
  (cmpl_unique inf_comm sup_comm inf_top sup_bot inf_distrib inf_cmpl sup_cmpl
    (cmpl a) a
    (by rw [sup_comm (cmpl a) a]; exact sup_cmpl a)
    (by rw [inf_comm (cmpl a) a]; exact inf_cmpl a)).symm

/-! ## De Morgan laws -/

/-- `cmpl (inf a b) = sup (cmpl a) (cmpl b)`.

    `X = sup (cmpl a) (cmpl b)` is a complement of `inf a b`:
    `inf (inf a b) X = bot` and `sup (inf a b) X = top`; then
    `cmpl_unique` gives `X = cmpl (inf a b)`. -/
theorem de_morgan_inf
    (inf_comm : ∀ a b, inf a b = inf b a)
    (sup_comm : ∀ a b, sup a b = sup b a)
    (inf_assoc : ∀ a b c, inf (inf a b) c = inf a (inf b c))
    (sup_assoc : ∀ a b c, sup (sup a b) c = sup a (sup b c))
    (inf_top : ∀ a, inf a top = a)
    (sup_bot : ∀ a, sup a bot = a)
    (inf_absorb : ∀ a b, inf a (sup a b) = a)
    (sup_absorb : ∀ a b, sup a (inf a b) = a)
    (inf_distrib : ∀ a b c, inf a (sup b c) = sup (inf a b) (inf a c))
    (sup_distrib : ∀ a b c, sup a (inf b c) = inf (sup a b) (sup a c))
    (inf_cmpl : ∀ a, inf a (cmpl a) = bot)
    (sup_cmpl : ∀ a, sup a (cmpl a) = top)
    (a b : α) : cmpl (inf a b) = sup (cmpl a) (cmpl b) :=
  have hinf : inf (inf a b) (sup (cmpl a) (cmpl b)) = bot :=
    calc inf (inf a b) (sup (cmpl a) (cmpl b))
        = sup (inf (inf a b) (cmpl a)) (inf (inf a b) (cmpl b)) :=
          inf_distrib (inf a b) (cmpl a) (cmpl b)
      _ = sup (inf (inf b a) (cmpl a)) (inf (inf a b) (cmpl b)) := by
          rw [inf_comm a b]
      _ = sup (inf b (inf a (cmpl a))) (inf (inf a b) (cmpl b)) := by
          rw [inf_assoc b a (cmpl a)]
      _ = sup (inf b bot) (inf (inf a b) (cmpl b)) := by rw [inf_cmpl]
      _ = sup bot (inf (inf a b) (cmpl b)) := by
          rw [inf_bot inf_assoc sup_bot inf_absorb inf_cmpl b]
      _ = sup bot (inf a (inf b (cmpl b))) := by rw [inf_assoc a b (cmpl b)]
      _ = sup bot (inf a bot) := by rw [inf_cmpl]
      _ = sup bot bot := by
          rw [inf_bot inf_assoc sup_bot inf_absorb inf_cmpl a]
      _ = bot := sup_bot bot
  have hsup : sup (inf a b) (sup (cmpl a) (cmpl b)) = top :=
    calc sup (inf a b) (sup (cmpl a) (cmpl b))
        = sup (sup (inf a b) (cmpl a)) (cmpl b) :=
          (sup_assoc (inf a b) (cmpl a) (cmpl b)).symm
      _ = sup (sup (cmpl a) (inf a b)) (cmpl b) := by
          rw [sup_comm (inf a b) (cmpl a)]
      _ = sup (inf (sup (cmpl a) a) (sup (cmpl a) b)) (cmpl b) := by
          rw [sup_distrib (cmpl a) a b]
      _ = sup (inf (sup a (cmpl a)) (sup (cmpl a) b)) (cmpl b) := by
          rw [sup_comm (cmpl a) a]
      _ = sup (inf top (sup (cmpl a) b)) (cmpl b) := by rw [sup_cmpl]
      _ = sup (inf (sup (cmpl a) b) top) (cmpl b) := by
          rw [inf_comm top (sup (cmpl a) b)]
      _ = sup (sup (cmpl a) b) (cmpl b) := by rw [inf_top]
      _ = sup (cmpl a) (sup b (cmpl b)) := sup_assoc (cmpl a) b (cmpl b)
      _ = sup (cmpl a) top := by rw [sup_cmpl]
      _ = top := sup_top sup_assoc inf_top sup_absorb sup_cmpl (cmpl a)
  (cmpl_unique inf_comm sup_comm inf_top sup_bot inf_distrib inf_cmpl sup_cmpl
    (inf a b) (sup (cmpl a) (cmpl b)) hsup hinf).symm

/-- `cmpl (sup a b) = inf (cmpl a) (cmpl b)`.  Dual of `de_morgan_inf`:
    `Y = inf (cmpl a) (cmpl b)` is a complement of `sup a b`. -/
theorem de_morgan_sup
    (inf_comm : ∀ a b, inf a b = inf b a)
    (sup_comm : ∀ a b, sup a b = sup b a)
    (inf_assoc : ∀ a b c, inf (inf a b) c = inf a (inf b c))
    (sup_assoc : ∀ a b c, sup (sup a b) c = sup a (sup b c))
    (inf_top : ∀ a, inf a top = a)
    (sup_bot : ∀ a, sup a bot = a)
    (inf_absorb : ∀ a b, inf a (sup a b) = a)
    (sup_absorb : ∀ a b, sup a (inf a b) = a)
    (inf_distrib : ∀ a b c, inf a (sup b c) = sup (inf a b) (inf a c))
    (sup_distrib : ∀ a b c, sup a (inf b c) = inf (sup a b) (sup a c))
    (inf_cmpl : ∀ a, inf a (cmpl a) = bot)
    (sup_cmpl : ∀ a, sup a (cmpl a) = top)
    (a b : α) : cmpl (sup a b) = inf (cmpl a) (cmpl b) :=
  have hsup : sup (sup a b) (inf (cmpl a) (cmpl b)) = top :=
    calc sup (sup a b) (inf (cmpl a) (cmpl b))
        = inf (sup (sup a b) (cmpl a)) (sup (sup a b) (cmpl b)) :=
          sup_distrib (sup a b) (cmpl a) (cmpl b)
      _ = inf (sup (sup b a) (cmpl a)) (sup (sup a b) (cmpl b)) := by
          rw [sup_comm a b]
      _ = inf (sup b (sup a (cmpl a))) (sup (sup a b) (cmpl b)) := by
          rw [sup_assoc b a (cmpl a)]
      _ = inf (sup b top) (sup (sup a b) (cmpl b)) := by rw [sup_cmpl]
      _ = inf top (sup (sup a b) (cmpl b)) := by
          rw [sup_top sup_assoc inf_top sup_absorb sup_cmpl b]
      _ = inf top (sup a (sup b (cmpl b))) := by rw [sup_assoc a b (cmpl b)]
      _ = inf top (sup a top) := by rw [sup_cmpl]
      _ = inf top top := by
          rw [sup_top sup_assoc inf_top sup_absorb sup_cmpl a]
      _ = top := inf_top top
  have hinf : inf (sup a b) (inf (cmpl a) (cmpl b)) = bot :=
    calc inf (sup a b) (inf (cmpl a) (cmpl b))
        = inf (inf (sup a b) (cmpl a)) (cmpl b) :=
          (inf_assoc (sup a b) (cmpl a) (cmpl b)).symm
      _ = inf (inf (cmpl a) (sup a b)) (cmpl b) := by
          rw [inf_comm (sup a b) (cmpl a)]
      _ = inf (sup (inf (cmpl a) a) (inf (cmpl a) b)) (cmpl b) := by
          rw [inf_distrib (cmpl a) a b]
      _ = inf (sup (inf a (cmpl a)) (inf (cmpl a) b)) (cmpl b) := by
          rw [inf_comm (cmpl a) a]
      _ = inf (sup bot (inf (cmpl a) b)) (cmpl b) := by rw [inf_cmpl]
      _ = inf (sup (inf (cmpl a) b) bot) (cmpl b) := by
          rw [sup_comm bot (inf (cmpl a) b)]
      _ = inf (inf (cmpl a) b) (cmpl b) := by rw [sup_bot]
      _ = inf (cmpl a) (inf b (cmpl b)) := inf_assoc (cmpl a) b (cmpl b)
      _ = inf (cmpl a) bot := by rw [inf_cmpl]
      _ = bot := inf_bot inf_assoc sup_bot inf_absorb inf_cmpl (cmpl a)
  (cmpl_unique inf_comm sup_comm inf_top sup_bot inf_distrib inf_cmpl sup_cmpl
    (sup a b) (inf (cmpl a) (cmpl b)) hsup hinf).symm

/-! ## Corollaries -/

/-- `cmpl bot = top`.  `top` is the complement of `bot`. -/
theorem cmpl_bot
    (inf_comm : ∀ a b, inf a b = inf b a)
    (sup_comm : ∀ a b, sup a b = sup b a)
    (inf_assoc : ∀ a b c, inf (inf a b) c = inf a (inf b c))
    (inf_top : ∀ a, inf a top = a)
    (sup_bot : ∀ a, sup a bot = a)
    (inf_absorb : ∀ a b, inf a (sup a b) = a)
    (inf_distrib : ∀ a b c, inf a (sup b c) = sup (inf a b) (inf a c))
    (inf_cmpl : ∀ a, inf a (cmpl a) = bot)
    (sup_cmpl : ∀ a, sup a (cmpl a) = top)
    : cmpl bot = top :=
  (cmpl_unique inf_comm sup_comm inf_top sup_bot inf_distrib inf_cmpl sup_cmpl
    bot top
    (by rw [sup_comm bot top]; exact sup_bot top)
    (by rw [inf_comm bot top]; exact inf_bot inf_assoc sup_bot inf_absorb inf_cmpl top)).symm

/-- `cmpl top = bot`.  `bot` is the complement of `top`. -/
theorem cmpl_top
    (inf_comm : ∀ a b, inf a b = inf b a)
    (sup_comm : ∀ a b, sup a b = sup b a)
    (inf_top : ∀ a, inf a top = a)
    (sup_bot : ∀ a, sup a bot = a)
    (inf_distrib : ∀ a b c, inf a (sup b c) = sup (inf a b) (inf a c))
    (inf_cmpl : ∀ a, inf a (cmpl a) = bot)
    (sup_cmpl : ∀ a, sup a (cmpl a) = top)
    : cmpl top = bot :=
  (cmpl_unique inf_comm sup_comm inf_top sup_bot inf_distrib inf_cmpl sup_cmpl
    top bot (sup_bot top)
    (by rw [inf_comm top bot]; exact inf_top bot)).symm

end BooleanAlgebra

/-! ## Concrete instance: `α = Bool` (`and / or / not / false / true`)

All twelve axioms hold by `decide` on the closed `∀`-over-`Bool` goals,
which is axiom-clean for `Bool` ops.  This both inhabits the structure
and specializes the abstract De Morgan laws to `Bool`. -/

section BoolInstance

theorem bool_inf_comm : ∀ a b : Bool, (a && b) = (b && a) := by decide
theorem bool_sup_comm : ∀ a b : Bool, (a || b) = (b || a) := by decide
theorem bool_inf_assoc : ∀ a b c : Bool, ((a && b) && c) = (a && (b && c)) := by decide
theorem bool_sup_assoc : ∀ a b c : Bool, ((a || b) || c) = (a || (b || c)) := by decide
theorem bool_inf_absorb : ∀ a b : Bool, (a && (a || b)) = a := by decide
theorem bool_sup_absorb : ∀ a b : Bool, (a || (a && b)) = a := by decide
theorem bool_inf_distrib :
    ∀ a b c : Bool, (a && (b || c)) = ((a && b) || (a && c)) := by decide
theorem bool_sup_distrib :
    ∀ a b c : Bool, (a || (b && c)) = ((a || b) && (a || c)) := by decide
theorem bool_sup_bot : ∀ a : Bool, (a || false) = a := by decide
theorem bool_inf_top : ∀ a : Bool, (a && true) = a := by decide
theorem bool_sup_cmpl : ∀ a : Bool, (a || !a) = true := by decide
theorem bool_inf_cmpl : ∀ a : Bool, (a && !a) = false := by decide

/-- The abstract De Morgan law specialized to `Bool`:
    `!(a && b) = (!a || !b)`. -/
theorem bool_de_morgan_inf (a b : Bool) : (!(a && b)) = (!a || !b) :=
  de_morgan_inf
    (inf := Bool.and) (sup := Bool.or) (cmpl := Bool.not)
    (bot := false) (top := true)
    bool_inf_comm bool_sup_comm bool_inf_assoc bool_sup_assoc
    bool_inf_top bool_sup_bot bool_inf_absorb bool_sup_absorb
    bool_inf_distrib bool_sup_distrib bool_inf_cmpl bool_sup_cmpl a b

/-- The abstract dual De Morgan law specialized to `Bool`:
    `!(a || b) = (!a && !b)`. -/
theorem bool_de_morgan_sup (a b : Bool) : (!(a || b)) = (!a && !b) :=
  de_morgan_sup
    (inf := Bool.and) (sup := Bool.or) (cmpl := Bool.not)
    (bot := false) (top := true)
    bool_inf_comm bool_sup_comm bool_inf_assoc bool_sup_assoc
    bool_inf_top bool_sup_bot bool_inf_absorb bool_sup_absorb
    bool_inf_distrib bool_sup_distrib bool_inf_cmpl bool_sup_cmpl a b

/-- The abstract double-complement specialized to `Bool`: `!!a = a`. -/
theorem bool_cmpl_cmpl (a : Bool) : (!!a) = a :=
  cmpl_cmpl
    (inf := Bool.and) (sup := Bool.or) (cmpl := Bool.not)
    (bot := false) (top := true)
    bool_inf_comm bool_sup_comm bool_inf_top bool_sup_bot
    bool_inf_distrib bool_inf_cmpl bool_sup_cmpl a

end BoolInstance

end E213.Lib.Math.Order.BooleanAlgebra
