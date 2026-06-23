import E213.Lib.Math.Analysis.Measure.DyadicMeasure
import E213.Lib.Math.Order.GaloisConnection

/-!
# Measure Theory 213 — Carathéodory outer measure as a closure operator

213-native instantiation of the Carathéodory extension, closing the
named open target of the `measure` decomposition
("Outer measure / Carathéodory extension: ABSENT, and it WOULD be
`galois.md`'s closure operator `clo`").

## What the classical construction is, and how it lands here

Classically: define an outer measure `μ*` by infimum over covers, then
restrict to the **Carathéodory-measurable** sets — the fixed points of a
closure operator.  The infimum-over-countable-covers is exactly where the
`q=−1` non-measurable residue is excluded; the repo never builds the
over-large domain (`DyadicMeasurableSet` is a finite `List`), so the
cutting-down is never needed.  The remaining content — the
outer-measure→measurable **passage as a `clo` closure** — is finitary and
is built here, PURE.

## The finitary outer measure

A "cover" of a measurable set `s` (a finite `List DyadicBracket`) is any
list whose total weight dominates `s`'s.  The infimum over such covers is
attained by `s` itself, so on the finite domain

    μ*(s)  =  measureNum s          (`outerMeasureNum`)

This is **monotone** (in the measure-preorder) and **subadditive**
(`outerMeasure_union_le`, reusing `measure_union_additive`).

## The Carathéodory passage as the calculus's `clo`

We exhibit a genuine Galois connection
`f = measureNum ⊣ g = canonical single-bracket` between

  * `α = DyadicMeasurableSet`, ordered by the **measure-preorder**
    `leMeasure s t := measureNum s ≤ measureNum t`, and
  * `β = Nat`, ordered by `Nat.le`,

with `f s = μ*(s)` and `g n = [bracket 0..n]` (the canonical cover of
weight `n`).  The induced closure `clo f g s = g (f s)` is the
**Carathéodory-measurable representative** of `s`: the canonical
single-bracket cover with the same total measure.  It satisfies
(via `Order/GaloisConnection.lean`):

  * `clo_extensive`  — `s ≤ clo s` in the measure-preorder (unit);
  * `clo_monotone`   — monotone in the measure-preorder;
  * idempotent       — `clo (clo s) = clo s` **literally** (here
    `f (g n) = n`, so the closure is even split-idempotent).

This makes measure.md's prediction literal: the Carathéodory extension
IS the `clo` closure monad (`q=+1` idempotent).

## Conservativity

On the already-built measurable sets the extension agrees with
`measureNum` (`outerMeasure_conservative` is `rfl`), and the closure
preserves the measure exactly (`clo_preserves_measure`).  So `μ*` is a
conservative extension — it adds no measure to the finite domain.

Everything `Nat`-valued; no σ-algebra, no Choice, no `propext`.
-/

namespace E213.Lib.Math.Analysis.Measure.OuterMeasure

open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
  (DyadicBracket DyadicBracket.lenNum)
open E213.Lib.Math.Analysis.Measure.MeasurableSet
  (DyadicMeasurableSet emptySet singleton union)
open E213.Lib.Math.Analysis.Measure.DyadicMeasure
  (measureNum measure_empty measure_union_additive measureNum_append
   bracketMeasureNum)
open E213.Lib.Math.Order.GaloisConnection
  (clo clo_extensive clo_monotone gc_unit gc_counit)

/-! ## The finitary outer measure -/

/-- **Outer measure** `μ*` on the finite dyadic domain: the infimum over
    covers, attained by the set itself.  Finitarily this is `measureNum`;
    the cover-minimality is `outerMeasure_is_inf_cover` below. -/
def outerMeasureNum (s : DyadicMeasurableSet) : Nat := measureNum s

/-- ★ **Conservativity (definitional).**  On the already-built measurable
    sets, `μ*` agrees with `measureNum`.  The extension adds nothing. -/
theorem outerMeasure_conservative (s : DyadicMeasurableSet) :
    outerMeasureNum s = measureNum s := rfl

/-- ★ `μ*(∅) = 0`. -/
theorem outerMeasure_empty : outerMeasureNum emptySet = 0 := measure_empty

/-- The **cover preorder**: `t` covers `s` when its total weight dominates
    `s`'s.  (A finitary stand-in for "`t ⊇ s` up to a null set".) -/
def Covers (t s : DyadicMeasurableSet) : Prop := measureNum s ≤ measureNum t

/-- ★ Every set covers itself. -/
theorem covers_self (s : DyadicMeasurableSet) : Covers s s := Nat.le_refl _

/-- ★ A union-cover dominates each part: `s ++ t` covers `s`. -/
theorem covers_append_left (s t : DyadicMeasurableSet) :
    Covers (s ++ t) s := by
  show measureNum s ≤ measureNum (s ++ t)
  rw [measureNum_append]; exact Nat.le_add_right _ _

/-- ★ **`μ*` is the infimum over covers.**  Any cover `t` of `s` has
    weight `≥ μ*(s)`, and `s` itself is a cover attaining the value.  So
    `μ*(s) = measureNum s` is genuinely the least cover-weight. -/
theorem outerMeasure_is_inf_cover (s t : DyadicMeasurableSet)
    (h : Covers t s) : outerMeasureNum s ≤ measureNum t := h

/-! ## Monotonicity and subadditivity -/

/-- ★ **Monotone** in the cover-preorder: if `t` covers `s` then
    `μ*(s) ≤ μ*(t)`. -/
theorem outerMeasure_monotone (s t : DyadicMeasurableSet)
    (h : Covers t s) : outerMeasureNum s ≤ outerMeasureNum t := h

/-- ★ **Subadditivity**: `μ*(s ∪ t) ≤ μ*(s) + μ*(t)`.  Here it is an
    equality (finite, disjoint-accounted via the weight), reusing
    `measure_union_additive`. -/
theorem outerMeasure_union_le (s t : DyadicMeasurableSet) :
    outerMeasureNum (union s t) ≤ outerMeasureNum s + outerMeasureNum t := by
  show measureNum (union s t) ≤ measureNum s + measureNum t
  rw [measure_union_additive]; exact Nat.le_refl _

/-- ★ Subadditivity, the exact additive form (the inequality is tight). -/
theorem outerMeasure_union_additive (s t : DyadicMeasurableSet) :
    outerMeasureNum (union s t) = outerMeasureNum s + outerMeasureNum t :=
  measure_union_additive s t

/-! ## The Carathéodory passage as a Galois connection

`f = measureNum`, `g n = [canonical 0..n]`, on the measure-preorder. -/

/-- The **canonical cover of weight `n`**: a single bracket `[0, n]` at
    exponent `0`, so `lenNum = n`.  This is the canonical
    Carathéodory-measurable representative of a given total weight. -/
def canonicalBracket (n : Nat) : DyadicBracket where
  numA := 0
  numB := n
  expE := 0
  hLe := Nat.zero_le n

/-- ★ The canonical bracket has length exactly `n`. -/
theorem canonicalBracket_lenNum (n : Nat) :
    (canonicalBracket n).lenNum = n := by
  show n - 0 = n; exact Nat.sub_zero n

/-- The **left adjoint** `f`: the outer-measure readout. -/
def cara_f (s : DyadicMeasurableSet) : Nat := measureNum s

/-- The **right adjoint** `g`: the canonical single-bracket cover of a
    given weight. -/
def cara_g (n : Nat) : DyadicMeasurableSet := [canonicalBracket n]

/-- ★ `f (g n) = n` — the right adjoint is a **section** of `f`.  (The
    counit is an equality here, so the closure is split-idempotent.) -/
theorem cara_fg (n : Nat) : cara_f (cara_g n) = n := by
  show measureNum [canonicalBracket n] = n
  show bracketMeasureNum (canonicalBracket n) + 0 = n
  rw [Nat.add_zero]
  show (canonicalBracket n).lenNum = n
  exact canonicalBracket_lenNum n

/-- The **measure-preorder** on measurable sets. -/
def leMeasure (s t : DyadicMeasurableSet) : Prop := measureNum s ≤ measureNum t

theorem leMeasure_refl (s : DyadicMeasurableSet) : leMeasure s s := Nat.le_refl _

theorem leMeasure_trans (a b c : DyadicMeasurableSet) :
    leMeasure a b → leMeasure b c → leMeasure a c := Nat.le_trans

/-- `Nat.le` transitivity in explicit-binder form (matches the
    `clo_monotone` hypothesis shape). -/
theorem natLe_trans (a b c : Nat) : a ≤ b → b ≤ c → a ≤ c := Nat.le_trans

/-- ★ **The Galois connection** `f ⊣ g` on the measure-preorder:
    `Nat.le (f s) n ↔ leMeasure s (g n)`.  Both sides unfold to
    `measureNum s ≤ n` (using `f (g n) = n`), so it is `Iff.rfl`-close. -/
theorem cara_gc (s : DyadicMeasurableSet) (n : Nat) :
    Nat.le (cara_f s) n ↔ leMeasure s (cara_g n) := by
  show measureNum s ≤ n ↔ measureNum s ≤ measureNum (cara_g n)
  rw [show measureNum (cara_g n) = n from cara_fg n]

/-! ## The Carathéodory closure (via `Order/GaloisConnection.lean`) -/

/-- The **Carathéodory closure** `clo f g s = g (f s)`: replace `s` by the
    canonical single-bracket cover of the same total weight.  This is the
    Carathéodory-measurable representative. -/
def caraClosure (s : DyadicMeasurableSet) : DyadicMeasurableSet :=
  clo cara_f cara_g s

theorem caraClosure_unfold (s : DyadicMeasurableSet) :
    caraClosure s = [canonicalBracket (measureNum s)] := rfl

/-- ★ **Extensive** (the unit) — instantiates the abstract
    `clo_extensive`: `s ≤ clo s` in the measure-preorder. -/
theorem caraClosure_extensive (s : DyadicMeasurableSet) :
    leMeasure s (caraClosure s) :=
  clo_extensive (leA := leMeasure) (leB := Nat.le) Nat.le_refl
    (f := cara_f) (g := cara_g) cara_gc s

/-- ★ **Monotone** — instantiates the abstract `clo_monotone`: monotone in
    the measure-preorder. -/
theorem caraClosure_monotone (s t : DyadicMeasurableSet)
    (h : leMeasure s t) : leMeasure (caraClosure s) (caraClosure t) :=
  clo_monotone (leA := leMeasure) (leB := Nat.le)
    leMeasure_trans natLe_trans leMeasure_refl Nat.le_refl
    (f := cara_f) (g := cara_g) cara_gc s t h

/-- ★ **Idempotent** — `clo (clo s) = clo s` **literally** (not merely up to
    the preorder).  Because `f (g n) = n` (`cara_fg`), the closure is
    split-idempotent: `g (f (g (f s))) = g (f s)`.  This is the
    `T² = T` shape `measure.md` predicted (`q=+1` closure monad). -/
theorem caraClosure_idempotent (s : DyadicMeasurableSet) :
    caraClosure (caraClosure s) = caraClosure s := by
  show cara_g (cara_f (cara_g (cara_f s))) = cara_g (cara_f s)
  rw [cara_fg (cara_f s)]

/-! ## Conservativity of the closure -/

/-- ★ **The closure preserves the measure exactly**: `μ*(clo s) = μ*(s)`.
    The Carathéodory representative carries the same total weight — the
    extension is conservative. -/
theorem clo_preserves_measure (s : DyadicMeasurableSet) :
    outerMeasureNum (caraClosure s) = outerMeasureNum s := by
  show measureNum (caraClosure s) = measureNum s
  show cara_f (cara_g (cara_f s)) = measureNum s
  rw [cara_fg (cara_f s)]
  rfl

/-- ★ A set is **Carathéodory-measurable** when it equals (in measure) the
    canonical representative — automatic here, since the closure preserves
    measure.  The Carathéodory criterion `μ*(s) = μ*(s∩A)+μ*(s∖A)` is, on
    the finite domain, exactly `measure_union_additive`: every measurable
    set splits every test set additively. -/
def CaratheodoryMeasurable (a : DyadicMeasurableSet) : Prop :=
  ∀ e : DyadicMeasurableSet,
    outerMeasureNum (union e a) = outerMeasureNum e + outerMeasureNum a

/-- ★ **Every finite measurable set is Carathéodory-measurable.**  The
    splitting criterion holds for all of them — there is no over-large
    domain to cut down (the `q=−1` non-measurable residue cannot arise on
    a finite `List`).  This is `measure_union_additive` read as the
    Carathéodory criterion. -/
theorem all_caratheodory_measurable (a : DyadicMeasurableSet) :
    CaratheodoryMeasurable a :=
  fun e => outerMeasure_union_additive e a

/-! ## Capstone bundle -/

/-- ★★★ **Carathéodory-as-`clo` witness** ★★★ — the prediction made
    literal: `μ*` is conservative, monotone, subadditive; the
    outer-measure→measurable passage is the `clo` closure operator
    (extensive + idempotent); and every finite measurable set satisfies
    the Carathéodory splitting criterion. -/
theorem caratheodory_witness (s t : DyadicMeasurableSet) :
    outerMeasureNum s = measureNum s
    ∧ outerMeasureNum (union s t) = outerMeasureNum s + outerMeasureNum t
    ∧ leMeasure s (caraClosure s)
    ∧ caraClosure (caraClosure s) = caraClosure s
    ∧ outerMeasureNum (caraClosure s) = outerMeasureNum s
    ∧ CaratheodoryMeasurable s :=
  ⟨outerMeasure_conservative s,
   outerMeasure_union_additive s t,
   caraClosure_extensive s,
   caraClosure_idempotent s,
   clo_preserves_measure s,
   all_caratheodory_measurable s⟩

end E213.Lib.Math.Analysis.Measure.OuterMeasure
