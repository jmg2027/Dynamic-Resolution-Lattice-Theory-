import E213.Theory.Raw.API
import E213.Lens.Bool213.SelfReferenceForms

/-!
# SelfReferenceEscapeBridge — the escape reduces to the oscillation, via one schema

`Lens.SelfReferenceThreeOutcomes` bundles the three §5.2 outcomes of one Raw self-pointing
— **oscillate** (Bool / liar, `not` has no fixed point), **converge** (Nat / Lambek, the
peel descent terminates), **escape** (residue, the diagonal is reached by none) — and states
that the bundle is a conjunction of three facts about three *different* objects, with the
caveat that *"no operator is forced across the three types, and none reduces to another."*

That caveat is **too strong for the escape/oscillate pair**, and this file draws the line
the caveat says is undrawn.  The construction-level escape schema
`Theory.Raw.CoResidue.diag_via_modifier` — *a modifier `m` fixpoint-free at the diagonal
makes `fun a' => m a' (c a' a')` reached by no row* — is **one operator that covers the
escape**, and its fixpoint-free hypothesis is **exactly the oscillation fact**: with the
Bool-style modifier `m a b := not b`, the hypothesis `∀ a, not (c a a) ≠ c a a` *is*
`SelfReferenceForms.bool_not_no_fixed_point` (the liar's "never settles").  So:

  > **Escape (the Bool-modifier diagonal) reduces to Oscillation (the Bool no-fixed-point)
  > through `diag_via_modifier`.**  The two are not independent: the no-fixed-point that
  > makes the Bool turn oscillate is the same fact that forces the diagonal out of every
  > row's image.

The dual pole is the Nat-style side: a modifier *with* a period-1 fixed point at a row
(`m a (c a a) = c a a` — the Lambek `decompose` self-coincidence, the convergent reading)
leaves that row **reached, not escaped** (`fixed_point_row_reached`).  So the single bit
that `diag_via_modifier` turns on — *does the modifier have a fixed point at the diagonal?*
— **is** the §5.2 Bool-vs-Nat bit: no fixed point (oscillate) ⟹ escape; fixed point
(converge) ⟹ reached.  This connects `seed/AXIOM/05_no_exterior.md` §5.2
(`SelfReferenceForms`) to `CoResidue` §22 (`diag_via_modifier`) — the link both were missing.

`bool_cantor_via_modifier` also shows the schema subsumes the canonical Bool-valued Cantor
(the diagonal of `cantor_raw_bool`), so this is not a toy specialisation.

All zero-axiom.
-/

namespace E213.Lens.Bool213.SelfReferenceEscapeBridge

open E213.Theory (Raw)
open E213.Lens.Bool213.Raw (not isBool)
open E213.Lens.Bool213.SelfReferenceForms (bool_not_no_fixed_point)
open E213.Theory.Raw.CoResidue (diag_via_modifier)

/-! ## §1 — escape via the Bool-style modifier, driven by the oscillation fact -/

/-- ★★★ **The Bool diagonal escapes every row — driven by the oscillation.**  For any cover
    `c : A → (A → Raw)` whose diagonal is Bool-valued (`isBool (c a a)`), the Bool-negation
    diagonal `fun a' => not (c a' a')` is reached by no row.  The proof is
    `diag_via_modifier` with the Bool-style modifier `m a b := not b`, whose fixpoint-free
    hypothesis is supplied — **verbatim** — by `bool_not_no_fixed_point`.  So the escape is
    the §5.2 oscillation no-fixed-point, run through the diagonal schema. -/
theorem bool_diagonal_escapes {A : Type} (c : A → (A → Raw))
    (hb : ∀ a, isBool (c a a) = true) :
    ∀ a, c a ≠ (fun a' => not (c a' a')) :=
  diag_via_modifier c (fun _ r => not r)
    (fun a => bool_not_no_fixed_point (c a a) (hb a))

/-- ★★ **The escape's hypothesis IS the oscillation fact.**  The two halves named together:
    the Bool diagonal escapes every row, **and** the very hypothesis that makes it escape is
    `∀ a, not (c a a) ≠ c a a` — the Bool-style no-fixed-point (`SelfReferenceForms`).  This
    is the reduction the `SelfReferenceThreeOutcomes` caveat said was absent: escape (on a
    Bool-valued cover) is *not* independent of oscillate — it is its diagonal consequence. -/
theorem escape_engine_is_bool_oscillation {A : Type} (c : A → (A → Raw))
    (hb : ∀ a, isBool (c a a) = true) :
    (∀ a, c a ≠ (fun a' => not (c a' a')))
    ∧ (∀ a, not (c a a) ≠ c a a) :=
  ⟨bool_diagonal_escapes c hb, fun a => bool_not_no_fixed_point (c a a) (hb a)⟩

/-! ## §2 — the dual pole: a Nat-style fixed point is a non-escaping (reached) row -/

/-- ★★ **A period-1 fixed point leaves the row reached.**  If the modifier has a fixed point
    at row `a`'s diagonal (`m a (c a a) = c a a` — the Nat-style / Lambek self-coincidence,
    the convergent reading), then the diagonal construction `fun a' => m a' (c a' a')` agrees
    with `c a` at `a`: the row is **reached**, not escaped.  `diag_via_modifier`'s separating
    step fails at exactly the rows where the modifier settles — so the escape/non-escape
    split *is* the no-fixed-point / fixed-point (Bool / Nat) split of §5.2. -/
theorem fixed_point_row_reached {A B : Type} (c : A → (A → B)) (m : A → B → B) (a : A)
    (hfix : m a (c a a) = c a a) :
    (fun a' => m a' (c a' a')) a = c a a :=
  hfix

/-! ## §3 — the schema subsumes the canonical Bool-valued Cantor (not a toy) -/

/-- The Bool negation has no fixed point — `(!b) ≠ b` for both values.  Propext-free
    (`Bool.noConfusion`, not `decide`).  The Lean-`Bool` twin of
    `SelfReferenceForms.bool_not_no_fixed_point` (which is on the Raw-valued Bool213). -/
theorem bool_not_ne_self : ∀ b : Bool, (!b) ≠ b
  | true  => fun h => Bool.noConfusion h
  | false => fun h => Bool.noConfusion h

/-- ★★★ **The canonical Cantor diagonal is `diag_via_modifier` at the Bool negation.**  For
    any `c : A → (A → Bool)`, the diagonal `fun a' => !(c a' a')` is reached by no row — the
    content of `cantor_raw_bool` (at `A = Raw`), here obtained as the modifier schema with
    `m a b := !b`, whose fixpoint-free hypothesis is `bool_not_ne_self`.  So the Bool
    no-fixed-point is not merely *one* escape's hypothesis: it is the engine of the canonical
    diagonal itself. -/
theorem bool_cantor_via_modifier {A : Type} (c : A → (A → Bool)) :
    ∀ a, c a ≠ (fun a' => !(c a' a')) :=
  diag_via_modifier c (fun _ b => !b) (fun a => bool_not_ne_self (c a a))

/-! ## §4 — capstone: the escape/converge split is the Bool/Nat self-reference bit -/

/-- ★★★ **One bit, two §5.2 forms, two §22 outcomes.**  `diag_via_modifier` turns on a
    single bit — whether the modifier has a fixed point at the diagonal value — and that bit
    is exactly the §5.2 Bool-vs-Nat self-reference distinction:

    1. **Bool / oscillate** (no fixed point): the Bool-negation modifier is fixpoint-free
       (`bool_not_no_fixed_point`), so it **escapes** every Bool-valued row
       (`bool_diagonal_escapes`) — the residue is reached by none;
    2. **Nat / converge** (fixed point): a modifier settling at a row's diagonal
       (`m a (c a a) = c a a`) leaves that row **reached** (`fixed_point_row_reached`) — the
       diagonal construction coincides there.

    So escape and convergence are not two independent outcomes among three: through the one
    schema `diag_via_modifier`, the escape (Bool-modifier form) is *driven by* the
    oscillation's no-fixed-point, and convergence is *the same schema's* fixed-point pole.
    This draws the §5.2 ↔ §22 line. -/
theorem escape_converge_is_bool_nat_bit {A : Type} (c : A → (A → Raw))
    (hb : ∀ a, isBool (c a a) = true) (a : A) :
    -- Bool/oscillate (no fixed point) ⟹ escape
    ((∀ x, not (c x x) ≠ c x x) → c a ≠ (fun a' => not (c a' a')))
    ∧ -- Nat/converge (fixed point at the diagonal) ⟹ reached, not escaped
    (not (c a a) = c a a → (fun a' => not (c a' a')) a = c a a) :=
  ⟨fun _ => bool_diagonal_escapes c hb a,
   fun hfix => fixed_point_row_reached c (fun _ r => not r) a hfix⟩

end E213.Lens.Bool213.SelfReferenceEscapeBridge
