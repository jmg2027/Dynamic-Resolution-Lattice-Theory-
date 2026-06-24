/-!
# The residue–cost bridge: where the omniscience cost actually attaches (∅-axiom)

`theory/essays/foundations/the_conserved_residue.md` claimed a criterion — *reaches the
power-object → costs something* — but the investigation found a **crack**: the residue
(`DiagonalBase.cantor_stream_not_enumerable`, `object1_not_surjective`) *reaches* the power-object
`ℕ → Bool` yet costs **nothing** (it is a free ∅-axiom theorem, the ledger's cost-0 base), while
`LPO`/`WLPO` concern the *same* `ℕ → Bool` and *do* cost.  So "reaches the power-object" does **not**
imply "costs an omniscience principle."

This file fixes the criterion and verifies it.  The correct dial is the **positive/negative** split
(the positive twin, `Order/KnasterResidue.bool_selfref_iff_no_fpf`), crossed with **finite/infinite**:

  * **negative / existential** (∃ a diagonal escapee — the residue) is **free at every size**: one
    witness suffices (`diag_escapes_free` below; `cantor_stream_not_enumerable` is the full form);
  * **positive / universal** (decide *all* of `f` — `LPO`/`WLPO`) is **free on a finite domain**
    (`finite_lpo_free`, `finite_wlpo_free` — `Bool` in place of `ℕ`, by `decide`-style case bash) and
    **costs** only over an *infinite* domain.

So the omniscience cost of `LPO`/`WLPO` is **entirely the infinity of `ℕ` in the positive
direction**: the very same verdict over a finite carrier is an ∅-axiom theorem.  The cost attaches
exactly at *positive ∧ infinite*; *negative* (any size) and *finite* (any polarity) are free.

**The corrected criterion (predictive, retrodicts the ledger).**  A decision is ∅-axiom-free iff it
is **negative** (an existential diagonal) **or** over a **finite** domain; it costs an omniscience
principle iff it demands a **positive/universal verdict over an infinite (power-object) domain**.
Checking `Logic/Capstone.reverse_math_ledger` against this:

  | ledger entry | polarity / domain | predicted | ledger |
  |---|---|---|---|
  | `cantor_stream_not_enumerable`, `object1_not_surjective` | negative, infinite | free | cost-0 ✓ |
  | `lpo_decides_pi01` ("decide infinite-below") | positive, infinite | cost | LPO ✓ |
  | `finite_{lpo,wlpo}_free` (here) | positive, finite | free | ∅-axiom ✓ |

The criterion retrodicts the existing cost-0/cost split on entries it was not built from — the
positive/negative dial *explains* the ledger's free/cost boundary rather than restating it.
All ∅-axiom.
-/

namespace E213.Lib.Math.Logic.ResidueCostBridge

/-! ## Finite LPO / WLPO are free — the cost is the infinity, in the positive direction -/

/-- ★★★ **Finite LPO is free.**  The `Bool` analogue of `LPO` (`Omniscience.LPO`, `∀ f : ℕ → Bool,
    (∃ n, f n = true) ∨ (∀ n, f n = false)`) needs **no omniscience**: over a finite domain the
    existential-or-universal verdict is decided by a case bash.  So `LPO`'s cost is *entirely* the
    infinity of `ℕ` in the positive/universal direction. -/
theorem finite_lpo_free (f : Bool → Bool) :
    (∃ b, f b = true) ∨ (∀ b, f b = false) := by
  cases hT : f true with
  | true => exact Or.inl ⟨true, hT⟩
  | false =>
    cases hF : f false with
    | true => exact Or.inl ⟨false, hF⟩
    | false => exact Or.inr (fun b => by cases b with | true => exact hT | false => exact hF)

/-- ★★★ **Finite WLPO is free.**  The `Bool` analogue of `WLPO` (`∀ f : ℕ → Bool, (∀ n, f n = false)
    ∨ ¬ (∀ n, f n = false)`): over `Bool` the universal-or-its-negation is an ∅-axiom theorem.  The
    omniscience cost of `WLPO` is located *precisely* at the finite→infinite transition. -/
theorem finite_wlpo_free (f : Bool → Bool) :
    (∀ b, f b = false) ∨ ¬ (∀ b, f b = false) := by
  cases hT : f true with
  | true => exact Or.inr (fun h => Bool.noConfusion ((h true).symm.trans hT))
  | false =>
    cases hF : f false with
    | true => exact Or.inr (fun h => Bool.noConfusion ((h false).symm.trans hF))
    | false => exact Or.inl (fun b => by cases b with | true => exact hT | false => exact hF)

/-! ## The negative direction is free even over the infinite power-object -/

private theorem bnot_ne : ∀ b : Bool, (!b) ≠ b
  | true  => fun h => Bool.noConfusion h
  | false => fun h => Bool.noConfusion h

/-- ★★★ **The negative diagonal is free over `ℕ → Bool`.**  The diagonal `fun k => !(e k k)` differs
    from *every* row `e n` — witnessed at the single point `k = n`, no omniscience.  Existence needs
    one escapee, so the negative direction stays cost-0 even over the infinite power-object (the full
    enumeration form is `DiagonalBase.cantor_stream_not_enumerable`).  This is the complement of
    `finite_{lpo,wlpo}_free`: negative is free at every size, positive is free only when finite. -/
theorem diag_escapes_free (e : Nat → Nat → Bool) (n : Nat) :
    (fun k => !(e k k)) ≠ e n :=
  fun h => bnot_ne (e n n) (congrFun h n)

end E213.Lib.Math.Logic.ResidueCostBridge
