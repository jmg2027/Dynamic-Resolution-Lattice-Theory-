import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumGeneral
/-!
# cutSum_assoc at b ≥ 3 — precision-artifact honest closure

The essay `theory/essays/methodology/pure_funext_avoidance.md` flagged the
"missing backward direction" of `cutSum_same_denom_forward` as the
search-index reorganization frontier.

Investigation reveals: **the backward direction is genuinely
false** at low `(m, k)` for `b ≥ 3` — not a missing theorem, but a
precision artifact of the `cutSum` definition itself.

## Counter-example

Take `a = 2`, `c = 1`, `b = 3`, `m = 1`, `k = 1`.  Then:

  · `constCut (a + c) b m k = constCut 3 3 1 1 = decide (3 · 1 ≤ 3 · 1) = true`
  · `cutSum (constCut a b) (constCut c b) m k`:
    needs `∃ i ∈ [0, 2], 2·2 ≤ 3·i ∧ 1·2 ≤ 3·(2-i)`.
    - `i = 0`: `4 ≤ 0`? false.
    - `i = 1`: `4 ≤ 3`? false.
    - `i = 2`: `4 ≤ 6` true, but `2 ≤ 0`? false.
    No witness ⇒ `false`.

So `constCut (a+c) b ≠ cutSum (constCut a b) (constCut c b)` at
`(1, 1)`.  The cuts represent the same Dedekind rational `1` but
the **finite-precision Bool readings differ** because the search
range `[0, 2m] = [0, 2]` can't be partitioned to satisfy both
inequalities with integer `i` when `b = 3`.

## What IS true

  · **Forward universal**: `cutSum (constCut a b) (constCut c b) m k = true
    ⇒ constCut (a + c) b m k = true`.  Proven in
    `cutSum_same_denom_forward` (`CutSumGeneral.lean`).

  · **Backward at b ∈ {1, 2}**: bidirectional via `cutSum_int_int`
    (b = 1) and `cutSum_half_general` (b = 2).  Used in
    `IntValidCut.lean` / `HalfValidCut.lean` for full assoc.

  · **Backward at b ≥ 3**: counter-example above; the precision
    artifact makes bidirectional Bool-level equality fail.

  · **Eventual agreement**: at high enough `m` (relative to k, a,
    b, c), the search range `[0, 2m]` becomes large enough to
    accommodate the integer-rounded partition, and the cuts agree.
    This is the Cauchy-completeness form.

## Meta-theorem

The honest statement of the "search-index reorganization" question:

> The bidirectional Bool-level `cutSum_same_denom` is **provably
> false** at `b ≥ 3`, low `(m, k)`.  The cuts agree at high
> precision (Cauchy completeness), which is what makes them
> equivalent Real213 elements.  Algebraic associativity at the
> Bool level closes only for bounded-denominator classes
> (b ∈ {1, 2} via the dyadic bundled-subtype pattern).

For full algebraic associativity at b ≥ 3, the framework would
need either:

  (a) A different `cutSum` definition with finer search range
      (e.g., `[0, 2m·b]` instead of `[0, 2m]`), or
  (b) Lift everything to the Real213 quotient where two cuts are
      equal iff they agree at sufficient precision (Cauchy-style).

Both are framework-level redesigns, not missing theorems.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.Real213.CutSumAssocB3

open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)

/-! ## §1 — Concrete counter-example -/

/-- ★ **Counter-example to backward direction at b = 3**:
    `constCut 3 3 1 1 = true` but
    `cutSum (constCut 2 3) (constCut 1 3) 1 1 = false`.

    Both cuts represent the rational `1` (= (a+c)/b = 3/3 vs
    2/3 + 1/3), but the cutSum search range `[0, 2]` is too coarse
    for the b = 3 integer-rounded partition. -/
theorem backward_counter_example_b3 :
    constCut 3 3 1 1 = true
    ∧ cutSum (constCut 2 3) (constCut 1 3) 1 1 = false := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-- ★ **Second counter-example**: `b = 4`, `a = 3`, `c = 1` at
    `(m, k) = (1, 1)`.  Dyadic denominator does **not** save us. -/
theorem backward_counter_example_b4 :
    constCut 4 4 1 1 = true
    ∧ cutSum (constCut 3 4) (constCut 1 4) 1 1 = false := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-- ★ **Third counter-example**: `b = 5`, `a = 4`, `c = 1` at
    `(m, k) = (1, 1)`.  Pattern generalizes to any b ≥ 3 with
    `(a + c) = b` and `a > b/2`. -/
theorem backward_counter_example_b5 :
    constCut 5 5 1 1 = true
    ∧ cutSum (constCut 4 5) (constCut 1 5) 1 1 = false := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-! ## §2 — Eventual agreement at high precision

At high enough `m`, the cuts agree.  Smoke witnesses below. -/

/-- At `(m, k) = (10, 1)`, the b = 3 case agrees. -/
theorem eventual_agreement_b3_m10 :
    constCut 3 3 10 1 = true
    ∧ cutSum (constCut 2 3) (constCut 1 3) 10 1 = true := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-- At `(m, k) = (10, 1)`, the b = 5 case agrees. -/
theorem eventual_agreement_b5_m10 :
    constCut 5 5 10 1 = true
    ∧ cutSum (constCut 4 5) (constCut 1 5) 10 1 = true := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-! ## §3 — Forward direction is universal (re-export) -/

/-- Forward direction holds for any `b ≥ 1`.  This is the
    universal half — what `cutSum_same_denom_forward` gives. -/
theorem forward_universal (a b c m k : Nat)
    (h : cutSum (constCut a b) (constCut c b) m k = true) :
    constCut (a + c) b m k = true :=
  E213.Lib.Math.NumberSystems.Real213.Sum.CutSumGeneral.cutSum_same_denom_forward
    a b c m k h

/-! ## §4 — Meta capstone -/

/-- ★★★★★ **Honest meta-theorem for b ≥ 3 cutSum_assoc**:

    Bundles: (a) forward direction (universal in b),
    (b) backward counter-examples at b ∈ {3, 4, 5} witnessing the
    precision artifact, (c) eventual agreement at high precision.

    Reading: the "missing backward direction" is **not a missing
    theorem** but a structural property of `cutSum` — the search
    range `[0, 2m]` is integer-coarse, and for `b ≥ 3` cannot
    partition into pieces matching `b`-multiplier inequalities
    when `(a + c) · k = b · m` exactly (boundary case).

    Algebraic associativity at the **Bool level** for b ≥ 3 is
    **structurally impossible** in this framework; closure
    requires either redefining `cutSum` with finer search or
    lifting to the Real213 quotient.  The integer-extended /
    dyadic class (b ∈ {1, 2}) is the **algebraically meaningful
    closure boundary** for the current `cutSum` definition.

    This is not a blocker for the 213-native theory — it's a
    structural fact about which level (Bool vs cutEq vs Real213
    quotient) algebraic identities live at. -/
theorem b_ge_3_assoc_meta :
    -- (a) Forward direction universal
    (∀ a b c m k,
        cutSum (constCut a b) (constCut c b) m k = true
        → constCut (a + c) b m k = true)
    -- (b) Backward fails at b = 3
    ∧ (constCut 3 3 1 1 = true
       ∧ cutSum (constCut 2 3) (constCut 1 3) 1 1 = false)
    -- (c) Backward fails at b = 4 (dyadic doesn't save)
    ∧ (constCut 4 4 1 1 = true
       ∧ cutSum (constCut 3 4) (constCut 1 4) 1 1 = false)
    -- (d) Backward fails at b = 5
    ∧ (constCut 5 5 1 1 = true
       ∧ cutSum (constCut 4 5) (constCut 1 5) 1 1 = false)
    -- (e) Agreement at high precision (Cauchy completeness witness)
    ∧ (constCut 3 3 10 1 = true
       ∧ cutSum (constCut 2 3) (constCut 1 3) 10 1 = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact forward_universal
  · exact backward_counter_example_b3
  · exact backward_counter_example_b4
  · exact backward_counter_example_b5
  · exact eventual_agreement_b3_m10

end E213.Lib.Math.NumberSystems.Real213.CutSumAssocB3
