# Async growth — open seeds after the chapter closed

**Closure record**: `theory/math/foundations/async_growth.md` (the
full 8-item agenda, 74 PURE; origin `seed/ORIGIN_RAW.md`).  These are
the residual open directions the chapter's "Open frontier" section
names; they live here.

## 1. Exact-membership converse of reachability
`Closed P ∧ Nodup P ⟹ ∃ reachable s, MemEq s P`.  `list_reached`
gives the ⊇ form; the exact form needs the argmin-by-depth fill
construction (`List213.length_filter_lt_of_mem` as the measure;
atoms case via "depth 0 ⟹ ∈ {a,b}").

## 2. Fused step-3 swap-class census (= 4)
Machine-enumerated in the debate (fused ladder 1, 1, 4, 19); the
Lean closure needs a state-enumeration function over `Async.Step`,
then `decide`.

## 3. Uniform dagSize bounds
`depth ≤ dagSize ≤ leaves − 1` for ALL Raw by `Raw.rec` induction
(census closes depth ≤ 3 only), and minimal-run-length = `dagSize`
(fused) — the event-cost reading as a theorem.

## 4. Axes of growth
A definition of "stable independent directions" of the ancestor
order, and whether `(NS, NT) = (3, 2)` forces their count.
Constraint already proven in spirit: the bare ordering fraction
diverges (no finite dimension readout lives on a depth scale), so
any finite axis-count must anchor at the past-completeness boundary
or in the deployment Lens — touches the geometrization ansatz's
chart-Lens knot.
