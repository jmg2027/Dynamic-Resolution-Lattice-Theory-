# Session Handoff — 2026-06-04 (G121 M2 universal close)

## Branch
`claude/g121-geometric-knot-OIMkV` — pushed.
`cd lean && lake build` ✓ (full package).  New + touched modules
∅-axiom verified via `tools/scan_axioms.py`.

## What Was Done This Session

### G121 knot M2 — universal δ⁰-kernel = constants (structural close)

M2 ("chart-Lens visible count = chartBase − 1") was an **abstract
close for K_{3,2}^{(c=2)} only**: `KChartLens` carried
`selfPointingAxes` as a user-supplied value, grounded by a `decide`
on the single deployment (`V32Betti`).  The fully universal
`∀ NS NT c` version was flagged open in three files
("requires graph-walk connectedness induction").

Now closed **universally and ∅-axiom** at the structural level:

- **NEW** `lean/E213/Lib/Math/Cohomology/Bipartite/Parametric/KernelConstancyUniversal.lean`
  (14 PURE / 0 DIRTY).  For every connected K_{NS,NT}^{(c)}
  (NS ≥ 1, NT ≥ 1, c ≥ 1):
    · `isKer_iff_const` — δ⁰-kernel cochain ⟺ globally constant
    · `isKer_const_false_or_true` — kernel = exactly the 2 constants
    · `isKer_root_determines` — root colour = single free parameter
      (`dim ker δ⁰ = 1`, b₀ = 1)
    · `visible_plus_one` — `(NS+NT) − 1` additively
    · ★★★★★ `universal_kernel_close` — the bundle.
  Uses a **product-indexed coboundary** `delta0Tri`
  (edges `Fin NS × Fin NT × Fin c`, no integer-decode division) and
  additive T-index recovery via `Nat.le.dest`, so the connectedness
  proof carries zero `propext`.  Pointwise statements throughout
  (no `funext` → no `Quot.sound`).

- **Consumer** `Geometry/GeometrizationConjecture/KChartLensAbstract.lean`:
  `forcedKChartLens` (selfPointingAxes = 1, chartVisibleAxes =
  `(NS+NT).pred`, forced by connectedness — no supplied value) +
  ★★★★★★ `m2_universal_forced_partition` +
  `forcedKChartLens_chartVisible_eq_ansatz` (forced value = ansatz
  `chartVisibleAxes NS NT = (NS+NT)−1`, by `rfl`).

- `Ansatz.selfPointingAxes` docstring updated: the `1` is now the
  *derived* kernel dimension, not a committed value.

### Why the old enumeration route was blocked (recorded)
Counting flat cochain indices universally forces core Lean's
`Nat.div` / `Nat.mod` lemmas to decode `Fin (c·NS·NT)` → `(s,t,m)`;
**all** of them carry `propext` (probe-verified), and
`Nat.add_sub_cancel'` / `Nat.sub_lt_left_of_lt_add` likewise.  So the
universal-flat statement is axiom-dirty by Lean-core construction —
a purity artifact, not a math gap.  The product-form route avoids it.

## G121 knot status (after this session)

| Knot | Status |
|---|---|
| M1 (why d_213 = 5) | two-route close (atomicity a₀=2 + Möbius c=2); irreducible at a₀=2 = Raw Clause 1 |
| M2 (chart count = d−1) | **UNIVERSAL CLOSE (structural)** — δ⁰-kernel = constants (dim 1) for all connected K, ∅-axiom |
| M3 (NT-axis split) | **open frontier** — derive *which* T-axis is time vs self-pointing, and why the split is T-side not S-side (the live knot) |
| M4 (KK firewall) | doc-level stereotype warnings |

The headline `d_M = d_213 − 1` now holds **universally**:
`chartVisibleAxes = chartBase − 1` for every connected K, the "−1"
being the universally 1-dimensional self-pointing kernel.

## Open Problems (Priority Order)

1. **M3 (NT-axis split)** — the lone knot needing a genuine
   derivation.  M2 proves *one* axis is self-pointing (the 1-dim
   kernel); M3 asks which of the N_T axes is time vs self-pointing
   and why the donation is T-side (cardinality 2), not S-side.
   Candidate handles: c=2 binary cover acts on T-side; K_{3,2}
   bipartite asymmetry.  Note: the originator deprioritized M3 as
   "downstream of physics interpretation" — confirm before pushing.
2. **M2 operator-flat bridge (optional)** — a division-free
   `Fin (c·NS·NT) ≃ Fin NS × Fin NT × Fin c` re-indexing would
   transport the structural kernel result to the flat
   `CochSpaces.delta0`, giving the universal-flat statement
   ∅-axiom.  Not a math obstruction; the structural content is
   closed.

## File Map
```
lean/E213/Lib/Math/Cohomology/Bipartite/Parametric/KernelConstancyUniversal.lean  ← NEW (14 PURE): universal δ⁰-kernel = constants
lean/E213/Lib/Math/Cohomology/Bipartite/Parametric/INDEX.md                       ← +KernelConstancyUniversal row + universal-closure section
lean/E213/Lib/Math/Geometry/GeometrizationConjecture/KChartLensAbstract.lean       ← +forcedKChartLens, m2_universal_forced_partition (import KernelConstancyUniversal)
lean/E213/Lib/Math/Geometry/GeometrizationConjecture/Ansatz.lean                   ← selfPointingAxes docstring (derived)
lean/E213/Lib/Math/Geometry/GeometrizationConjecture/INDEX.md                      ← M2 status → UNIVERSAL CLOSE
theory/math/cohomology/bipartite.md                                               ← universal-kernel narrative section
research-notes/frontiers/G121_dim4_self_pointing_axis.md                          ← Part 4: M2 universal close
```

## Three-tier state
- **Promotions this session**: none new (M2 narrative lives in the
  existing `theory/math/cohomology/bipartite.md` chapter).
- **Active scratchpad**: `research-notes/frontiers/G121_dim4_self_pointing_axis.md`
  (Part 4 added).  Sink rule holds.
