# G19 — Pure-Equality Cluster Stratified by Proof Method

**Author:** Claude (inspection); Mingu Jeong (methodology directive)
**Date:** 2026-05-XX (continues G17/G18)
**Companion files:**
  - `research-notes/G17_inspect_equality_rfl.md`     (50 specimens / 519 total)
  - `research-notes/G17_inspect_equality_decide.md`  (50 / 1263)
  - `research-notes/G17_inspect_equality_rw.md`      (50 / 377)
  - `research-notes/G17_inspect_equality_match.md`   (30 / 38)
  - `research-notes/G17_inspect_equality_cases.md`   (30 / 105)

## §0  How to read this note

Per Mingu's methodology directive: classification must EMERGE from
patient inspection, not be imposed.  This note partitions the 2,548
pure-equality decls (42% of the codebase) by *proof method only* —
mechanical, not interpretive — and presents one paradigm specimen
from each stratum side by side.  Read the specimens, and let
your own intuition tell you what the strata *express*.

The strata cover 2,302 of the 2,548 (90%); the remaining 246 use
other tactic combinations (refine without rfl/decide/rw, etc.) and
are not displayed here.

## §1  The five strata at a glance

```
  519  rfl-only    (identity by definitional unfolding)
 1263  decide-only (identity by computation, no structural rw)
  377  rw-using    (identity by structural propagation)
  105  cases-using (identity by inductive pattern destruction)
   38  match-using (identity by term-mode case analysis)
─────
 2302  ≈ 90% of pure-equality decls
```

Frequencies suggest: *the two computational strata together are 78%*
(rfl + decide); the two structural strata are 22% (rw + cases + match).

## §2  Side-by-side paradigm specimens

### §2.1  rfl-shape — identity by definitional unfolding

```lean
-- Firmware/Raw/CmpIndependence.lean
theorem transport_a (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2) :
    transport cmp1 cmp2 h1 h2 (RawBy.a cmp1) = RawBy.a cmp2 := rfl

-- Hypervisor/Lens/Compose/OnLensImage.lean
theorem boolToConstLens_true : boolToConstLens true = constTrueLens := rfl
theorem boolToConstLens_false : boolToConstLens false = constFalseLens := rfl
```

What the kernel does: unfold both sides, observe identical normal forms.
What the theorem expresses: "by definition, these two expressions
denote the same Lean term."  Single-step reduction.

### §2.2  decide-shape — identity by computation

```lean
-- Hypervisor/Lens/Instances/AB.lean
theorem leaves_equates : Lens.leaves.view rAAB = Lens.leaves.view rABB := by decide

-- Hypervisor/Lens/Morphism/NoDepthParity.lean
theorem rA1_depth_odd : Lens.depth.view rA1 % 2 = 1 := by decide

-- Math/CayleyDickson/CDDouble.lean
theorem K_squared : (I' * J) * (I' * J) = ⟨⟨-1, 0⟩, 0⟩ := by decide

-- Math/Cohomology/Dyadic/Pisano/Predictor.lean
theorem pisano_predict_correct_at_3 : pisano_predict 3 (by decide) = 4 := by decide
```

What the kernel does: execute LHS to a value, execute RHS, compare.
What the theorem expresses: "compute both sides; they yield the
same finite value."  Multi-step reduction; depth bounded by the
specific input size.

### §2.3  rw-shape — identity by structural propagation

```lean
-- Firmware/Raw/CmpIndependence.lean
theorem canonicalBy_Tree_cmp (t : Tree) :
    canonicalBy Tree.cmp t = t.canonical := by
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      unfold canonicalBy Tree.canonical
      rw [ihx, ihy]
      rfl
```

What the kernel does: induct on the structure; in each base case the
equality is rfl; in the recursive case rewrite using the IHs to
reduce to rfl.
What the theorem expresses: "the property holds for all instances
of this inductive type because (a) it holds at the base, and (b)
it propagates compositionally through the constructor."

### §2.4  cases-shape — identity by inductive pattern destruction (tactic mode)

```lean
-- Firmware/Raw/CmpIndependence.lean
theorem Ordering_swap_swap (o : Ordering) : o.swap.swap = o := by
  cases o <;> rfl
```

What the kernel does: split on the inductive type's constructors;
in each branch the equality is rfl.
What the theorem expresses: "the equality holds for every
constructor case independently; verifying each gives the universal
statement."  No recursion — just exhaustive enumeration.

### §2.5  match-shape — identity by term-mode case analysis

```lean
-- typical pattern (paraphrased from samples):
theorem foo (x : Fin 3) : f x = g x :=
  match x with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
```

What the kernel does: exactly the same as cases-shape — exhaustive
constructor enumeration — but in term mode rather than tactic mode.
What the theorem expresses: identical content to cases; choice
between tactic vs term mode is stylistic / readability.

## §3  Common thread (descriptive, not categorical)

Every equality theorem in this cluster says:

  > "**LHS-expression** and **RHS-expression** name the same finite
  >  trajectory endpoint."

The five proof methods are five ways the kernel verifies this:

  1. **rfl**:    the two expressions reduce to the same normal form
                in one step (definitional).
  2. **decide**: both expressions execute to the same value, possibly
                across many reduction steps but bounded.
  3. **rw**:    sub-expressions inside the LHS can be replaced by
                already-known equal sub-expressions until the result
                matches the RHS (compositional from sub-equalities).
  4. **cases**: split the variable into all constructor cases; in
                each, the equality holds (often by rfl after the split).
  5. **match**: term-mode version of cases.

The DIFFERENCE between strata is *how the kernel reaches the verdict*,
not *what the verdict says*.  All five strata produce the same kind
of statement: a finite-trajectory closure between two named endpoints.

## §4  What this might suggest (for Mingu's intuition)

(Description-level only; not a classification.)

  · **rfl + decide (78%)** are *computational* closures — the kernel
    just runs the trajectory and checks the endpoint matches.

  · **rw (15%)** is *compositional* closure — the kernel assembles
    the closure from sub-closures.

  · **cases + match (5%)** are *enumerative* closures — the kernel
    splits the input space and verifies each piece independently.

If 213-trajectories were a programming language:
  · rfl = "two ways to write the same constant"
  · decide = "evaluate this expression to a concrete value"
  · rw = "structural rewriting / definitional inlining"
  · cases/match = "case statement, all branches handled"

These are *programming-style equalities* — the kind a compiler can
verify by execution and substitution.  Contrast with classical-math
equalities like "the metric on this manifold is unique" — those have
no executor.

## §5  What's NOT here

  · The 246 "other-method" equality decls (use `exact`, `apply`,
    `refine` without rfl/decide/rw/cases/match dominant).  These
    might split further on inspection.
  · The 1888 `rw` *occurrences* across all decls (the cluster
    above counts decls, not occurrences; many decls use rw
    alongside other tactics).
  · The 9 Classical.* decls — already inspected (G7/G9 demos).

## §6  Where the data points (no proposal)

The empirical fact: **78% of equality theorems are computational
closures** (rfl + decide).  Another 15% are structural propagation
(rw).  Only 5% genuinely use case-split or recursion.

Whether this *means* something about the trajectory framework —
whether it constitutes a hierarchy, whether the strata represent
"levels of complexity", whether the dominance of rfl+decide is
an empirical signature of 213's substrate — is for further
inspection and Mingu's intuition.  This note records the
distribution; interpretation is open.
