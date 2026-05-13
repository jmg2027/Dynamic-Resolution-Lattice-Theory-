import E213.Lib.Math.CascadeCalculus.Core

/-!
# Cascade-Delete Calculus — branch-instance test case

The propext-extermination work of session 27 (stages 1-4) reduced
to a minimal 6-node graph.

## Picture (post-parallel-construction state)

```
 facade chain:           [DIRTY] 2 ─→ 1 ─→ 0
                            ↑       ↑     ↑
                       -tier  leaf
                       capstone capstone cut

 parallel chain:        [PURE]  5 ─→ 4 ─→ 3
                            ↑       ↑      ↑
                        phase_pure  _pure  _at
```

Initial: nodes 0,1,2 = DIRTY; nodes 3,4,5 = PURE.
PURE chain doesn't link into facade chain (parallel by design).

## Forced cascade order

  delete(2) → delete(1) → delete(0)

Reverse fails (node 0 still has consumer 1).
-/

namespace E213.Lib.Math.CascadeCalculus.Instance

open E213.Lib.Math.CascadeCalculus.Core

/-- The 6-node graph.  Edges: 2→1, 1→0, 5→4, 4→3. -/
def g : DepGraph := fun n d =>
  match n, d with
  | 2, 1 => true
  | 1, 0 => true
  | 5, 4 => true
  | 4, 3 => true
  | _, _ => false

/-- Initial labeling: 0,1,2 dirty; 3,4,5 pure. -/
def l0 : Labeling := fun n =>
  match n with
  | 0 | 1 | 2 => .dirty
  | _         => .pure

/-- After Stage 1: node 2 deleted. -/
def l1 : Labeling := fun m => if m = 2 then .pure else l0 m

/-- After Stage 2: node 1 deleted. -/
def l2 : Labeling := fun m => if m = 1 then .pure else l1 m

/-- N = 5: bound covers all 6 nodes. -/
def N : Nat := 5

/-- Stage 1: node 2 is deletable in initial state. -/
example : isDeletable g l0 N 2 = true := by decide

/-- Stage 2: node 1 is deletable AFTER node 2 is gone. -/
example : isDeletable g l1 N 1 = true := by decide

/-- Stage 3: node 0 is deletable AFTER node 1 is gone. -/
example : isDeletable g l2 N 0 = true := by decide

/-- Reverse order fails: node 0 NOT deletable initially. -/
example : isDeletable g l0 N 0 = false := by decide

/-- And node 1 is not deletable initially either. -/
example : isDeletable g l0 N 1 = false := by decide

end E213.Lib.Math.CascadeCalculus.Instance
