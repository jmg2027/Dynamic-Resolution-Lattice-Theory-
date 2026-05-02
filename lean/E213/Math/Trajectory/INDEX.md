# Math/Trajectory/ — INDEX

Sub-cluster for *trajectory-based* mathematical structures in 213
— bridges, classifiers, and capstones over the cohomological-
trajectory primitives (`Kernel/Tactic/Mod213`) and the chiral
decomposition (`Math/Linalg213/Chiral`).

See `research-notes/G2_trajectory_principle.md` for the unifying
trajectory frame.

## Files (production)

| File | Topic | Status |
|---|---|---|
| `PhaseChiralBridge.lean` | View A (mod 6 phase) ↔ View B (5 = 3+2 chiral) bridge — canonical "d = 5" anchor | 4/4 ∅-axiom |

## Forward roadmap (planned)

  - `D2TierClassifier.lean` — formalise the rational/algebraic/
    transcendental classifier via trajectory-closure depth
    (research-notes/D2_complexity_class_hierarchy.md).
  - `RawFoldChain.lean` — explicit Raw-trajectory composition
    theorem (G3 §6).
  - `TrajectoryBordism.lean` — Lens-bordism as constructive
    equality (replaces propext for geometric arguments).

## Layering

This sub-cluster lives at *Hypervisor* layer mechanically:
PhaseChiralBridge imports `Mod213` (Kernel) + `Counts` (Firmware-
or-higher).  Future files may pull in Lens framework (Hypervisor)
or stay at lower layers.

## Naming convention

Files here describe *trajectory structures* (not just helpers).
Each file = one structural theorem or classifier.
