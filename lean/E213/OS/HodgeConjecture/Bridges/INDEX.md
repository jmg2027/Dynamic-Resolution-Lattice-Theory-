# `OS/HodgeConjecture/Bridges/` — HC²¹³ cross-discipline interfaces

OS-layer orchestration: each file is a public interface adapting
the HC²¹³ subsystem (Math/Cohomology/HodgeConjecture/) for a
specific classical discipline.

A non-213 mathematician working in any of these areas can start
*here*: each Bridge file is the entry point for that classical
discipline's 213-native form.

## Files (7)

  · `Tate.lean`                  → ℓ-adic / Frobenius / char-p
  · `MumfordTate.lean`           → Galois algebraic groups
  · `BlochBeilinson.lean`        → motivic cohomology / Chow
  · `BeilinsonRegulator.lean`    → L-function values (CLAUDE.md L1)
  · `BeilinsonLichtenbaum.lean`  → motivic ↔ étale equivalence
  · `ChernCharacter.lean`        → K-theory ↔ cohomology
  · `HodgeTate.lean`             → p-adic Hodge (Real213-p deferred)

## Layer position

These files sit at the **OS layer** of 213's vertical architecture
(per ARCHITECTURE.md §1.4.5 + G12 §5).  They orchestrate the
HC²¹³ definitional subsystem (in Math/Cohomology/HodgeConjecture/)
into stable APIs for downstream consumers.

The previous location at `Math/Cohomology/HodgeConjecture/Bridge/`
was conceptually mismatched: Math/ is for *definitions*, OS/ is
for *orchestration / public adapters*.

## Migration history

Migrated 2026-05-XX (session HANDOFF part-16 follow-up).
- 7 files moved via `git mv`
- Namespaces updated: `E213.Math.Cohomology.HodgeConjecture.Bridge`
  → `E213.OS.HodgeConjecture.Bridges`
- Importer updated: `HodgeConjecture/API.lean`
- Build verified clean + axiom invariance preserved (Tate, etc.
  all PURE post-move)
