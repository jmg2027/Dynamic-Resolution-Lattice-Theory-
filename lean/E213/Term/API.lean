import E213.Term.Term
import E213.Term.Compare
import E213.Term.Pair
import E213.Term.Rat
import E213.Term.Decide
import E213.Term.Sound
import E213.Term.MonomialAxioms

/-!
# Kernel: Public API (re-export shim)

G12 D1: single-import entry point for the Kernel layer's public API.
Pattern follows `Firmware/Raw.lean` precedent (refactor shim).

Downstream code can `import E213.Term.API` and access K1+K2+K3:

**K1 — Data API**: 213 syntactic objects
  - `Term` (deep-embedded AST)
  - `Term.eval`, `Term.{nS, nT, d, c}` (atomic constants)

**K2 — Computation API**: Bool-returning total functions (∅-axiom)
  - `Term.{equiv, le_b, lt_b}` (comparators)
  - `Term.{pair, offDiag}` (Lens distinguishability primitive)
  - `Term.{equivQ, leQ}` (rational cross-multiplication)
  - `Decide.{allBelow, existsBelow}` (bounded quantifiers)

**K3 — Soundness API**: Bool→Prop bridges (load-bearing for upstream)
  - `Sound.{of_equiv, of_le_b, of_lt_b}`
  - `Sound.{of_equivQ, of_leQ}`

**Sealed (NOT API)**:
  - `Cap_*.lean` (capability ledgers, end-of-pipeline summaries)
  - `Demo.lean` (examples only)
  - `MonomialAxioms.lean` (concrete monomial equalities — borderline)

**Cross-cutting (separate import)**:
  - `Tactic/{Omega213, Nat213, Mod213, Pow213, Fin213, QuadNorm}` (K4)
    — these are 213-native proof automation, consumed at every layer
    above Kernel; deliberately not re-exported here.

**Axiom status**: every Kernel theorem is *literally 0-axiom*.
`#print axioms` returns "does not depend on any axioms".  Verified
by `tools/kernel_regress.sh` and `tools/scan_all_axioms.py`.

See `research-notes/G12_layered_api_classification.md` §2 for the
rigorous public-API classification.
-/
