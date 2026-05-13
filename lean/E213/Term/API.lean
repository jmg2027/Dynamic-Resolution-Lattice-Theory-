import E213.Term.Term
import E213.Term.Compare
import E213.Term.Pair
import E213.Term.Rat
import E213.Term.Decide
import E213.Term.Sound
import E213.Term.MonomialAxioms
import E213.Term.Tree

/-!
# Term ring — public API (re-export shim)

Single-import entry point for Term ring per ARCHITECTURE.md
(2026-05-12).  Downstream code (`Theory`, …) imports this for the
Raw-implementation substrate.

**K1 — Data API**:
  - `Term` (deep-embedded AST of 213's syntactic objects)
  - `Term.eval`, `Term.{nS, nT, d, c}` (atomic constants)
  - `Tree`, `Tree.cmp`, `Tree.canonical` (Raw 의 구현체 — used by
    `Theory.Raw.Core` to define `Raw := {t : Tree // canonical t}`)

**K2 — Computation API** (Bool-returning total functions, ∅-axiom):
  - `Term.{equiv, le_b, lt_b}` (comparators)
  - `Term.{pair, offDiag}` (Lens distinguishability primitive)
  - `Term.{equivQ, leQ}` (rational cross-multiplication)
  - `Decide.{allBelow, existsBelow}` (bounded quantifiers)

**K3 — Soundness API** (Bool→Prop bridges):
  - `Sound.{of_equiv, of_le_b, of_lt_b}`
  - `Sound.{of_equivQ, of_leQ}`

**Not bundled** (separate concerns):
  - `Demo` — bare-metal demonstration of axiom-free reasoning
  - `MonomialAxioms` — concrete monomial equalities cited by
    `rust-engine/crates/kernel/src/normal_form.rs`

**Axiom status**: every Term theorem is *literally 0-axiom*.
`#print axioms <thm>` returns "does not depend on any axioms".
Verified by `tools/kernel_regress.sh`.
-/
