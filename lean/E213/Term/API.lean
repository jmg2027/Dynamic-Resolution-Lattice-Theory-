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
.  Downstream code (`Theory`, …) imports this for the
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
  - `Sound.of_equiv` (`equiv = true → eval a = eval b`)
  - `Sound.of_le_b` (`le_b = true → eval a ≤ eval b`)
  - `Sound.to_equiv` (converse: `eval a = eval b → equiv = true`)
  - `Sound.dim_law_eq`, `Sound.d_sq_eq_25`, `Sound.two_nSsq_lt_dsq`
    (Lean-Eq application capstones)

(Note: `Sound.of_lt_b`, `Sound.of_equivQ`, `Sound.of_leQ` are not
provided — `lt_b` and the rational `equivQ`/`leQ` are consumed via
`of_le_b` plus `eval (mul · ·)` rewriting at call sites.)

**Not bundled** (separate concerns):
  - `Demo` — bare-metal demonstration of axiom-free reasoning
  - `MonomialAxioms` — concrete monomial equalities cited by
    `rust-engine/crates/kernel/src/normal_form.rs`

**Axiom status**: every Term theorem is *literally 0-axiom*.
`#print axioms <thm>` returns "does not depend on any axioms".
Verified by `tools/kernel_regress.sh`.
-/
