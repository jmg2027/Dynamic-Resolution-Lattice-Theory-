import E213.Term.API
import E213.Term.Compare
import E213.Term.Decide
import E213.Term.Demo
import E213.Term.MonomialAxioms
import E213.Term.Pair
import E213.Term.Rat
import E213.Term.Sound
import E213.Term.Term

/-! Spec-as-code entry point for `E213.Term`.

  Bare-metal type-theory layer — Term ring (ARCHITECTURE.md
  2026-05-12).  Raw 의 구현체 (Tree 등) 와 Theory 에 공개할
  API 구현부.

  ## Core engine (Term ring substrate)

    * `Term`              — deep-embedded 4-constructor AST
                            (zero/succ/add/mul → ℕ via eval)
    * `Compare`           — Bool comparators `le_b`, `lt_b`
    * `Sound`             — Bool↔Prop bridge
                            (`equiv = true ↔ eval Eq`)
    * `Pair`              — G_ij distinguishability primitive
    * `Rat`               — rational equivalence via cross-mul (ℕ-only)
    * `Decide`            — bounded ∀/∃ as Bool functions
                            (`allBelow`, `existsBelow`)
    * `MonomialAxioms`    — concrete Nat equalities used by
                            `rust-engine/crates/kernel/src/normal_form.rs`
                            as rewrite-rule citations
    * `Demo`              — first 0-axiom capstone demonstrations
    * `API`               — K1+K2+K3 public surface re-export

  ## What's NOT here (moved out)

  - `Tactic/` (Nat213, Mod213, Fin213, Pow213, Omega213, QuadNorm)
    — moved to `Meta/Tactic/` per ARCHITECTURE.md spec update
    (2026-05-12).  These are Lean-side helpers (Lean Nat / Mod /
    Fin 위 PURE 보조 도구) — ring-independent, so they belong in
    Meta (Lean 4 bridge).

  - `Cap_*.lean` capability ledgers (PhysicsAtomicIE, PeriodicTable,
    etc.) — deleted from Term/.  End-of-pipeline content endpoints,
    not Term ring engine parts.  Future capstone ledgers will be
    rebuilt in `Lib/{Math,Physics}/Capstones/`.
-/
