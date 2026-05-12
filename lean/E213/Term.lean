import E213.Term.API
import E213.Term.Compare
import E213.Term.Decide
import E213.Term.Demo
import E213.Term.MonomialAxioms
import E213.Term.Pair
import E213.Term.Rat
import E213.Term.Sound
import E213.Term.Tactic
import E213.Term.Term

/-! Spec-as-code entry point for `E213.Term`.

  Bare-metal type-theory layer — lowest in the ARCHITECTURE.md
  vertical stack (Ring 0).

  ## Core engine (Ring 0 substrate)

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

  ## Sub-cluster

    * `Tactic/`           — 213-native tactic suite (Nat213, Mod213,
                            Fin213, Pow213, Omega213, QuadNorm).
                            K4 layer; consumed by every ring above.

  ## What's NOT here (moved out)

  Earlier `Cap_*.lean` capability ledgers (PhysicsAtomicIE,
  PeriodicTable, etc.) were deleted from Term/ — they are
  end-of-pipeline content endpoints (terminal nodes), not Ring 0
  engine parts.  Future capstone ledgers will be rebuilt in
  `Lib/{Math,Physics}/Capstones/` where they belong semantically.
-/
