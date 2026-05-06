import E213.Math.NatHelpers.AddMod213
import E213.Math.NatHelpers.EncodePair213
import E213.Math.NatHelpers.IntHelpers
import E213.Math.NatHelpers.Max213
import E213.Math.NatHelpers.NatDiv213
import E213.Math.NatHelpers.PureNat

/-! Spec-as-code entry point for `E213.Math.NatHelpers`.

  Pure-ℕ / pure-ℤ utility helpers used across Math + Physics.
  Every file is leaf-level — no E213-internal imports beyond
  `Kernel.Tactic.Nat213` and friends.

  These were previously 6 loose files at `Math/` root; M14 Phase B1
  collected them into this sub-cluster.

  ## Files

    * `AddMod213`    — addition modulo small primes (`mod 3`, `mod 5`, …)
    * `EncodePair213` — pair-encoding `(ℕ × ℕ) → ℕ` injection
    * `IntHelpers`   — shared `Int` helpers
    * `Max213`       — `Nat.max` lemma library
    * `NatDiv213`    — `Nat.div` / `Nat.mod` helper lemmas
    * `PureNat`      — `Nat`-arithmetic primitives without `omega`
-/
