import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.Beq213
import E213.Meta.Nat.EncodePair213
import E213.Meta.Nat.NatRing213
import E213.Meta.Nat.IntHelpers
import E213.Meta.Nat.Max213
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.PairOp
import E213.Meta.Nat.UnitList
import E213.Meta.Nat.UnitGrid
import E213.Meta.Nat.BinTree213
import E213.Meta.Nat.TwoThreeUnique
import E213.Meta.Nat.Valuation
import E213.Meta.Nat.VpMul
import E213.Meta.Nat.PureNat
import E213.Meta.Nat.PolyNat
import E213.Meta.Nat.PowBasic
import E213.Meta.Nat.RootFloor

/-! Spec-as-code entry point for `E213.Meta.Nat`.

  Pure-ℕ / pure-ℤ utility helpers used across Math + Physics.
  Every file is leaf-level — no E213-internal imports beyond
  `Kernel.Tactic.Nat213` and friends.

  ## Files

    * `AddMod213`    — addition modulo small primes (`mod 3`, `mod 5`, …)
    * `EncodePair213` — pair-encoding `(ℕ × ℕ) → ℕ` injection
    * `IntHelpers`   — shared `Int` helpers
    * `Max213`       — `Nat.max` lemma library
    * `NatDiv213`    — `Nat.div` / `Nat.mod` helper lemmas
    * `PureNat`      — `Nat`-arithmetic primitives without `omega`
    * `PolyNat`      — ∅-axiom reflection prover for univariate `Nat`
                       polynomial identities (`poly_id`; replaces hand
                       `ring`-style expansion)
    * `PowBasic`     — `Nat.pow` comparison toolkit, arbitrary base
    * `RootFloor`    — integer `s`-th root, floor reading
-/
