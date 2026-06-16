import E213.Lib.Math.Order.GaloisConnection
import E213.Lib.Math.Order.BooleanAlgebra
import E213.Lib.Math.Order.KnasterTarski

/-! Spec-as-code entry point for `E213.Lib.Math.Order` — order theory.

  * `KnasterTarski` — the fixed-point theorem: a monotone map on a complete
    lattice (set-indexed `glb`) has a least fixed point `lfp = glb {x | f x ≤ x}`
    (`lfp_fixed`, `lfp_least`) and dually a greatest fixed point via `lub`.
  * `BooleanAlgebra` — abstract Boolean algebra (parametrized Huntington
    axioms): complement uniqueness, double-complement, both De Morgan laws,
    with the `Bool` algebra as a concrete instance.
  * `GaloisConnection` — Galois connections over a parametrized order:
    unit / counit, monotonicity of both adjoints, the triangle identities
    `f∘g∘f = f` / `g∘f∘g = g` (pointwise), and the induced `g∘f` closure
    operator (extensive / monotone / idempotent). The multiply/divide
    adjunction `(·*p) ⊣ (·/p)` on `Nat` as a concrete witness.
-/
