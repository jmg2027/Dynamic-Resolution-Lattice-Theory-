import E213.Lib.Math.Order.GaloisConnection

/-! Spec-as-code entry point for `E213.Lib.Math.Order` — order theory.

  * `GaloisConnection` — Galois connections over a parametrized order:
    unit / counit, monotonicity of both adjoints, the triangle identities
    `f∘g∘f = f` / `g∘f∘g = g` (pointwise), and the induced `g∘f` closure
    operator (extensive / monotone / idempotent). The multiply/divide
    adjunction `(·*p) ⊣ (·/p)` on `Nat` as a concrete witness.
-/
