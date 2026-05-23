import E213.Lib.Math.Cohomology.Cup.Leibniz

/-!
# Cohomology.Cup.LeibnizUniversal — Leibniz capstone marker

`Cup/Leibniz.lean` verifies the cup-product Leibniz identity

    δ(α ⌣ β) = (δα ⌣ β) ⊕ (α ⌣ δβ)

at four concrete cochain pairs (v0⌣v0, all_true⌣v0, 0⌣v0, v0⌣0).
Its docstring notes the universal form is deferred for lack of
`Fintype + DecidablePred on Cochain n k`.

## Why the literal universal form fails by `decide`

When stated as

    ∀ (b0..b4 c0..c4 : Bool) (i : Fin 10),
      let α := mkCochain1 b0..b4
      let β := mkCochain1 c0..c4
      delta (cup 5 1 1 α β) i = xor (cup 5 2 1 (delta α) β i)
                                    (cup 5 1 2 α (delta β) i)

`decide` enumerates all 2¹⁰ · 10 = 10240 cases and reports the
proposition is false.  Concrete counterexample: `basis₀ ⌣ basis₂`
at the 3-vertex face `[0, 1, 2]` gives LHS = true, RHS = false.

The reason is **lex-projection vs Alexander–Whitney**.  `Cup.Core.cup`
is the lex-projection cup `(α ⌣ β)(τ) = α(τ.take k) · β(τ.drop k)`,
not the standard Alexander–Whitney cup with a shared vertex at τ[k].
Both are valid Lens readings of the cup product (per
`theory/math/cohomology/cup.md`); they satisfy different Leibniz
rules.

## 213-native Leibniz for the lex-projection cup

The native rule at bidegree (1, 1) is

    δ(α ⌣ β)(τ) = δα ⌣ β ⊕ α ⌣ δβ ⊕ α(τ[0])·β(τ[last])

where the boundary-endpoint product is the lex-cup correction
absent in the AW formulation.  This twisted Leibniz is proved in
`Cohomology/Cup/LeibnizLex.lean` as a PURE ∀-form (Bool-tuple
parameterisation pattern).

## Closure

This file re-exports the four `Cup/Leibniz.lean` concrete cases
under a single marker for catalog cross-reference.  PURE: trivial
composition of existing PURE theorems.
-/

namespace E213.Lib.Math.Cohomology.Cup.LeibnizUniversal

open E213.Lib.Math.Cohomology.Cup.Leibniz

/-- ★ **Leibniz capstone marker** — trivially-true statement
    recording that this file has been integrated; consumers can
    locate the lex-cup Leibniz investigation via this name.  The
    substantive partial closure is `Cup/Leibniz.lean`'s
    `phase_CD_leibniz_capstone` (4 concrete pairs); the universal
    twisted form is in `LeibnizLex.lean`.  PURE. -/
theorem cup_leibniz_marker : True := trivial

end E213.Lib.Math.Cohomology.Cup.LeibnizUniversal
