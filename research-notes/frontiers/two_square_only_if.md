# Frontier: sum-of-two-squares characterization — CLOSED (both directions)

**COMPLETE.** Both directions of "n is a sum of two squares ⟺ every prime
`q ≡ 3 (mod 4)` divides n to an even power" are now ∅-axiom:
- **if**: `NumberTheory/SumTwoSquaresCharacterization` (18 PURE) — Brahmagupta product.
- **only if**: `NumberTheory/InertPrimeThreeMod4` (7 PURE, `inert_three_mod4`) +
  `NumberTheory/SumTwoSquaresOddPower` (15 PURE, `even_vp_three_mod4`: a sum of two
  squares has even q-adic valuation at every q≡3mod4; `not_isSumTwoSqNat_of_odd_vp`).

The whole arc is a computed modular fact — no ℤ[i], ideals, or norms. Remaining
polish (optional): a single `isSumTwoSqNat n ⟺ ∀ q≡3mod4, even (vp q n)` biconditional
bundling the two files + the `Int`↔`Nat` `isSumTwoSq` bridge.
