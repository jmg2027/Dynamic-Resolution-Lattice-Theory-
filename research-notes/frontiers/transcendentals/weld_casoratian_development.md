# Frontier — the weld Casoratian: flip criterion + ratio descent

**Status**: OPEN (identity proven; consequences undeveloped).  **Tier**: 1.
Anchor: `LambertOrder` §9 `weld_casoratian` (PURE) — the exact
`i`-invariant unimodular identity on the pair `(R_J(i), M_J(i))`:

    R_{J+1}(i)·M_J(i) = R_J(i)·M_{J+1}(i) + K_J,
    K_J = (2J+3)·s_J − (2J+1)·c_J  ≥ 2·c_J

(`tcross_id` collapse; det-one floor `P_i·devB_i = q²·devA_i·Q_i + 1`).
The weld itself is closed without it (`theory/math/analysis/lambert_weld.md`)
— this note tracks the identity's own programme:

1. **Flip criterion** as a theorem: `K_J > |R_J|·M_{J+1} ⟹ R_{J+1} > 0`
   (sign-flip forcing, ℕ-form with the |·| dissolved by case split).
2. **Ratio descent**: pre-flip telescoping `|R_J|·M_0 ≤ |R_0|·M_J`.
3. Whether the criterion yields an *independent* (bridge-free) proof of
   `LowerBase`, and at what slack — a second certificate of the same
   closure, valuable as a cross-check brick.

Provenance: discovered in the 2026-06-11 multi-agent round (Discovery 1 of
the archived blueprint, `archive/transcendentals/lowerbase_blueprint.md`).
