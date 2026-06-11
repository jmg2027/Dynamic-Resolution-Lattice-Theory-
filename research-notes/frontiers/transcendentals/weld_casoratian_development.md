# Frontier — the weld Casoratian: flip criterion + ratio descent

**Status**: PARTIALLY CLOSED — the named ℤ recurrence and the flip
criterion are now ∅-axiom (`LambertOrder` §10); ratio descent + the
bridge-free `LowerBase` remain open.  **Tier**: 1.
Anchor: `LambertOrder` §9 `weld_casoratian` (PURE) — the exact
`i`-invariant unimodular identity on the pair `(R_J(i), M_J(i))`:

    R_{J+1}(i)·M_J(i) = R_J(i)·M_{J+1}(i) + K_J,
    K_J = (2J+3)·s_J − (2J+1)·c_J  ≥ 2·c_J

(`tcross_id` collapse; det-one floor `P_i·devB_i = q²·devA_i·Q_i + 1`).
The weld itself is closed without it (`theory/math/analysis/lambert_weld.md`)
— this note tracks the identity's own programme:

1. **Flip criterion** — **CLOSED** (`LambertOrder` §10, ∅-axiom).  The raw
   subtraction-free ℕ shadow is now lifted to the **named ℤ recurrence**
   `weld_casoratian_int : R_{J+1}·M_J = R_J·M_{J+1} + K_J` (signed `weldR`,
   `weldM`, `weldK`; the whole difference factors as `K_J·(detpair−detval)`,
   one firing of the det-one floor `dev_cross_det` cast to ℤ kills it), and
   `weld_flip_criterion : 0 < M_J → −(R_J·M_{J+1}) < K_J → 0 < R_{J+1}` —
   sign-flip forcing by cancelling the positive margin.  (The blueprint's
   `K_J > |R_J|·M_{J+1}` is the `0 ≤ M_{J+1}` specialisation; the signed
   form is sharper.)
2. **Ratio descent** (OPEN): pre-flip telescoping `|R_J|·M_0 ≤ |R_0|·M_J`.
   Foothold: now stated cleanly on `weld_casoratian_int`; needs a positivity
   schedule for `weldM` across `J`.
3. (OPEN) Whether the criterion yields an *independent* (bridge-free) proof
   of `LowerBase`, and at what slack — a second certificate of the same
   closure, valuable as a cross-check brick.  Now has the ℤ recurrence as a
   foothold (research-open: needs the `weldM > 0` schedule that `LowerBase`
   itself establishes, so independence is non-trivial).

Provenance: discovered in the 2026-06-11 multi-agent round (Discovery 1 of
the archived blueprint, `archive/transcendentals/lowerbase_blueprint.md`).
