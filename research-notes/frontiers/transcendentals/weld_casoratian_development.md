# Frontier — the weld Casoratian: flip criterion + ratio descent

**Status**: items 1–2 CLOSED ∅-axiom; item 3 SKELETON closed + residual
pinned (`LambertOrder` §10 — named ℤ recurrence, flip criterion,
K-positivity, single-step + telescoped ratio descent, bridge-free
LowerBase propagation, elementary `M ≥ 0`).  Only the certificate's two
inputs' *elementary strict* proofs (`0 < M_J`, `0 < R_0`) remain.  **Tier**: 1.
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
2. **Ratio descent** — **CLOSED** (`LambertOrder` §10, ∅-axiom).
   `weldK_nonneg : 0 ≤ K_J` (= `t_mono` cast to ℤ) makes the single step
   unconditional: `weld_descent_step : R_J·M_{J+1} ≤ R_{J+1}·M_J` (the ratio
   `R/M` climbs).  `weld_ratio_descent : (∀j, 0 < M_j) → R_0·M_J ≤ R_J·M_0`
   telescopes it through the positive margins — i.e. pre-flip (`R<0`)
   `|R_J|·M_0 ≤ |R_0|·M_J`, the magnitude descent.
3. **Bridge-free certificate** — SKELETON CLOSED, residual characterized
   (`LambertOrder` §10, ∅-axiom).  Ratio descent *is* a positivity-propagation
   engine: `weld_lowerbase_propagate : (∀j, 0 < M_j) → 0 < R_0 → 0 < R_J`
   (every `J`, incl. `J = 2i+1` = `LowerBase`) — `0 < R_0·M_J ≤ R_J·M_0`, cancel
   `M_0`.  This is a **second, bridge-free certificate** of `LowerBase`'s content,
   independent of the `LambertBridge` budget/saturation/mirror machinery.  Its two
   inputs are now pinned: `weldM_nonneg : 0 ≤ M_J` is **elementary**
   (`series_below_odd_core`, cross-`le` + det-one floor — *not* the bridge), so the
   residual independence question is exactly (a) the *strictness* `0 < M_J` (the
   det-one `+1` slack, untracked here) and (b) the base `0 < R_0 = dev(BP_{2i+1}) −
   dev(AP_{2i+1})`.  The certificate *structure* is bridge-free; closing (a)+(b)
   elementarily would make the whole second proof bridge-free.

Provenance: discovered in the 2026-06-11 multi-agent round (Discovery 1 of
the archived blueprint, `archive/transcendentals/lowerbase_blueprint.md`).
