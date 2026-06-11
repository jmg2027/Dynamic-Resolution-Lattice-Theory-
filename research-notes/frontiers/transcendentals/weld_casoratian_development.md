# Frontier — the weld Casoratian: flip criterion + ratio descent

**Status**: items 1–2 CLOSED ∅-axiom; item 3's *structural* half closed,
the *quantitative* half open (`LambertOrder` §10 — named ℤ recurrence, flip
criterion, K-positivity, single-step + telescoped ratio descent at any
anchor, forward positivity persistence, elementary `M ≥ 0`).  **Tier**: 1.
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
3. **Bridge-free certificate** — *reduced to a single last-step inequality*
   (`LambertOrder` §10, ∅-axiom; found via multi-agent + numerical probe).
   The structural facts hold (ratio `R/M` climbs, `weld_positivity_persists`,
   `weldM_nonneg`).  **Key discovery** (evaluation `i ≤ 3`, all `q`): the cross
   flips negative→non-negative at **exactly one** step, `J = 2i → 2i+1` (the last
   step before `N`); `|R_J|` descends monotonically, then jumps.  So the Casoratian
   at that step + ratio descent give a *theorem-backed* reduction
   (`weld_lowerbase_reduction`):
   > `0 ≤ R_{J+1}` follows (bridge-free) from `0 < M_j` (∀j) and the **single
   > inequality** `(−R_0)·M_J·M_{J+1} ≤ K_J·M_0`.
   This converts item 3 from "the whole telescoped sum reaches `≥0` by `J=2i+1`"
   (≡ the bridge) into **one** ℤ-native inequality at `J = 2i`, which holds with
   **large slack** in every evaluated case (ratio `K_{2i}M_0 / (|R_0|M_{2i}M_{2i+1})`
   ≈ 58–346× for `i ≤ 3`).  The flip criterion (item 1) is its engine — now
   *instantiated*, not decorative.
   **Residual** (genuinely localized): prove `(−R_0)·M_{2i}·M_{2i+1} ≤ K_{2i}·M_0`
   ∅-axiom — `K_{2i} = (4i+3)s_{2i} − (4i+1)c_{2i}` is factorially large, `−R_0` and
   the `M`'s comparatively small; the slack suggests a crude growth bound may close
   it (open: the growth estimate).  Plus elementary strict `0 < M_j` (det-floor `+1`).

Provenance: discovered in the 2026-06-11 multi-agent round (Discovery 1 of
the archived blueprint, `archive/transcendentals/lowerbase_blueprint.md`).
