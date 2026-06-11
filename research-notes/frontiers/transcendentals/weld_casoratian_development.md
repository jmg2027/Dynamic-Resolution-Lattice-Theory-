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
3. **Bridge-free certificate** — *structural* half closed, *quantitative*
   half OPEN (`LambertOrder` §10, ∅-axiom).  The structural facts: the ratio
   `R/M` is non-decreasing forward (`weld_ratio_descent`, any anchor `J₀`:
   `R_{J₀}·M_{J₀+d} ≤ R_{J₀+d}·M_{J₀}`), so **once non-negative the cross stays
   non-negative** (`weld_positivity_persists`); and `weldM_nonneg : 0 ≤ M_J` is
   **elementary** (`series_below_odd_core`, cross-`le` + det-one floor, *not* the
   bridge).
   **But this is *not* (yet) a bridge-free `LowerBase`.**  `LowerBase` is
   `0 ≤ R_{2i+1}`, and the cross starts **negative** —
   `R_0 = dev(BP_{2i+1}) − dev(AP_{2i+1}) ≤ 0` (`= 0` at `i=0`, `< 0` for `i ≥ 1`;
   evaluation-checked, e.g. `i=1,q=2`: `61 − 66 = −5`).  Persistence has no positive
   anchor at `J₀ = 0`.  A genuine second certificate would still have to certify the
   climbing ratio reaches `≥ 0` **by** `J = 2i+1` — the *quantitative flip-timing*
   that is exactly the `LambertBridge` content.  So the structural half (climb +
   persistence + flip criterion) is bridge-free; the quantitative "flips by `2i+1`"
   half is the open, genuinely bridge-equivalent residue.

Provenance: discovered in the 2026-06-11 multi-agent round (Discovery 1 of
the archived blueprint, `archive/transcendentals/lowerbase_blueprint.md`).
