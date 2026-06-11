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
   **Residual** (localized but NOT lowered): the single inequality
   `(−R_0)·M_{2i}·M_{2i+1} ≤ K_{2i}·M_0` is *not* crudely provable.  Decisive probe:
   the obvious crude bound `M_J ≤ P·s_J` (drop the subtracted term) **fails by 10⁹–10²⁵×**,
   because `M` is a **small near-cancellation**: `M_0 = P − q²Q` with `q²Q ≈ P` (e.g.
   `q=2,i=1`: `P=1861, q²Q=1720, M_0=141` — 13× smaller), the det-one floor
   (`P·devB = q²·devA·Q + 1`) being the only gap.  So the localized residue **inherits
   the bridge's essential delicate content** — the near-cancellation in the margin — and
   there is no internal handle that avoids it (§5.4, stated plainly).  *Net:* item 3's
   reduction is theorem-backed (`weld_lowerbase_reduction`), and the wall is now
   *precisely located* at the M near-cancellation = det-floor structure; it is not
   *lowered*.  The bridge-equivalence (suspected earlier) is now evidenced, not asserted.

   Related discovery: the repo already carries the **scalar** lower-cross recursion
   `R_recursion`: `R_{J+1} = (2J+2)(2J+3)q²·R_J + ((2J+3)devB − devA)` (M-free), and
   `lower_step`/`lower_of_base` use it for the same forward persistence — so the
   Casoratian `weld_positivity_persists` re-derives an existing fact; the genuinely new
   §10 content is the *named ℤ Wronskian recurrence + flip criterion + single-inequality
   reduction*, the M-margin "second certificate" view of the same wall.

   **The det-floor resolves the near-cancellation (the cleanest reframing).** The margin
   `M_J` is *not* independent of the cross `R_J`: the det-one floor gives
   `weldM_devB : M_J·devB = s_J − q²·Q·R_J` (∅-axiom) — the small `M` is exactly the
   det-floor residue against the *explicit* sinh sequence.  Substituting into the
   Casoratian cancels the `q²Q·R_J R_{J+1}` cross-terms, leaving the **M-free Wronskian**
   `weld_rs_wronskian : R_{J+1}·s_J − R_J·s_{J+1} = devB·K_J` — the lower cross and the
   explicit `sinh` numerator are a Casoratian pair.  This gives the *cleanest* reduction
   `weld_lowerbase_reduction_rs`: `0 ≤ R_{J+1}` from the **single M-free inequality**
   `(−R_J)·s_{J+1} ≤ devB·K_J` and `s_J > 0` (no `M`, no ratio descent).

   **Core marathon (2026-06-11, two agent rounds + formalization).**  The assembly chain
   is now theorem-backed: `weld_lowerbase_of_core` (∅-axiom) derives `LowerBase`
   (`0 ≤ R_{2i+1}`) from positive margins, `R_0 ≤ 0`, `q²Q > 0`, **M-monotonicity**
   `M_{2i} ≤ M_0`, and **Core** `M_0·devB·M_{2i+1} ≤ q²Q·K_{2i}` (mechanism: det-floor
   residue `weldM_devB` at `J=0` + `M_{2i} ≤ M_0` + Core ⟹ the `weld_lowerbase_reduction`
   master inequality).  Three Wronskians built (`weld_rs_wronskian` R·sinh,
   `weldM_wronskian` M·cosh `= P·K_J`, `weldM_s_wronskian` M·sinh `= q²Q·K_J`).  **Honest
   verdict on the two residuals (both bottom out in the bridge's count):**
   - **M-monotonicity**: the M·sinh Wronskian gives `(M_J − M_{J+1})·s_J = q²Q·K_J −
     (s_{J+1}−s_J)·M_J`, so antitone ⟺ `(s_{J+1}−s_J)·M_J ≤ q²Q·K_J` — but that is
     *self-equivalent* to antitone (no ring discharge); the antitone fact is a genuine
     quantitative induction, **not yet found** (the agent's "provable now" was an over-claim,
     corrected).
   - **Core**: the flip value `R_{2i+1}` has leading term *exactly* `(4i+2)!!` (the
     `LambertMasterId` diagonal), and no clean `i`-induction or sufficient sub-lemma exists
     (agent: every drop crosses over) — Core **genuinely needs the `(4i+2)!!` counting** =
     the existing `LambertBridge` machinery.
   **Net:** the Casoratian/Wronskian split removes the counting from the *structure*
   (a complete, clean, ∅-axiom spine: three Wronskians + det-floor resolution + the reduction
   cascade) but **not from the core** — `LowerBase` is bridge-*equivalent*, now demonstrated by
   multiple independent reductions all terminating at the `(4i+2)!!` flip-timing.  Since
   `LowerBase` is *already* closed in `LambertBridge`, this route's value is the M-free spine,
   not a second closure.  (Originator `LowerBase`-via-bridge remains the proof of record.)

Provenance: discovered in the 2026-06-11 multi-agent round (Discovery 1 of
the archived blueprint, `archive/transcendentals/lowerbase_blueprint.md`).
