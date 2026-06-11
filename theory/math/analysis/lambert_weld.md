# The Lambert weld: `coth(1/q)`'s two pointings are one

**Status**: closed ∅-axiom.  Eight modules, 297 PURE / 0 DIRTY
(`LambertWeld` 47, `LambertMinor` 20, `LambertOrder` 40,
`LambertMasterId` 37, `LambertPoly` 34, `LambertBridge` 77,
`CothSeriesCut` 22, `ExpMoebius` 20).  Companion chapters:
`holonomic_modulus.md` (the modulus ladder the result lands on),
`form_margin_modulus.md` (the rate-vs-form mechanism divide).

## Overview

`coth(1/q)` has two natural pointings: the **Lambert continued fraction**
(partial quotients `(2J+1)q`) and the **series** (the cleared ratio
`(2J+1)q·coshNum/sinhNum` of Taylor partials).  Each is a residue-internal
approximant sequence; neither *is* the real (`object1_not_surjective`) —
so their agreement is a theorem to prove, not a definition to inherit.
The weld proves it: the two limit cuts agree on **every** probe,
unconditionally, with total modulus `k+2` (`weld_closed`,
`cothSeriesCauchySep`).  En route, the same machinery closes
`exp(2/q)` unconditionally through a cut-Möbius step (`ExpMoebius`).

Everything is ℕ-arithmetic: list convolutions, weight-threading
accumulators, division-free budgets.  No real analysis is consumed —
the analytic content (Padé remainder of the Lambert CF) is reorganized
into finite, subtraction-free combinatorial identities.

## Lean source

- Path: `lean/E213/Lib/Math/NumberSystems/Real213/ExpLog/`
- Files: `LambertWeld.lean` (47 PURE), `LambertMinor.lean` (20),
  `LambertOrder.lean` (40), `LambertMasterId.lean` (37),
  `LambertPoly.lean` (34), `LambertBridge.lean` (77),
  `CothSeriesCut.lean` (22), `ExpMoebius.lean` (20)
- ∅-axiom status: 0 DIRTY — every theorem
  `#print axioms → "does not depend on any axioms"`.
- Umbrella: imported by `E213.Lib.Math.NumberSystems.Real213`.

## Narrative

### 1. The ladder and the pairing (`LambertWeld`)

Both pointings obey the same three-term ladder
`x_{J+1} = (2J+3)q·x_J + x_{J-1}` (`weld_ladder`).  The convergent
numerators/denominators are packaged as coefficient lists `AP/BP`
with a descending evaluation `dev`, and `cf_bridge` identifies the CF
convergents with `dev` of the lists.  The Chebyshev engine
(`weight_dom`, `cross_le`) transfers a minor-sign condition into
cross-order between any two ladder positions.

### 2. Total positivity of the minors (`LambertMinor`)

The coefficient functions `apF/bpF` (totalized, vanishing off support)
satisfy a closed four-family induction `minorSys` — adjacent minors plus
three cross-level families, the two-apart family derived by `ratio_chain`
with a zero-pivot fallback — giving the all-gap minor positivity
`minor_all`: continuant total positivity, exactly the input `cross_le`
consumes.  §5 adds the halving laws `2·apF n (s+1) ≤ apF n s` (and `bpF`
twin), the geometric decay that later pays the budget.

### 3. The order transfer and the one remaining brick (`LambertOrder`)

Transporting the sign system onto the weld lists gives `series_le_odd`:
the series sits below **every** odd CF convergent.  One direction of the
weld follows (`cf_limit_false_of_series_false`, W1).  The other
direction reduces, through the `lower_step` propagation and the side
condition `devA_le_three_devB`, to a single base family —
`LowerBase q`: for all `i`,

```
dev q (AP (2i+1)) · sinhNum q (2i+1)
  ≤ (4i+3) · dev q (BP (2i+1)) · coshNum q (2i+1)
```

Everything downstream (`series_ge_even_of_base`,
`cothSeriesCauchySepOfBase`, `weld_limit_agreement`) was proven
conditional on it.

### 4. The master identity (`LambertMasterId`)

The Padé-cancellation core, entirely over ℕ:

```
Asum (2k+1) N + cfpos (2k+1) N = Bsum (2k+1) N      (master_odd)
cfpos n N = 2^n · descFac N n                        (= 0 for N < n)
```

The weighted sums are computed by **weight-threading accumulators**
`Aacc/Bacc` that carry `cc = 2N−2s+1` and the running weight `w`, so the
subtraction `2N−2s` is never formed.  The engine is `cfpos_moved`
(`cfpos(n+2,N) + (2n+3)·cfpos(n+1,N) = 2N(2N+1)·cfpos(n,N−1)`), and the
proof is `master_pair`, a paired two-step induction carrying the
`(2k, 2k+1)` block.  `master_diagonal` evaluates the flip at `N = n`:
the `(4i+2)!!` value the weld's last brick consumes.

### 5. The graded connection layer (`LambertPoly`)

`evc` (constant-first polynomial evaluation, length-condition-free) and
`lmulC` (convolution) with `evc_lmulC` multiplicativity connect the
`dev`-world to coefficient lists (`dev_eq_evc_rev`).  Both `LowerBase`
sides become `evc`s of explicit convolutions (`conn_A/conn_B`).  The
**Abel transfer** `evc_dom_joint` then eliminates `q` entirely:
equal-length *suffix dominance* (every suffix coefficient-sum of `A`
below `B`'s) implies `evc q A ≤ evc q B` for all `q ≥ 1` — the joint
induction carries the cross-statement `evc q a + evc 1 b ≤ evc q b +
evc 1 a`.  `lowerbase_of_suffdom` reduces `LowerBase` to a `q = 1`
statement about two lists.

### 6. The bridge and the closure (`LambertBridge`)

The last brick — general-`i` suffix dominance — is the convolution–master
bridge, in seven moves:

1. **Reversal (F1)**: `rev (AP (2i+1)) = truncA (2i+1) i` — the reversed
   convergent lists ARE the coefficient stacks `[apF n m, …, apF n 0]`
   (`rev_trunc`, a 4-way joint induction over the parity ladder).
2. **Snoc (F2)**: the threaded weight in closed product form
   (`wprod`), and the accumulator's last-step peel (`Aacc_snoc`,
   `wprod_shift` aligning head-peel with threading).
3. **Bridges (F3)**: `bridgeA/bridgeB` — the `Mf(g)`-scaled convolution
   coefficient at `p` completes the `g`-headed accumulator to `p+g+1`
   steps, `N̂ = J+g` invariant along the head-peel, the weight match
   (`wmatchA/B`, `prod_match`) aligning each peel with the snoc.
4. **Budget (F4)**: `budgetGen` — `(2J+2)·Bacc ≤ w·wprod·(2·bpF n s)`
   whenever `2J+1+2·steps ≤ cc`: each accumulator step pays the
   `(2J+2)` factor out of the threaded weight, halving covering the
   doubling.  Division-free; the weight later cancels by `wprod_pos`.
5. **Saturation + mirrors (F5)**: the accumulators saturate at their
   support (`AaccSum (2i+1) N (i+1) = Asum (2i+1) N` for **every** `N` —
   support vanishing or weight vanishing, whichever first), and past the
   stack the convolution reads saturated accumulators at lowered level
   (`mirrorA/B`, via `sig_eq_wprod`, `gam_eq`, `wprod_split`).
6. **Per-coefficient laws**: on the two level-`i` lists (`LAl/LBl`,
   both length `3i+2`): `entry_eq` — equal entries past the diagonal
   (`cfpos` vanishes below the level, so the master identity is an
   *equality*); `diag` — `LB_i = LA_i + cfpos n n`, the `(4i+2)!!` Padé
   flip; `slack` — `(2n+2)·LA_p ≤ (2n+2)·LB_p + 2·bpF n 0` below the
   diagonal (bridges + master + budget, `wprod`-cancelled).
7. **Descent (F6–F7)**: `inv_descent` — descending from the diagonal,
   the scaled `A`-suffix plus the scaled flip stays below the
   `B`-suffix plus `d` slack quanta; the counting
   `2i·(4i+1)!! ≤ (4i+4)·(4i+2)!!` (`bpF_le_cfpos`, levelwise
   `(2n+1) ≤ (2n+2)`) lets the one diagonal flip absorb all ≤ `i`
   slacks.  `SuffDom` follows (`suffdom_LAl`), then

```
theorem lowerBase (q) (hq : 1 ≤ q) : LowerBase q
```

and the weld closes: `cothSeriesCauchySep` (total modulus `k+2`, no
hypotheses) and `weld_closed` (limit cuts equal on every probe).

### 7. The two spin-offs

- **`ExpMoebius`**: odd Lambert convergents under `z ↦ (z+1)/(z−1)`
  climb with cross-determinant `2·a_{2L+3}`; `exp(2/q)` completes
  unconditionally (`expTwoOverQCFCauchySeq`, modulus `k+2`),
  `e² ∈ (22/3, 37/5]` — independent of the weld's hard direction.
- **`CothSeriesCut`**: the coth series as an `AbCutSeq` fold
  (`cothSeriesAb`), with the exact `q²`-cancelling cross identity; the
  weld upgrades its completion from probe-instances to all probes.

### 8. What the closure says, 213-natively

The two pointings are different *presentations*; holonomicity of the
modulus is a property of the pointing, not the real
(`PresentationDependence`).  The weld is the non-trivial fact that these
two particular pointings — one a fraction ladder, one a series ratio —
converge to the **same cut**, provable entirely inside the residue with
a uniform `k+2` modulus on both sides.  The mechanism is the Padé
remainder reorganized as ℕ-combinatorics: one diagonal double-factorial
flip per level, paying for all sub-diagonal slack with tenfold room.

## Open frontier

- `exp(p/q)`, `p ≥ 2`, **free** modulus: the factorial presentation
  provably overtakes (`exp_pq_presentation_overtakes`); the fold exists
  (`ExpRationalCut`), the unconditional modulus needs effective
  irrationality (tracked in `modulus_degree_ladder` frontier, rung 0″).
- ζ(3) e-grade upgrade: two verified blueprints (Apéry integrality as
  divisibility chains; Chebyshev 30-block lcm bound), formalization
  pending (tracked in the `zeta3_free_modulus` / `zeta3_blueprint`
  frontier notes).
- The weld Casoratian (`LambertOrder` §9, `weld_casoratian`): the exact
  `i`-invariant unimodular identity — proven, but its flip-criterion
  consequences are not yet developed.
