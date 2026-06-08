# Cross-domain insights: the Casoratian / spiral-axis branch ↔ main's CKM CP-phase arc

**Tier 1 (volatile).**  Written at the merge of `claude/spiral-axis-classification-ZvaNO`
(Casoratian determinantal ladder + spiral-axis A1/A3/A5) into `origin/main` (CKM CP-phase
marathon: CP phase as one imaginary unit, `ℤ[i]^×=C₄`, Hodge `⋆²=−1`, permutation under three
readouts, Legendre/Zolotarev).  Honest split: **proven shared object** vs **thematic thread**.

## 1. The order-4 axis point *is* the CKM CP-phase's `C₄` — same object (PROVEN both sides)

The spiral axis `{2,4,6}` has its middle point at order `4 = |ℤ[i]^×|` (the Gaussian unit group,
`CayleyDickson/Integer/ZIUnits.ZI_units_exact_four`).  Main's CP-phase arc forces the CKM phase
into `ℤ[i]^× = C₄` (the Hodge structure `⋆²=−1`, `ℤ[J]≅ℤ[i]`, `theory/physics/cp_phase.md`).

These are not two `C₄`'s by coincidence — they are the **same ring `ℤ[i]`** read in two domains:
the spiral axis reads `ℤ[i]^×` as the order-4 *floor rotation* of a continued-fraction
cross-determinant (`GaussianCrossDet.gaussian_floor_rotation`, multiplier `−i`); the CP phase
reads it as the order-4 *Hodge rotation* `⋆` on `H*(Δ⁴)`.  Both are the order-4 element `i`.  So
**the CKM CP-violating phase sits at the `i`-point (order 4, disc `−4`) of the spiral axis** — the
Gaussian rung, not the Eisenstein (`ω`, order 6) one.  The two CM points of G185 (disc `−4`, disc
`−3`) are the same two that index the axis; the CP phase selects `−4`.

This is the strongest link: a single object (`ℤ[i]^×=C₄`) proven on both sides, one branch reading
(floor rotation) and one main reading (Hodge `⋆`).  Candidate for a synthesis essay.

## 2. The companion-determinant sign `altSign(k−1)` IS a permutation sign (PROVEN ↔ thematic)

The all-orders Casoratian multiplier is `Hₖ(n+1) = altSign(k−1)·a₀·Hₖ(n)`
(`CasoratianDeterminant.casoratian_det_step`).  The sign `altSign(k−1) = (−1)^{k−1}` is the
**determinant of the companion shift's cyclic part** — and `(−1)^{k−1}` is exactly the sign
(`psign`) of the `k`-cycle permutation `(0 1 … k−1)`.  Main's `the_permutation_under_three_readouts`
essay shows one permutation read three ways: `psign` (sign) = `det(permMatrix)` = Legendre/Zolotarev
(`(−1)^inv`).  The companion determinant's sign is a **fourth instance** of that single
inversion-sign readout: the Casoratian multiplier carries the `psign` of the shift cycle.

Proven on the branch side: `det_companion` yields `(−1)^{k−1}·a₀`.  The identification with
`psign((0 1 … k−1))` is immediate (a `k`-cycle has sign `(−1)^{k−1}`) but is stated here as a
reading, not yet a Lean bridge `det_companion ↔ psign`.  Buildable: relate `altSign(k−1)` to
`PermSign.psign` of the cyclic-shift permutation list.

## 3. `det(AB)=det A·det B` is the shared engine (TOOL-LEVEL)

The branch proof of `casoratian_det_step` runs entirely through `DetMul.det_matMul`
(`det(C·H)=det C·det H`).  Main's Jarlskog/Hodge CP machinery is likewise determinant-based
(commutator determinant, signed Hodge star).  Both arcs are downstream of the one ∅-axiom
`Linalg213` determinant theory (Leibniz expansion, multiplicativity, row operations) — the same
`DetN`/`DetMul`/`Laplace` stack now serves a *physics* invariant (Jarlskog) and a *sequence-depth*
invariant (Casoratian).  A single linear-algebra core, two domains.

## 4. The central `−1`: Cassini sign ↔ `⋆²=−1` ↔ `i²=−1` (THEMATIC — guard against glyph-reuse)

The branch's binary cover `{2,4,6}=2·{1,2,3}` is the central `−1` (Cassini sign) doubling; main's
`⋆²=−1` (Hodge) and `i²=−1` are the same `−1` *when carried by `ℤ[i]`* (link 1).  But per the G185
audit's guard rail, a shared `−1` glyph is **not** a morphism: the Cassini *determinant sign* `−1`
(an order-2 multiplier) and the Hodge `⋆²=−1` (an order-4 generator squared) coincide only through
the proven `ℤ[i]` identification of link 1, not by symbol.  Recorded to *avoid* re-importing the
"one central −1 threads all" stereotype G185 already flagged.

## Buildable next (ranked)

1. **`det_companion ↔ psign(cyclic shift)`** (link 2): a Lean bridge `altSign(k−1) =
   PermSign.psign (cyclicShift k)`, putting the Casoratian multiplier sign on the same
   inversion-sign readout as `det(permMatrix)`/Legendre/Zolotarev.  Med, genuine.
2. **Synthesis essay for link 1**: "the CKM CP phase sits at the `i`-point of the spiral axis" —
   ties `theory/physics/cp_phase.md` to `theory/math/analysis/spiral_coordinate_classification.md`
   through the one object `ℤ[i]^×=C₄` (floor rotation = Hodge `⋆`).  Essay, not Lean.
