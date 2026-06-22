# Decomposition: probability / measure (atomic mass, independence, expectation, the continuous limit)

*213-decomposition of "how likely" — per `../README.md`. Tests the model-breaker hypothesis:
**probability = the count-reading normalized**, `P(A) = count(A)/count(Ω)` = the count-Lens composed
with the ratio-Lens (the same ratio-Lens `fractions`/`integers.md` ride). Honest verdict at the end:
does it FIT, EXTEND, or BREAK the model?*

> **Note on repo coverage.** This target was flagged as *likely thin / likely model-breaker*. It is
> not thin: `lean/E213/Lib/Math/Probability/` is a 25-file tree (`Probability/INDEX.md`) with a
> declared paradigm — **"Probability = atomic rational mass: `num/den` with `0 < den`, `num ≤ den`.
> No σ-algebra; no measure-theoretic completion."** So every leg below is grounded in a *verified
> ∅-axiom Lean theorem*, not conceptual hand-waving. That the repo already built it as `num/den`
> is itself the first confirmation of the hypothesis.

## The decomposition

- **Construction `C`** — the same distinguishing as `cardinality.md`: a **family of distinguishables**
  (the outcome space Ω is `C`, before any reading). Nothing new is constructed for probability. The
  events `A ⊆ Ω` are sub-families — sub-distinguishings already inside the same act. (Lean shadow:
  there is *no `Ω` type at all* — `Probability/Foundation/Cut.lean` carries only the readout, the
  pair `(num, den)`. The construction is implicit; the file holds the reading.)

- **Reading `L = ratio ∘ count`** — a **composite of two readings already in the calculus**:
  1. the **count-reading** (`cardinality.md`): `A ↦ count(A)`, `Ω ↦ count(Ω)`;
  2. the **ratio-reading** (`integers.md`/fractions, `NatPairToQPos`): a *pair of counts* `(num, den)`
     read as a positive rational. Probability is the ratio-Lens applied to the count-pair
     `(count(A), count(Ω))`, constrained to `num ≤ den` (so the readout lands in `[0,1]`).

  Verified: `ProbabilityCut { num, den, den_pos : 0 < den, mass_le : num ≤ den }`
  (`Cut.lean:27`). This is *literally* `QPair = Nat213 × Nat213`
  (`NatPairToQPos.qpair_is_nat_pair_shaped`, ∅-axiom `rfl`) with one extra constraint `num ≤ den`.
  The same two-count container, the same ratio fold, plus a clamp.

- **Residue** — the count-reading's residue is `cardinality.md`'s diagonal (the uncountable). The
  *ratio* fold adds nothing transcendent of its own (it is faithful where it closes — same as
  `integers.md`/fractions). The **only new residue is at dialed resolution**: when the finite tally
  is replaced by a `h→0` modulus (density / continuous probability), the residue is the *limit of the
  Riemann sample-sum* — the **same modulus residue** as `derivative.md`/`continuity.md`, not a new
  kind. (Lean: `Bridge/RiemannBridge.lean`, `Bridge/CauchyModulus.lean`.)

## Re-seeing — ⟨C | L⟩

```
   outcome space Ω        =  ⟨ family of distinguishables | — ⟩          (C; the cardinality.md C)
   event A ⊆ Ω            =  a sub-distinguishing inside the same C
   P(A)                   =  ⟨ (count A, count Ω) | ratio-reading ⟩       = count-reading ∘ ratio-Lens
   P : [0,1]              =  the ratio-Lens clamped by  num ≤ den         (mass_le, Cut.lean:31)
   complement P(Aᶜ)=1−P(A)=  the count-pair (den−num, den)               (complement, Cut.lean:55)
   independence           =  ⟨ product of two count-pairs | ratio ⟩       (the ×-character on counts)
   expectation E[X]       =  the ratio-Lens of a *weighted* count-sum     (Σ mᵢ·vᵢ)/D
   density / ∫            =  the SAME reading at h→0 resolution           (Riemann modulus)
```

**(1) Normalization fits an existing axis — no new axis needed.** `P(A) = count(A)/count(Ω)` is
exactly the ratio-Lens of two counts. `ProbabilityCut` *is* `NatPairToQPos`'s `QPair` plus the clamp
`num ≤ den`. Complement is the pair `(den−num, den)` — the count-complement read through the same
ratio — and it is *involutive* (`probabilityCut_master`'s last conjunct, `den−(den−num)=num`,
∅-axiom). The "1" and "0" of probability are `unit = 1/1`, `zero = 0/1` — the ratio-Lens's own unit
and zero. **No "measure" / weight axis is introduced for the basic theory.** (See strain note for
where a weight *does* appear.)

**(2) Independence is a multiplicative character — the count-reading respecting a product
construction.** `joint a b = (a.num·b.num)/(a.den·b.den)` (`Independence.joint`, `Cut.lean`/
`Independence.lean:27`): the joint mass is the *product of the two count-pairs*, exactly the way
`vp_mul`/`det2_mul` make `×` a character (`prime_factorization.md`/`determinant.md`). It is a
commutative monoid: `joint_comm_num` (`Nat.mul_comm`) and `joint_assoc_num` (∅-axiom via
`mul_assoc_213`), with unit `joint unit a = a` (`joint_unit_left_num`) and absorbing `zero`
(`joint_zero_left_num`). So `P(A∩B)=P(A)P(B)` is **the same `×↦·` character fact** the calculus
already classified — independence is not a probability primitive, it is the count-reading being a
homomorphism on the product distinguishing. *This is a genuine collapse:* independence = `det2_mul` =
`vp_mul` = parity's `L₂`, all one bidirectional multiplicative-character pattern (README batch-2).

**(3) Continuous probability dials the resolution — discrete → residue, no new realm.** The
discrete `ProbabilityCut` (finite tally) and the continuous density (∫) are the *same reading at two
resolutions*, exactly `derivative.md`'s Δ/d and Σ/∫ dial. `RiemannBridge.lean` width-scales the
dyadic Riemann sum to a `(num, den)` pair and inherits a **Cauchy modulus**
(`convergence_modulus_const`: depth `≥ k` ⇒ precision `< 1/k`, ∅-axiom). `CauchyModulus.lean` puts a
`(Nat,Nat)`-only Cauchy modulus on sequences of `ProbabilityCut`s (`absDevCross`, the
cross-multiplied deviation; `absDevCross_self = 0`, ∅-axiom), and the Law of Large Numbers is the
modulus closing: `LLN_unit` — a balanced length-`2n` fair sample has mean *exactly* `n/(2n)=1/2`
(∅-axiom). The LLN file states the collapse in its own header: *"frequency-Lens and expectation-Lens
readings agree structurally at balance"* (`bernoulli_LLN_exact`, ∅-axiom). The "continuous
distribution" is the **modulus residue** of the count-ratio reading — `continuity.md`'s dial, not a
measure-theoretic completion (the INDEX is explicit: *"no σ-algebra, no σ-additivity"*).

## Revelation (collapse) + honest strain-report

**Collapse (the payoff).** Three classically-separate pillars of probability are shown to be readings
already in the calculus, certified ∅-axiom:
- **`P(A)` itself** = `ratio ∘ count` = `cardinality.md`'s count-reading post-composed with
  `integers.md`/fractions' ratio-Lens, clamped `num ≤ den`. *Same container, `QPair`.*
- **independence** = the **multiplicative character** `×↦·` on count-pairs — *the same arrow* as
  `vp_mul`/`det2_mul`/parity-`L₂`. Not a probability axiom; a homomorphism fact.
- **continuous/density** = the **resolution dial** of `derivative.md`/`continuity.md`; its "limit" is
  the modulus residue, finite-signature-pinned (the `convergence_modulus_const` recipe).

So Kolmogorov's three axioms re-read: *non-negativity + normalization* = the ratio-Lens clamp
(`mass_le`); *P(Ω)=1* = `unit = 1/1`; *(finite) additivity* = `discreteNum_append` (linearity, below) +
complement involutivity. No σ-additivity is in the repo and the decomposition does not need it for any
of the above — σ-additivity is the *infinitary* extension, which would live (if built) as the same
resolution residue, not a new axis.

**Where the model genuinely strains — expectation needs a weight the basic ratio-Lens lacks.**
Honest report, as the prompt demanded:

- **The strain is real but small, and the calculus already has the part to absorb it.** `P(A)` is
  ratio∘count with *no weight* — every outcome counted once. **Expectation is not**: `E[X] =
  (Σ mᵢ·vᵢ)/D` (`Expectation.discrete`/`discreteNum`) weights each outcome by a *value* `vᵢ`. That
  `·vᵢ` is a genuine **weighted-count reading** — the plain count-Lens (tally = "each outcome → 1")
  does *not* produce it; you need "each outcome → its value `vᵢ`." So expectation does **extend** the
  count-reading to a **value-weighted count**.
- **But this weight is not a new fundamental axis** — it is the *measure/weight on the construction*
  the prompt's question (1) asked about, and it lands inside the model as **a Lens whose readout is a
  number (the value `vᵢ`), i.e. the README's "character" pattern: a reading whose readout is itself a
  number-construction.** Crucially it is *additive*, not multiplicative: `discreteNum_append`
  (∅-axiom) proves `Σ` over `xs++ys` splits — **linearity of expectation is the count-reading
  respecting the `+`/concatenation construction**, the additive dual of independence's multiplicative
  character. So expectation = the *additive* character of the value-weighted count, exactly mirroring
  independence = the *multiplicative* character of the bare count. The strain resolves into the
  existing bidirectional character-mode (`×↦·` for independence, `+↦+`-respecting for expectation),
  not a new construct.
- **The one honest gap:** the plain `cardinality.md` count-Lens is *uniform* (counts, doesn't weight).
  A *non-uniform measure* (general weight `w : outcome → mass`, the real "measure" of measure theory)
  is the value-weighted reading with the weight detached from a value — and the repo builds it only
  in the special discrete forms (`discrete`, distributions in `Distribution/`), never as a general
  σ-additive measure. **That generality is genuinely absent** (INDEX: no σ-algebra). The model
  *accommodates* it (a weighted count-reading) but does not yet *force* its general form; calling it
  a "new axis" overstates — it is the count-reading with a per-outcome weight, which the calculus
  files Expectation already instantiates. **Verdict on the strain: EXTEND, not BREAK** — the weight is
  a parameter on the count-reading (value-weighting), absorbed by the character-mode, not a fourth
  fundamental slot.

## Note for the technique (CRUCIAL + honest)

**Does probability force a NEW construct?** No — and this is a strong, clean confirmation, with one
honest qualification.

- **The hypothesis holds: `P = ratio ∘ count`.** Probability introduces *no new construction* `C`
  (Ω is `cardinality.md`'s family of distinguishables; there is literally no `Ω`/`Measure`/σ-algebra
  type in `lean/E213`). It introduces *no new reading*: it is the **composition of two readings the
  calculus already has** — count (cardinality) and ratio (integers/fractions) — with a clamp. The
  repo's own encoding (`ProbabilityCut` = `QPair` + `num ≤ den`) makes the composition literal and
  ∅-axiom. This is the calculus's first **composite-reading** entry: it shows readings *compose*, and
  that probability is a *derived* reading, not a primitive realm. The model **FITS** for the core.

- **The one place it EXTENDS (not breaks):** expectation requires a **value-weighted** count — the
  uniform count-Lens does not weight. This surfaces a refinement the map should record: the count-
  reading has a **weight parameter** (uniform vs per-outcome), and *linearity of expectation*
  (`discreteNum_append`) is that weighted count being the **additive character**, the dual of
  *independence* (`joint_assoc_num`/`joint_comm_num`) being the **multiplicative character**. So the
  README's "character-mode is bidirectional" gets a second instance pair *inside one target*:
  `independence : ×↦·` and `expectation-linearity : +↦+`. The weight is a Lens parameter (like
  resolution), not a new fundamental axis.

- **Suggested map update.** `L`'s parameter list gains a **weight** parameter alongside resolution and
  character-mode: `L = reading + {resolution, character-mode, weight}`, where `weight = uniform`
  recovers the bare count (cardinality, plain `P`) and `weight = per-outcome value` gives expectation /
  the discrete measure. The general σ-additive measure is the `weight`-parameter pushed to the `h→0`
  resolution — i.e. it sits at the *intersection of two existing parameters* (weight × resolution),
  exactly where the README predicts the deepest results live ("every deepest result sits where two of
  these meet"). **Honest ceiling:** the repo realizes this intersection only in special discrete cases;
  a general weighted-measure-at-limit theorem is an *open Lean target*, not a closed collapse. The
  calculus *predicts* it; it has not yet *proven* it. Recording that prediction-without-proof is the
  honest deliverable here.

**Verdict: probability FITS as `ratio ∘ count` and EXTENDS the model by one parameter (a `weight` on
the count-reading) — it does NOT break it.** The would-be breaker (expectation's weight) lands as the
additive twin of independence's multiplicative character, both inside the existing bidirectional
character-mode.

---

### Verified Lean anchors (all ∅-axiom unless noted; checked via `#print axioms` + `lake build`)

| Leg | Theorem (file:name) | Status |
|---|---|---|
| `P` = clamped count-pair | `Probability/Foundation/Cut.lean : ProbabilityCut` (struct, `num≤den`); `probabilityCut_master` (unit/zero/complement-involutive) | ∅-axiom ✓ |
| ratio-Lens container shared | `Lens/Number/Nat213/Tower/NatPairToQPos.lean : qpair_is_nat_pair_shaped`, `two_pair_equiv` | ∅-axiom (`rfl`) ✓ |
| independence = × character | `Probability/Foundation/Independence.lean : joint` (def), `joint_assoc_num`, `joint_comm_num`, `joint_unit_left_num`, `joint_zero_left_num` | `joint_assoc_num` ∅-axiom ✓ |
| × character (cross-domain) | `vp_mul` (`Meta/Nat/VpMul`), `det2_mul` (`determinant.md`) | cited, prior ✓ |
| expectation = weighted count | `Probability/Foundation/Expectation.lean : discrete`, `discreteNum`, `expectation_master`, `discreteNum_append` (linearity) | `discreteNum_append`, `expectation_master` ∅-axiom ✓ |
| LLN / frequency=expectation | `Probability/Limit/LLN.lean : LLN_unit`, `bernoulli_LLN_exact` | ∅-axiom ✓ |
| resolution dial (modulus) | `Probability/Bridge/CauchyModulus.lean : absDevCross_self`, `ProbCauchy`; `Bridge/RiemannBridge.lean : convergence_modulus_const` | `absDevCross_self` ∅-axiom ✓ |
| resolution discipline (prior) | `continuity.md` anchors (`IsContinuousModulus`, `uniform_limit_continuous`); `derivative.md` | cited, prior ✓ |

**Conceptual-only legs:** none for the core claims — every leg above cites a built theorem. The
*general σ-additive measure* and the *weighted-measure-at-limit* intersection are stated as **absent /
open** (honestly), not asserted; INDEX confirms "no σ-algebra, no σ-additivity."
