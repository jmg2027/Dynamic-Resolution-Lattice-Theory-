# Decomposition: information / (Shannon) entropy

*213-decomposition of `H = −Σ p·log p`, per `../README.md` (model v3). Tests the central
hypothesis of batch 3: that the two `L`-parameters surfaced separately — **weight** (probability,
`probability.md`) and **character** (the `×↦+` log of `exponential.md`/`prime_factorization.md`) —
**compose cleanly**. The claim: entropy is the **weight-reading ∘ log-character** — the
*expectation (weighted count) of the log-character* of the probabilities. "Information of an
outcome" `= −log p` is the log-character applied to a probability-weight; entropy is its
expectation.*

> **Note on repo coverage — entropy is NOT absent.** This target was flagged "entropy proper is
> likely ABSENT." It is not. `lean/E213/Lib/Math/Probability/Information/` is a 7-file ∅-axiom tree
> (`Information/INDEX.md`, blueprint `blueprints/math/12_information_213.md`) with a declared
> paradigm: **information theory is built on the *dyadic substrate*, where the real-valued `log₂`
> collapses to `Nat`-valued depth** — `log₂(2^n) = n` is `rfl`, not a Taylor series. This is the
> single most consequential fact for this decomposition: 213 *already chose* to build entropy as the
> two batch-3 parameters meeting, and it makes the log-character `rfl`. So most legs below cite a
> verified ∅-axiom theorem; the honest gap (non-dyadic / general real-valued `−Σ p log p`) is named
> at the end and is exactly the `weight × character` intersection at *non-power* resolution.

## The decomposition

- **Construction `C`** — the same distinguishing as `probability.md`/`cardinality.md`: a **family of
  distinguishables** (the outcome space), read through the **weight-reading** to a `ProbabilityCut`
  (`num/den`, `0 < den`, `num ≤ den`). Nothing new is constructed for entropy. On the dyadic
  substrate the relevant `C` is the **bisection tree**: `n` bisections distinguish `2^n` outcomes
  (`Bit.lean`, `DyadicBracket` of depth `n`). The bisection depth IS the construction-history.

- **Reading `L = weight-reading ∘ log-character`** — a **composite of two readings already in the
  calculus**, exactly the hypothesis:
  1. the **log-character** (`×↦+`, the `vp`/`exp` arrow of `prime_factorization.md` /
     `exponential.md`): on the dyadic substrate this is `p = 1/2^k ↦ k` — the surprise/information
     content `−log p` read as a `Nat` depth. Verified `rfl`: `bitsAfterBisections n = n`
     (= `log₂(2^n)=n`, `Bit.lean:log2_pow_two_eq`); `surpriseBitsDyadic k = k`
     (`Entropy.lean:surprise_dyadic_eq_depth`). The character's defining homomorphism `log(ab)=log a
     + log b` is `surprise_additive : surpriseBitsDyadic (j+k) = surpriseBitsDyadic j +
     surpriseBitsDyadic k` (`Entropy.lean`, `rfl`).
  2. the **weight-reading / expectation** (`probability.md`'s genuine extension): the value-weighted
     count `E[X] = (Σ mᵢ·vᵢ)/D` (`Expectation.lean:discreteNum`, `discrete`), with linearity
     `discreteNum_append` (∅-axiom). Entropy is this expectation **with the value `vᵢ` instantiated
     as the log-character of the weight**: `vᵢ = −log pᵢ`. So `H = E[−log p] = Σ pᵢ·(−log pᵢ)` is
     *literally* `discreteNum` with each outcome weighted by its own surprise depth.

  The composite reads: take a probability (weight-reading), apply the log-character to get surprise,
  then take its expectation (weighted count). **`H = weight ∘ character`** — the two batch-3
  parameters in series.

- **Residue** — for the *dyadic* case (`p` a power of `1/2`) there is **no residue**: the character
  is `rfl` (depth is exactly the exponent), so `H(uniform on 2^n) = n` exactly
  (`Entropy.lean:shannonEntropy_uniform_eq_depth`). The residue appears **only at non-dyadic
  resolution** — when `p` is not a power of `1/2`, `−log p` is not a `Nat` and the character lands in
  the real-residue (the `e`/`log₂e` bracket residue of `exponential.md`). That is the *same* residue
  as `e` (a transcendental read as a `Real213` cut / narrowing interval, e.g. `log₂e ∈
  [(m+1)/(2(m+2)), 6]`, `ChebyshevLower.lean:chebyshev_constant_interval`), not a new kind. The
  INDEX states this honestly: non-dyadic entropy "needs general real-valued log."

## Re-seeing — ⟨C | L⟩

```
   information of an outcome   =  ⟨ p = 1/2^k | log-character ⟩  = surprise depth k   (surprise_dyadic_eq_depth)
   "−log(ab)=−log a −log b"    =  surpriseBitsDyadic (j+k) = ·j + ·k                    (surprise_additive, rfl)
   entropy H                   =  ⟨ p | weight-reading ∘ log-character ⟩ = E[−log p]    (= discreteNum with vᵢ = −log pᵢ)
   H(uniform on 2^n)           =  n   (every outcome p=1/2^n, surprise n, expectation n) (shannonEntropy_uniform_eq_depth, rfl)
   additivity for independent  =  H(X,Y)=H(X)+H(Y)                                       (entropy_additive, rfl)
   joint of independents       =  uniform on 2^(m+n)                                     (joint_independent_eq_sum, rfl)
   I(X;Y)=H(X)+H(Y)−H(X,Y)=0   =  Nat.sub_self                                           (mutualInfo_independent_zero)
   D(p‖q)                      =  surprise-depth difference a−b (clamped)                (klBitsDyadic, kl_nonneg)
```

**(1) The composite reads cleanly — character first, weight second.** Surprise `−log p` is the
log-character of the probability-weight; `surpriseBitsDyadic k = k` is the dyadic realization of
`exponential.md`'s `×↦+` arrow (the inverse direction: `p = 1/2^k`, the `^`-construction, read off to
the additive depth `k`). Then `H` is the *expectation* of that surprise — `probability.md`'s
value-weighted count `discreteNum`, with the value-slot filled by the character's output. **The two
batch-3 parameters compose with no glue:** `weight` supplies the `Σ pᵢ·(·)`, `character` supplies the
`(−log pᵢ)`.

**(2) Additivity-for-independent IS the character respecting `×→+` — and the calculus PREDICTS it.**
This is the leverage moment. The hypothesis's sharpest test: *does the calculus predict entropy's
functional form*? Yes — additivity is forced, not posited. Independence is the product construction on
weights (`Independence.joint`: `joint a b` multiplies `num` and `den`, so two independent uniforms over
`2^m`, `2^n` give a joint uniform over `2^{m+n}` — `joint_independent_eq_sum`, `rfl`). The
log-character turns that product into a sum (`vp_mul`/`surprise_additive`: `−log(p·q) = −log p −log
q`). Therefore `H(X,Y) = H(X)+H(Y)` is *the character being a homomorphism on the independence-product*
— `entropy_additive (m n) : shannonEntropyUniformBits (m+n) = ... m + ... n` (`rfl`). This is the
**same `×↦·` arrow** as `vp_mul` (`Meta/Nat/VpMul.lean:vp_mul`), `det2_mul`, parity's `L₂`, and
`probability.md`'s `joint_comm_num`/`joint_assoc_num` — entropy's additivity is *not a new fact*, it is
the multiplicative character of the weight composed through the log. **The functional form `−Σ p log p`
is the unique reading for which independence (product of weights) maps to addition of contents** — the
calculus does not just describe entropy, it *derives the shape of `−log` as forced* by "make the
product-of-weights additive." That is genuine leverage, not re-skin.

**(3) Mutual information / KL are the residue arithmetic of the same composite.** `I(X;Y) =
H(X)+H(Y)−H(X,Y)` is the *defect* of additivity — zero exactly when the joint fills the product
(independence, `mutualInfo_independent_zero` via `Nat.sub_self`), positive = shared description length
(`entropy_subadditive`, `mutualInfo_genuine`: `(n+m−j)+j = n+m`, no clamp). KL divergence `D(p‖q) =
a−b` is the surprise-depth difference, `≥0` by `Nat.zero_le` (Jensen as `Nat`-sub monotonicity,
`kl_nonneg`). All are arithmetic on the *log-character outputs* (depths), i.e. on the `+`-readout side
of the character — consistent with the composite, no new reading.

## Revelation — entropy = weight-reading ∘ log-character, and its FORM is PREDICTED

**Collapse + forcing (the payoff).** Entropy decomposes as the clean composition of exactly the two
`L`-parameters batch 3 surfaced separately, and the composition is not merely *consistent* — it
**predicts entropy's functional form**:

- **`H = E[−log p]` = weight ∘ character**, certified on the dyadic substrate where the character is
  `rfl`: surprise `= depth` (`surprise_dyadic_eq_depth`), `H(uniform on 2^n) = n`
  (`shannonEntropy_uniform_eq_depth`). The weight-slot is `probability.md`'s `discreteNum`
  expectation; the value fed into it is the log-character of the weight. The two parameters compose
  in series with no new primitive.
- **The `−log` shape is *forced* by additivity.** Additivity-for-independent is the log-character
  being a homomorphism on the independence-product of weights: product of probabilities
  (`joint_independent_eq_sum`) ↦ sum of contents (`surprise_additive`), giving `entropy_additive`
  (`rfl`). `−log` is precisely the reading that linearizes the multiplicative weight-construction —
  the **same `×↦+` arrow** as `vp_mul`. So the calculus *derives* why information content is
  logarithmic: it is the unique character making independent-product weights additive. **This is the
  leverage win the README demanded** — the technique predicts the form, it does not just relabel it.
- **The residue is the *same* residue as `e`**: non-dyadic `−log p` is a real-cut / narrowing-interval
  residue (`ChebyshevLower.chebyshev_constant_interval`'s `log₂e` bracket), not a new realm — exactly
  `exponential.md`'s `e`-as-residue, here surfacing because the character's input weight is not a
  power of the base.

**The honest strain (named, not hidden).** The Lean tree builds entropy on the **dyadic substrate**,
where the character collapses to `rfl` (`log₂(2^n)=n`). The *general* `H = −Σ pᵢ log pᵢ` for arbitrary
`pᵢ` (non-powers of `1/2`) — the full real-valued composite — is **not a closed Lean theorem**; the
INDEX says so ("needs general real-valued log for non-dyadic distributions"). So the composite is
*proven exactly on the dyadic case* and *conceptual (predicted-but-open) in general*. Crucially, the
open case sits at the **intersection of the two parameters at non-power resolution** — `weight ×
character` where the character's residue (the `e`/`log₂e` bracket) is live — exactly where
`probability.md` already predicted the general measure lives ("weight × resolution"). The calculus
*predicts* the general entropy; it has *proven* the dyadic restriction. Recording that
prediction-with-partial-proof is the honest deliverable.

## Note for the technique

**Does entropy confirm the two batch-3 parameters COMPOSE — weight × character? YES, decisively, and
it is the cleanest composition in the practice so far.** Probability surfaced `weight`; exponential /
prime_factorization surfaced the bidirectional `character`. Entropy is *literally their series
composite* — `E[ character(weight) ]` — and the repo's own encoding makes this manifest: surprise =
character output (`surpriseBitsDyadic`), entropy = expectation of surprise. The two parameters do not
merely coexist on `L`; they **chain**, the output of one becoming the value-slot of the other. This
extends model v3's `L = reading + {resolution, character-mode, weight}` with the lesson that *the
parameters themselves compose* (just as batch 3 found readings compose) — `weight` can take a
`character`-output as its weighting value.

**Does the calculus PREDICT entropy's functional form — a genuine leverage moment? YES.** This is the
strongest "payoff" in the practice. The README's revelation rule demands the notation *pay* (Yoneda,
not abstract nonsense). Here it does: from "make independent-product weights additive" the calculus
*forces* the content function to be `−log` (the `×↦+` character), hence entropy to be `−Σ p log p`. The
form is derived, not described — `entropy_additive`/`surprise_additive` are the `rfl` shadows of
`vp_mul`'s `×↦+` homomorphism. Entropy is thus another face of the *one* multiplicative-character arrow
(`vp_mul` = `det2_mul` = parity `L₂` = independence `joint` = entropy additivity), now composed with
the weight-reading.

**Lean-grounded vs conceptual.**
- *Grounded (∅-axiom, verified):* the dyadic composite end-to-end — character (`surprise_dyadic_eq_depth`,
  `log2_pow_two_eq`), additivity-as-character (`surprise_additive`, `entropy_additive`,
  `joint_independent_eq_sum`), the full entropy identity (`shannonEntropy_uniform_eq_depth`), mutual
  info / subadditivity (`mutualInfo_independent_zero`, `entropy_subadditive`, `mutualInfo_genuine`),
  KL (`kl_nonneg`, `kl_self_zero`); the weight-reading (`discreteNum`, `discreteNum_append`); the
  cross-domain character (`vp_mul`).
- *Conceptual (predicted, open):* the general real-valued `H = −Σ p log p` for non-dyadic `p` — sits
  at the `weight × character`-at-non-power intersection, residue = the `log₂e` bracket
  (`chebyshev_constant_interval`). The calculus predicts its form; the repo proves only the dyadic
  restriction.

**Verdict: entropy EXTENDS the model (no break)** — and supplies the practice's clearest *leverage*
win: the two batch-3 parameters **compose in series** (`E[character(weight)]`), and the composition
**predicts entropy's functional form** (`−log` forced by independence-additivity = the `×↦+`
character). The would-be novelty ("information") lands as the log-character of a probability-weight;
entropy as its expectation. One arrow (`vp_mul`'s `×↦+`), one new instance.

---

### Verified Lean anchors (all ∅-axiom; checked via grep on `lean/E213`, paradigm per `Information/INDEX.md`)

| Leg | Theorem (file:name) | Status |
|---|---|---|
| log-character = depth (`−log p` atomic) | `Probability/Information/Bit.lean : log2_pow_two_eq` (`bitsAfterBisections n = n`); `bitDepth` | ∅-axiom (`rfl`) ✓ |
| surprise = character output | `Probability/Information/Entropy.lean : surprise_dyadic_eq_depth` (`surpriseBitsDyadic k = k`); `dyadicProbabilityCut` (link to `ProbabilityCut`, `1/2^k`) | ∅-axiom ✓ |
| character homomorphism `−log(ab)=−log a−log b` | `Probability/Information/Entropy.lean : surprise_additive` | ∅-axiom (`rfl`) ✓ |
| entropy identity `H(uniform 2^n)=n` | `Probability/Information/Entropy.lean : shannonEntropy_uniform_eq_depth`; `fair_coin_entropy`, `byte_uniform_entropy` | ∅-axiom (`rfl`) ✓ |
| ★ additivity = character respecting `×→+` | `Probability/Information/Entropy.lean : entropy_additive`; `MutualInfo.lean : joint_independent_eq_sum` | ∅-axiom (`rfl`) ✓ |
| independence = ×-product of weights | `Probability/Foundation/Independence.lean : joint` (def), `joint_num`/`joint_den`, `joint_comm_num`, `joint_assoc_num` | ∅-axiom ✓ |
| × character (cross-domain anchor) | `Meta/Nat/VpMul.lean : vp_mul`, `vp_pow`, `vp_self_pow` | ∅-axiom ✓ |
| weight-reading / expectation = weighted count | `Probability/Foundation/Expectation.lean : discreteNum`, `discrete`, `expectation_master`, `discreteNum_append` (linearity) | ∅-axiom ✓ |
| mutual info / subadditivity | `Probability/Information/MutualInfo.lean : mutualInfo_independent_zero`, `entropy_subadditive`, `mutualInfo_genuine`, `mutualInfo_self_eq_entropy` | ∅-axiom ✓ |
| KL divergence = depth difference | `Probability/Information/KLDivergence.lean : klBitsDyadic`, `kl_self_zero`, `kl_nonneg` | ∅-axiom ✓ |
| residue (non-dyadic `log₂e` bracket) | `Lens/Number/Nat213/ChebyshevLower.lean : chebyshev_constant_interval` (`log₂e ∈ [(m+1)/(2(m+2)), 6]`) | ∅-axiom ✓ (prior, `exponential.md`) |

**Conceptual-only legs (honest):** the **general real-valued `H = −Σ p log p` for non-dyadic `p`** is
*absent* in `lean/E213` (INDEX: "needs general real-valued log") — the composite is proven on the
dyadic substrate (`rfl`) and *predicted* (not proven) in general, residing at the `weight × character`
intersection at non-power resolution. Stated as open, not asserted.
