# Decomposition: Shannon information theory — channels, capacity, the coding theorems

*213-decomposition per `../README.md` (model v7.1: `OBJECT = ⟨C | L⟩ ⊕ Residue(L,C)`, the REVELATION
rule) and `../SYNTHESIS.md` (the two invariants — the character arrow `×↦+`/`×↦·`, the `q=±1` residue
tag — the weight axis, the `q=±1` spine). Neighbors: `entropy.md` (KEY — `H = −Σ p log p` as the `×↦+`
surprise character, `surprise_additive`/`klBitsDyadic`), `information_geometry.md` (KL/Fisher),
`coding_theory.md` (JUST DONE — linear codes = cochain complexes, the syndrome = `q=±1`),
`probability.md` (the weight axis), `gaussian_clt.md`/`convex_duality.md` (the variational optimum).*

*This note is about **CHANNELS / capacity / the coding theorems** — `entropy.md` already grounded the
`×↦+` surprise character `H = −Σ p log p`, so that is cross-referenced, not re-derived.*

**Thesis tested:** Shannon information theory is the `×↦+` entropy character read **on a CHANNEL**, with
**capacity the optimum** and the **coding theorem the `q=±1` rate-vs-capacity threshold** that ties to
`coding_theory.md`'s syndrome-zero achievability. The new datum (not a re-skin of `entropy.md`): **mutual
information `I(X;Y) = H(X)+H(Y)−H(X,Y)` is the same `×↦+` character read on the joint-vs-conditional —
the channel's *preserved* information = the residue of `H` under conditioning**; **capacity `C = max
I(X;Y)` is its variational optimum** (the weight axis maximized); and the **noisy-channel coding theorem
(reliable ⟺ rate < C) is the `q=±1` threshold** (rate<C = `q=+1` converge/achievable pole, errors→0, the
code corrects = `coding_theory.md`'s syndrome=0; rate>C = `q=−1` escape, errors bounded away from 0).

## The decomposition (C / Reading / Residue)

- **Construction `C`** — `probability.md`/`entropy.md`'s `C` exactly: a **family of distinguishables**
  (input alphabet `X`, output alphabet `Y`), read through the **weight-reading** to `ProbabilityCut`s.
  A **channel** adds nothing new to `C` — it is a *pair* of distinguishable families with a transition
  weight `p(y|x)`. On the dyadic substrate the relevant `C` is the **bisection tree**: `n` bisections
  distinguish `2^n` input words; the BSC's noise is the dyadic flip weight `1/2^k`
  (`Channel.lean:44` `bscCapacityNum`, the noise depth `k`). The channel is two copies of `entropy.md`'s
  bisection `C` glued by a transition weight — the same `C`, indexed twice.

- **Reading `L`** — three readings of the *one* `×↦+` entropy character, in series:
  1. **Mutual information = the `×↦+` character on joint-vs-conditional.** `I(X;Y) = H(X)+H(Y)−H(X,Y)`
     is `entropy.md`'s additive surprise character read *across the channel*: the information the channel
     preserves = the defect of additivity = the *residue of `H` under conditioning*. In-repo it is
     literally `mutualInfoBits h_x h_y h_joint = h_x + h_y − h_joint` (`MutualInfo.lean:50`), the joint
     `≤` the product (correlation lowers the joint, `entropy_subadditive:70`). `I = 0` ⟺ joint fills the
     product ⟺ independence (the channel preserves nothing, `mutualInfo_independent_zero:42`); `I(X;X) =
     H(X)` (a noiseless channel preserves everything, `mutualInfo_self_eq_entropy:84`). This is the SAME
     `×↦+` arrow as `entropy.md`'s `surprise_additive`/`vp_mul` — *not a new reading*, the additive
     character read on a directed pair `X→Y`.
  2. **Capacity = the variational optimum of reading (1).** `C = max_{p(x)} I(X;Y)` is the weight axis
     (`probability.md`) *maximized over input distributions* — the same optimization shape as
     `convex_duality.md`'s `f**`/Fenchel optimum and `gaussian_clt.md`'s fixed point. In-repo the
     *optimum value* is built numerically: `noiselessChannel = 1` (capacity 1 bit/symbol,
     `noiseless_capacity:33`), BSC at dyadic noise `1/2^k` has capacity `k/2^k`
     (`bscCapacityNum/Den:44-45`, `bsc_half_capacity:52`, `bsc_byte_capacity:56`). The *named `max I`
     variational object* (the optimization over all `p(x)`) is ABSENT — only the optimum value per
     channel is recorded (see Dropped/flagged).
  3. **The coding theorem = the `q=±1` rate-vs-capacity threshold.** Reliable communication ⟺ rate `R <
     C`. `R < C` = the **`q=+1` converge/achievable pole** (errors→0, a code exists, ties to
     `coding_theory.md`'s `s=0` syndrome-zero corrected codeword, `ResidueTag` `converge`); `R > C` = the
     **`q=−1` escape** (errors bounded away from 0, no code, the parity-check forces an uncorrectable
     residue, `coding_theory.md`'s `s≠0`). The **source coding theorem** (entropy = compression limit) is
     built on the dyadic substrate: `optimalCodeLength n = n` = `H(uniform 2^n)`
     (`Coding.lean:70`, `source_coding_optimal:74`) — the achievable rate equals the entropy *exactly*,
     no asymptotics needed (the dyadic case is already tight, per INDEX). The **noisy-channel** coding
     theorem proper (the asymptotic `R<C` achievability + converse) is ABSENT — it is the `Real213`/limit
     residue (INDEX: "Channel coding lower bound (Shannon converse) — needs general real-valued log").

- **Residue (`q=±1` tag)** — two stratified poles, the channel read at its threshold:
  - **`R < C` ⟺ `q=+1` (converge / achievable / errors→0).** A code exists driving error probability to
    zero; this is `coding_theory.md`'s `s=0` syndrome-zero corrected-codeword pole
    (`ResidueTag.golden_is_converge:180`, multiplier `+1`). On the dyadic substrate it is *exact*:
    `optimalCodeLength n = n = H` (`source_coding_optimal`), `I(X;X)=H(X)` lossless
    (`mutualInfo_self_eq_entropy`).
  - **`R > C` ⟺ `q=−1` (escape / error floor).** Error probability is bounded away from 0; the channel
    cannot carry the rate — `entropy.md`/`cardinality.md`'s `q=−1` escape, the information the reading
    forces but the channel's image cannot capture, `coding_theory.md`'s `s≠0` uncorrectable residue
    (`ResidueTag.escape_residue_outside:133`, multiplier `−1`).
  - **The data-processing inequality** `I(X;Z) ≤ I(X;Y)` for a Markov chain `X→Y→Z` = **monotonicity of
    the `×↦+` character under composition** (the preserved-information residue can only *shrink* down a
    chain — the same monotone-shrink as `kl_nonneg`/`klBitsDyadic` depth-difference). The named DPI
    theorem is ABSENT (no `dataProcessing` in-repo, grep-confirmed); it is predicted as the composition-
    monotonicity of `mutualInfoBits`.
  - **The AEP / typical sequences** = the `q=+1` concentration (LLN): the empirical surprise per symbol
    concentrates at `H`, so the typical set has `≈2^{nH}` sequences each of probability `≈2^{−nH}`. This
    is `gaussian_clt.md`/`probability.md`'s weight-axis LLN (`balanced_LLN_modulus` `CLTLimit.lean:31`,
    `countTrue_append`/`bernoulli_LLN_exact` `LLN.lean:29,66`), the `q=+1` converging modulus — the
    *engine is built*; the named `typical set`/`AEP` object is ABSENT.

## Re-seeing — `⟨C | L⟩ ⊕ Residue(q=±1)`

```
  channel X→Y           =  ⟨ two bisection families | transition weight p(y|x) ⟩   (entropy.md's C, indexed twice)
  mutual info I(X;Y)     =  H(X)+H(Y)−H(X,Y)  = the ×↦+ character on joint-vs-cond   (mutualInfoBits, MutualInfo.lean:50)
  I = 0 ⟺ independent     =  joint fills product (channel preserves nothing)          (mutualInfo_independent_zero:42)
  I(X;X) = H(X)           =  noiseless channel preserves everything                   (mutualInfo_self_eq_entropy:84)
  I ≥ 0 (genuine)         =  (n+m−j)+j = n+m, no clamp (subadditivity)                (mutualInfo_genuine:77, entropy_subadditive:70)
  capacity C = max I      =  the variational optimum over input weights (weight axis) (noiseless_capacity:33; bscCapacity*:44 — value only)
  BSC(1/2^k) capacity     =  k/2^k  (dyadic, exact rational, not transcendental)      (bsc_half_capacity:52, bsc_byte_capacity:56)
  source coding: R = H    =  optimalCodeLength n = n = H(uniform 2^n)                 (source_coding_optimal, Coding.lean:74)
  noisy coding: R<C ⟺ ok  =  q=+1 achievable (errors→0) vs q=−1 escape (error floor)  (ResidueTag; coding_theory.md s=0/s≠0)  [thm ABSENT]
  data-processing ineq    =  I(X;Z) ≤ I(X;Y)  = ×↦+ character monotone under ∘        (predicted; no dataProcessing in-repo)
  AEP / typical set       =  empirical surprise → H  (q=+1 LLN concentration)         (balanced_LLN_modulus CLTLimit.lean:31)  [named obj ABSENT]
```

**(1) Mutual information IS the `×↦+` character — read on the directed pair, not a new object.** This is
the note's new datum over `entropy.md`. `entropy.md` read the additive surprise character on *one*
distribution; the channel reads it on the *joint vs conditional* — `I = H(X)+H(Y)−H(X,Y)` is the
*defect* of `entropy.md`'s additivity, exactly when the joint fails to be the product. So the channel's
preserved information is `entropy.md`'s residue-of-additivity, read as a quantity. In-repo
`mutualInfoBits = h_x+h_y−h_joint` (`MutualInfo.lean:50`) and `mutualInfo_self_eq_entropy`
(`I(X;X)=H(X)`) make "a noiseless channel transmits its full entropy" a `Nat`-identity.

**(2) Capacity is the variational optimum — the weight axis maximized.** `C = max_{p(x)} I(X;Y)` is the
same optimization shape as `convex_duality.md`'s biconjugate `f**` and `gaussian_clt.md`'s fixed point:
the weight-reading dialed to its extremum. The repo builds the *optimum value* (noiseless = 1, BSC =
`k/2^k`) but not the `max`-over-`p(x)` object — capacity here is a *recorded optimum*, not a *computed*
one. The dyadic substrate makes the BSC capacity `k/2^k` an **exact rational** (not the transcendental
`1 − h(1/2^k)` of the continuous theory) — the same dyadic collapse `entropy.md` exploits.

**(3) The coding theorem is the `q=±1` threshold tying to `coding_theory.md`.** "Reliable ⟺ R < C" is
the residue tag verbatim: `R<C` = `q=+1` (a code exists, errors→0 — `coding_theory.md`'s syndrome-zero
corrected codeword, `s=0`); `R>C` = `q=−1` (error floor — `coding_theory.md`'s uncorrectable `s≠0`). The
*source* coding theorem (entropy = compression limit) is built **exact** on the dyadic substrate
(`source_coding_optimal: optimalCodeLength n = n = H`); the *channel* coding theorem proper is asymptotic
(achievability + Fano converse) and is the `Real213`/limit residue, named-absent in the INDEX.

## Revelation (collapse + forcing + the `q=±1` spine)

**Collapse — mutual information, channel capacity, and the coding theorem are ONE `×↦+` character read
on a channel, three ways.** `I(X;Y)` is `entropy.md`'s additive surprise character read on the
joint-vs-conditional (`mutualInfoBits` = the additivity-defect); capacity is that reading's variational
optimum (`probability.md`'s weight axis, `convex_duality.md`'s `f**`-optimum shape); the coding theorem
is its `q=±1` threshold (the same `ResidueTag` poles `coding_theory.md` uses for syndrome-zero/nonzero).
No new primitive: the channel is `entropy.md`'s bisection `C` indexed twice, and all three readings are
the *one* `×↦+` arrow (`surprise_additive`/`vp_mul`) read on a directed pair. **Source coding and channel
capacity collapse to one number on the dyadic substrate**: `optimalCodeLength n = n =
shannonEntropyUniformBits n = noiselessChannel·n` — compression limit, entropy, and noiseless capacity
are *the same depth* `n` (`Coding.lean:74` = `Entropy.lean:35` = `Channel.lean:33`).

**Forcing — `I ≥ 0` and DPI are forced by the character, not posited.** `I(X;Y) ≥ 0` is *forced* by
subadditivity (the joint cannot carry more bits than its marginals, `entropy_subadditive:70`,
`mutualInfo_genuine:77`: `(n+m−j)+j = n+m` with no `Nat.sub` clamp) — i.e. the `×↦+` character's
homomorphism makes the product-of-marginals an upper bound. The data-processing inequality `I(X;Z) ≤
I(X;Y)` is *forced* as the same character being **monotone under composition** (a longer Markov chain can
only lose preserved information) — the same monotone-shrink as `klBitsDyadic`'s depth difference. The
channel cannot *create* mutual information by post-processing, exactly as the residue can only shrink down
a chain (README's "residue of a reading's self-application", here along `X→Y→Z`).

**The `q=±1` spine — the coding theorem IS the residue tag, shared with `coding_theory.md`.** This is the
load-bearing link. `coding_theory.md` tagged syndrome-zero `s=0` as `q=+1` (the code corrects, residue
empty) and `s≠0` as `q=−1` (uncorrectable error class surfaces, `cycle_vs_contractible_qpm`). The
noisy-channel coding theorem is the *same* tag at the rate threshold: `R<C` is the achievable `q=+1` pole
where such a syndrome-zero code *exists*, `R>C` the `q=−1` escape where it cannot. So Shannon's theorem
and the algebraic syndrome are one `ResidueTag` distinction read at two granularities — the *existence* of
the corrected code (`R<C`) and the *correction itself* (`s=0`). The AEP supplies the `q=+1` converge
mechanism (`balanced_LLN_modulus`'s concentration is *why* the typical-set code achieves `R<C`).

## Note for the technique — does information theory VALIDATE the calculus?

**EXTEND by consolidation; the discrete legs BUILT ∅-axiom, the asymptotic coding theorem the `Real213`
residue.** Information theory adds **no new axis**: `C` = `entropy.md`'s bisection family (indexed twice
for a channel); `I(X;Y)` = the `×↦+` character on the joint-vs-conditional (`mutualInfoBits`); capacity =
the weight-axis variational optimum (`convex_duality.md`'s `f**` shape, value built per channel); the
coding theorem = the `q=±1` rate-vs-capacity threshold (`ResidueTag`, shared with `coding_theory.md`'s
syndrome tag); the AEP = the `q=+1` LLN concentration (`balanced_LLN_modulus`). Model v7.1 carries all of
it. The new datum beyond `entropy.md`/`coding_theory.md`: **mutual information is the entropy character
read on a directed pair** (the preserved-information = the additivity-defect = the channel residue), and
the coding theorem **links the analytic threshold (`R<C`) to the algebraic syndrome (`s=0`) via one
`ResidueTag`** — Shannon's reliable-communication theorem and `coding_theory.md`'s corrected codeword are
one `q=±1` distinction.

**Lean-grounded vs conceptual.**
- *Grounded (∅-axiom, verified):* mutual information end-to-end (`mutualInfoBits`,
  `mutualInfo_independent_zero`, `mutualInfo_self_eq_entropy`, `entropy_subadditive`,
  `mutualInfo_genuine`, MutualInfo 12/0); channel capacity *values* (`noiseless_capacity`,
  `bscCapacityNum/Den`, `bsc_half_capacity`, `bsc_byte_capacity`, Channel 8/0); **source coding theorem**
  on dyadic substrate (`source_coding_optimal: optimalCodeLength n = n = H`, Coding 10/0); the capstone
  bundle (`channel_witness`, `total_witness`, Capstone 7/0); the AEP/threshold engines
  (`balanced_LLN_modulus`, `ResidueTag.residue_tag_two_poles`, cross-domain).
- *Conceptual (predicted, open):* the **noisy-channel coding theorem** proper (asymptotic `R<C`
  achievability + Fano converse — INDEX names it "needs general real-valued log", the `Real213`/limit
  residue); the **`C = max I` variational object** (only optimum values built, not the max-over-`p(x)`);
  the **data-processing inequality** as a named monotonicity theorem (predicted = `mutualInfoBits`
  monotone under ∘); **typical sequences / AEP** as a named object (engine = `balanced_LLN_modulus`);
  **rate-distortion** (the lossy weight-vs-distortion trade-off — absent).

**Verdict: EXTEND (consolidation).** Shannon information theory = `entropy.md`'s `×↦+` character read on
a channel (mutual information = the character on the joint-vs-conditional = the preserved-information
residue, `mutualInfoBits`) + capacity = the weight-axis variational optimum (value built per channel) +
the coding theorem = the `q=±1` rate-vs-capacity threshold linking to `coding_theory.md`'s syndrome=0
achievability. The discrete/dyadic load-bearing legs (mutual information, capacity values, source coding,
the AEP/threshold engines) are STRICT ∅-axiom in-repo; the asymptotic noisy-channel coding theorem, the
`max I` variational object, the named DPI, typical-set, and rate-distortion objects are predicted-not-
built — the asymptotic coding theorem being the `Real213`/limit residue (the channel side of the same
limit `entropy.md` named for non-dyadic `−Σ p log p`).

---

### Verified Lean anchors (file : line : theorem) — all grep-confirmed; scan tallies via `tools/scan_axioms.py` from repo root

- `Lib/Math/Probability/Information/MutualInfo.lean` (**12 pure / 0 dirty**) — mutual information = the
  `×↦+` character on joint-vs-conditional:
  - `:50` `mutualInfoBits h_x h_y h_joint = h_x + h_y − h_joint` (def) — **`I(X;Y) = H(X)+H(Y)−H(X,Y)`**.
  - `:42` `mutualInfo_independent_zero` (`I = 0` ⟺ independence, via `Nat.sub_self`).
  - `:84` `mutualInfo_self_eq_entropy` (`I(X;X) = H(X)`, noiseless channel preserves all).
  - `:70` `entropy_subadditive` (`2^j ≤ 2^n·2^m ⟹ j ≤ n+m`) + `:77` `mutualInfo_genuine`
    (`(n+m−j)+j = n+m`, the non-vacuous `I ≥ 0`).
  - `:28` `jointEntropyIndependentUniforms`, `:32` `joint_independent_eq_sum`, `:55` `mutualInfo_clamped`.
- `Lib/Math/Probability/Information/Channel.lean` (**8 pure / 0 dirty**) — channel + capacity (value):
  - `:30` `noiselessChannel = 1`, `:33` `noiseless_capacity` (capacity 1 bit/symbol, `rfl`).
  - `:44-45` `bscCapacityNum k = k`, `bscCapacityDen k = 2^k` (BSC at dyadic noise `1/2^k`, capacity
    `k/2^k` exact rational); `:48` `bsc_capacity_pos`, `:52` `bsc_half_capacity`, `:56` `bsc_byte_capacity`.
  - `:39` `randomChannelCapacity = 0` (the `q=−1` zero-capacity / uncorrelated-output pole).
- `Lib/Math/Probability/Information/Coding.lean` (**10 pure / 0 dirty**) — source coding theorem (dyadic):
  - `:70` `optimalCodeLength n = bitsAfterBisections n`, `:74` `source_coding_optimal` (`= n = H(uniform
    2^n)` — **achievable rate = entropy, exact**); `:78` `byte_optimal`, `:81` `kilobyte_optimal`.
  - `:27` `hammingDistance`, `:34` `hamming_self`, `:50` `hamming_symm`, `:63` `hamming_triangle_concrete`.
- `Lib/Math/Probability/Information/Capstone.lean` (**7 pure / 0 dirty**) — the bundle:
  - `:44` `channel_witness` (`noiselessChannel = 1 ∧ bscCapacityNum k = k`); `:57` `total_witness`
    (6-fact grand bundle incl. mutual info + channel + source coding).
- `Lib/Math/Probability/Information/Entropy.lean` (entropy character, cross-ref `entropy.md`) —
  `:35` `shannonEntropy_uniform_eq_depth` (`H(uniform 2^n)=n`), `:90` `surprise_additive`
  (the `×↦+` homomorphism), `:83` `entropy_additive`. (Per `entropy.md`, not re-scanned this pass.)
- `Lib/Math/Probability/Information/KLDivergence.lean` — `:26` `klBitsDyadic a b = a − b`, `:29`
  `kl_self_zero`, `:33` `kl_nonneg` (the monotone depth-difference DPI-flavour; cross-ref `entropy.md`/
  `information_geometry.md`). (Not re-scanned this pass.)
- `Lib/Math/Probability/Limit/CLTLimit.lean` — `:31` `balanced_LLN_modulus` (the `q=+1` LLN
  concentration = the AEP engine). `Lib/Math/Probability/Limit/LLN.lean` — `:29` `countTrue_append`,
  `:66` `bernoulli_LLN_exact`. (Cross-ref `gaussian_clt.md`/`probability.md`, not re-scanned.)
- `Lib/Math/Foundations/ResidueTag.lean` — `:228` `residue_tag_two_poles`, `:180` `golden_is_converge`
  (`q=+1` achievable `R<C`), `:133` `escape_residue_outside` (`q=−1` error floor `R>C`). (Per
  `SYNTHESIS.md`, not re-scanned.)
- cross-frame (BUILT, per their notes): `coding_theory.md`'s `ml_decoder_capstone`/`spin_glass_213_capstone`
  (syndrome-zero `s=0` = the `q=+1` corrected codeword the coding theorem promises at `R<C`);
  `convex_duality.md`/`OllivierRicci.kantorovich_weak_duality` (the variational-optimum shape of capacity);
  `entropy.md`'s `surprise_additive`/`vp_mul` (the `×↦+` character).

Scan tallies this pass (`python3 tools/scan_axioms.py <module>` from repo root): `…Information.MutualInfo`
**12/0**, `…Information.Channel` **8/0**, `…Information.Coding` **10/0**, `…Information.Capstone` **7/0**.

### Dropped / flagged (could not verify or predicted-not-built)

- **The noisy-channel coding theorem proper** (asymptotic `R<C` achievability + Fano converse) is ABSENT
  — grep for `noisy_channel`/`coding_theorem`/`achievableRate`/`Shannon` finds only `shannonEntropyUniformBits`
  and docstrings; the INDEX names it out of scope ("Channel coding lower bound (Shannon converse) — needs
  general real-valued log for non-dyadic distributions"). The `Real213`/limit residue — the channel side
  of `entropy.md`'s non-dyadic `−Σ p log p` limit. Flagged, NOT cited as proven.
- **The `C = max I(X;Y)` variational object** (the maximization over input distributions `p(x)`) is ABSENT
  — only the *optimum value* per channel is built (`noiselessChannel=1`, `bscCapacityNum=k`). No
  `channelCapacity`/`channel_capacity` theorem in-repo (grep-confirmed). The optimization shape is
  predicted (`convex_duality.md`'s `f**`), the named max-object not built. Flagged predicted-not-built.
- **The data-processing inequality** `I(X;Z) ≤ I(X;Y)` is ABSENT — no `dataProcessing`/`data_processing`
  in-repo (grep-confirmed). Predicted as **monotonicity of `mutualInfoBits` under composition** (the
  `×↦+` character monotone down a Markov chain, the same shrink as `klBitsDyadic`). Not cited as proven.
- **Typical sequences / AEP** as a named object is ABSENT — no `typical`/`AEP`/`asymptotic_equipartition`
  in-repo (grep-confirmed). The **engine is built** (`balanced_LLN_modulus`, the `q=+1` LLN concentration);
  the named typical-set/AEP object predicted-not-built.
- **Rate-distortion** (lossy compression, the weight-vs-distortion trade-off) is ABSENT — no
  `rate_distortion`/`rateDistortion` in-repo (grep-confirmed). Predicted as the weight axis at a fixed
  distortion budget; not built.
- **Conditional entropy `H(X|Y)`** as a named def is ABSENT — present only implicitly via the joint
  `mutualInfoBits = h_x+h_y−h_joint` (the `H(X|Y)=H(X,Y)−H(Y)` form is not a separate Lean object). Flagged.
- No buildable witness proposed beyond what is built: the discrete legs (`mutualInfoBits`,
  `source_coding_optimal`, `bscCapacity*`, `channel_witness`) are already closed ∅-axiom theorems; the
  open legs (asymptotic coding theorem, `max I`, DPI, AEP, rate-distortion) need either the `Real213`
  real-valued log (coding theorem) or new named objects, so no new `decide` witness is asserted (per the
  prompt's caution against proposing unverified inequalities).
