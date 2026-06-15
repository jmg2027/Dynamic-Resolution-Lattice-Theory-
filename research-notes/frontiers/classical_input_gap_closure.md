# Closing the classical-input gaps — forced, not frozen

**Program (sustained).**  The framework forces the *numbers* of physics
(2,3,5; 8; the coupling integers — ∅-axiom, `decide`).  But several
structural-physical *identifications* ride on classical mathematics / asserted
definitions / readings.  This program closes each gap to one of:
- **(a) ∅-axiom-forced + drawable** (close the MATH), or
- **(b) honest irreducible reading** (never ontologize the PHYSICS).

**The freezing line (the discipline).**  Close the math; do NOT freeze the
meaning.  Forcing `coker ι* = (F₂)⁸` is math.  "(F₂)⁸ IS the SU(3) gluon octet"
is a reading — `(F₂)⁸` is a char-2 vector space, the SU(3) adjoint is an 8-dim
*real Lie algebra*; the match is the **number 8 = NS²−1**, not the object.
Gate: if it can't be drawn in one plain sentence, it isn't真知.

## Gap map (ranked)

### CLOSEABLE

- **G1 — `coker ι* = H¹(K)` (the octet cokernel).  ◑ TYPED + LES-free + bug-fixed
  (∅-axiom), but Unit-MODELLED, not a genuine `ι*`-construction
  (re-examination).**
  Was: `ChannelCohomologyLoss.H2_relative_dim := H1_K` (asserted LES, classical);
  `gluon_octet_identification` proved only supporting numbers.  Now:
  `Cohomology/Bipartite/OctetCokernel.octet_is_cokernel_of_zero_map` (PURE) —
  `H¹(Δ⁴)` is the one-element group (genuine certificate
  `reduced_betti_d4_contractible`, reduced `b̃₁=0`; **fixed an indexing slip** —
  the old proof cited `kerSizeDelta 5 2`, a `C²`/`H²` datum, as the `H¹`
  certificate), so the induced `ι*` is the zero map, image `{0}`, **coker =
  H¹(K)**, rank 8.  Drawable: *"ι embeds K into the contractible Δ⁴; Δ⁴ has one
  H¹-class, so ι* is zero, so the leftover (cokernel) is all 8 loops — no LES."*
  Physics ("= SU(3) octet") kept as a reading, not ontologized.

- **G2 — `8 = adjoint SU(3)` naming.**  Partly real: the `Sym(3)` action on
  `H¹(K)` decomposing `2·triv ⊕ 3·std` over `𝔽₂` IS built (`Sym3IrrepDecomp`,
  `C3ChainCapstone`).  Irreducible residue: "SU(3) = the strong-force gauge
  group" is a physics dictionary entry.  Drawable forced part: *"the 8 loops
  carry a faithful Sym(3) action = 2·trivial ⊕ 3·standard."*

### IRREDUCIBLE READINGS (leave honestly open; closing = forcing)

- **G3 — "Δ⁴ = spacetime."**  No Lean metric/Lorentz/3+1; only face counts.
  Forced part: `d=5`, `C(5,k)` counts.  "= spacetime" is a reading.
- **G4 — "3 channels = 3 forces" / sector↔force.**  Already self-tagged as a
  Lens-output label (`AtomicBase/Force.lean:32-42`).  Correctly open.
- **G5 — χ(K)=−7 "stress forces 8 holes."**  `χ=b₀−b₁=−7` true; "stress forces"
  is rhetoric (`b₁=8` is forced by `E−V+1`, not by χ).  Cosmetic.

## Next targets (tractability order)

- **T1 — tree-independence of `H¹(K)` rank.**  `H1K.lean` *picks* a spanning
  tree {0,2,4,8}; that the rank `8` is the same for **any** spanning tree is the
  real cohomological content and is `decide`-able (enumerate spanning trees of
  K, each leaves `12−4=8` non-tree edges).  Drawable: *"pick any 4 edges
  touching all 5 dots; the other 8 always make the 8 loops."*
- **T2 — the genuine relative `H²(Δ⁴, K)`.**  Build the relative cochain complex
  and `decide` its rank = 8 directly, instead of aliasing `H2_relative_dim :=
  H1_K`.  Medium (needs the relative complex defined).
- **T3 — `1/α₂ = 30` cohomology-functional parity audit.**  Is 30 a genuine
  `H*(K)` cup-ring quantity or a bare count wearing a cohomology costume?  Audit
  identical to G1 (predict: prose, like G1 was).

## Systematic audit — the pattern is universal (multi-agent, verified)

A two-agent audit (auditor + anti-forcing skeptic) tested whether the
"numbers-forced / identifications-prose" split holds across the major
observables.  **Sharpened verdict: the framework forces (a) integer/combinatorial
skeletons and (b) a few genuine *counting* structural facts; but every map onto a
named Standard-Model object (SU(3) octet, SU(5) adjoint, α_i, mass ratios, J∝Im)
rides on docstring prose or a definition-smuggled projection.**  One line:
**the numbers and the counting are ∅-axiom; the physics dictionary is not in Lean.**

| Observable | Tier | Forced content (drawable) |
|---|---|---|
| `1/α₃ = 8` (octet) | **A math + C label** | `coker(0-map) = H¹(K)` rank 8; "= SU(3)" is a reading |
| `1/α₂ = 30` | **B** | `30 = 12·NT·5/4` **IS a proven `decide` theorem** (`Bare.lean:61` `inv_alpha_2 = 30`; also `SpectrumComplete`, `ResolutionDepth`) — what is prose is the *identification* `30 = 1/α₂` with the SU(5)/electroweak object + the sector labelling, not the arithmetic |
| `m_p/m_e = 6π⁵` | **B (purest)** | only `6 = NS·NT`; the falsifier is literally `6=6`; π/1836/ppm all prose.  **π is never derived in these files** (`Basel/Bound.lean:51` disclaims the ζ(2) bracket as "not a Lean theorem") |
| Basel depths `{1,2,∞}` | **A (integers) + C (force-binding)** | saturation `C(3,3)=1, C(2,3)=0` derived; the force-binding is posited (`NeffDerivation` + `WhyBasel` **agree** on this — earlier "self-contradiction" was over-stated; it is a *naming smell*, the theorem name `basel_formula_axiom_derived` reads broader than what it covers) |
| CP exists, 1 phase | **A (genuine)** | `(3−1)(3−2)/2 = 1` vs `N=2 → 0` — real KM counting, falsifiable |
| CP phase `= 90°` (C₄) | **A+B+C mixed** | "one phase"/"i²=−1" forced; "J∝Im" (`imPart := u.2`, defined not proven), "∈C₄" (hand-written `def c4`), "360/4=90" (`decide`) are seams |

**Two genuine (A) survivors** (neither a precision number): CP-phase
existence+uniqueness (`CPPhaseCount`), the depth integers (`NeffDerivation`).
Every coupling/mass identification is (B).  The repo's own self-flags
("posited", "open", "conjecture", "hunter-found") confirm the audit.

This is the program's core insight, and the physics form of "don't fix the
meaning": **the math (numbers, counting, cohomology) is the forced skeleton; the
physics names (octet, spacetime, mass, CP) are readings, promotable toward forced
only where genuine math sits underneath (octet→cokernel; CP→Hodge star), and even
then the final SM label stays a reading.**

## The deepest layer — does the discrete forcing climb into the CONTINUOUS?

The readings split discrete vs continuous: the closeable ones stayed **discrete**
(octet = finite `(F₂)⁸` cohomology; CP = the order-4 group `ℤ[i]^×`), the
resisting ones need **continuous** objects (SU(3) Lie group, spacetime manifold,
`π` to ppb).  The π fed as a literal (`GradedFormula.lean:34`) marks the
discrete→continuous boundary.  But the framework's own `Real213` says the
continuous is **not above** the discrete — it is the *never-closing modulus* of
a discrete pointing (`PiCut`, the limit "reached by none").  So the boundary is
not fundamental; the fed-π is a shortcut.  **Test: can the discrete modulus
provably bracket a continuous value, ∅-axiom?**

**Finding (two-agent, verified): YES — as a BRACKET (forced-discrete-pointing),
not a value; achievable now via the framework's own machinery.**

- `Basel/Bound.lean` computes rational endpoints `S(N)`, `upper(N)=S(N)+1/N`
  (`decide`), but the **bracketing of ζ(2) is asserted in prose, not proven**
  (`:49-52`: "Proof of ζ(2) ≤ upper(N) ... not needed as a Lean theorem").
- The genuine closure is the **`Zeta3Cut` template**: define ζ(2) as the
  `AbCutSeq` limit of `S(N)` (a monotone, positive, rational sequence), then the
  bracket transports to the real via `AbCutSeq.limit_brackets`
  (`Real213/AbCutSeq.lean:166`).  Reachable now, **~120–180 lines, easier than
  `Zeta3Cut.lean` (718 lines)** — Basel needs no holonomic recurrence engine
  (`S` is a direct partial sum).  **Correction (independent re-audit): the
  load-bearing lemma `S_le_upper` was MIS-labelled as "trivial `n ≤ n+1`".** The
  per-term `1/(n+1)² ≤ 1/(n(n+1))` is trivial, but the full `∀i, S(i) ≤ S(N)+1/N`
  does NOT induct directly — it needs the tighter invariant `S(i) ≤ S(N)+1/N−1/i`,
  i.e. the `Htel` cross-multiplication induction over **factorially-growing
  unreduced denominators** (`S(n).2 = ∏k²`).  Feasible (a `ring_nat` reduction to
  the `i ≤ i+1` core, no hard wall) but it is the **one genuinely non-trivial
  lemma**, not a one-liner.
- **Honest framing (corrected): the `Zeta3Cut` template brackets a HYPOTHESISED
  limit, not a constructed real.**  `AbCutSeq.limit_brackets` / `toCauchy` take
  the completion modulus + Cauchy schedule as **explicit hypotheses**
  (`AbCutSeq.lean:86-94,166`); `Zeta3Cut`'s `zeta3Limit_in_bracket` is likewise
  conditional.  So a built `Zeta2Cut` gives a bracket of a *hypothesised* ζ(2)
  (modulus as argument) — the **unconditional** content is only the *approximant*
  bracket `∀ n, S(n) brackets` (the analogue of `zeta3Cut_in_bracket`).  The
  reach to a *constructed* real still owes the separation hypothesis `hsep`
  (`AbCutSeq.lean:120`).  Basel IS better positioned (explicit rate
  `1/(N(N+1))` → `toCauchySep`) — "more plausible", not "done".  The cut is
  **reached by no finite N** (the framework's "reached by none") — the continuous
  is a bracket to any precision, not a value.
- **Honest limit**: closing ζ(2) converts **one of four** coupling terms
  (`1/α_em = 60ζ(2) + 30 + d²/NS + 1/(NS·NT·π⁵)`) from fed-literal to
  forced-discrete-bracket.  `π⁵` stays a fed literal (`PiFiveGap.lean:88,96`),
  and the `5.4×10⁻⁴` central-value gap is **provably bracket-independent**
  (`StructuralGap.lean:11-15`).  So the *continuous coupling* is not closed by
  this; one continuous *constant* (ζ(2)) becomes a genuine discrete bracket.

**Deepest answer (drawable, corrected).**  The discrete forcing brackets the
continuous value to any precision via the framework's own `AbCutSeq` — but
**unconditionally only at the *approximant* level** (`∀ n, S(n)` brackets); the
*real-number* ζ(2) still imports a modulus hypothesis, exactly as π/ζ(3) do.  So
"climbs into the continuous" is honest as "discrete brackets a *hypothesised*
ζ(2), reached by no finite N", NOT "forces a constructed real".  `Zeta2Cut.lean`
is **specified, not built**; the load-bearing lemma is a real `Htel` induction
(not the trivial `n ≤ n+1` earlier claimed).  This closes one fed-π'd *constant*
(ζ(2)) of one coupling term — the continuous coupling stays open (`π⁵` literal,
central gap bracket-independent).

## Re-examination — self-audit + INDEPENDENT 5-agent re-audit (honest downgrade)

Both Lean closures are PURE + build-green and remove the worst prose, but they
are **typed/structured arguments resting on a model or abstraction**, not full
constructions — my "genuine (A)" framing over-claimed.  A self-review caught
some of this; an **independent 5-reviewer audit caught MORE, including factual
errors my self-review missed** (the corrections above + below):
- **`OctetCokernel`**: `H¹(Δ⁴)` *modelled* as `Unit`, `ι_star` *defined* `= 0`, so
  "image trivial" is `rfl` by definition — not constructed from `ι_pullback`.
  **The genuine `ι_pullback` EXISTS in the repo (`IotaKToDelta4.lean:97`) but is
  unused** — the real closure would push it through `im δ⁰`.  Tier ◑, not ★★★★★.
- **`CPPhaseHodgeBridge`**: NOT "sounder than octet" (my error) — also a relabel.
  "replaces `c4`" was FALSE (no import); `J`-as-`⋆` unsupported while the genuine
  `hodgeStar` (`Hodge/Star.lean:65`) exists unused (details above).
- **Pattern audit**: two errors corrected — `1/α₂=30` DOES have a theorem
  (`Bare.lean:61`); the `NeffDerivation`/`WhyBasel` "contradiction" is a naming
  smell, not a contradiction (both above).
- **Star ratings**: the `★★★★★` on my matrix-`rfl`/`decide` bundles
  (`cp_c4_is_signed_hodge_group`, `gram_hermitian_gravity_gauge_split`,
  `metric_J_is_holonomy_S`) over-signal — downgraded to ◑ to match the prose.

**What HELD under independent audit (credit):** the pattern "numbers/counting
forced, physics dictionary is a reading" is accurate across the 6 spot-checked
observables; `K ≈ 3–7` is honest (if anything conservative); "π fed as a literal
in the coupling files" is accurate and correctly scoped (π IS built genuinely in
`PiCut.lean`).  The `atomic_c`, `delta4`, `evidential`, `gravity` notes are
exemplary self-deflating audits.  The ζ(2)-bracket finding is corrected below.

## Status + next

- **G1 — typed/LES-free/bug-fixed via a Unit-model** (`OctetCokernel`, PURE,
  build-green, wired; `IotaKToDelta4` docstring softened).  Fuller closure
  (construct `ι*` from `ι_pullback`) remains.
- **Concrete honesty items (corrected by the independent re-audit):** (i)
  `NeffDerivation`/`WhyBasel` is **NOT a self-contradiction** (earlier over-stated)
  — both agree the depth *integers* are derived and the *force-binding* is
  posited; it is a **naming smell** (`basel_formula_axiom_derived` reads as if it
  covered the binding; rename/clarify).  (ii) `1/α₂ = 30` **does have a theorem**
  (`Bare.lean:61`, earlier claim of "no theorem" was FALSE); only the SU(5)/force
  *identification* is prose.
- **CP `δ = 90°` C₄ — ◑ TYPED, leaning relabel (independent re-audit corrected
  TWO over-claims of mine).**  `Mixing/CPPhaseHodgeBridge.cp_c4_is_signed_hodge_group`
  (PURE, build-green) proves the four `C₄` units `= {I,J,−I,−J}` = powers of the
  matrix `J = (0,−1,1,0)`, `J²=−I`, order 4, `360/4=90`.  Two corrections:
  - **"replaces `CPPhaseC4Forcing`'s hand-written `c4`" was FALSE** —
    `CPPhaseC4Forcing` does **not** import the bridge; its `def c4` is untouched
    and still drives the capstones.  The bridge is a *parallel* leaf module, not a
    replacement.
  - **"`J` = the signed Hodge star ON `Δ⁴`" is unsupported** — `J` is a standalone
    2×2 integer matrix; the genuine `hodgeStar` operator on real cochains EXISTS
    (`Hodge/Star.lean:65`) but the bridge does **not** connect `J` to it (no
    `J = hodgeStar 4 1 3`).  So `J`-as-`⋆` is a docstring identification, like the
    CKM/`J∝Im` readings.  It is **not "sounder than octet"** (my earlier claim) —
    both are typed-but-modelled/abstract.
  Genuine gain: a typed `C₄` with `ℤ[J]≅ℤ[i]` ring structure (`i²=−1` proven by
  matrix mult, not posited).  A genuine closure would prove `J = hodgeStar …`.
- Then T1 (tree-independence), T2 (relative H²), T3 (α₂ audit — done: B, with the
  correction that `30` IS a theorem; only the SU(5) identification is prose).
