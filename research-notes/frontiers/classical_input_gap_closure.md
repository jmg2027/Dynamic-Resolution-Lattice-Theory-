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

- **G1 — `coker ι* = H¹(K)` (the octet cokernel).  ✅ CLOSED (∅-axiom, no LES).**
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
| `1/α₂ = 30` | **B** | only the partition `NS²+NT²+2NS·NT = 25`; **no theorem `inv_α₂=30`**; "30"/"SU(5)" prose (and the prefactor-sector is mislabelled in-docstring) |
| `m_p/m_e = 6π⁵` | **B (purest)** | only `6 = NS·NT`; the falsifier is literally `6=6`; π/1836/ppm all prose.  **π is never derived in these files** (`Basel/Bound.lean:51` disclaims the ζ(2) bracket as "not a Lean theorem") |
| Basel depths `{1,2,∞}` | **A (integers) + C (force-binding)** | saturation `C(3,3)=1, C(2,3)=0` derived; but **repo self-contradicts**: `NeffDerivation` says "axiom_derived", `WhyBasel.lean:60` says "posited, open" |
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
  (`S` is a direct partial sum).  Exact construction: `zeta2RawSeq`,
  `zeta2_isAbMonotonic` (reduces to `0 ≤ S(n).2²`), the single load-bearing new
  lemma **`S_le_upper`** (`∀ i, S(i) ≤ S(N)+1/N`, the telescoping
  `1/(n+1)² ≤ 1/(n(n+1)) ⟺ n ≤ n+1`, a `Nat` induction), then instantiate
  `limit_brackets`.  New file `Real213/Zeta2Cut.lean`.
- **Honest framing**: the cut is **reached by no finite N** — the modulus never
  closes (the framework's own "Limit deified" / "reached by none").  So the
  continuous becomes a **bracket** to any precision, NOT a computed value.  That
  IS "the continuous is the discrete modulus's never-closing shape."  The
  completion modulus stays a hypothesis (as for π, ζ(3)) — but Basel is *better*
  positioned (explicit rate `1/(N(N+1))` via `toCauchySep`, a constructed
  modulus is plausible).
- **Honest limit**: closing ζ(2) converts **one of four** coupling terms
  (`1/α_em = 60ζ(2) + 30 + d²/NS + 1/(NS·NT·π⁵)`) from fed-literal to
  forced-discrete-bracket.  `π⁵` stays a fed literal (`PiFiveGap.lean:88,96`),
  and the `5.4×10⁻⁴` central-value gap is **provably bracket-independent**
  (`StructuralGap.lean:11-15`).  So the *continuous coupling* is not closed by
  this; one continuous *constant* (ζ(2)) becomes a genuine discrete bracket.

**Deepest answer (drawable).**  The discrete forcing **does** climb into the
continuous — as a never-closing bracket, via the framework's own `AbCutSeq`.
"Why does our universe match" at the continuous layer = the discrete modulus
brackets the continuous value to any precision (forced-discrete-pointing),
reached by none.  The build (`Zeta2Cut.lean`) is specified and achievable; not
yet built (substantial unreduced-rational induction) — recorded as the precise
next construction.

## Status + next

- **G1 closed** (`OctetCokernel`, PURE, build-green, wired; `IotaKToDelta4`
  docstring softened to cite it + flag the reading).
- **Concrete honesty fixes surfaced by the audit:** (i) `NeffDerivation` vs
  `WhyBasel` contradiction on the depth force-binding (integers derived, binding
  posited — reconcile); (ii) `1/α₂ = 30` has no theorem, only a docstring +
  mislabelled prefactor-sector.
- **CP `δ = 90°` C₄ — ✅ CLOSED (the math), second genuine (A).**
  `Mixing/CPPhaseHodgeBridge.cp_c4_is_signed_hodge_group` (PURE, build-green,
  wired to the Mixing aggregator): the four `C₄` Gaussian units, via `elt`, are
  exactly the powers `{J⁰,J¹,J²,J³}` of the **genuine signed Hodge star `J = ⋆`**
  on the `d−1=4` simplex (`SignedStarC4.signed_hodge_is_cp_i`), which has order 4
  (`⋆²=−I, ⋆⁴=I, ⋆²≠I`) ⇒ `360/4 = 90°`.  This replaces `CPPhaseC4Forcing`'s
  hand-written `def c4` with the actual `⋆`-operator — the `C₄ ⇒ 90°` is now
  structural, from the real Hodge geometry on `Δ⁴`.  Residual readings (kept, not
  ontologized): "this `⋆`-phase IS the CKM phase" and "Jarlskog `J ∝ Im`" (the
  `imPart := u.2` projection).  Drawable: *"⋆ on the 4-simplex squares to −1, so
  ⋆⁴ = id — a 90° rotation; the CP phase is one of its four powers."*
- Then T1 (tree-independence), T2 (relative H²), T3 (α₂ audit — now done: B).
