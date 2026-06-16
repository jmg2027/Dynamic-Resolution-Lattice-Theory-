# Δ⁴ is 2nd-tier (not forced like 2,3,5); the dual-defect is real on gauge, a slogan on gravity

**Status: open / clarifying finding.**  Raised by the originator: "the 4-simplex
may not be forced like 2,3,5 (or at least not in the repo)."  A multi-agent
cycle (developer + anti-forcing skeptic) confirms it and pins the honest status
of the `Δ⁴ ↔ K_{3,2}` dual-filling frame.

## Δ⁴ is a reading, not forced (confirmed)

- `(NS, NT, d) = (3, 2, 5)` forced (`PairForcing`/`NonDecomposable`, `d=NS+NT`);
  `K_{3,2}` forced by the `(3,2)` split.
- **`Δ⁴` is the maximal/trivial completion** of the 5 forced vertices — the
  repo itself calls it "the **maximal-non-commitment combinatorial filling**"
  (`theory/physics/foundations/atomic_constants.md:206`), contractible, `χ=1`.
  It is canonical given 5 vertices but is NOT a distinguishing-act property the
  way `(2,3,5)` are.
- **"Δ⁴ = spacetime" has zero Lean support.** Reading `d−1 = 4` as "4D
  spacetime" is a forced map (CLAUDE.md "External classification" / "stereotype
  matching" failure modes); the Lean only proves `Δ⁴` contractible (`H¹=0`,
  `IotaKToDelta4.lean:117,124`).  So Δ⁴-as-substrate (gravity/Hodge/CP) is a
  **2nd-tier deployment**, like `c` and the sector↔force naming — it rides on
  the forced atoms, not forced itself.

## The dual-defect: REAL on gauge, SLOGAN on gravity

The Euler defect `χ(Δ⁴) − χ(K) = 1 − (−7) = 8`:
- **Genuinely the same 8 as the gauge `b₁`** — via real relative-χ, not
  numerology: `ι: K ↪ Δ⁴` exists (`IotaKToDelta4.lean:60`), `Δ⁴` contractible,
  so `χ(Δ⁴)−χ(K) = rank H¹(K) = E−V+1 = 8`.  But honest precision: the PURE
  theorem `gluon_octet_identification` (`IotaKToDelta4.lean:157`) proves only the
  **supporting numbers** (`kerSizeDelta 5 2 = 16` ⇒ `H¹(Δ⁴)=0`; `2⁸ = 256`); the
  **coker-identification `coker ι* = H¹(K) = octet` is the docstring's classical
  LES**, not the theorem body.  So the *number* 8 = b₁ is ∅-axiom; the
  *cohomological identification* (octet IS the cokernel) rides on the LES
  (`ChannelCohomologyLoss.lean:87` `H2_relative_dim := H1_K`, asserted).  (No
  b₁=2-vs-8 conflation: `χ=−7` uses the `c=2` 12-edge graph; the simple-K
  `b₁=2` is tracked separately as `scaffold_loops`, `8 = 6 + 2`.)
- **Gravity side is a slogan** ("gravity = the defect"): zero Lean support.  The
  `Δ⁴ ↔ K` duality is between two fillings of the *same 5 vertices* (same `V`,
  same `b₀`); it carries no second simplex, no transport, no varying metric — it
  does NOT open the gravity curvature block (`gravity_reconnection_hinge_holonomy.md`).
  The hypothesis "gravity lives in the dual-defect" was a **forced extension,
  rejected** by the anti-forcing check.

## Honest sub-gaps (∅-axiom integrity)

- The topological meaning of `chi_rel = 8` (that it equals the relative
  cohomology rank via the long exact sequence) is **asserted as a definition** —
  `H2_relative_dim := H1_K` (`ChannelCohomologyLoss.lean:87`), docstring concedes
  "the LES itself is classical algebraic topology."  `decide`-purity certifies
  only the Int arithmetic `1−(−7)=8`; the LES is classical input baked in.  A
  genuine ∅-axiom frontier: derive the `coker ι* = H¹(K)` identification
  structurally (it IS proven pure in `IotaKToDelta4`; reconcile with the
  asserted-LES framing in `ChannelCohomologyLoss`).
- A natural, PURE-reachable next test (verify the space-match first — `h` is
  4-dim on Δ⁴'s `H¹`, the gauge module is 8-dim `H¹(K)`; do NOT bridge them
  without a real map): is gravity `h` the **`Sym(NS)`-invariant** and gauge `Q`
  the **`Sym(NS)`-covariant** of the proven Hermitian split `G = h + iQ`?
  (`Sym3OnH1KMatrix`, `H1K.lean:204`.)  Drawable: swap the 3 S-vertices →
  permutes the 8 gauge generators → is `h` fixed?  Only if the spaces genuinely
  match — otherwise it is the 4≠8 trap.

## Net

`(NS,NT,d)=(3,2,5)` forced; `c`, `Δ⁴`-as-spacetime are 2nd-tier readings.  The
dual-defect is a genuine gauge structure (relative χ of `ι: K↪Δ⁴`, octet =
coker) with an honest LES-as-definition gap; the gravity extension is not
supported and was correctly rejected as forcing.
