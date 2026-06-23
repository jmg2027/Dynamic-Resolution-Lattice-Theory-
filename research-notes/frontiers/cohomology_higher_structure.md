# Cohomology higher structure — the open frontier

**Status**: open (unformalized).  Recorded here per `PROCESS.md` sink rule
after the Phase-8 citation audit found the prose chapter
`theory/math/cohomology/k32_higher_cohomology.md` claiming these as closed
∅-axiom results while **no corresponding Lean exists**.  This note is the
honest live agenda; the chapter now points here.

## What IS closed (so the frontier is bounded, not vague)

Genuinely formalised at the K_{3,2}^{(c=2)} 2/3/4-skeleton truncations
(∅-axiom PURE, `lean/E213/Lib/Math/Cohomology/Bipartite/`):

- face dependence → `b_1 = 6`, `b_2 = 1` (`Filled3CellCohomology.face_dependence`,
  `cohomology_dims_at_full_simple`);
- ω = (1,1,1) the Sym(3)-invariant 2-cocycle
  (`Filled3CellCohomology.phase2_omega_invariant_2cocycle`);
- the cup_1 / cup_2 face ladder (`FaceCup1At3Cell`, `FaceCupHigher`);
- the Steenrod–Whitehead bridge `cup_1(ω,ω) = δ²(ω)`
  (`FaceCup1At3Cell.omega_face_cup_1_eq_delta2`);
- the L²-trace square identity (`SelfPairingTrace.bilinear_self_trace_eq_L1_sq`);
- the `Sq⁰ / Sq¹` ladder at ω with the single **vacuous** `Sq¹·Sq¹ = 0`
  (`SteenrodSquaresAtOmega.steenrod_squares_at_omega_master`,
  `Sq_1_squared_eq_zero` over `C⁴ = ∅`);
- the parametric (NS,NT,c)-family `b₀/b₁` + universal kernel
  (`Parametric/EulerAndCapstone.parametric_close_capstone`,
  `Betti/KernelConstancyUniversal.universal_kernel_close`).

## What is OPEN (cited as closed in prose, but no Lean exists)

Each line below names Lean that does **not** exist anywhere in the repo
(grep-verified absent, 2026-06-23):

1. **Universal Adem / non-vacuous Cartan.** Only the vacuous `Sq¹·Sq¹=0`
   is formalised.  The higher relations (`Sq²·Sq² = Sq³·Sq¹`, the Cartan
   formula `Sq¹(α⌣₀β) = Σ Sqⁱα ⌣₀ Sqʲβ`) and any `∀ a,b,k` ladder need
   the complex extended so target degrees host non-trivial classes, plus an
   Adem–Wu basis.  (Phantom files: `AdemUniversal`, `CartanAtTruncation`.)
2. **Explicit chain-level Sq²** at the 4-skeleton (currently only the
   vacuous `C⁴ = ∅` reading).  (Phantom: `Sq2At4Cell`.)
3. **5-skeleton extension + non-vacuous `H⁵` substrate.**  (Phantoms:
   `Filled5CellExtension`, `Filled5CellMultiExtension`.)
4. **Massey products.**  Both the `H¹`-triple `⟨h1,h3,h4⟩` via an
   opposite-edge cup, and the `H²`-triple `⟨ω,ω,ω⟩` landing-space audit,
   with the topological model `K_{3,2}^{(c=2)} ≃ S² ∨ (∨₆ S¹)`.  (Phantoms:
   `MasseyTripleH1Witness`, `MasseyTripleOmega`.)
5. **K_{3,3}^{(c=2)} secondary cohomology** — `b₂ = 5`, multi-dimensional
   Massey output, and the `c`-counter behaviour.  (Phantoms: all `V33*`,
   `Mobius213K33StateClass`.)
6. **General 213-native Steenrod algebra** — cup_i + Adem + Cartan +
   Steenrod squares as one framework.

## Entry points (where to start the real build)

- The cup_i ladder already exists at `i ∈ {0,1,2}` on K_{3,2}^{(c=2)} face
  cochains; the first genuine extension is `Sq²` chain-level (item 2),
  which only needs an Alexander–Whitney lift of `cup_0` at the 4-cell —
  smallest closable step.
- The `H¹`-triple Massey (item 4, first half) is the next: it needs an
  opposite-edge cup that descends to cohomology (`decide`-checkable over
  the finite (coboundary × cocycle) pairs) — no new skeleton required.
- K_{3,3} (item 5) is the larger program; defer until the K_{3,2} Massey
  machinery is real.

## Cross-refs

- `theory/math/cohomology/k32_higher_cohomology.md` — the chapter (closed
  part + this frontier in its "Open frontier (unformalized)" section)
- `theory/math/cohomology/bipartite.md` — parent (`b₀/b₁`)
- `research-notes/frontiers/G35_chiral_cup_ring_catalog.md` — chiral cup ring
