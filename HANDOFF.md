# Session Handoff — 2026-06-21

## Branch
`claude/multi-agent-research-pxzpls` (tracks `origin/`). This session reorients the
research direction; read `research-notes/frontiers/the_substance_test.md` first.

## What this session was (the convening)
A multi-agent investigation + adversarial debate to infer the originator's ultimate
purpose and start the research that serves it (directive: "not peripheral theorems —
the true intent"). Six agents: four evidence (repo trajectory, physics centrality,
Proof-ISA depth, math breadth) + three personas (Foundationalist, Engineer, Skeptic).
Full synthesis: `research-notes/frontiers/the_substance_test.md`.

## The inferred purpose (진의)
The repo is a machine for determining whether "everything is the residue under a Lens"
(primacy / no-exterior) is **substance or wordplay** — and for making that
determination *without self-deception* (hence the large anti-over-claim apparatus:
CLAUDE.md failure modes, `scan_all_axioms.py`, the publishability audit).

Key findings carried forward (evidence in the frontier note):
- Breadth is genuine (~26k thms, spot-PURE); **novelty is not** — the publishability
  audit finds "no new mathematics" anywhere; the one artifact is the ∅-axiom corpus.
- The **Proof-ISA is a classification scaffold, not an engine** (lifts are post-hoc
  relabels; only original demo is Euclid; "geometrization" = `8−3=5`).
- Physics is a **test surface**, not the goal.

## The reorientation (what counts as progress now)
Stop adding isolated ∅-axiom re-derivations of classical theorems (novelty ≈ 0, and
type-mismatched to the primacy claim). Two lines instead:
- **Line A — genuine cross-domain unifications**: a unification counts only when it
  carries a *proven map / shared engine* (never a value-coincidence, never prose).
  This is the only artifact that tests *unity across domains*, not constructivity per
  domain — the operational content of no-exterior.
- **Line B — exposure**: the no-exterior claim cannot be falsified from inside; ship
  the formalization paper (already scoped in the publishability audit) and run one
  pre-registered, time-boxed ISA attack on a recognized open problem.

## Closed this session (Line A, first deposit)
**COUNT-duality** — `lean/E213/Lib/Math/Combinatorics/CountDuality.lean` (7/7 PURE).
The Erdős union bound (Ramsey, row read) and the LYM inequality (Sperner, column
read) are **proven** to be the two marginals of one incidence double-count
(`incidence_balance` = `Sperner.sumOver_swap`). The union bound is re-derived
*through* the swap it previously bypassed (`union_bound_via_balance`); `count_duality`
carries both faces. Converts the corpus's narrated "two faces, one matrix"
(`PROOF_ISA.md`, `counting_as_cardinality.md`) into a theorem.
- Essay: `theory/essays/proof_isa/count_duality.md` (+ INDEX entry).
- Wired into `lean/E213/Lib/Math/Combinatorics.lean`; umbrella build green.
- `tools/scan_axioms.py E213.Lib.Math.Combinatorics.CountDuality` → 7 pure / 0 dirty.

## Closed (Line A — Markov orbit Cassini conservation; family II's two sub-domains unified)
`lean/E213/Lib/Math/NumberSystems/Real213/Markov/MarkovCassiniUnimodular.lean` (6 PURE).
The Markov/Stern-Brocot matrix orbit's `c`-entries `s(k)=(M_l^k·M_r).c` obey a 2nd-order
recurrence `s(k+2)=tr(M_l)·s(k+1)−1·s(k)` (Cayley–Hamilton Vieta, `markoff_vieta`, needs
`det₂ M_l=1`), so by `CassiniUnimodular.det_step` (multiplier `q`) their Cassini determinant
is **conserved** (`markov_orbit_cassini_const`: `det s n = det s 0`) — the same `q=1`
conservation as the golden Cassini. So `det₂=1` (the SL₂ unimodular invariant) **is** the
Cassini multiplier `q=1`: family II's two sub-domains (Markov SL₂ ↔ Cassini/Fibonacci) are
one law. Queue item #2, closed. Wired into `Real213.lean`; essay `unimodular_invariant.md`
cross-frame updated.

## Closed (Line A, fourth deposit — unimodular invariant, a SECOND unification family)
**One `det₂ = 1` drives the Stern-Brocot tree and the Markov recurrence** —
`lean/E213/Lib/Math/NumberSystems/Real213/Markov/UnimodularSynthesis.lean` (1 PURE,
reused lemmas PURE). The multiplicative law `det2_mul` (det(MN)=detM·detN, `ring_intZ`)
propagates `det=1` over the whole Stern-Brocot tree (`mNode_det1`) AND supplies the `det=1`
hypothesis that forces Frobenius monotonicity (`markoff_frobenius`, slope-injectivity engine)
and the Vieta jump `m'=3m₁m₂−m₃` (`markoff_vieta`). Capstone
`unimodular_drives_tree_and_markov` (genuine derivation chain, not a pairing). This
diversifies Line A beyond the incidence-algebra family — a second proven cross-domain family
(SL₂(ℤ) unimodularity). Essay `theory/essays/synthesis/unimodular_invariant.md`; wired into
`Real213.lean`. Selected by Scout C (HIGH genuineness × buildability). Next rung: extend the
same invariant to continuant (`ContinuantMarkov`) + Minkowski cocycle (`MinkowskiCocycle`)
readings. NOTE: essay-count INDEX rows for the 3 new essays still need a doc-sync table pass
(headline counts updated to 101/251).

## Closed (Line A — the two incidence families share ONE Fubini engine)
`lean/E213/Lib/Math/Combinatorics/IncidenceFubini.lean` (9/9 PURE). `genSwap` is a
carrier-general Fubini swap (any commutative-monoid carrier, proven once). Bridges:
`sumOver_eq_genSum` (Sperner.sumOver = genSum@Nat — COUNT-duality's engine) and
`sumZ_eq_genSum` (BinomialInversion.sumZ = genSum@Int over `rangeL` — the inversion engine).
Capstone `incidence_fubini_one_engine`: both COUNT-duality (Nat) and the inversion engine
(Int) are the two carrier-specializations of one `genSwap`. Synthesises the session's two
incidence unifications at their root. Essay `synthesis/incidence_fubini_one_engine.md`.
NOTE: Int additive laws must be the PURE `E213.Meta.Int213.{add_comm,add_assoc,zero_add}`;
core `Int.add_*` carry `propext` (would turn it DIRTY). Wired into `Combinatorics.lean`.

## Closed (Line A — falling factorials = signed-Stirling expansion of monomials)
`lean/E213/Lib/Math/Combinatorics/StirlingFallingInversion.lean` (2 PURE). `(x)_n =
Σ_k s(n,k)·x^k` is the partition-lattice inversion (`stirling_inversion_via_engine`) of the
forward `x^n = Σ_k S₂(n,k)·(x)_k` (`StirlingFalling.stirling_falling_sum`, bridged
sumTo→sumZ). The partition counterpart of the derangement (binomial) corollary — the two
Stirling expansions as the two faces of the antipode on `Π_n`. Wired into `Combinatorics.lean`.

## Closed (Line A — derangements = binomial inverse of factorial)
`lean/E213/Lib/Math/Combinatorics/DerangementInversion.lean` (2 PURE). The classical
`D(n) = Σ_k (−1)^{n−k}C(n,k)·k!` is a direct instance of `binomial_inversion_via_engine`
applied to the forward identity `n! = Σ_k C(n,k)·D(k)` (`DerangementConvolution.TZ_eq_fact`,
bridged to the engine's `sumZ`). Inclusion–exclusion for derangements = the Boolean-lattice
antipode on `(ℕ,≤)`, not a separate technique. Wired into `Combinatorics.lean`; essay
`incidence_inversion.md` cross-frame updated.

## Closed (Line A, third deposit — incidence-algebra inversion, three posets)
**Stirling inversion = the same engine on the partition lattice** — extends
`IncidenceInversion.lean` to **9/9 PURE**. `inversion_from_orthogonality` now has three
literal triangular instances: chain `(ℕ,≤)` (binomial), partition lattice `Π_n` (Stirling
both directions, via `stirling_orthogonality`/`stirling_orthogonality2` bridged to the
engine's `sumZ`/`delta`), plus the divisibility poset `(ℕ,∣)` (Möbius, ring route).
Capstone `incidence_inversion_three_posets`. Scouted by 3 parallel agents; Stirling was the
LOW-risk highest-value pick (a genuine third domain through one engine). Essay
`incidence_inversion.md` + INDEX updated to "three posets". `scan_axioms` → 9 pure / 0 dirty.

## Closed (Line A, second deposit)
**Two-cut antipode** — `lean/E213/Lib/Math/IncidenceInversion.lean`. Binomial
inversion (additive cut, Pascal poset `(ℕ,≤)`, signed-binomial antipode) and Möbius
inversion (multiplicative cut, divisibility poset `(ℕ,∣)`, antipode `μ`) are exhibited as
the **same incidence-algebra antipode**: a shared engine `inversion_from_orthogonality`
(one Fubini swap + the orthogonality collapse `S·M=δ`) instantiated on the additive cut, and
the inverse-element computation `μ∗(1∗f)=(μ∗1)∗f=ε∗f=f` on the multiplicative cut
(`incidence_inversion_two_cuts`). Closes frontier F2 of
`convolution_comultiplication_crossdomain.md`. Essay
`theory/essays/proof_isa/incidence_inversion.md` (+ INDEX). Wired into `Lib/Math.lean`.
`scan_axioms.py E213.Lib.Math.IncidenceInversion` → 6 pure / 0 dirty. The antipode partner
of COUNT-duality's Fubini: inversion vs double-count on the incidence matrix.
Open refinement: a *single* Lean engine covering both faces over one index convention
(divisor poset as triangular matrix over `[0,n]`); conceptual unification proven, single
shared term is the rung. F1 (bialgebra distributivity of `Δ_+`/`Δ_×`) still open.

## Next (priority order, Line A) — with this session's feasibility assessments
1. **`e`'s two homes — product form `N! = Π lcm(1..⌊N/i⌋)`** — **CLOSED ∅-axiom this session.**
   - `FTAEquality` (6 PURE): the full "number = its prime-valuation vector" FTA half —
     `vp_div_self`/`vp_div_other` (vp under division), `dvd_of_countOcc_le_vp`,
     `eq_of_vp_eq`. **The propext leak was core `Nat.mul_assoc`** (propext-carrying); the PURE
     `ring_nat` fixed it (standing lesson: avoid core `Nat.mul_assoc`, use `ring_nat`).
   - `FactorialLcmProduct` (5 PURE): `prodTo`, `vp_prod`, and
     `factorial_eq_prod_lcm : N! = prodTo N (fun i => lcmUpTo (N/(i+1)))` — the two homes of
     `e` welded by matching prime exponents (`eq_of_vp_eq` + `vp_factorial_eq_sum_vp_lcm`).
     Essay `synthesis/the_two_homes_of_e.md`. Wired into `ModArith`.
2. **Cassini ↔ Markov unimodular bridge** — **CLOSED** (`MarkovCassiniUnimodular`, 6 PURE):
   `det₂=1` is the Cassini multiplier `q=1`, so the Markov orbit's Cassini determinant is
   conserved (same law as golden Cassini). Family II's two sub-domains unified.
3. **Bell/Dobinski via the partition antipode** (`BellStirling`): `B(n) = Σ_k S₂(n,k)`; wire a
   falling-factorial/moment forward identity to `stirling_inversion_via_engine`. Risk MED.
4. **Cross-domain `LensIso`** — **CLOSED this session** (`ModArith.LensCRTGeneral`, 3 PURE):
   `leavesModNat_crt : LensIso (L_{mk}) (prodLens L_m L_k)` for `gcd(m,k)=1` — the general
   coprime CRT as a kernel coincidence (CRT direction via `crt_unique`, meet via
   `divides_refines`). Generalizes the corpus's concrete `L_6`. The number-theoretic
   primacy-witness, now for all coprime moduli. Essay
   `synthesis/crt_is_a_cross_domain_lensiso.md`. (The abstract-`Lens`-instance LensIso remains
   tautology-prone — not a clean target; the genuine cross-domain one is CRT.)

## Line B (the genuinely-remaining frontier — exposure)
The no-exterior claim cannot be falsified from inside (§5.1 blind spot). Next real test is
external:
(a) **STARTED** — the ITP/CPP/JAR formalization paper drafted at
   `research-notes/drafts/strict_zero_axiom_formalization_paper.md` (residue-metaphysics
   stripped; honest scope per the publishability audit; corpus stats 2,109 modules / ~15.6k
   thms; methodology = pure-twins + scanner + forcing-vs-bookkeeping; §5.2 uses this session's
   cross-domain unification family as the "breadth generated by shared engines" evidence).
   Next on (a): tighten to a venue's page limit, add a worked methodology figure (the
   `Nat.mul_assoc` propext-bisection makes a good one), pick venue (CPP experience track).
(b) one pre-registered, time-boxed ISA attack on a recognized open problem (not yet started).
These are the Skeptic's recommendation and the honest next phase.

Standing technique note (recurs every deposit): existing identities are stated over
*different `sumZ`/`sumTo` clones* (BinomialInversion / StirlingOrthogonality /
AlternatingBinomial / MobiusFunction / DyadicFSM.Sum). To feed one into the shared engine,
write a ~6-line **defeq bridge** (`X.sumZ N f = engine.sumZ N f` by induction) — done for
Stirling, derangements, and `genSum`. Core `Int.add_*` carry `propext`; use the PURE
`E213.Meta.Int213.*` for Int additive laws.

## Line B (parallel, when ready)
- The ITP/CPP/JAR formalization paper, residue-metaphysics stripped (audit §"the one
  publishable kernel").
- One time-boxed, pre-registered ISA attack on a recognized open problem.

## Verify
```
cd lean && lake build E213.Lib.Math.Combinatorics   # green
python3 tools/scan_axioms.py E213.Lib.Math.Combinatorics.CountDuality   # 7 pure / 0 dirty
```

## File map
```
lean/E213/Lib/Math/Combinatorics/CountDuality.lean         ← NEW (7 PURE): the unification
lean/E213/Lib/Math/Combinatorics.lean                      ← import + docstring
theory/essays/proof_isa/count_duality.md                   ← NEW essay
theory/essays/proof_isa/INDEX.md                           ← entry
research-notes/frontiers/the_substance_test.md             ← NEW: convening synthesis + 진의 + reorientation
```
