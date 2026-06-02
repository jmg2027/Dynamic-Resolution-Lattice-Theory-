# Session Handoff — 2026-06-02 (self-reference / µF↔νF / FSM marathon)

## Branch
`claude/concrete-non-fixed-point-witness-vi1IQ` (self-reference / µF↔νF / FSM marathon).
Working tree clean.  `lake build E213.Theory.Raw.API` clean.  All new theorems ∅-axiom.
(Concurrent `claude/newton-gregory-generalization-F6gYv` work — 41 PURE `NewtonGregory` —
is already on `main`; detailed in "What Was Done This Session / Arc B" below.)

## Current arc — the residue's self-pointing functor: µF, νF, and the FSM Lens

The self-pointing functor `F X = {a}⊎{b}⊎{x/y : x≠y}` is built out on both faces:

- **µF = Raw** (`Theory/Raw/Lambek`, `MuNuMirror`): initial algebra; descent well-founded
  (`isPart_wf`, `no_infinite_descent`), ascent unbounded (`ascent_unbounded`), `rawTower` the
  free-running counter at the seam.
- **νF = `CoResidue.SlashNu`** (`Theory/Raw/CoResidue`, **94 PURE**): the exact slash-νF via the
  M-type / path-function presentation (no coinduction primitive); `lAna`, `slashNu_final`
  (finality up to pointwise eq among anti-reflexive coalgebras), anti-reflexivity *positive*
  (`Distinct`, `treeDiffPath` — no bisimulation), `spineL` the infinite inhabitant escaping
  every finite Raw.  **νF populated** (§13–§17, the G178 proof-line): `spineOf` family (one
  escape per finite Raw, `spine_family_populates_nu`), `coSwap` (the `swap` automorphism acting
  on νF, `coSwap_nu_endomorphism`), `boolSpine` (`(Nat→Bool) ↪ SlashNu` preserving `Distinct` —
  honest ∅-axiom "uncountable", `boolSpine_injects_bitstreams`), `spineL_unique` (left-spine
  fixpoint), `nu_population_capstone`.  Dual µF tight bound: `StateMachine.exact_descent`.
- **The form of the residue** (`Lib/Math/ResidueForm`, essay `the_form_of_the_residue.md` — in
  the CLAUDE.md boot sequence): source-without-enclosure.
- **The inversion** (essay `the_residue_as_primitive.md`): Raw=µF, νF=SlashNu, view difference.
- **FSM / coalgebra Lens** (`Theory/Raw/StateMachine`, **20 PURE**, 9 sections, closed-arc;
  essay `the_residue_as_state_machine.md`): a §6 Lens reading (state read as state-transition;
  NOT an identity).  §1 state≅transition decode + `transition_deterministic` (single-valued);
  §2 determinacy (`transition_determines_behaviour` = finality); §3 excluded self-loop
  (`allBranchL ∉ SlashNu`); §4 counter never returns; §5 reachability (`BuildsIn` `n`-step
  build, `counter_reachable` clock, `every_state_reachable` whole-µF within `depth`);
  §6 behavioural/trace equivalence (`TraceEq = ¬Distinct` via decidable `Option Bool`, no
  bisimulation; `behaviours_traceEq` = determinacy as trace eq); §7 reducedness/minimality
  (`traceEq_finite_minimal` — trace map injective; `finite_states_finitely_separated`);
  §8 capstone (`mu_carrier_reachable_reduced_machine` — total+deterministic+reachable+reduced;
  Myhill-Nerode *uniqueness* explicitly NOT formalised); §9 loop-closing
  (`residue_escapes_minimal_machine` — `spineL` a genuine behaviour outside every finite state =
  source-without-enclosure at the FSM scale).  Adversarial-reviewed each round.

**Merged to main this session**: the FSM batch (`StateMachine.lean` +
`the_residue_as_state_machine.md`), alongside the form/inversion batch (merged earlier).

---

## What Was Done This Session

### Arc A — G171 Apéry zeta tower marathon
**`Cauchy/DepthAperyCubic` (23) + `DepthQuadraticGeneric` (7) + `CasoratianStep` (5, incl.
`telescope`: `(∏P)g(n)=(∏Q)g(0)`, the ζ(3) Casoratian `1/n³` cube-product shape) +
`CasoratianSigned` (17: signed law + signed telescope as ℕ-pair `npairEquiv`, sign = axis
swap; `telescope_pair` ζ(3) constant `+6/n³`, `telescope_pair_alt` ζ(2) alternating `±5/n²`
via `iterNeg n`=`(−1)ⁿ`, concrete `cube_casoratian_telescope`; ℤ caveat dissolved
213-natively via `NatPairToInt`) + `CassiniSigned` (2: the residue floor's Cassini
cross-determinant `fib(n+2)fib(n)−fib(n+1)²=(−1)ⁿ⁺¹` as the depth-0 signed Casoratian —
`cassini_pair`: `npairEquiv (fib(n+2)fib n, fib(n+1)²) (iterNeg (n+1) (1,0))`, magnitude 1
floor + sign Oscillate) + `DepthCubicGeneric` (5: `cubic_polyDepth` — `∀ A B C D, polyDepth 3
(A·n³+B·n²+C·n+D)`, COMPLETE; `cube_eq` `n³=6·C(n,3)+6·C(n,2)+n`) +
`DepthResidueFloor` (2) + `DepthSelfReference` (3) = 64 PURE (+ infra `Meta/Nat/PolyNatM` 22
PURE) + research-notes
`G171_apery_zeta_tower.md` / `G171_self_pointing_depth_213.md` / `G171_casoratian_pair_213.md`.**

**Infra (this session, the user's "build infra not Lean core" push):**
`Meta/Nat/PolyNatM` (22 PURE) — a ∅-axiom **multivariate** `Nat` polynomial reflection prover
`poly_idM` (flat monomial-map normal form; the `k`-variable generalization of `PolyNat`
(1-var) / `PolyInt2` (2-var)).  The `ring`-replacement that `ac_rfl` (propext-dirty) cannot be
over ℕ.  Discharges any multivariate `Nat` identity in one line — used to land `cube_reorder`
and the two `cubic_eq` reorders, unblocking the generic cubic.  Plus `Meta/Nat/PolyNatMTactic` — the **`ring_nat`** elaboration tactic (auto-reifies a `Nat` `=` goal and discharges via `poly_idM`), the ergonomic ∅-axiom `ring` for ℕ; `DepthCubicGeneric` now uses `by ring_nat` throughout (no hand-written `PE` trees).
`DepthResidueFloor.self_pointing_depth_ladder` reads the depth count in 213: `diff` = a
pointing event, depth = re-pointings to self-coincidence; from the `P`/φ Cassini floor
(`DepthFloorDetOne`, depth 0, self-same rule = own fixed point) the depth is the drift of a
rule's `n`-dependence from pure self-reference — e:1, ζ(2):2, ζ(3):3.
`DepthSelfReference.diff_converge_or_escape` ties this to the concurrent session's
`Lens.SelfReferenceThreeOutcomes`: `diff` is the `Nat`-sequence realisation of Converge
(`W` settles at the unit `1 = det P = NS−NT`) / Escape (`2ᵏ` never closes = the residue,
`DepthCeilingResidue` / `object1_not_surjective`), parallel to the Raw realisation, unit `1`.
The divergence-depth thread carried to ζ(2)/ζ(3): the minimal-holonomic recurrence
coefficients of ζ(2) (`(n+1)²uₙ₊₁=(11n²+11n+3)uₙ+n²uₙ₋₁`, degree 2) and ζ(3)
(`n³aₙ=(34n³−51n²+27n−5)aₙ₋₁−(n−1)³aₙ₋₂`, degree 3) are discrete polynomials whose
finite-difference depth equals their degree (`apery_cubic_rung`, `zeta2_quadratic_rung`,
`zeta2_to_zeta3_degree_step`), depths pinned **exactly** (`aperyTop_depth_exact` /
`zeta2Top_depth_exact`).  ζ(3) cubics reindexed to `n=m+2` (all-positive); difference
identities by the `Meta.Nat.PolyNat` reflection ring; lower bounds by `decide`.
`casoratian_step` — the subtraction-free discrete-Wronskian law `c₂Cₙ=−c₀Cₙ₋₁`: the middle
coefficient cancels, so the Casoratian propagates by the outer coefficients
(`aperyTop=n³`, `aperyBot=(n−1)³`) alone — why the invariant is `deg c₂=deg c₀`.  The whole
order-2 degree-2 Apéry-like (Zagier sporadic) family is capped ∅-axiom:
`quadratic_polyDepth : ∀ A B C, polyDepth 2 (A·n²+B·n+C)` (Newton-form transfer + new
reusable `polyDepth_congr`).  **Honest correction (red-team)**: coefficient degree is
*incidental to irrationality* (ζ(4) order-2 doesn't prove it, Catalan β(2) open, ζ(5)
order-3); the e→ζ(2)→ζ(3) degree run does NOT continue as a tower — ζ(3) deg 3 is the
exception above the sporadic family.

### Arc B — Newton–Gregory generalization (concurrent branch, merged)
A full marathon on the **Newton–Gregory forward-difference reconstruction**, the
HANDOFF Open Problem #4 ("Newton–Gregory blocked over `ℕ`").  Diagnosis: the ℕ
forward difference `s(n+1)−s n` truncates, so the converse `polyDepth d ⟹ Newton
form` cannot be stated.  Generalization: run the calculus over `ℤ` (the readout
group in which `Δ` closes under iteration — `Int213.Core` is ∅-axiom).

New file `lean/E213/Lib/Math/Cauchy/NewtonGregory.lean` (41 PURE):

- **G1 `newton_gregory`** — universal `s(m+n) = Σ_{j≤n} binom(n,j)·(Δʲs)(m)` for
  *every* `s : ℕ → ℤ` (operator `Eⁿ=(I+Δ)ⁿ`, no hypothesis).  Single induction on
  `n` ∀`m`, expand `(Δʲs)(m+1)=(Δʲs)(m)+(Δʲ⁺¹s)(m)`, Pascal-recombine (`bsum_pascal`).
- **G2 `newton_gregory_inverse`** — `(Δⁿs)(m)=Σ_{j≤n}(−1)^{n−j}binom(n,j)s(m+j)`;
  `binomial_transform_roundtrip` (`F∘G=id`).  Sign handled by *reusing* `bsum_pascal`
  (on `j≤n`, `(−1)^{n−j}=(−1)ⁿ(−1)ʲ`) — no second induction.
- **G3 `reconstruct`** — `polyDepthZ d s ⟹ s n = Σ_{i≤d}(Δⁱs 0)·binom(n,i)`.
  **Closes Open Problem #4** (the ℤ converse ℕ could not state).
- **G4 `poly_bound`** — `polyDepthZ d s ⟹ ∃C, |s n| ≤ C·(n+1)^d`, `C=Σ|Δⁱs 0|`.
  **Unblocks T4** (∅-axiom half of Hurwitzian ⟹ poly-bounded p.q. ⟹ μ=2).
  New reusable pure infra: `natAbs_add_le` (ℤ triangle; core pulls propext),
  `natAbs_ofNat_mul`, `binom_le_pow` (`binom n i ≤ (n+1)ⁱ`), `one_le_succ_pow`.
- **G5 obstruction** — `vObs=(n−2)(n−1)`: `obstruction_nat` (¬polyDepth 2),
  `obstruction_first_diff_clamp` (ℤ slope −2 clamps to 0 over ℕ),
  `obstruction_int_constant` (ℤ 2nd diff const 2).  All `decide` (stays pure).

**Agents**: A (literature) confirmed G1=Thread 1A, G2=Thread 2B, G4=Thread 4
(Pólya–Ostrowski basis), the Hurwitzian⟹μ=2 chain a novel synthesis.  B (red-team)
gave three framing corrections, all folded in (see below).

**Three-tier**: promoted `theory/math/analysis/newton_gregory.md` (new chapter);
updated `theory/math/INDEX.md` (12 analysis sub-clusters), `cf_holonomicity_hierarchy.md`
(bridge no longer Newton–Gregory-blocked).  Scratch: `research-notes/G173`.

## Red-team corrections folded in (don't re-slip)
- **ℤ-lift framing**: NOT "ℤ keeps the signed distinguishing" (that's a
  Count-Lens-import-as-Raw slip) and NO ℕ-vs-ℤ dichotomy.  Say: **ℤ is the readout
  group the difference-Lens `Δ` lands in** (Δ doesn't close under iteration over ℕ).
- **Involution**: the binomial transform is **fixed-point-RICH = Nat-style**
  grounding, NOT a Bool-style/liar oscillation (that inverts §5.2's criterion —
  stereotype-matching).  "Two readings of one object" (change of basis) is fine.
- **Obstruction**: the *values* don't truncate (all nonneg); only the **first
  difference** clamps `−2→0`.  ℕ-`diff` is a *different Lens*, not broken.

## Current Precision Results (0 free parameters)
**No physics constants changed this session** (pure math: finite-difference
calculus / interpolation / growth bounds).  Precision table unchanged — see
`catalogs/physics-constants.md` and `catalogs/falsifiers.md`.  DRLT Validation
Standard status unchanged.

## Open Problems / Next (priority order)

0. **C1 ✅ DONE** (`Cauchy/QuasiPolyBound.lean`, 14 PURE): `quasiPolyCFZ_poly_bounded`
   — quasi-polynomial CFs are polynomially bounded (Hurwitzian⟹μ=2 spine, μ cited).
   Witnesses: periodic (Lagrange, bounded) + e (transcendental).  Used ℤ-faithful
   `QuasiPolyCFZ` (ℕ `polyDepth` does NOT imply `polyDepthZ` — `[3,2,1,0,0]` clamp).
1. **C2 ✅ DONE** (`Cauchy/FiniteDepthAlgebra.lean`, 22 PURE): `polyDepthZ_mul`
   (finite-depth ring, depth-additivity) via discrete Leibniz `diffZ_mul` +
   `mul_vanish`.  Plus module structure (add/smul/shift).  π "depth 6=1+1+4" now a
   theorem.
2. **C5 ✅ DONE** (`Cauchy/BinomialTransform.lean`, 6 PURE): `binomialT_involutive`
   (`T∘T=id`) + `binomialT_fixed` (`s+Ts` always fixed) — binomial transform is a
   fixed-point-rich (Nat-style) involution, settling the §5.2 self-reference question.
3. **C3 (partial)** e/π depth separation: ℤ witnesses now exist —
   `WallisDepthProduct.polyDepthZ_affine` gives e's ratio `n+1` depth 1; π's ratio
   `polyDepthZ 4` (`pi_ratio_polyDepthZ`, via the ring).  Remaining: the *exact*
   lower bounds (depth ≠ smaller).  Do NOT slide to "explains the e–π separation"
   (metaphysical); transcendence part classically open.
4. **C4 ✅ DONE** (`FiniteDepthAlgebra` §5, +5 PURE): `periodic_finite_depth_const`
   — periodic ℤ-sequence of finite depth is constant; finite-depth and periodic
   (Markov/quadratic) sectors meet only at constants.  Frontier left: eigenspace
   structure (dimension/basis of `{s : T s = s}`) over ℤ.
5. π non-holonomicity (classical open, from prior session, `G170`) — unchanged.
6. ζ(3) Apéry depth — DEFERRED to another branch (user).  Do NOT build here.

## Dead ends / cautions (don't repeat)
- `funext` pulls `Quot.sound` (DIRTY).  Use pointwise congruence lemmas
  (`bsum_congr`, `liftKZ_congrZ`, `vanishZ_congr`) instead.
- Core `Int.zero_add` pulls **propext** (asymmetric — `Int.add_zero` is fine); use
  `Int213.zero_add`.
- `conv_lhs`/`conv_rhs`, `omega`, `Nat.one_le_pow` are **unavailable** (Mathlib /
  version).  Use base `conv`, explicit rewrites, local `one_le_succ_pow`.
- Core `Int.natAbs_add_le`, `Int.natAbs_mul` pull **propext** — use the local pure
  `natAbs_add_le` / `natAbs_ofNat_mul` in `NewtonGregory.lean`.
- Coercion `(k : Int)` ≠ syntactic `Int.ofNat k` for `rw` matching — state lemmas
  with the `(k : Int)` coercion form, bridge to `Int.ofNat` by `show` inside.

## File Map
```
NEW Lean (∅-axiom, 41 PURE):
  lean/E213/Lib/Math/Cauchy/NewtonGregory.lean   ← G1-G5: universal id, inverse
                                                    transform, reconstruction,
                                                    growth bound, obstruction
  lean/E213/Lib/Math/Cauchy/QuasiPolyBound.lean  ← C1: quasi-poly CF ⟹ poly-bounded
                                                    (periodic + e witnesses), 14 PURE
  lean/E213/Lib/Math/Cauchy/FiniteDepthAlgebra.lean ← C2 ring (polyDepthZ_mul,
                                                    Leibniz) + C4 boundary, 27 PURE
  lean/E213/Lib/Math/Cauchy/BinomialTransform.lean ← C5: involution T∘T=id +
                                                    fixed-point richness + ±1 eigendecomp, 9 PURE
  lean/E213/Lib/Math/Cauchy/WallisDepthProduct.lean ← C2 applied to π: degree-4
                                                    ratio depth via the ring, 6 PURE
NEW theory chapter:
  theory/math/analysis/newton_gregory.md
NEW research note:
  research-notes/G173_newton_gregory_generalization.md
MODIFIED:
  lean/E213/Lib/Math/Cauchy.lean                 ← umbrella import
  theory/math/INDEX.md                           ← 12 analysis sub-clusters
  theory/math/analysis/cf_holonomicity_hierarchy.md ← bridge unblocked
```
