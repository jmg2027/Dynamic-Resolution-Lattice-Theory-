# Session Handoff — 2026-06-02

## Branch
`claude/goal-g171-marathon-research-Dj9Go` (G171 Apéry zeta marathon) — **merged to `main`**.
Working tree clean.  Full `lake build` clean (1500+ modules).  All new theorems ∅-axiom
(`tools/scan_axioms.py` → `N pure / 0 dirty` on every module below).

## What Was Done This Session

### 0. G171 Apéry zeta tower marathon (this branch, merged here)
**`Cauchy/DepthAperyCubic` (23 PURE) + `Cauchy/DepthQuadraticGeneric` (7 PURE) +
`Cauchy/CasoratianStep` (2 PURE) = 32 PURE + `research-notes/G171_apery_zeta_tower.md`.**
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

### 1. Merged `origin/main` (88 commits) into the branch
Resolved 5 conflicts (umbrella imports, `IntensionalCompletability` add/add cross-branch
convergence, `tower_native_completeness.md`, HANDOFF).  Adapted `RefinedCompletabilityEngine`
to main's `crossDetSmall_rescale_antitone` API.  Verified PURE + full build.

### 2. Spiral-axis exhaustiveness + binary cover + crystallographic bridge
- `CayleyDickson/Integer/ImaginaryQuadraticUnitTrichotomy.lean` (9 PURE).
  `unitForm_generic_axis` (Diophantine: `a²+d·b²=1`, `d≥2` ⇒ only `±1`),
  `imaginary_quadratic_unit_trichotomy` (axis = closed range `{2,4,6}`),
  `maximal_order_no_complex_unit` (the `d≡3 mod4` reduced form too), `axis_binary_cover`
  (`{2,4,6}=2·{1,2,3}`, midpoint `μᵏ=−1` = Cassini sign), `crystallographic_cosines`
  (Eisenstein `ztrace(ζ6^k)=2cos(2πk/6)={1,−1,−2,−1,1,2}`).
- `CayleyDickson/Tower/SpiralAxisCrystallographic.lean` (1 PURE): `{2,4,6}` = even half of
  crystallographic `{1,2,3,4,6}` = `2·{1,2,3}` (verified bridge to `crystallographic_restriction`).

### 3. π non-holonomicity MARATHON → `Cauchy/HurwitzianCF.lean` (21 PURE)
The CF-holonomicity hierarchy on the **partial-quotient sequence** `(aᵢ)` (third spiral-layer
reading).  `QuasiPolyCF p a` (= Hurwitzian: polynomial on each residue class mod p).  Tiers:
**0** `periodic_quasipoly` (quadratic irrationals); **1** `e_cf_quasipoly` (e=[2;1,2k,1] is
`QuasiPolyCF 3` — folklore "Hurwitzian ⟹ holonomic" made explicit) + `tan_cf_quasipoly`;
certificate `polyDepth_diff_recurrence` (`Δ^{d+1}=0`); **properness** `geometric_not_quasipoly`
(`2ⁿ ∉ QuasiPolyCF`, yet C-finite ⟹ `QuasiPolyCF ⊊ C-finite ⊊ holonomic` STRICTLY);
μ=2 bridge half `ePQ_linear_bound`/`tanPQ_linear_bound`.  **4 research agents** (literature,
repo-infra, red-team, synthesis).  Promoted `theory/math/analysis/cf_holonomicity_hierarchy.md`.

### 4. μ-positioning grounded (vs the irrationality measure)
A 4th research agent vs literature confirmed: the rate modulus `N(m,k)` IS the
irrationality-measure function `ψ(q)` (genuinely finer than μ = its limsup); divergence depth
is ORTHOGONAL + presentation-dependent (does NOT separate numbers); the CF-tier separates e/π.

### 5. Markov spectrum from the repo's own forms (`Real213/GoldenFormMarkov` 9 PURE, `MarkovTree` 13 PURE)
- `golden_anisotropic` (Vieta descent `(m,k)↦(k,m−k)`, no mod-5): golden form `m²−mk−k²`
  (disc 5) is the **first Markov form**, value `√5` = Lagrange minimum (φ).  `silver_anisotropic`
  (reuses `sqrt2_irrational`): disc-8 form, `√8`.  `golden_min_attained_on_fib` (= `fib_cassini_norm`):
  the `W=±1` floor IS the form's minimum, on φ's Fibonacci convergents.
- `markov_vieta` (Vieta jumping preserves `x²+y²+z²=3xyz`, coeff `3=NS`, no-subtraction
  invariant `x²+y²=z·z'`), `markov_tree_branch`, `markov_symm`, `markov_fibonacci_branch`
  (odd Fib 1,2,5,13,34) + `markov_pell_branch` (odd Pell 1,5,29,169) = the two spines,
  `markov_first_fork` ((1,2,5) forks to Fibonacci/Pell = Stern-Brocot binary node).
- Promoted `theory/math/analysis/markov_spectrum.md`.

### 6. Modular tower + Lagrange extremes
- `Real213/ModularElliptic.lean` (7 PURE): `modular_generator_orders` — `S` order 4, `U`
  order 6, det 1; `PSL(2,ℤ)=ℤ₂*ℤ₃`, elliptic orders `{4,6}` = Gaussian/Eisenstein axis,
  `−I` central = Cassini 2.  (Grounds a user-proposed axis/lattice/shape table — note G171.)
- `Real213/LagrangeExtremes.lean` (4 PURE): φ = spectrum floor (all-1s CF, `Periodic 1`,
  `QuasiPolyCF 1`, partial quotients pointwise minimal); π = opposite pole (unbounded pq).

## Current Precision Results (0 free parameters)
**No physics constants changed this session** (all work is pure math: irrationality /
approximation / Markov spectrum).  Precision table unchanged — see
`catalogs/physics-constants.md` (1/α_em, m_μ/m_e 0.48 ppb, R∞ 4.3 ppb, Ω_Λ, etc.) and
`catalogs/falsifiers.md`.  DRLT Validation Standard status unchanged.

## Open Problems (Priority Order)

### 1. π non-holonomicity (the marathon headline) — classically OPEN
`(aᵢ)` of π not P-recursive.  NOT closable ∅-axiom.  Provable neighbours closed
(`HurwitzianCF`).  Credible route = Flajolet–Gerhold–Salvy asymptotic obstruction (holonomic
⟹ asymptotics `C·ρ⁻ⁿ·nθ·(log n)ᵏ`, π's Gauss–Kuzmin statistics incompatible — itself
conditional on π being GK-normal).  See `research-notes/G170`.

### 2. ζ(3) Apéry divergence depth — DONE (`DepthAperyCubic`, this branch)
Built on the dedicated `claude/goal-g171-...` branch (per user): coefficient-degree
statistic ζ(2):2, ζ(3):3, exact, ∅-axiom + the sporadic-family cap + Casoratian step.
Headline reframed honestly (degree ≠ irrationality cause).  See
`research-notes/G171_apery_zeta_tower.md`; open follow-ups there are generic *cubic* depth-3
and the Casoratian telescoping `n³Cₙ=(n−1)³Cₙ₋₁ ⟹ Cₙ∝1/n³` (C-C).

### 3. Markov uniqueness ↔ Stern-Brocot indexing — classically OPEN
The binary fork + two spines are anchored (`markov_first_fork`).  A full ∅-axiom bijection
`Markov triples ↔ Stern-Brocot rationals` needs the L/R-word indexing; injectivity = the
Markov uniqueness conjecture (open).  See `research-notes/G172` thread A.

### 4. `QuasiPolyCF ⟹ polynomially-bounded` (general) — Newton–Gregory blocked
General growth bound fails over `ℕ` truncated subtraction for non-monotone polyDepth
sequences (Newton–Gregory reconstruction breaks).  Only witness-specific linear bounds done
(`ePQ_linear_bound`, `tanPQ_linear_bound`).  Don't re-attempt the general version naively.

## Unresolved from This Session (dead ends — don't repeat)
- **Newton–Gregory converse** (`polyDepth d s ⟹ s = newton form`) FAILS over `ℕ`: truncated
  `diff` corrupts non-monotone sequences (e.g. `[2,0,2,…]`).  So T4 general μ=2 bridge blocked.
- **propext landmines** (cost many DIRTY→PURE fixes; for next time): `rw` on an `Iff` pulls
  `propext`; `rw` inside an `ite` *condition* pulls `propext` (use `if_pos`/`if_neg`);
  leaking core lemmas to AVOID — `Nat.mul_assoc`, `Nat.mul_right_comm`, `Nat.add_mul`,
  `Nat.mul_add_mod`, `Nat.mul_add_div`, `Nat.pow_mul`, `Nat.pow_add`, `Nat.add_left_cancel`,
  `Nat.mul_lt_mul_right` (Iff), `Int.natAbs_eq_zero`, `Int.mul_neg`, `Int.eq_of_mul_eq_mul_left`.
  PURE replacements: `NatHelper.{add_mul,mul_assoc}`, `PureNat.pow_add`, `Int.natAbs_eq`, and
  local `add_left_cancel_pure`/`sq_lt_sq`/`pow_mul_pure`/`mul_sub_pure_le` (in GoldenFormMarkov/
  HurwitzianCF).  `abbrev` (not `def`) for Prop-shapes you want `decide` to see.

## Next
Options (none uniquely forced — ask user):
- **Hecke-group Lagrange spectra** (deepen thread C: `2cos(π/q)` ↔ spectrum) — needs cos infra.
- **Lagrange spectrum `<3` discrete part** entirely from anisotropic forms (extend
  `GoldenFormMarkov` along the Markov tree).
- New direction entirely.  (ζ(3) Apéry depth now done — see arc 0.)

## Three-tier state
- **Promotions this session**: `theory/math/analysis/cf_holonomicity_hierarchy.md`,
  `theory/math/analysis/markov_spectrum.md` (both new chapters); updated
  `spiral_coordinate_classification.md` frontier, `tower_native_completeness.md`,
  `theory/math/INDEX.md` (now 11 analysis sub-clusters).
- **Promotion candidates**: `Real213/{ModularElliptic, LagrangeExtremes}` and
  `crystallographic_cosines` are PURE but only noted in research-notes G171/G172 — could fold
  into a short `theory/math/analysis/modular_lagrange.md` if the thread continues.
- **Active scratchpad**: `research-notes/G170` (π non-holonomicity marathon, conjectures
  C1–C7), `G171` (modular tower table), `G172` (three Lagrange threads).

## File Map
```
NEW Lean (all ∅-axiom):
  lean/E213/Lib/Math/Cauchy/HurwitzianCF.lean                              ← CF-holonomicity tiers (21 PURE)
  lean/E213/Lib/Math/CayleyDickson/Integer/ImaginaryQuadraticUnitTrichotomy.lean ← axis {2,4,6} exhaustive + cosines (9)
  lean/E213/Lib/Math/CayleyDickson/Tower/SpiralAxisCrystallographic.lean   ← {2,4,6}=even half of {1,2,3,4,6} (1)
  lean/E213/Lib/Math/Real213/GoldenFormMarkov.lean                         ← golden/silver Markov forms √5,√8 (9)
  lean/E213/Lib/Math/Real213/MarkovTree.lean                               ← Vieta tree, spines, fork (13)
  lean/E213/Lib/Math/Real213/ModularElliptic.lean                          ← PSL(2,ℤ)=ℤ₂*ℤ₃ orders 4,6 (7)
  lean/E213/Lib/Math/Real213/LagrangeExtremes.lean                         ← φ floor / π pole (4)
NEW theory chapters:
  theory/math/analysis/cf_holonomicity_hierarchy.md                        ← Hurwitzian / π frontier
  theory/math/analysis/markov_spectrum.md                                  ← √5,√8, Vieta tree, spines
NEW research notes:
  research-notes/G170_pi_cf_nonholonomicity.md                             ← marathon + conjectures C1–C7
  research-notes/G171_modular_tower_axes.md                                ← axis/lattice/shape table analysis
  research-notes/G172_lagrange_threads.md                                  ← Stern-Brocot / φ-π / cosines
MODIFIED:
  lean/E213/Lib/Math/Real213.lean, CayleyDickson.lean, Cauchy.lean         ← umbrella imports
  lean/E213/Lib/Math/Real213/{SpiralCoordinate,RefinedCompletabilityEngine}.lean ← capstone + merge-adapt
  theory/math/INDEX.md, theory/math/analysis/spiral_coordinate_classification.md ← index + frontier
```

---

## Merged: the form of the residue + the inversion (claude/concrete-non-fixed-point-witness)

This merge also brings the foundational **residue-form / inversion** arc (originator's
"잔여의 형식 = 다 포괄하는 개념"):

- **(i) the form** — *source without enclosure* (`Lib/Math/ResidueForm.no_exterior_source_without_enclosure`):
  initial out (`SemanticAtom.raw_initial`) ∧ un-enclosed (`object1_not_surjective`) ∧ unit-name
  (`det = NS−NT`) ∧ forced shape (`atomic_iff_five`).  Canonical essay
  `theory/essays/the_form_of_the_residue.md` (in the boot sequence).  Escape at every scale
  (`research-notes/G180`: predicate / Raw-floor / tower-ceiling).  Synthesis: `research-notes/G178`.
- **(ii) the inversion** (`Theory/Raw/{MuNuMirror,CoResidue}`; `research-notes/G179`): residue/act
  as primitive, Raw = µF.  `MuNuMirror` (descent terminates / ascent unbounded).  `CoResidue` (26
  thm): the νF face via the M-type/path-functions — structural escape (`allBranch`), **finality**
  (`final_coalgebra`: `CoShape` final for `Bool×X×X`, existence + pointwise uniqueness, no
  coinduction), faithful embedding (`lToShape_faithful`), **anti-reflexivity is positive**
  (`treeDiffPath`/`slash_children_distinct` — no bisimulation), named infinite anti-reflexive
  inhabitant (`spineL`, the left-spine, `spineL_antiRefl` + `spineL_escapes`).
- §10: the everywhere-distinct subtlety **resolved** — it IS canonicity (`canonical_slash_decompose`
  ⟹ `cmp x y=.lt` ⟹ `x≠y`).  `lToShape_antiRefl`/`raw_embeds_antiRefl`: every Raw embeds
  **anti-reflexively** (+ faithfully, §6) into the leaf-labelled co-tree model; `spineL` the infinite
  anti-reflexive escapee.  §11–§12: the exact slash-νF **fully realised** —
  `SlashNu := {s//Consistent s ∧ AntiRefl s}` (carrier); `rawToSlashNu`(+`_faithful`, Raw=µF embeds),
  `spineSlashNu`∈SlashNu, `slashNu_carrier`; and **finality** `slashNu_final` — `lAna` (leaf-absorbing
  M-type anamorphism) is consistent (`lAna_consistent`), anti-reflexive given hAR (`lAna_antiRefl`),
  and the UNIQUE hom (`lAna_unique`, pointwise, finite-path induction, no funext/simp).  So SlashNu is
  the residue's exact slash-νF, ∅-axiom, **no coinduction primitive**.  INVERSION ARC COMPLETE
  (carrier + faithful embedding + named escapee + finality).  Honest: finality up to pointwise eq,
  among anti-reflexive coalgebras; M-type (path-function) presentation.  CoResidue ~43 thm, 64/0 PURE.
  Whole arc critique-hardened (6 adversarial rounds).
