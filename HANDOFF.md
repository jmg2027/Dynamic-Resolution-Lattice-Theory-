# Session Handoff — 2026-06-02

## Branch
`claude/non-holonomicity-rGhug` — pushed.  Working tree clean.  All new theorems ∅-axiom
(`tools/scan_axioms.py` → `13 pure / 0 dirty` on the new module).

## What Was Done This Session (π non-holonomicity marathon, cont.)

### π's boundedness frontier → `Cauchy/PositiveFloorUnbounded.lean` (13 PURE)
The structural reason the CF-holonomicity tiers above periodic live on **unbounded** partial
quotients, proved constructively (no LPO):
- **`positive_floor_unbounded`** — a positive *constant* top finite-difference
  (`polyDepth (m+1) s`, `liftK (m+1) s 0 ≥ 1`) ⟹ `s` **unbounded** with an *explicit* witness
  `n = N+(B+1)`.  Engine: positive top diff ⟹ `Δᵐs` strictly increasing everywhere;
  `evStrictMono_down`/`evStrictMono_descend` push it down to `s`; `evStrictMono_unbounded`
  telescopes.
- **`bounded_floor_zero`** — decidable-on-`ℕ` contrapositive: bounded depth-`(m+1)` ⟹ top
  difference `= 0`.
- **`positive_linear_exact`** — depth-1 positive-floor closes to the *exact* `s n = s 0 + c·n`
  (truncation vanishes for `c ≥ 1`); the ∅-axiom positive-linear case of the Newton–Gregory-
  blocked `QuasiPolyCF ⟹ poly-bounded` bridge.
- **`ePQ_unbounded`** — e's `2k+2` section has positive top difference ⟹ e's partial quotients
  unbounded *through the structural theorem*.
- **3 agents** (literature / red-team / repo-infra).  Promoted to
  `theory/math/analysis/cf_holonomicity_hierarchy.md` (frontier + boundedness subsection);
  scratch `research-notes/G173_pi_cf_boundedness_frontier.md`.

**Honest scope (red-team-corrected):** the theorem covers *positive-degree polynomial sections
only*.  Periodic floor (`φ`,`√2`) is not finite-difference-depth; the `2ⁿ` gap is exponential
(no finite depth) — both OUTSIDE the hypothesis class, NOT explained by this lemma.  "bounded
⟹ eventually constant" = LPO (Mandelkern 1988), deliberately NOT ∅-axiom (mirrors
`MonotonicBounded`).  Propext landmine caught: `Nat.sub_eq_zero_of_le` → replaced by
`Nat.sub_le_sub_right`+`Nat.sub_self`.

### Key agent findings (for next session)
- π's partial-quotient **boundedness is OPEN** — not even a sharp conjecture; unboundedness is
  only the Gauss–Kuzmin heuristic, and π is not known GK-normal.  (Correct G170's "conjecturally
  unbounded" wording.)
- "**bounded integer P-recursive ⟹ eventually periodic**" IS a (classical) theorem — mod-`m`
  periodicity of the polynomial recurrence coefficients (Garrabrant–Pak).  Not ∅-axiom here.
- **Klazar bound** (holonomic ⟹ `|aₙ| ≤ cⁿ·(n!)^d`): super-`(n!)^d` growth ⟹ non-holonomic —
  route to a *genuinely* non-holonomic witness (C10, next).

---

## Prior session (branch `claude/goal-g166-A6MVE`, merged to `main` at `c1ed6a7`)

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
(`HurwitzianCF`, `PositiveFloorUnbounded`, `NonHolonomicWitness`).  The **genuine
non-holonomic tier is now inhabited ∅-axiom** by `(n!)ⁿ` (`superFact_nonHolonomic`, via the
elementary Klazar growth majorant — C10 CLOSED this session).  **But π is provably NOT
reachable by that growth route** (π's p.q. don't grow super-factorially), so π's tier-3
membership needs a *different* obstruction.  **Next (C11):** the FGS *asymptotic-shape*
obstruction (holonomic ⟹ `C·ρ⁻ⁿ·n^θ·(log n)^κ`), incompatible with π's Gauss–Kuzmin
statistics — the genuinely hard, still-open core (and conditional on π GK-normal, also open).
See `research-notes/G173` + `G170`.

### 2. ζ(3) Apéry divergence depth — DEFERRED TO ANOTHER BRANCH (user)
The depth tower `e=3 → π=6 → ζ(3)=?` via the Apéry recurrence
`n³aₙ=(34n³−51n²+27n−5)aₙ₋₁−(n−1)³aₙ₋₂`.  Would precise the "constant+depth" of G171's
3-axis row.  **Do NOT build here.**

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
- New direction entirely.  (ζ(3) is on another branch.)

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
  lean/E213/Lib/Math/Cauchy/NonHolonomicWitness.lean                       ← (n!)ⁿ genuinely non-holonomic, Klazar envelope (22 PURE) [this session]
  lean/E213/Lib/Math/Cauchy/PositiveFloorUnbounded.lean                    ← positive top diff ⟹ unbounded (13 PURE) [this session]
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
