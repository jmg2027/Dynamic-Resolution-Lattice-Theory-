# Session Handoff — 2026-06-02 (G171 Apéry-zeta depth + the ∅-axiom `ring` infra)

## Branch
`claude/goal-g171-marathon-research-Dj9Go` — pushed, **fast-forward merged to `main`**
(`main` = branch HEAD).  Full `lake build` clean (1500+ modules).  Every theorem below is
∅-axiom (`tools/scan_axioms.py` → `N pure / 0 dirty`).  Concurrent sessions
(`newton-gregory-generalization`, `concrete-non-fixed-point-witness`) also merged to `main`;
their work is summarised under "Adjacent work on main".

---

## What Was Done This Session

The arc began as a G171 marathon (the divergence-depth tower for ζ(2)/ζ(3)) and turned into
building a reusable **∅-axiom `ring` infrastructure** for ℕ and ℤ, then using it.

### 1. The divergence-depth / Apéry-zeta math (`Lib/Math/Cauchy/`)
- **`DepthAperyCubic` (23 PURE)** — the Apéry zeta coefficient-degree statistic: ζ(2)
  recurrence coefficients (`(n+1)²`, `11n²+11n+3`, `n²`) are `polyDepth 2`; ζ(3) (`n³`,
  `34n³−51n²+27n−5`, `(n−1)³`, reindexed `n=m+2` to clear ℕ truncation) are `polyDepth 3`;
  depths pinned **exactly** (`aperyTop_depth_exact`, `zeta2Top_depth_exact`).
  **Honest correction (red-team agent):** coefficient degree is *incidental to irrationality*
  (ζ(4) order-2 doesn't prove it; Catalan β(2) order-2 OPEN; ζ(5) order-3) — the e→ζ(2)→ζ(3)
  degree run does NOT continue; ζ(3) deg-3 is the exception above the order-2 sporadic family.
- **`DepthQuadraticGeneric` (7 PURE)** — `quadratic_polyDepth : ∀ A B C, polyDepth 2
  (A·n²+B·n+C)` (whole order-2 sporadic family) via Newton-form transfer + `polyDepth_congr`.
  `quad_eq` now closes with `by ring_nat` (the old hand `add4_reorder` deleted).
- **`DepthCubicGeneric` (5 PURE)** — `cubic_polyDepth : ∀ A B C D, polyDepth 3 (A·n³+…)`,
  crux `cube_eq` (`n³ = 6·C(n,3)+6·C(n,2)+n`); all multivariate reorders via `by ring_nat`.
- **`CasoratianStep` (5 PURE)** — subtraction-free discrete-Wronskian law `c₂Cₙ=−c₀Cₙ₋₁`
  (`casoratian_step`; middle coeff cancels) + `telescope` (`(∏P)g(n)=(∏Q)g(0)`).
- **`CasoratianSigned` (17 PURE)** — the signed Casoratian over **ℕ-pairs** (`NatPairToInt`:
  ℤ = ℕ-pair, sign = axis swap).  `casoratian_signed` (= `casoratian_step` repackaged),
  `telescope_pair` (ζ(3) constant `+6/n³`), `telescope_pair_alt` (ζ(2) alternating `±5/n²`,
  `iterNeg n` = `(−1)ⁿ`), `cube_casoratian_telescope`.  **The "needs ℤ" caveat dissolved
  213-natively** — sign is the residue's binary axis-distinguishing.
- **`CassiniSigned` (2 PURE)** — the residue floor's Cassini cross-determinant
  `fib(n+2)fib(n)−fib(n+1)²=(−1)ⁿ⁺¹` as the **depth-0** signed Casoratian (`cassini_pair`):
  magnitude 1 (det-P/φ floor) + sign Oscillate.
- **`DepthResidueFloor` (2 PURE)** — `self_pointing_depth_ladder`: depth read in 213 as
  drift from the `P`/φ Cassini floor — e:1 → ζ(2):2 → ζ(3):3.
- **`DepthSelfReference` (3 PURE)** — `diff` realises the Converge/Escape outcomes of
  `Lens.SelfReferenceThreeOutcomes` (`W` settles at unit `1=det P=NS−NT`; `2ᵏ` never closes).
- **`PolynomialDepth` (13 PURE)** — ★ the general **degree = depth** theorem:
  `polyDepthZ_polySeq : ∀ a d, polyDepthZ d (polySeq a d)` (`polySeq a d n = Σ_{i≤d} aᵢ·nⁱ`,
  any ℤ coeffs), via the finite-depth **ring** (`idZ` depth 1, `powSeq i` depth i by
  `polyDepthZ_mul`, `polyDepthZ_mono`+`polyDepthZ_add`) — no Stirling.  `aperyLeadZ_depth`:
  the ζ(3) coeff `34n³−51n²+27n−5` (negative coeffs) has depth 3 over ℤ with **no reindex**
  (vs the ℕ version's `n=m+2`); `aperyLeadZ_value` = 117 at n=2.

### 2. The ∅-axiom `ring` infrastructure (the durable reusable win — `Meta/`)
The user's "build infra, not Lean core" push.  Lean-core `ring`/`omega`/`ac_rfl` pull
`propext`/`Quot.sound`; these are ∅-axiom replacements.
- **`Meta/Nat/PolyNatM` (22 PURE)** — multivariate **ℕ** polynomial reflection prover
  `poly_idM` (flat monomial-map normal form; the `k`-variable generalization of `PolyNat`
  (1-var) / `PolyInt2` (2-var ℤ)).  All `Nat.beq`-based (`eq_of_beq`/`==` pull propext).
- **`Meta/Nat/PolyNatMTactic`** — **`ring_nat`** elab tactic (auto-reify a `Nat` `=` goal,
  discharge via `poly_idM`; `consumeMData` for `show`-wrapped goals).
- **`Meta/Int213/PolyIntM` (26 PURE)** — multivariate **ℤ** prover `poly_idMZ`.  Adds
  Int coeffs + `neg` + **zero-coefficient drop** (`insertAddZ`/`isZeroZ`) so signed
  cancellation (`(a−b)(a+b)=a²−b²`) normalises.  Powers via repeated-mult `powInt` (no core
  Int `^`); Int ring corners PURE (Int213 kit + local `one_mulZ`/`mul_zeroZ`/`neg_zeroZ`).
- **`Meta/Int213/PolyIntMTactic`** — **`ring_intZ`** elab tactic (auto-reify; `Sub`→add+neg,
  `Neg`→`PE.neg`).

> **Infra stack now: `PolyNat`(1,ℕ) · `PolyInt2`(2,ℤ) · `PolyNatM`(k,ℕ)+`ring_nat` ·
> `PolyIntM`(k,ℤ)+`ring_intZ`** — a ∅-axiom `ring` for both ℕ and ℤ, multivariate.

### 3. Research notes (Tier-1, `research-notes/`)
`G171_apery_zeta_tower.md` (standard-math + falsifiers + conjectures C-A done),
`G171_self_pointing_depth_213.md` (213-native: depth = self-pointing distance from floor),
`G171_casoratian_pair_213.md` (213-native: ℤ=ℕ-pair, sign=axis, magnitude/sign = two
SelfReferenceThreeOutcomes readings).

### Adjacent work on `main` (concurrent sessions — do not re-derive)
- `Cauchy/NewtonGregory` (41 PURE): `newton_gregory`, `reconstruct` (`polyDepthZ d s ⟹ s =
  Σ(Δⁱs0)binom(·,i)`), `poly_bound`.  `Cauchy/FiniteDepthAlgebra`: `polyDepthZ_{add,smul,mul}`
  (finite-depth **ring**) — `PolynomialDepth` builds on this.  `Cauchy/QuasiPolyBound`,
  `Cauchy/BinomialTransform`.
- `Theory/Raw/{CoResidue (94 PURE), StateMachine (20 PURE), MuNuMirror}`, `Lib/Math/ResidueForm`
  — µF=Raw / νF=SlashNu self-pointing functor, FSM Lens.

## Current Precision Results (0 free parameters)
**No physics constants changed this session** (pure math: finite-difference calculus /
divergence depth / multivariate-identity tactics).  Precision table unchanged — see
`catalogs/physics-constants.md` (1/α_em, m_μ/m_e 0.48 ppb, R∞ 4.3 ppb, Ω_Λ, …) and
`catalogs/falsifiers.md`.  **DRLT Validation Standard status unchanged** — see Open #1.

## Open Problems (Priority Order)

### 1. DRLT Validation Standard — the repo's stated "real target" (untouched this session)
`CLAUDE.md`: from `(NS,NT,d)=(3,2,5)`, 0 free parameters, deliver a **strict ∅-axiom
precision theorem AND falsifier for the same observable**.  This session was pure-math infra;
it did not advance the physics validation.  Next concrete step: audit which catalog results
(`1/α_em` via `AlphaEM/GramStructuralCapstone`, `m_μ/m_e = NS·137/NT`, `N_gen=C(NS,NT)=3`,
`θ_QCD`, Cabibbo `λ=5/22`) are strict ∅-axiom in Lean vs still Python/numerical.

### 2. `ring_intZ` retrofit / reach (low-risk consolidation)
Apply `ring_intZ`/`ring_nat` to remaining hand-written multivariate identities **in
owned files** (e.g. `DepthAperyCubic` `poly_id` chains).  Do NOT touch concurrent-session
files (`FiniteDepthAlgebra`, `NewtonGregory`, `PolyInt2`, `CoResidue`, `StateMachine`) —
merge-conflict risk while they are active.

### 3. π non-holonomicity (classically OPEN) — `research-notes/G170`
`(aᵢ)` of π not P-recursive.  NOT closable ∅-axiom.  FGS asymptotic-obstruction is the
credible route.  Provable neighbours closed (`HurwitzianCF`).

### 4. ζ(4)/ζ(5)/Catalan boundary (a falsifier exhibit, not a tower rung)
The degree=depth coincidence stops at ζ(3); encoding ζ(4)'s order-2 recurrence as a
*boundary marker* (it does NOT prove irrationality) would document this in-repo.

## Unresolved from This Session (don't repeat)
- **Generic cubic over ℕ by hand** is a 7-term multivariate AC grind with combines
  (`3n+3n=6n`); `ac_rfl` is propext-dirty.  RESOLVED by building `PolyNatM`/`ring_nat` —
  use the tactic, do not hand-grind.
- **propext landmines (Int + ℕ):** `Int.add_comm`, `Int.add_sub_cancel`, `eq_of_beq`, `==`,
  `Nat.mul_assoc`, `Nat.add_mul` all leak `propext`.  PURE replacements: `Int213.{add_comm,
  add_assoc,mul_*,add_neg_cancel,zero_add,sub_add_cancel_int}`, `NatHelper.{add_mul,mul_assoc,
  add_right_comm}`, `Nat.beq`+structural induction (`nat_eq_of_beq`).
- **`monoEval []`/`zipAdd []` reductions** need an explicit `show` (WF-vs-structural); a
  `show <reduced> = _` before `rw` unblocks; goals wrapped by `show` carry `Expr.mdata`
  (use `consumeMData` in tactics before `ty.eq?`).

## Next
Either (a) **pivot to the DRLT Validation Standard** (Open #1 — the repo's real target; audit
α_em / m_μ-m_e / falsifiers for strict ∅-axiom status), or (b) continue the
infra/depth thread (retrofit Open #2, or a `polyDepthZ` ↔ "is a polynomial" characterization
combining `PolynomialDepth` + `NewtonGregory.reconstruct`).  Recommend (a) — the math infra is
mature; the physics validation is where the stated standard lives.

## Three-tier state
- **Promotions this session**: none (all new Lean is Tier-2 source; the depth/Casoratian
  sub-trees are PURE-closed and are **promotion candidates** for `theory/math/analysis/`).
- **Promotion candidates**: `Cauchy/{DepthAperyCubic, PolynomialDepth, CasoratianSigned}` +
  the `Meta` `ring` infra — eligible for a `theory/math/analysis/divergence_depth.md` chapter
  per `theory/PROMOTION_CRITERIA.md`.
- **Active scratchpad**: `research-notes/G171_*` (this thread), `G170` (π), `G178` (νF, other
  session).

## File Map
```
NEW Lean infra (∅-axiom):
  lean/E213/Meta/Nat/PolyNatM.lean            ← k-var ℕ poly reflection prover (poly_idM)
  lean/E213/Meta/Nat/PolyNatMTactic.lean      ← ring_nat tactic
  lean/E213/Meta/Int213/PolyIntM.lean         ← k-var ℤ prover (poly_idMZ), zero-drop
  lean/E213/Meta/Int213/PolyIntMTactic.lean   ← ring_intZ tactic
NEW Lean math (∅-axiom):
  lean/E213/Lib/Math/Cauchy/DepthAperyCubic.lean       ← ζ(2):2, ζ(3):3 coeff degrees, exact
  lean/E213/Lib/Math/Cauchy/DepthQuadraticGeneric.lean ← ∀ quadratic depth 2 (ring_nat)
  lean/E213/Lib/Math/Cauchy/DepthCubicGeneric.lean     ← ∀ cubic depth 3 (ring_nat)
  lean/E213/Lib/Math/Cauchy/CasoratianStep.lean        ← discrete-Wronskian law + telescope
  lean/E213/Lib/Math/Cauchy/CasoratianSigned.lean      ← signed Casoratian as ℕ-pair
  lean/E213/Lib/Math/Cauchy/CassiniSigned.lean         ← residue floor = depth-0 signed Casoratian
  lean/E213/Lib/Math/Cauchy/DepthResidueFloor.lean     ← self-pointing depth ladder
  lean/E213/Lib/Math/Cauchy/DepthSelfReference.lean    ← diff = Converge/Escape
  lean/E213/Lib/Math/Cauchy/PolynomialDepth.lean       ← ★ general degree=depth + Apéry-ℤ
NEW research notes:
  research-notes/G171_apery_zeta_tower.md
  research-notes/G171_self_pointing_depth_213.md
  research-notes/G171_casoratian_pair_213.md
MODIFIED:
  STRICT_ZERO_AXIOM.md  ← entries for all the above
```
