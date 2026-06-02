# Session Handoff — 2026-06-02 (Newton–Gregory generalization marathon)

## Branch
`claude/newton-gregory-generalization-F6gYv` — pushed.  Working tree clean.
Full `lake build` clean (1500+ modules).  All new theorems ∅-axiom
(`tools/scan_axioms.py E213.Lib.Math.Cauchy.NewtonGregory` → **41 pure / 0 dirty**).

## What Was Done This Session

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
3. **C3 (next, combinatorial part ∅-axiom)** the e/π depth separation as a structural
   invariant (e depth 1, π Wallis-coeff depth 2 — provable they differ).  Do NOT slide
   to "explains the e–π separation" (metaphysical).  Transcendence part classically open.
4. **C4 (∅-axiom-statable)** boundary marker: finite-depth (Newton-reconstructible)
   sector vs periodic (Markov/quadratic) sector are disjoint.  Eigenspace structure (C5
   frontier): dimension/basis of `{s : T s = s}` over ℤ.
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
  lean/E213/Lib/Math/Cauchy/FiniteDepthAlgebra.lean ← C2: finite-depth ring
                                                    (polyDepthZ_mul, Leibniz), 22 PURE
  lean/E213/Lib/Math/Cauchy/BinomialTransform.lean ← C5: involution T∘T=id +
                                                    fixed-point richness, 6 PURE
NEW theory chapter:
  theory/math/analysis/newton_gregory.md
NEW research note:
  research-notes/G173_newton_gregory_generalization.md
MODIFIED:
  lean/E213/Lib/Math/Cauchy.lean                 ← umbrella import
  theory/math/INDEX.md                           ← 12 analysis sub-clusters
  theory/math/analysis/cf_holonomicity_hierarchy.md ← bridge unblocked
```
