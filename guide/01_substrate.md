# 01 — Substrate: From Raw to ℂ-like Structure

**Tier:** T0/T3 hybrid
**Status:** T0 part closed (Raw type, swap, atomicity);
T3 part (Frobenius/π₁ external derivation) remains classical-only.
**Lean:** `Firmware/Raw.lean`, `Firmware/RawSwap.lean`, `Meta/R4Codomain`.

## Best current statement

A universe with non-trivial structure requires relations between
distinguishable things. The substrate question is: **what is the
minimal algebra in which such relations can take values?**

Two derivations exist; both reach `ℂ⁵ = ℂ² ⊕ ℂ³`:

### T3 path (classical, paper2 / drlt-book ch01)

Four necessary conditions on the relation algebra 𝕂:

- R1 magnitude (geometry) → 𝕂 normed
- R2 phase (gauge forces) → unit-norm forms connected Lie group
- R3 determinant (gravity) → 𝕂 commutative
- R4 winding (charge quantization) → π₁(phase group) ≅ ℤ

By Frobenius, candidates are {ℝ, ℂ, ℍ}. ℝ fails R2 (discrete phase
group), ℍ fails R3 (non-commutative). Only ℂ survives.

### T0 path (213-internal, partial)

Raw + swap automorphism + atomicity yields:

- d = 5 as **theorem** (`Firmware/Atomicity/Five.lean`): unique 2a+3b decomposition
  with both odd, irreducible by Bézout shifts.
- (NT, NS, d) = (2, 3, 5) = (F₃, F₄, F₅): consecutive Fibonacci
  (`Physics/Foundations/FibonacciAtomic.lean`, Phase 1 Discovery 1).
- R1–R4 codomain typeclass hierarchy (`Meta/R4Codomain.lean`) +
  `#verify_r4` command — checks any candidate codomain at compile time.

The T0 path does not yet derive ℂ from Raw alone. It produces a
**5-dimensional atomic substrate** with the right combinatorial
properties; mapping that substrate onto ℂ⁵ is currently inherited from
the T3 path, not re-derived in 213.

## 213 sharpening

- d = 5 is no longer an empirical input; it is a theorem.
- The four R1–R4 conditions are no longer informal philosophy; they are
  a Lean typeclass hierarchy with mechanical instance checking.
- XOR fails R4 — formally proven (`Meta/LensCatalog.lean`). This is the
  first concrete falsifier of an alternative substrate candidate.

## Open / next

- **T3 → T0 migration of ℂ uniqueness.** Currently the proof that
  d=5 substrate must carry ℂ-like phase structure leans on Frobenius.
  213-internal counterpart unknown.
- **Why exactly four conditions?** R1–R4 feel canonical but lack a
  meta-proof of jointly-minimal (analog of `AxiomMinimality.lean`).
- Tighten Fibonacci discovery — currently F₃..F₁₀ appearance is
  catalogued, not yet derived from a single underlying generator.

## Sources

- `papers/paper1_chiral_decomposition.tex` — ℂ⁵ = ℂ²⊕ℂ³ uniqueness.
- `papers/paper2_frobenius_to_gauge.tex` — full T3 substrate argument.
- `papers/drlt-book/chapters/ch01_whyC.tex` — narrative version.
- `lean/E213/Theory/Atomicity/Five.lean` — d=5 theorem.
- `lean/E213/Meta/R4Codomain.lean` — R1–R4 typeclass.
