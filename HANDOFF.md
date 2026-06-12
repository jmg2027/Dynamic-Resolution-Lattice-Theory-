# Session Handoff — 2026-06-12 (ζ(3): nucleus CLOSED + denominator bridged; numerator opened)

## Branch
`claude/zeta3-apery-integrality-y9jy1x` — main merged in (clean), pushed,
**ready to merge to main** (full `/ready-to-merge` audit passed; verdict below).
The ζ(3) `HolonomicReal` route: discharge the two classical inputs of
`Zeta3Cut.zeta3_reduced_conditional` (I1 integrality, I2 lcm race).

## What Was Done This Session

### ★★★ THE NUCLEUS — CLOSED: Apéry's recurrence, ∅-axiom (`AperyRecurrence.lean`, 45 PURE)
`apery_recurrence` — **`(j+2)³B(j+2)+(j+1)³B(j)=aperyLead(j)·B(j+1)`** for
`B(n)=Σ_k C(n,k)²C(n+k,k)²`.  The WZ / creative-telescoping identity — the thing the
whole program reduces to — is a 0-axiom theorem.  **No clean certificate was
available a priori**: the certificate `Ĝ(j,k)=−4k⁴(2j+3)(4j²+12j−2k²+3k+8)C(j+2,k)²
C(j+k,k)²` was *found* by exact bivariate interpolation, verified, then re-derived
bottom-up: `reduced_wz_identity` (polynomial core, subtraction-free in `j=k+d`),
`colrec`/`lowrec` + `R0/R1/R2/G1` (`W`-factoring), `redid_eq`, `per_k`,
`sumTo_shift_eq` (telescope), sum→cancel `(j+1)²(j+2)²`.  All-`ℕ` (no `Int`; `Q>0`
in range keeps `ring_nat` additive).

### Denominator bridge (`Zeta3Apery.lean`, 4 PURE)
`zeta3Den_eq` — **`zeta3Den n = (n!)³·B(n)`** (2-step induction; orbit
`aperyOrbit_exact` ↔ `P_recurrence` for `(n!)³B`, seeds `1,5`).  Identifies the
recurrence-orbit denominator with the explicit binomial sums.

### Numerator marathon opened (`Zeta3Numerator.lean`, 3 PURE)
`harmonic_part_recurrence` — the cleared `H₃` part of the numerator recurrence,
from `apery_recurrence` + harmonic telescoping (`HL_step`).  Verified structure:
`A(n)=H₃(n)B(n)+K(n)`, `A` satisfies the same recurrence iff the kernel `K`
satisfies an inhomogeneous one; Abel single-sum form `K=Σ_m δ(n,m)Btail(n,m)`.
**KEY NEGATIVE FINDING**: the numerator has **no clean WZ certificate** (`cert_A`,
`cert_K`, `cert_A−cert_B·c` all messy) — the explicit Apéry kernel telescoping is
mandatory.

### Marathon (merge + skills)
Merged main (53 commits: weld/Bessel, slot-tower, vp essays).  `/process` (sink
clean, frontier INDEX updated).  **Promotion**: the closed ζ(3) Apéry arithmetic
(140 PURE) → `theory/math/numbertheory/apery_zeta3_arithmetic.md` + STRICT_ZERO_AXIOM
catalog + log row 75.  Cross-domain note (Apéry Casoratian = weld's "forced by
two"; lcm race = `vp`-log bound; certificate dichotomy = hypergeometric/harmonic
boundary).  `/essay`: `the_certificate_boundary` (essay 96).  `/org-audit`,
`/purity-check` (0 forbidden), `/ready-to-merge` (READY).

## Open Problems (Priority Order)

### 1. Numerator integrality `(n!)³ ∣ 2·lcm³·zeta3Num n` — the remaining half
The numerator `A=H₃B+K` is harmonic; `2lcm³A∈ℤ` and `zeta3Num=(n!)³A`, but **no
clean certificate** (research-grade, no CAS shortcut).  Needs: (a) the kernel
inhomogeneous recurrence via **explicit Apéry kernel telescoping** (Abel form
`K=Σ_m δ·Btail`; `δ`/`Btail` cross-`n` structure) ⟹ `A`-recurrence ⟹
`zeta3Num=(n!)³A`; (b) the §4 ℚ-free integrality assembly (`heart_lcm` kernel +
`cube_dvd_lcm_cube` harmonic + pos/neg split).  `H₃` part already cleared
(`harmonic_part_recurrence`).  Then piecewise `(c,p,q)` (`c n=(n!)³/(2lcm³)`,
`q n=2lcm³B(n)` from `zeta3Den_eq`+`two_lcmCube_dvd_factCube`) + `htel`
(`lcmUpTo_le` vs `zeta3Den_geom`, 28>27) ⟹ `zeta3HolonomicReal` unconditional.
Frontier: `research-notes/frontiers/zeta3_wz/numerator_plan.md` (+ `zeta3_blueprint`,
`zeta3_free_modulus`); registered in `frontiers/INDEX.md`.

### 2. vp namespace dedup (informational)
`Meta/Nat/VpMul.vp_pow` (`IsPrime213`) vs `PrimeValuation.vp_mul` /
`FactorialLcmDvd.vp_pow3` (`Prime213`) — two prime predicates; a dedicated
consolidation.  Recorded in `research-notes/frontiers/zeta3_crossdomain.md`.

## Unresolved from This Session
The numerator WZ certificate hunt was a **confirmed dead end** (no clean
certificate exists — verified three ways via `numcert2.py`).  The next session
should NOT re-attempt certificate fitting; the explicit kernel-telescoping route is
the only path.

## Next
Open the kernel inhomogeneous recurrence: formalize the Abel single-sum
`K=Σ_m δ(n,m)·Btail(n,m)` and its cross-`n` telescoping (the explicit Apéry / van
der Poorten kernel identity).  Target file: `lean/E213/Lib/Math/NumberTheory/
Zeta3Numerator.lean` (extend).

## Three-tier state
- **Promotions this session**: `theory/math/numbertheory/apery_zeta3_arithmetic.md`
  ← the closed ζ(3) Apéry arithmetic (140 PURE).
- **Promotion candidates**: none outstanding (the closed sub-tree is promoted; the
  numerator is open and stays in `frontiers/`).
- **Active scratchpad**: `research-notes/frontiers/zeta3_wz/` (numerator marathon).

## File Map
```
lean/E213/Lib/Math/NumberTheory/AperyRecurrence.lean   ← nucleus: apery_recurrence (45 PURE)
lean/E213/Lib/Math/NumberSystems/Real213/Zeta3Apery.lean ← zeta3Den_eq bridge (4 PURE)
lean/E213/Lib/Math/NumberTheory/Zeta3Numerator.lean    ← numerator H₃ part (3 PURE)
lean/E213/Lib/Math/NumberTheory/AperyIntegrality.lean  ← Brick 2: KeyDiv, Heart (31 PURE)
lean/E213/Lib/Math/NumberTheory/FactorialLcmDvd.lean   ← 2lcm³∣(n!)³ (11 PURE)
theory/math/numbertheory/apery_zeta3_arithmetic.md     ← promotion chapter (new)
theory/essays/analysis/the_certificate_boundary.md     ← essay (new)
research-notes/frontiers/zeta3_wz/                      ← numerator frontier + verify scripts
research-notes/frontiers/zeta3_crossdomain.md          ← cross-domain note (new)
```
