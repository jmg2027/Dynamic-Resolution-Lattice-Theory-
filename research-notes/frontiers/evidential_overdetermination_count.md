# The honest evidential count — how many independent measured numbers does (3,2,5) pin with 0 dials?

**Status: research finding (the K-count is genuinely debatable; recorded with
both bounds).**  The program's pattern finding ("the math is forced, the physics
dictionary is a reading") raises the evidential question: with **0 free
parameters**, how many *genuinely independent* measured numbers does the forced
atom set `(NS,NT,d)=(3,2,5)` reproduce?  A two-agent audit (auditor + anti-
inflation skeptic) gave a range, reconciled below.

## The deflation (what does NOT count)

- **Re-readings of a handful of forced integers.**  The repo's own catalogs say
  it: `correspondences.md:7-71` lists **6, 8, 12, 24** each read ~6–12 ways
  (Pauli/Lorentz/3!/SU(3)-roots/… = one `6 = NS·NT`; α₃/adjoint/b₁/Einstein-8π/
  Hawking/… = one `8 = NS²−1`).  `FalsifierRosterForced.falsifier_roster_forced`
  binds nine "falsifiers" to ONE polynomial-in-(3,2,5) theorem.  The headline
  "23 observables / 26 falsifiers" is an inventory of *readings*, not of
  independent content.
- **Algebraically-derived results.**  `sin²θ_W = α_em/α_2` (`WeinbergAngle.lean:6`),
  `m_t/m_c = 137` (= 1/α_em), `m_μ/m_e ∝ 1/α_em` (`MuOverE.lean:7,28`) — zero new
  information beyond the couplings they are built from.
- **π-fed precision.**  The ppb digits ride on a **literal π input**:
  `GradedFormula.lean:34` ("π enters as a literal"), `GradedFormulaPrecision.lean:172,204`
  ("a higher-precision π input would absorb" the residual); `Basel/Bound.lean:51`
  disclaims the ζ(2) bracket as "not a Lean theorem".  So `1/α_em = 137.036` to
  ppb is **not** a 0-input match — only its integer skeleton `60ζ(2)+30+25/3` is
  0-input combinatorics.  `README.md:59` agrees: "the residual is in the assembly."
- **Absolute scales.**  `m_p`, `m_H`, `R∞` = ratio × a measured CODATA scale
  (`physics-constants.md:11-13`).

## The honest core (what DOES count, 0-input, independent)

| K# | Measured number | Forced expression | Why it counts |
|---|---|---|---|
| K1 | `N_gen = 3` (fermion families) | `C(NS,NT) = 3`, forbids 4th (`C(3,4)=0`) | integer counting, 0-input, falsifiable |
| K2 | 8 gluons / SU(3) color | `NS²−1 = 8` (now `coker ι*`, `OctetCokernel`) | gauge color structure, 0-input |
| K3 | Koide `Q = 2/3` | `NT/NS` | a non-trivial measured dimensionless real, bare atom ratio, no π/scale — the strongest single item |
| K4? | gauge-rank pattern SU(3)×SU(2)×U(1), `d²−1=24` | `NS, NT, d` ranks | structural, but overlaps K2 (same `{3,2,5}` as ranks) |
| K5? | `m_p/m_e` skeleton `6` | `NS·NT` (×π⁵, π fed) | skeleton 0-input; the π⁵ and ppm are fed/prose |
| K6? | Cabibbo `λ = 5/22` | `d/(d²−NS)` | a new atom combo; mixing sector |

**Honest range: K ≈ 3 (tight floor: N_gen, color-8, Koide) to K ≈ 7 (generous:
+ the three coupling skeletons, m_p/m_e skeleton, Cabibbo).**  Not 23.

## The genuine over-determination engine (the strongest evidence)

Beyond the raw count, the sharpest non-trivial piece is the **triple coupling**:
the *same* atoms `(3,2,5)` + the *same* α_GUT are forced to produce three
coupling structures that differ only by a **forced depth** `{1, 2, ∞}` (Basel
truncation), themselves derived from rank exhaustion (`NeffDerivation.
basel_formula_axiom_derived`, PURE, no observed-α on the RHS) and **load-bearing**
(wrong depth ⇒ wrong answer, `DOF_LEDGER:139`).  You cannot tune one coupling to
fix the other two — that is genuine over-determination at the integer-skeleton
level (the precision is π-fed; the *skeleton + depth structure* is 0-input).
Residual: the sector→force naming is posited (a 3-element reading).

## Drawable bottom line

> **Strip the re-readings and the fed-in π, and DRLT pins ~3–4 genuinely
> independent measured numbers — 3 generations, the 8-gluon SU(3) structure, the
> Koide ratio 2/3 — with zero dials, plus the genuine over-determination that one
> atom set must produce the three couplings' integer-skeletons at three forced
> depths.  A small honest K with truly 0 dials is remarkable; but it is K ≈ 3–7,
> not 23 — the catalog inflates the count ~3–7-fold via re-readings and π-fed
> precision.**

This is the honest evidential strength, in the framework's own falsifiability
spirit (`07_primacy`: breadth is the proof — but breadth counted as *independent*
content, not as re-readings).  The forced core is genuine and 0-dial; the
headline precision/observable count is inflated and should be stated as
skeleton-forced + π-fed-precision, not "23 observables to ppb."
