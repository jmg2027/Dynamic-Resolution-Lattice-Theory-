# Session Handoff — 2026-06-04 (0=∞ / the two folds / modular group)

## Branch
`claude/non-holonomicity-rGhug` — fast-forwarded onto `origin/main` (concurrent determinant /
CFinite / OrbitDimension threads merged in).  Every new theorem ∅-axiom
(`python3 tools/scan_axioms.py <mod>` from repo root → `N pure / 0 dirty`).  Build clean:
`cd lean && lake build E213.Lib.Math E213.Lens.Number`.

## Headline this leg: 0 = ∞ is one residue; the two folds generate PSL(2,ℤ)

A `det = 0` / "is `0` a value?" intuition opened into a full thread, now closed end to end and
promoted.  Spine: `0` and `∞` are **one pre-Lens residue** (not a dual pair); a fold may handle the
pair only status-symmetrically; the two founding folds (negation, reciprocal) are mirror involutions
whose product is the founding elliptic swap, and the elliptic generators give `PSL(2,ℤ) = ℤ₂ * ℤ₃`.

- **`Cauchy/ZeroInfinityHole` (5 PURE)** — `0` = the single reciprocal hole (`zero_no_reciprocal`);
  reciprocal-fixed core = the units (`self_reciprocal_iff_unit`, via `Int213.int_sq_le_one`);
  `det = 0` collapses the Casoratian (`cas_zero_collapses`).
- **`MaxEntropy` (8 PURE)** — structurelessness as a *positive* property `¬∃d, polyDepthZ d s`
  (incompressibility, measure-free); a max-entropy sequence forces the Newton generator
  non-surjective (`maxEntropy_not_surjective`); witnesses `thueMorse_maxEntropy`,
  `golden_cassini_maxEntropy`.
- **`DetSpectrumPoles` (1 PURE)** — `det_spectrum_poles_and_center`: `q=0` multiplicative hole,
  `q=−1` additive ceiling (MaxEntropy), `q=+1` doubly-finite centre.
- **`Lens/Number/IntFoldForms` (13 PURE)** — ℤ's two status-symmetric closures of negation:
  one-point `ℤ̂` (`0,∞` both fixed) and two-point `ℤ̄` (`0` fixed, `±∞` swapped); plain ℤ torsioned.
- **`Lens/Number/FoldDuality` (13 PURE)** — on `Q4 = {∞,0,±1}`, negation **fixes** `{0,∞}`/swaps
  `{±1}`; reciprocal the mirror (`two_folds_dual_on_pairs`).
- **`Lens/Number/FoldKlein` (9 PURE)** — the two folds generate `ℤ/2 × ℤ/2`; antipode
  `bothSwap = negQ∘recQ` is fixed-point-free; `klein_fixed_orbit_profile`.
- **`Real213/FoldReflections` (11 PURE)** — matrix witness: `N`(neg), `R`(recip) are reflections
  (`det −1`), `N·R = S` the founding swap (`det +1`), `S² = −I` (order 4 → proj 2).
- **`Real213/EllipticCycleFixtures` (7 PURE)** — `U` (proj order 3) as a 3-cycle `∞↦0↦−1↦∞`; with
  `S` gives `PSL(2,ℤ) = ℤ₂ * ℤ₃` (`elliptic_generators_are_two_and_three`).

## Canon + promotion
- **`seed/AXIOM/06_lens_readings.md` §6.9** — new: "0 and ∞ are pre-Lens, status-symmetric, never a
  single-stratum value" (refines §6.5/§6.6).  Failure-mode row added to CLAUDE.md
  ("0/∞ as a stratum-value (mixed-status fold)").
- **`theory/lens/zero_infinity_and_two_folds.md`** — promoted synthesis chapter mirroring the whole
  thread (registered in `theory/lens/INDEX.md`).

## Earlier this session (also on main)
Non-holonomicity / det-spectrum: `Meta/Int213/Order`, `Cauchy/{PolyDepthMonotone, ThueMorseRingEscape,
DepthMonotoneSynthesis, CFiniteHomogRec, EllipticPeriodicTier, DetZeroCollapse, WronskianDepth,
GoldenPiFaces, HomogRecPeriodic}`, `CeilingSchema`, `Lens/Number/FoundingDynamicBridge`.

## Open frontier / next candidates
- **hyperbolic side** — is the golden iterator `G` (det 1, disc 5) a product of two reflections
  (a boost), paralleling the elliptic `S = N·R`?  φ as the hyperbolic fold.
- **ℚ̂ reciprocal fold, full** — extend `Q4` to projective rationals via `NatPairToQPos` + `{0,∞}`.
- **π** — the elliptic irrational-rotation pole; CF non-holonomicity the standing open boundary
  (`theory/math/analysis/phi_pi_poles.md`).

## Marathon mode
Close one thread, open the next.  Commit after every increment; never amend; push to
`claude/non-holonomicity-rGhug` and fast-forward `main` (permission granted).
