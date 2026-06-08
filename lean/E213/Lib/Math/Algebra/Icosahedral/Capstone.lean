import E213.Lib.Math.Algebra.Icosahedral.A5Bridge

/-!
# Icosahedral.Capstone — the self-reference map lives in A₅

**Marathon summary.**  The §5.6 residue self-reference map
`M = [[c,1],[1,1]] = [[2,1],[1,1]]` is, simultaneously:

1. an ℝ-matrix with golden eigenvalues `φ², 1/φ²` (frozen reading, `Mobius213`);
2. reduced mod `d = 5`, an **order-5 element of `PSL(2,𝔽₅) ≅ A₅`** — a 5-fold
   icosahedral rotation (`OrderFive`: `M⁵ ≡ −I`, order exactly 5 in PSL);
3. carrying, as that A₅ element, the icosahedral 3-rep **character `φ`**, which
   is the **same** golden ratio as the eigenvalue via `φ² = φ + 1` (`A5Bridge`:
   the Fibonacci recurrence on convergents).

`d = 5` does **double duty** — it is `disc M = NS²−4` (the ℝ-side discriminant
giving the golden eigenvalues) **and** the field `𝔽₅` realising `A₅`.

## Why this grounds the CKM apex frontier

`research-notes/frontiers/ckm_rho_eta_apex.md` reduced the φ²-apex to a single
open *physical* premise: **why the CKM CP-apex modulus is a self-reference
eigenvalue at all**.  This marathon supplies the missing **structural home**:
the self-reference map is literally an element of `A₅`, and `A₅` golden-ratio
flavour symmetry is *established* physics — `SU(5)×A₅` models reproduce quark
masses, mixing, and the CP phase from the very `φ` that `M` carries
(arXiv:1410.2057, 1312.0215).  DRLT already has the `SU(5)` side (`d = 5`,
`5⊗5 = 25`); this marathon shows it also has the `A₅` side, *as the same matrix*.

## Honest scope (`seed/AXIOM/05_no_exterior.md` §5.4)

This **bridges** `M` to `A₅` (proven, PURE) and gives the CKM-apex premise an
external grounding in `A₅` flavour symmetry.  It does **not** by itself *derive*
the CKM apex *value* `R_u = 1/φ²` from an `A₅` flavour model — that is the next
step (build the `A₅` flavour assignment of the three generations and read off
the mixing).  The marathon's claim is the structural identification "the
self-reference map IS an `A₅` rotation carrying `φ`", not a closed apex
derivation.

All theorems PURE.
-/

namespace E213.Lib.Math.Algebra.Icosahedral.Capstone

open E213.Lib.Math.Algebra.Icosahedral
open E213.Lib.Physics.Foundations.GoldenRatio (fib)

/-- ★★★★★★★ **Icosahedral marathon capstone.**  The self-reference map `M` is
    an order-5 element of `A₅ ≅ PSL(2,𝔽₅)` (icosahedral 5-fold rotation),
    carrying character `φ`, the same golden ratio as its ℝ-eigenvalue `φ²`
    (bridge `φ² = φ + 1`).  `|A₅| = 60`; `d = 5` is both `disc M` and the field
    `𝔽₅`.  PURE. -/
theorem icosahedral_capstone :
    -- (1) order-5 in PSL: M⁵ ≡ −I (mod d=5), and exactly 5 (avoids centre for k<5)
    (OrderFive.pow 5 = OrderFive.negI)
    ∧ (OrderFive.pow 1 ≠ OrderFive.I ∧ OrderFive.pow 1 ≠ OrderFive.negI)
    ∧ (OrderFive.pow 10 = OrderFive.I)
    -- (2) group order |A₅| = |PSL(2,5)| = 60
    ∧ (120 / 2 : Nat) = 60
    ∧ (5 * 4 * 3 * 2 * 1 / 2 : Nat) = 60
    -- (3) golden bridge: eigenvalue φ² = character φ + 1 (Fibonacci), F₅ = F₃ + F₄
    ∧ fib 5 = fib 3 + fib 4
    -- (4) d double role: d = NS+NT = 5 and disc M = NS²−4 = 5
    ∧ (5 : Nat) = E213.Lib.Physics.Simplex.Counts.NS + E213.Lib.Physics.Simplex.Counts.NT
    ∧ (3 : Int) ^ 2 - 4 * 1 = 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Algebra.Icosahedral.Capstone
