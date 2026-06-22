import E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2CayleyHamilton
import E213.Meta.Int213.Order
import E213.Meta.Int213.PolyIntMTactic

/-!
# `Mat2` spectrum — the trace and determinant are the two elementary symmetric functions

The `representation.md` notebook entry located a **`det`/`tr` split** as the live edge of the
character arrow: `det` is the multiplicative `×↦·` character (`det2_mul`: `det(MN)=det M·det N`),
while `tr` is the *additive `×↦+` twin* that is **not** a homomorphism (`tr(MN)≠tr M·tr N`) and so
"falls outside" the `det`-character machinery.  Phrased as an opposition — multiplicative character
vs orphaned additive readout — the split looks like a gap.

This file dissolves the split: **`tr` and `det` are the two elementary symmetric functions of the
spectrum**, the two halves of one object (the characteristic polynomial), not two unrelated readouts.
A `2×2` matrix has spectrum `{λ₁, λ₂}` (the roots of its characteristic polynomial); then

  * `tr M = λ₁ + λ₂ = e₁` — the elementary symmetric function of degree 1, the **additive** `×↦+`
    character of the spectrum;
  * `det M = λ₁ · λ₂ = e₂` — the elementary symmetric function of degree 2, the **multiplicative**
    `×↦·` character of the spectrum.

Both are characters *of the spectrum*; the "split" is just `e₁` vs `e₂`, the two sides of one Vieta
factorization `charPoly = (λ−λ₁)(λ−λ₂) = λ² − (λ₁+λ₂)λ + λ₁λ₂`.  The matrix itself realizes this
factorization through Cayley–Hamilton (`Mat2CayleyHamilton.cayley_hamilton`): `M² = tr·M − det·I` is
the matrix shadow of the scalar `λ² = tr·λ − det`, the *same* monic quadratic whose roots are the
spectrum.

## What is ∅-axiom here vs what stays open

The **symmetric-function identity** is pure: `(λ−μ)(λ−ν) = λ² − (μ+ν)λ + μν`, and under the
factorization hypothesis `charPoly M = (λ−μ)(λ−ν)` (∀λ) it forces `tr M = μ+ν` and `det M = μν` by
matching coefficients — a finite `ℤ` identity (`ring_intZ`), no roots-exist assumption.  The
discriminant link `traceDisc M = (μ−ν)²` follows the same way.

What is **not** available in `Int` (nor in any non-algebraically-closed ring) is the *existence* of
the spectrum: for an arbitrary `M` the roots `μ, ν` need not lie in `Int` (e.g. `G = [[2,1],[1,1]]`
has spectrum `φ², φ⁻²`, irrational — a `Real213` cut, not an integer).  So the spectrum is honestly a
`Real213`/algebraic-closure object; what the calculus proves ∅-axiom is the **conditional** statement
"if the spectrum exists (in any commutative ring the entries embed into), then `tr = e₁` and
`det = e₂`" — the symmetric-function content, which is exactly what makes the split a non-split.

All ∅-axiom (`ring_intZ`; the factorization is a hypothesis, never assumed to hold).
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Spectrum

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace (Mat2)

/-- The characteristic polynomial of `M`, evaluated at `lam`: `λ² − tr(M)·λ + det(M)`.  The monic
    quadratic whose roots are the spectrum of `M`; its matrix shadow `M² = tr·M − det·I` is
    Cayley–Hamilton (`Mat2CayleyHamilton.cayley_hamilton`). -/
def charPoly (M : Mat2) (lam : Int) : Int :=
  lam * lam - Mat2.tr M * lam + Mat2.det M

/-! ## §0 — propext-free arithmetic helpers

The Lean-core `Int` lemmas (`Int.zero_mul`, `Int.neg_mul_neg`, `Int.add_left_cancel`, …) route
through `propext`; `ring_intZ` is the repo's ∅-axiom ring tactic but does not absorb a bare `0`
literal inside a product (`0·0`, `0−x`).  These few helpers, built only from the repo's pure
`E213.Meta.Int213` layer + `ring_intZ`, cover exactly the `0`-literal absorptions and the left
cancellation the coefficient extraction needs.  All ∅-axiom. -/

open E213.Meta.Int213 (zero_mul mul_comm neg_mul mul_neg zero_add)

/-- `a · 0 = 0` (pure). -/
private theorem mulZero (a : Int) : a * 0 = 0 := by rw [mul_comm]; exact zero_mul a

/-- `- -a = a` (pure, via `ring_intZ`). -/
private theorem negNeg (a : Int) : - -a = a := by ring_intZ

/-- `(0 − a)(0 − b) = a·b` (pure). -/
private theorem zeroSubMul (a b : Int) : (0 - a) * (0 - b) = a * b := by
  rw [E213.Meta.Int213.Order.zero_sub, E213.Meta.Int213.Order.zero_sub, neg_mul, mul_neg, negNeg]

/-- `0·0 − t·0 + d = d` (pure) — the constant term of `charPoly M 0`. -/
private theorem charPolyZero (t d : Int) : (0 : Int) * 0 - t * 0 + d = d := by
  rw [zero_mul, mulZero, E213.Meta.Int213.Order.sub_zero, zero_add]

/-- Left cancellation `a + b = a + c → b = c` (pure, via `ring_intZ`'s variable cancellation). -/
private theorem addLeftCancel {a b c : Int} (h : a + b = a + c) : b = c := by
  have nl : ∀ x : Int, -a + (a + x) = x := fun x => by ring_intZ
  rw [← nl b, ← nl c, h]

/-! ## §1 — Vieta on the spectrum: `(λ−μ)(λ−ν) = λ² − (μ+ν)λ + μν` -/

/-- ★★★★ **The spectrum's Vieta identity (the form of `charPoly`).**  A monic quadratic with roots
    `μ, ν` is `λ² − (μ+ν)λ + μν` — the coefficient of `λ` is `−e₁` (the additive symmetric function)
    and the constant is `e₂` (the multiplicative symmetric function).  Pure `ℤ` identity, ∀λ. -/
theorem vieta_factor (lam mu nu : Int) :
    (lam - mu) * (lam - nu) = lam * lam - (mu + nu) * lam + mu * nu := by ring_intZ

/-! ## §2 — under factorization, `tr = μ+ν = e₁` and `det = μν = e₂`

The hypothesis `hfac` is "`M`'s characteristic polynomial factors over the ambient ring as
`(λ−μ)(λ−ν)`, for all `λ`".  This is the *existence of the spectrum*; it is never assumed to hold for
an arbitrary `M` (it can fail in `Int` — the roots may be irrational, living in `Real213`).  Given it,
the symmetric-function readings of `tr` and `det` are forced. -/

/-- ★★★★ **`det` is `e₂` of the spectrum (the multiplicative `×↦·` character).**  If
    `charPoly M = (λ−μ)(λ−ν)` for all `λ`, then `det M = μ · ν`.  The multiplicative character of the
    spectrum *is* the determinant — `det2_mul`'s `×↦·` arrow read on the eigenvalues.  ∅-axiom. -/
theorem det_eq_e2 (M : Mat2) (mu nu : Int)
    (hfac : ∀ lam : Int, charPoly M lam = (lam - mu) * (lam - nu)) :
    Mat2.det M = mu * nu := by
  -- charPoly M 0 = 0·0 − tr·0 + det, defeq `det` via `charPolyZero`;  (0−μ)(0−ν) = μν.
  have hc : Mat2.det M = (0 - mu) * (0 - nu) :=
    (charPolyZero (Mat2.tr M) (Mat2.det M)).symm.trans (hfac 0)
  rw [zeroSubMul] at hc; exact hc

/-- ★★★★ **`tr` is `e₁` of the spectrum (the additive `×↦+` character).**  If
    `charPoly M = (λ−μ)(λ−ν)` for all `λ`, then `tr M = μ + ν`.  Proved by evaluating the
    coefficient match at two points and cancelling — the additive character of the spectrum *is* the
    trace.  ∅-axiom. -/
theorem tr_eq_e1 (M : Mat2) (mu nu : Int)
    (hfac : ∀ lam : Int, charPoly M lam = (lam - mu) * (lam - nu)) :
    Mat2.tr M = mu + nu := by
  -- charPoly M lam = lam² − tr·lam + det, and (lam−μ)(lam−ν) = lam² − (μ+ν)lam + μν.
  -- det = μν from det_eq_e2; evaluate the match at lam = 1 to extract the linear coefficient.
  have h0 : Mat2.det M = mu * nu := det_eq_e2 M mu nu hfac
  -- charPoly M 1 = (1−μ)(1−ν), i.e. 1·1 − tr·1 + det = (1−μ)(1−ν).
  have h1 : (1 : Int) * 1 - Mat2.tr M * 1 + Mat2.det M = (1 - mu) * (1 - nu) := hfac 1
  -- Normalise both sides to `det + (1 − tr)` and `μν + (1 − (μ+ν))` (pure `ring_intZ`).
  have e1 : (1 : Int) * 1 - Mat2.tr M * 1 + Mat2.det M
      = Mat2.det M + (1 - Mat2.tr M) := by ring_intZ
  have e2 : ((1 : Int) - mu) * (1 - nu) = mu * nu + (1 - (mu + nu)) := by ring_intZ
  rw [e1, e2, h0] at h1
  -- h1 : μν + (1 − tr) = μν + (1 − (μ+ν)).  Cancel μν, then cancel the `1`, then the double neg.
  have hcancel : (1 : Int) - Mat2.tr M = 1 - (mu + nu) := addLeftCancel h1
  have hsub : (1 : Int) + (-Mat2.tr M) = 1 + (-(mu + nu)) := by
    have l : (1 : Int) + (-Mat2.tr M) = 1 - Mat2.tr M := by ring_intZ
    have r : (1 : Int) + (-(mu + nu)) = 1 - (mu + nu) := by ring_intZ
    rw [l, r]; exact hcancel
  have hneg : -Mat2.tr M = -(mu + nu) := addLeftCancel hsub
  -- tr = -(-tr) = -(-(μ+ν)) = μ+ν
  calc Mat2.tr M = - -Mat2.tr M := (negNeg (Mat2.tr M)).symm
    _ = -(-(mu + nu)) := by rw [hneg]
    _ = mu + nu := negNeg (mu + nu)

/-- ★★★★ **The det/tr split is `e₂` vs `e₁` — one object, two symmetric functions.**  Under the
    factorization `charPoly M = (λ−μ)(λ−ν)`, *both* `tr = μ+ν` (additive `×↦+`, `e₁`) and
    `det = μν` (multiplicative `×↦·`, `e₂`) hold simultaneously.  The "split" the
    `representation.md` break located is not an opposition: the additive character and the
    multiplicative character are the two elementary symmetric functions of the *same* spectrum, the
    two coefficients of the *same* monic quadratic (Vieta).  ∅-axiom. -/
theorem tr_det_are_e1_e2 (M : Mat2) (mu nu : Int)
    (hfac : ∀ lam : Int, charPoly M lam = (lam - mu) * (lam - nu)) :
    Mat2.tr M = mu + nu ∧ Mat2.det M = mu * nu :=
  ⟨tr_eq_e1 M mu nu hfac, det_eq_e2 M mu nu hfac⟩

/-! ## §3 — the discriminant is the squared eigenvalue-gap -/

/-- The trace discriminant `tr² − 4·det` (= `Mat2.disc`, the order-2 dial of
    `HyperbolicEllipticTrace` / `CrossDetTraceField.traceDisc`). -/
theorem disc_eq_charPoly_discriminant (M : Mat2) :
    Mat2.disc M = Mat2.tr M * Mat2.tr M - 4 * Mat2.det M := rfl

/-- ★★★★ **The dial is the squared eigenvalue gap.**  Under the factorization, the order-2
    discriminant equals `(μ−ν)²`:

      `disc M = tr² − 4·det = (μ+ν)² − 4μν = (μ−ν)²`.

    So the hyperbolic / parabolic / elliptic trichotomy (the sign of `disc`,
    `HyperbolicEllipticTrace`) is the sign of the *squared eigenvalue gap*: distinct real eigenvalues
    (`disc > 0`, hyperbolic), a repeated eigenvalue (`disc = 0`, parabolic), or a conjugate pair
    (`disc < 0`, elliptic — `(μ−ν)²<0` forces `μ,ν` non-real, outside `Int`).  ∅-axiom. -/
theorem disc_eq_gap_squared (M : Mat2) (mu nu : Int)
    (hfac : ∀ lam : Int, charPoly M lam = (lam - mu) * (lam - nu)) :
    Mat2.disc M = (mu - nu) * (mu - nu) := by
  rw [disc_eq_charPoly_discriminant]
  obtain ⟨htr, hdet⟩ := tr_det_are_e1_e2 M mu nu hfac
  rw [htr, hdet]
  ring_intZ

/-! ## §4 — the matrix realizes its own characteristic factorization (Cayley–Hamilton link)

The scalar Vieta above and the matrix Cayley–Hamilton are the same identity at two levels: the
spectrum `{μ,ν}` satisfies `λ² = tr·λ − det` (scalar), and the matrix `M` satisfies
`M² = tr·M − det·I` (`Mat2CayleyHamilton.cayley_hamilton`).  Read together: `tr` and `det` are the
two symmetric functions appearing as the two coefficients of the one quadratic the matrix obeys. -/

/-- ★★★ **The spectrum solves the characteristic polynomial.**  Under the factorization, each
    eigenvalue is a root: `charPoly M μ = 0` and `charPoly M ν = 0` — the scalar `λ² = tr·λ − det`
    whose matrix shadow is Cayley–Hamilton.  Together with `tr_det_are_e1_e2` this pins `tr, det` as
    `e₁, e₂` of the roots of the *same* quadratic the matrix satisfies. -/
theorem spectrum_roots (M : Mat2) (mu nu : Int)
    (hfac : ∀ lam : Int, charPoly M lam = (lam - mu) * (lam - nu)) :
    charPoly M mu = 0 ∧ charPoly M nu = 0 := by
  refine ⟨?_, ?_⟩
  · rw [hfac mu, E213.Meta.Int213.Order.sub_self_zero, zero_mul]
  · rw [hfac nu, E213.Meta.Int213.Order.sub_self_zero, mulZero]

/-- ★★★★ **The det/tr split resolved.**  Bundling the result: for a `Mat2` whose characteristic
    polynomial factors as `(λ−μ)(λ−ν)`,

      `tr M = μ + ν`  (`e₁`, additive `×↦+` character of the spectrum),
      `det M = μ · ν`  (`e₂`, multiplicative `×↦·` character of the spectrum),
      `disc M = (μ − ν)²`  (the trichotomy dial = squared eigenvalue gap),
      and each of `μ, ν` is a root of `charPoly M` (the scalar shadow of Cayley–Hamilton).

    `tr` and `det` are not a multiplicative-character-and-orphaned-additive-readout opposition: they
    are the **two elementary symmetric functions of one spectrum**, the two coefficients of one monic
    quadratic.  The split is `e₁` vs `e₂`. -/
theorem det_tr_split_is_e1_e2 (M : Mat2) (mu nu : Int)
    (hfac : ∀ lam : Int, charPoly M lam = (lam - mu) * (lam - nu)) :
    Mat2.tr M = mu + nu
    ∧ Mat2.det M = mu * nu
    ∧ Mat2.disc M = (mu - nu) * (mu - nu)
    ∧ charPoly M mu = 0 ∧ charPoly M nu = 0 :=
  ⟨tr_eq_e1 M mu nu hfac, det_eq_e2 M mu nu hfac, disc_eq_gap_squared M mu nu hfac,
   spectrum_roots M mu nu hfac⟩

end E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Spectrum
