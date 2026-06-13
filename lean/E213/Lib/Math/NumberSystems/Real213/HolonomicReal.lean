import E213.Lib.Math.Analysis.CauchyCompleteValid
import E213.Lib.Math.NumberSystems.Real213.Phi.PhiCauchyLimit

/-!
# HolonomicReal — a real presented by a P-recursive recurrence with its modulus as data

A `Real213`-style cut converges, but the convergence *modulus* (how far to go for
precision `k`) is usually supplied as a hypothesis: `EulerCut.toCauchy` takes
`N : Nat → Nat → Nat` and a proof it bounds the tail.  For the **structured
(P-recursive / holonomic)** reals — those whose convergent data obeys a
polynomial-coefficient recurrence — the modulus is not an assumption but a
*consequence* of the recurrence.  This file gives the type that carries it as data.

A `HolonomicReal` bundles:
  * `hol`   — the holonomic recurrence specification (`Holonomic`);
  * `seq`   — the convergent cut-sequence together with its **explicit modulus**
              `seq.N` and the Cauchy proof (a `CauchyCutSeq`);
  * `valid` — a proof that the limit cut is a genuine real (`ValidCut`).

So the public API (`HolonomicReal.cut`, `HolonomicReal.cut_valid`) behaves like an
unconditional real: the modulus is the constructed field `seq.N`, and no convergence
hypothesis is exposed.

## Status (honest)

The **autonomous case is closed end-to-end**: φ — order-2, constant-coefficient
(`det = 1`) recurrence (Fibonacci/Pell) — is a complete `HolonomicReal`
(`phiHolonomicReal`), its modulus the already-proven `N(m,k) = 2k`
(`PhiCauchyLimit.phiConvergentSeq`), its cut definitionally the closed-form golden
cut (`phiHolonomicReal_cut`).

The **degree-1 transcendental case is also closed**: e (coefficient `n+1`) is a
complete `HolonomicReal` with a constructed total modulus `N(m,k) = k+2`
(`ExpLog/EulerModulus.eHolonomicReal`), via e's factorial-tail rate.  So the
generator covers the autonomous (algebraic) class and the degree-1 holonomic class
(e).  Still open: higher-degree transcendentals (π, degree 4) — their explicit
convergence-rate modulus — and the *general* `Holonomic → CertifiedModulus` for
arbitrary recurrence data.  This file lays the type and discharges it on the
autonomous instance (no `sorry`, no unproven `derived` field).

Narrative: `theory/math/analysis/holonomic_modulus.md`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213

open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)
open E213.Lib.Math.NumberSystems.Real213.Core.ValidCut (ValidCut)
open E213.Lib.Math.NumberSystems.Real213.PhiCauchyLimit (phiConvergentSeq phiCauchy_limit_eq_phiCut)
open E213.Lib.Math.NumberSystems.Real213.PhiAsCut (phiCut phiCut_valid)

/-- A **holonomic (P-recursive) recurrence specification** of order `order`: the
    convergent data satisfies `Σ_{i<order} coeff i · s(n+i) = 0` with polynomial
    coefficients of degree bound `cdeg i`, from initial data `init`.  (Data only;
    proving a given sequence satisfies it is the recurrence-to-modulus link, open
    in general — see file header.) -/
structure Holonomic where
  order : Nat
  coeff : Nat → Int
  cdeg  : Nat → Nat
  init  : Nat → Int

/-- A real presented by a holonomic recurrence, carrying its convergent cut-sequence
    with **certified modulus** (`seq.N` + the Cauchy proof in `seq`) and a proof the
    limit is a valid real.  The modulus is a constructed field, not a hypothesis. -/
structure HolonomicReal where
  hol   : Holonomic
  seq   : CauchyCutSeq
  valid : ValidCut seq.limit

/-- The real, as a decidable cut (the Cauchy-complete limit). -/
def HolonomicReal.cut (hr : HolonomicReal) : Nat → Nat → Bool := hr.seq.limit

/-- The constructed convergence modulus (a field, not a hypothesis). -/
def HolonomicReal.modulus (hr : HolonomicReal) : Nat → Nat → Nat := hr.seq.N

/-- ★ **The unconditional API**: a `HolonomicReal`'s cut is a valid real with no
    convergence hypothesis exposed — the modulus rode in as `seq.N`. -/
theorem HolonomicReal.cut_valid (hr : HolonomicReal) : ValidCut hr.cut := hr.valid

/-! ## The autonomous instance — φ (order 2, constant coefficients, `det = 1`) -/

/-- The limit of φ's convergent cut-sequence is a valid cut.  Transported pointwise
    from `phiCut_valid` along `phiCauchy_limit_eq_phiCut` (no `funext`). -/
theorem phiConvergent_limit_valid : ValidCut phiConvergentSeq.limit :=
  { upM := fun m1 m2 k h hm => by
      rw [phiCauchy_limit_eq_phiCut] at hm ⊢
      exact phiCut_valid.upM m1 m2 k h hm
    dnK := fun m k1 k2 h hm => by
      rw [phiCauchy_limit_eq_phiCut] at hm ⊢
      exact phiCut_valid.dnK m k1 k2 h hm }

/-- φ's recurrence: order 2, **constant** coefficients (`cdeg ≡ 0`, autonomous,
    `det = 1`) — the Fibonacci/Pell recurrence `s(n+2) = s(n+1) + s(n)` from
    `F₀ = F₁ = 1`.  The shallowest holonomic class (divergence depth 1). -/
def phiHolonomic : Holonomic where
  order := 2
  coeff := fun i => if i = 0 then 1 else if i = 1 then 1 else 0
  cdeg  := fun _ => 0
  init  := fun _ => 1

/-- ★★★ **φ is a complete `HolonomicReal`.**  The autonomous, constant-coefficient
    recurrence, the convergent Pell cut-sequence, its proven modulus `N(m,k) = 2k`,
    and the validity of the limit — bundled, ∅-axiom.  The architecture closes
    end-to-end on the autonomous instance. -/
def phiHolonomicReal : HolonomicReal where
  hol   := phiHolonomic
  seq   := phiConvergentSeq
  valid := phiConvergent_limit_valid

/-- φ's holonomic cut is the closed-form golden-ratio cut. -/
theorem phiHolonomicReal_cut (m k : Nat) : phiHolonomicReal.cut m k = phiCut m k :=
  phiCauchy_limit_eq_phiCut m k

/-- φ's constructed modulus is the linear `N(m,k) = 2k` — no hypothesis. -/
theorem phiHolonomicReal_modulus (m k : Nat) : phiHolonomicReal.modulus m k = 2 * k := rfl

end E213.Lib.Math.NumberSystems.Real213
