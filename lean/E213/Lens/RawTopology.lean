import E213.Theory.Raw.API
import E213.Lens.LensCore
import E213.Lens.Lattice.Lattice
import E213.Lens.Algebra.IdLensEq

/-!
# Lens.RawTopology — K_∞ ≡ point ≡ discrete vs indiscrete bookends

Formalisation of `seed/AXIOM/06_lens_readings.md` §6.5:
under different Lens readings, Raw exhibits two extreme
topological pictures.

  · **Indiscrete reading** (constLens):  every pair of Raws is
    equivalent.  Raw collapses to a single point — Lean witness
    of "K_∞ ≡ point ≡ infinite trivial-topology space" at raw
    level.  The "naming event" (Lens choice ≠ constLens) is what
    first introduces colour.

  · **Discrete reading** (idLens):  the kernel is exactly
    equality.  Every distinct pair separates — finest possible
    distinction.  Cf. `Lens/Algebra/IdLensEq.lean`.

Intermediate Lenses populate the lattice between these two
extremes.  This file formalises both bookends + the universal
property bracketing every Lens-induced kernel between them.
-/

namespace E213.Lens.RawTopology

open E213.Theory (Raw)
open E213.Lens (Lens)
open E213.Lens.Lattice.Lattice (constLens constLens_view all_refine_constLens)

/-! ## §1 — Indiscrete bookend (constLens / K_∞ at raw) -/

/-- ★ **constLens collapses Raw**: under the constant Lens, every
    Raw maps to the same α-value `e`.  This is the Lean witness
    of §9.5's "K_∞ ≡ point ≡ trivial-topology infinite space"
    equivalence at the Lens-quotient level — no Raw distinction
    survives the no-distinction reading. -/
theorem constLens_view_eq {α : Type} (e : α) (r s : Raw) :
    (constLens e).view r = (constLens e).view s := by
  rw [constLens_view, constLens_view]

/-- ★ The same fact at the kernel level: the constLens kernel is
    the total relation — every pair of Raws is equivalent.  This
    is the "K_∞ at raw" / "globally collapsed" / "indiscrete
    topology" form of `constLens_view_eq`, depending on which
    Lens-quotient name one prefers. -/
theorem constLens_equiv {α : Type} (e : α) (x y : Raw) :
    (constLens e).equiv x y :=
  constLens_view_eq e x y

/-- ★ **constLens is the lattice top**: every Lens refines
    constLens.  Universal-property witness that no Lens reading
    can be coarser than the no-distinction one. -/
theorem constLens_is_top {α : Type} (e : α) (L : Lens α) :
    L.refines (constLens e) :=
  all_refine_constLens e L

/-- ★★ **K_∞ ↔ point bundle** (§9.5).  Under the indiscrete
    reading, four equivalent facts:
      (i)   every Raw maps to the same α-value `e`
      (ii)  every pair of Raws is `.equiv`-related
      (iii) constLens is the lattice top (universal refinement)
      (iv)  every other Lens kernel is contained in constLens's
            (topological coarseness universal property)
    Conjoined, these realise §9.5: at the no-distinction
    reading, Raw is operationally a singleton. -/
theorem k_infty_at_raw_bundle {α : Type} (e : α) :
    (∀ r : Raw, (constLens e).view r = e)
    ∧ (∀ x y : Raw, (constLens e).equiv x y)
    ∧ (∀ L : Lens α, L.refines (constLens e))
    ∧ (∀ L : Lens α, ∀ x y : Raw,
          L.equiv x y → (constLens e).equiv x y) :=
  ⟨constLens_view e,
   constLens_equiv e,
   constLens_is_top e,
   fun _ x y _ => constLens_view_eq e x y⟩

/-! ## §2 — Discrete bookend (idLens / coarsest distinction) -/

/-- ★ **idLens kernel = equality**: the finest Lens kernel
    collapses to literal Raw equality.  Forwarded from
    `Lens/Algebra/IdLensEq.idLens_equiv_eq`. -/
theorem discrete_kernel_eq (x y : Raw) :
    E213.Lens.Instances.Identity.idLens.equiv x y ↔ x = y :=
  E213.Lens.Algebra.IdLensEq.idLens_equiv_eq x y

/-- ★ **Discrete distinguishes distinct Raws**: distinct `x` and
    `y` are not idLens-equivalent.  Mirror of `constLens_equiv`
    at the discrete end. -/
theorem discrete_distinguishes {x y : Raw} (h : x ≠ y) :
    ¬ E213.Lens.Instances.Identity.idLens.equiv x y := by
  intro hxy
  exact h ((discrete_kernel_eq x y).1 hxy)

/-! ## §3 — Two-bookend topology -/

/-- ★★★ **Two-bookend topology** (§9.5 end-to-end).  The Lens-
    refinement lattice is bracketed:

      · `constLens` (top, indiscrete): kernel is total; image
        is a singleton; every other Lens refines it; every
        other kernel is contained in it.
      · `idLens` (bottom, discrete): kernel = Raw equality;
        every distinct pair separates.

    Intermediate Lenses populate the interior of the lattice.
    For any distinct pair `x ≠ y`, the two bookends witness:
    constLens identifies them, idLens distinguishes them. -/
theorem topology_two_bookends {α : Type} (e : α)
    {x y : Raw} (h : x ≠ y) :
    (constLens e).equiv x y
    ∧ ¬ E213.Lens.Instances.Identity.idLens.equiv x y :=
  ⟨constLens_equiv e x y, discrete_distinguishes h⟩

end E213.Lens.RawTopology
