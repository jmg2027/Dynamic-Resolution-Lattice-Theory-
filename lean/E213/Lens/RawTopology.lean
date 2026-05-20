import E213.Theory.Raw.API
import E213.Lens.LensCore
import E213.Lens.Lattice.Lattice
import E213.Lens.UndifferentiatedRaw
import E213.Lens.Algebra.IdLensEq

/-!
# Lens.RawTopology — Lens kernels as Raw equivalence-topology

Deepening of `Lens/UndifferentiatedRaw.lean` and the §9.5
K_∞ ≡ point ≡ infinite topological space picture.

The Lens-refinement preorder on `Lens α` induces a corresponding
preorder on Raw equivalence relations.  Two extremes:

  - **Indiscrete reading** (constLens):  every pair of Raws is
    equivalent — the maximum-coarse kernel.  At this reading Raw
    behaves like K_∞ (no two vertices distinguishable, the entire
    object collapses to a singleton equivalence class).

  - **Discrete reading** (idLens):  the kernel is exactly
    equality — every distinct pair separates.  See
    `Lens/Algebra/IdLensEq.lean` for the kernel characterisation
    `idLens.equiv = (· = ·)`.

Intermediate Lenses populate the lattice between these two
extremes.  Per §9.5, the K_∞ ≡ point equivalence at raw level
holds *under the indiscrete reading*: with no Lens distinction
applied, Raw is operationally a single point.

This file formalises the indiscrete (K_∞-at-raw) bookend as a
bundle of ∅-axiom theorems — the universal and total properties
that together witness "Raw is a singleton under no distinction".
-/

namespace E213.Lens.RawTopology

open E213.Theory (Raw)
open E213.Lens (Lens)
open E213.Lens.Lattice.Lattice (constLens constLens_view all_refine_constLens)
open E213.Lens.UndifferentiatedRaw (constLens_collapses)

/-! ## §1 — Indiscrete reading (constLens kernel)

Every pair is equivalent.  The Lens-quotient is a singleton:
the entire Raw maps to a single value under the constant Lens.
-/

/-- **Total kernel**: the equivalence under constLens is the
    total relation on every pair. -/
theorem indiscrete_kernel_total {α : Type} (e : α) (x y : Raw) :
    (constLens e).equiv x y :=
  constLens_collapses e x y

/-- **Singleton image**: the constLens image is a singleton —
    only one value `e` appears. -/
theorem indiscrete_image_singleton {α : Type} (e : α) (r : Raw) :
    (constLens e).view r = e :=
  constLens_view e r

/-- **All-Raws-equivalent**: a stronger restatement.  For any
    chosen `e`, every Raw is `equiv`-related to every other Raw —
    not just pairwise, but globally collapsed.

    This is the "K_∞ at raw" statement: choosing any Raw as
    "basepoint", every other Raw is indistinguishable from it
    under the no-distinction reading.  Cf. Aut(K_∞) being the
    full symmetric group on vertices (§9.5). -/
theorem indiscrete_globally_collapsed
    {α : Type} (e : α) (r₀ : Raw) (r : Raw) :
    (constLens e).equiv r₀ r :=
  constLens_collapses e r₀ r

/-! ## §2 — Lattice bookend: indiscrete is the top

`Lens/Lattice/Lattice.lean` already establishes `constLens e` as
the top (coarsest) of the Lens-refinement preorder.  Here we
record the K_∞-at-raw / point / trivial-topology framing
explicitly.
-/

/-- **constLens is the top**: every Lens refines constLens.
    This is the K_∞-at-raw witness: no Lens reading can be
    coarser than the no-distinction one. -/
theorem indiscrete_is_top {α : Type} (e : α) (L : Lens α) :
    L.refines (constLens e) :=
  all_refine_constLens e L

/-- ★ **K_∞ ↔ point bundle** (§9.5).  Under the indiscrete
    reading:

      (i)   every Raw maps to the same α-value;
      (ii)  every pair of Raws is α-equivalent;
      (iii) the kernel is total — no internal differentiation
            (globally collapsed form);
      (iv)  the indiscrete Lens is the coarsest in the Lens lattice.

    Conjoined, these say: at the no-distinction reading, Raw is
    operationally a *singleton* with no internal structure —
    K_∞-at-raw / point / trivial-topology condition realised at
    the Lens-quotient level. -/
theorem k_infty_at_raw_bundle {α : Type} (e : α) :
    -- (i) singleton image
    (∀ r : Raw, (constLens e).view r = e)
    -- (ii) pairwise total kernel
    ∧ (∀ x y : Raw, (constLens e).equiv x y)
    -- (iii) globally-collapsed form (any basepoint)
    ∧ (∀ r₀ r : Raw, (constLens e).equiv r₀ r)
    -- (iv) coarsest in the lattice (universal property)
    ∧ (∀ L : Lens α, L.refines (constLens e)) :=
  ⟨indiscrete_image_singleton e,
   indiscrete_kernel_total e,
   indiscrete_globally_collapsed e,
   indiscrete_is_top e⟩

/-! ## §3 — Topological reading

A "Lens-equivalence topology" on Raw can be read off the kernel:
two Raws are "open-separable" iff some Lens distinguishes them.

  - **constLens-reading**: no Lens distinguishes any pair → the
    induced topology is *indiscrete* (only ∅ and Raw are open).
  - **idLens-reading**: every distinct pair is distinguished →
    the induced topology is *discrete* (every singleton is open).

This file's `k_infty_at_raw_bundle` captures the indiscrete end.
The discrete end is captured by `Lens/Algebra/IdLensEq.lean`'s
`idLens_kernel_eq` (kernel = equality).  Together they bracket
the Lens-induced topology lattice from coarsest to finest. -/

/-- The constLens-induced equivalence on Raw is the universally
    coarsest decidable kernel — every other kernel refines it
    (= adds distinctions).  This is the topological-coarseness
    bookend at the K_∞ end. -/
theorem indiscrete_is_coarsest_universal {α : Type} (e : α) :
    ∀ L : Lens α, ∀ x y : Raw,
      L.equiv x y → (constLens e).equiv x y := by
  intro L x y _
  exact constLens_collapses e x y

/-! ## §4 — Discrete end (idLens kernel)

The mirror bookend at the discrete-topology end.  Under the
identity reading every distinct pair separates, so the kernel
is exactly equality on Raw.
-/

/-- **idLens kernel = equality**: forwarded from
    `Lens/Algebra/IdLensEq.idLens_equiv_eq`.  The finest Lens-
    kernel collapses to literal Raw equality. -/
theorem discrete_kernel_eq (x y : Raw) :
    E213.Lens.Instances.Identity.idLens.equiv x y ↔ x = y :=
  E213.Lens.Algebra.IdLensEq.idLens_equiv_eq x y

/-- **Discrete distinguishes distinct Raws**: for distinct `x`
    and `y`, the idLens kernel does NOT relate them.  Direct
    consequence of `discrete_kernel_eq`. -/
theorem discrete_distinguishes_distinct {x y : Raw} (h : x ≠ y) :
    ¬ E213.Lens.Instances.Identity.idLens.equiv x y := by
  intro hxy
  exact h ((discrete_kernel_eq x y).1 hxy)

/-- ★ **Two-bookend topology bundle** (§9.5 end-to-end).

  Reading the Lens-refinement lattice from coarsest to finest:

    · `constLens` (top): kernel total, image singleton,
      K_∞-at-raw / point / indiscrete topology.
    · `idLens` (bottom): kernel = equality, every distinct pair
      separates, discrete topology.

  Every intermediate Lens lives strictly between these two
  bookends.  The Lens-induced topology lattice is bracketed by
  the constLens (indiscrete) and idLens (discrete) endpoints. -/
theorem topology_two_bookends {α : Type} (e : α) (x y : Raw) (h : x ≠ y) :
    -- indiscrete bookend (top)
    (constLens e).equiv x y
    -- discrete bookend (bottom) does not relate x, y
    ∧ ¬ E213.Lens.Instances.Identity.idLens.equiv x y :=
  ⟨constLens_collapses e x y,
   discrete_distinguishes_distinct h⟩

end E213.Lens.RawTopology
