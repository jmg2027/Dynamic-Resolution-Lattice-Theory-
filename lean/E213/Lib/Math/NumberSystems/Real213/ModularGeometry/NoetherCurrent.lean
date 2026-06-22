import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyLattice
import E213.Meta.Int213.Core
import E213.Meta.Int213.Order

/-!
# Noether's theorem as a discrete continuity equation — `∂·j = 0 ⟺ Aut-invariant`

This file closes the **structural** half of the continuous Noether current
named open in `research-notes/decomposition/practice/noether.md`: not the full
variational `∂_μ j^μ = 0` over a Lagrangian (which would need `Real213`
analytic machinery this file does not assume), but its discrete skeleton —
the **local continuity equation** whose telescoped sum is
`HolonomyLattice.det_holonomy_eq_one`, plus the **Noether iff** that ties
local conservation to symmetry-invariance.

## The reading

A *worldline* is a path `w : List Mat2` of state-transitions
(`HolonomyLattice`).  The **charge density / readout** carried along the
worldline is the conserved character

  `ρ w := det (holonomy w)`        (`density`)

— the `Aut(C)`-invariant character of `determinant.md`/`noether.md`.  Adding a
step `g` at time `0` advances the worldline by one tick; the **time-difference**
of the density is

  `(∂_t ρ)(g, w) := det (holonomy (g :: w)) − det (holonomy w)`   (`dtDensity`)

and the **current** carried by the step is the multiplicative deficit

  `j(g, w) := (det g − 1) · det (holonomy w)`                     (`current`)

so that the **discrete continuity equation** holds *identically*:

  `(∂_t ρ)(g, w) = j(g, w)`        (`continuity_eq`, by `det_mul`)

This is `∂_t ρ + ∂_x j = 0` read 213-natively: the time-change of the density
is exactly (minus) the divergence the step injects.  `det g` is the
multiplicative factor the symmetry generator applies; the source `j` is the
amount by which that factor differs from the unit.

## Noether (the iff)

  **The current vanishes for every worldline ⟺ the generator is Aut-invariant
  (`det g = 1`).**                                                (`noether_local`)

`(⇐)` if `det g = 1` the source `j` is `0` for every `w` (`current_zero_of_det_one`),
so the density is locally conserved (`∂_t ρ = 0`, `density_conserved_of_det_one`).
`(⇒)` if the density is conserved along *every* worldline, then in particular
along the empty worldline `det (holonomy [g]) = det (holonomy []) = 1`, forcing
`det g = 1` — no cancellation lemma needed, the empty path is the witness.

Telescoping the local conservation over a whole `det = 1` word reproduces
`det_holonomy_eq_one`: the global conserved charge (`noether_global`).  This is
Noether's theorem in the calculus's terms: **`Aut(C)`-invariant ⟺ `∂·j = 0`**,
local and global, all ∅-axiom.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ModularGeometry.NoetherCurrent

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace (Mat2)
open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyLattice
  (holonomy holonomy_nil holonomy_cons det_mul det_holonomy_eq_one)

/-! ## §1 — density, time-difference, current -/

/-- **Charge density / readout** carried along a worldline: the conserved
    character `det (holonomy w)` (the `Aut(C)`-invariant of `noether.md`). -/
def density (w : List Mat2) : Int := Mat2.det (holonomy w)

/-- **Discrete time-difference of the density** across one step `g` prepended at
    time `0`: `det(holonomy (g::w)) − det(holonomy w)`.  The 213-native `∂_t ρ`. -/
def dtDensity (g : Mat2) (w : List Mat2) : Int :=
  density (g :: w) - density w

/-- **Current injected by the step** `g`: the multiplicative deficit
    `(det g − 1) · det(holonomy w)`.  The 213-native source `j`. -/
def current (g : Mat2) (w : List Mat2) : Int :=
  (Mat2.det g - 1) * density w

/-! ## §2 — the discrete continuity equation `∂_t ρ = j` -/

/-- The density factorises across a step: `ρ (g :: w) = det g · ρ w`
    (the character homomorphism `det_mul` applied to `holonomy`). -/
theorem density_step (g : Mat2) (w : List Mat2) :
    density (g :: w) = Mat2.det g * density w := by
  show Mat2.det (holonomy (g :: w)) = Mat2.det g * Mat2.det (holonomy w)
  rw [holonomy_cons, det_mul]

/-- ★★★★ **Discrete continuity equation** — `∂_t ρ = j`, identically.
    The time-difference of the conserved density equals the current the step
    injects.  This is `∂_t ρ + ∂_x j = 0` read 213-natively (the source `j` is
    minus the spatial divergence), proved by the character homomorphism. -/
theorem continuity_eq (g : Mat2) (w : List Mat2) :
    dtDensity g w = current g w := by
  show density (g :: w) - density w = (Mat2.det g - 1) * density w
  rw [density_step]
  show Mat2.det g * density w - density w = (Mat2.det g - 1) * density w
  ring_intZ

/-! ## §3 — the Noether iff: `∂·j = 0  ⟺  Aut-invariant (det g = 1)` -/

/-- `(⇐)` An **Aut-invariant generator** (`det g = 1`) injects **no current**:
    `j(g, w) = 0` for every worldline. -/
theorem current_zero_of_det_one {g : Mat2} (h : Mat2.det g = 1)
    (w : List Mat2) : current g w = 0 := by
  show (Mat2.det g - 1) * density w = 0
  rw [h]
  show (1 - 1) * density w = 0
  rw [show (1 : Int) - 1 = 0 from rfl, E213.Meta.Int213.zero_mul]

/-- `(⇐)` Local conservation: an Aut-invariant generator leaves the density
    unchanged across the step (`∂_t ρ = 0`). -/
theorem density_conserved_of_det_one {g : Mat2} (h : Mat2.det g = 1)
    (w : List Mat2) : dtDensity g w = 0 := by
  rw [continuity_eq]; exact current_zero_of_det_one h w

/-- `(⇒)` The **empty worldline is the witness**: if the density is conserved
    along the empty worldline, the generator is Aut-invariant.  `det(holonomy []) = det I = 1`,
    so `dtDensity g [] = det g − 1 = 0` forces `det g = 1`.  No cancellation
    lemma is needed. -/
theorem det_one_of_conserved_nil {g : Mat2} (h : dtDensity g [] = 0) :
    Mat2.det g = 1 := by
  have hstep : density (g :: []) = Mat2.det g * density [] := density_step g []
  have hnil : density ([] : List Mat2) = 1 := by
    show Mat2.det (holonomy []) = 1
    rw [holonomy_nil]; decide
  -- dtDensity g [] = det g · 1 − 1 = det g − 1
  have : Mat2.det g - 1 = 0 := by
    have hd : dtDensity g [] = Mat2.det g - 1 := by
      show density (g :: []) - density [] = Mat2.det g - 1
      rw [hstep, hnil, E213.Meta.Int213.mul_one]
    rw [← hd]; exact h
  exact E213.Meta.Int213.Order.eq_of_sub_eq_zero this

/-- ★★★★ **Noether's theorem, local form** — `∂·j = 0  ⟺  Aut-invariant`.

    The current vanishes along **every** worldline (equivalently: the density
    is locally conserved along every worldline) **iff** the generator is
    `Aut(C)`-invariant (`det g = 1`).  This is the discrete continuity-equation
    statement of Noether: a symmetry of the action (`det g = 1`) is *equivalent*
    to the local conservation law `∂_t ρ = 0`.

    `(⇐)` is `current_zero_of_det_one`; `(⇒)` reads off the empty-worldline
    witness `det_one_of_conserved_nil`. -/
theorem noether_local (g : Mat2) :
    (∀ w : List Mat2, current g w = 0) ↔ Mat2.det g = 1 := by
  constructor
  · intro hj
    apply det_one_of_conserved_nil
    rw [continuity_eq]; exact hj []
  · intro hdet w
    exact current_zero_of_det_one hdet w

/-- ★ **Noether's theorem, local form (density phrasing)** — the density is
    locally conserved along every worldline (`∂_t ρ = 0`) iff the generator is
    Aut-invariant.  The continuity-equation twin of `noether_local`. -/
theorem noether_local_density (g : Mat2) :
    (∀ w : List Mat2, dtDensity g w = 0) ↔ Mat2.det g = 1 := by
  constructor
  · intro h; exact det_one_of_conserved_nil (h [])
  · intro hdet w; exact density_conserved_of_det_one hdet w

/-! ## §4 — telescoping to the global conserved charge

The local continuity equation, telescoped over a whole `det = 1` word, is the
global conservation `det (holonomy w) = 1` — `det_holonomy_eq_one` re-read as
the integrated charge of the locally-conserved current. -/

/-- ★★★★ **Noether's theorem, global form** (telescoped charge).
    If every step of the worldline is Aut-invariant (`det g = 1`), the global
    charge `ρ w = det (holonomy w)` is conserved — `= 1` around the whole
    worldline.  This is the telescoped sum of the local continuity equation:
    `det_holonomy_eq_one` read as Noether's conserved charge. -/
theorem noether_global (w : List Mat2)
    (h : ∀ g, g ∈ w → Mat2.det g = 1) : density w = 1 :=
  det_holonomy_eq_one w h

/-- ★ **Local ⊢ global**: if every step is Aut-invariant, then every step is
    locally currentless (`∂·j = 0` at each tick) *and* the global charge is
    conserved.  The two faces of Noether — local continuity + global charge —
    delivered by the same `det = 1` hypothesis. -/
theorem noether_local_implies_global (w : List Mat2)
    (h : ∀ g, g ∈ w → Mat2.det g = 1) :
    (∀ g, g ∈ w → ∀ v : List Mat2, current g v = 0) ∧ density w = 1 :=
  ⟨fun g hg v => current_zero_of_det_one (h g hg) v, noether_global w h⟩

/-! ## §5 — the conserved/deficit dichotomy at the fold (`q = ±1`)

The Noether iff has a sharp boundary: the fold generator `S` (`det S = 1`) is
Aut-invariant, so its current vanishes — yet its *holonomy* is the `q = −1`
deficit `holonomy [S,S] = −I` (`first_loop_is_the_fold`).  Conservation of the
*character* (`det`) is compatible with a nontrivial holonomy *deficit*: Noether
conserves the charge `det`, not the full state.  These two PURE facts pin the
distinction. -/

/-- The fold generator `S` is Aut-invariant (`det S = 1`), hence carries **no
    Noether current** — even though its holonomy is the order-4 deficit. -/
theorem fold_is_currentless (w : List Mat2) : current Mat2.S w = 0 :=
  current_zero_of_det_one (by decide) w

/-- ★ **Noether conserves the charge, not the state.**  `S` is currentless
    (`det`-conserved) yet its two-step holonomy lands at the deficit `−I ≠ I`:
    the Noether charge `det` is conserved (`= 1`) on the very loop whose
    *state* fails to close.  Conservation of the invariant character coexists
    with nontrivial holonomy. -/
theorem charge_conserved_state_not (w : List Mat2) :
    current Mat2.S w = 0
    ∧ density [Mat2.S, Mat2.S] = 1
    ∧ holonomy [Mat2.S, Mat2.S] = Mat2.negI
    ∧ Mat2.negI ≠ Mat2.I := by
  refine ⟨fold_is_currentless w, ?_, ?_, ?_⟩
  · show Mat2.det (holonomy [Mat2.S, Mat2.S]) = 1; decide
  · decide
  · decide

end E213.Lib.Math.NumberSystems.Real213.ModularGeometry.NoetherCurrent
