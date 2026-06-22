import E213.Lib.Math.Analysis.UniformLimitContinuous

/-!
# Topology — continuity ⟺ preimage-of-open-is-open (dyadic / `MetricModulus`)

`research-notes/decomposition/practice/continuity.md` flags the classical
topological characterisation of continuity

> `f` is continuous ⟺ the preimage of every open set is open

as a **prose-only** leg: 213 has modulus-continuity (`ContinuousWithModulus`)
and a notion of open set (`DyadicOpen`) as separate ∅-axiom objects, but no
single theorem welding them.  This file certifies that leg on the repo's
actual continuity law — `ContinuousWithModulus` over `MetricModulus`.

## The open-set notion (refinement-stable fibre)

In a `1/2^m`-graduated metric the native open set is the **refinement-stable
fibre**: a region you can keep refining and never leave.

    IsDyadicOpen M U  :=  ∀ x, U x → ∃ m, ∀ y, M.close m x y → U y

(every point of `U` carries a `close m`-ball that stays inside `U`).  This is
exactly `continuity.md`'s "`L_res`'s refinement-stable fibre", stated for the
`MetricModulus` the continuity law already lives on.  Pure `Prop`, no
decidability, no Choice.

## What is ∅-axiom and what is the wall (mirrors the Banach analysis)

* **Forward — `continuous_preimage_dyadicopen`** (`f` continuous ⟹ preimage of
  every open is open): **fully ∅-axiom, unconditional.**  The clean half.

* **Backward — `preimage_dyadicopen_pointwise_continuous`** (preimage of every
  open is open ⟹ `f` is *pointwise* continuous): **fully ∅-axiom.**  The
  canonical open neighbourhood `nbhd (f x) m` (the interior of the closed
  `m`-ball) is genuinely `IsDyadicOpen` (`nbhd_isDyadicOpen`); its preimage is
  open and contains `x`, which hands back the local input scale at `x`.

* **Backward, *uniform* — the choice wall.**  Recovering a *single*
  `ω : Nat → Nat` good at every point (the uniform `ContinuousWithModulus`)
  from the pointwise `∃` witnesses is **constructively blocked**: it is the
  same `AC₀,₀`-flavour modulus-extraction wall as `banach_fixed_point`'s
  generic wrapper (`gaussian_clt.md`).  The honest ∅-axiom uniform converse
  carries the modulus *as data* (the Bishop / `HasModulus` move):
  `preimage_dyadicopen_uniform_continuous_of_modulus` takes a supplied uniform
  witness and returns `ContinuousWithModulus`, ∅-axiom.

So: forward is a clean biconditional half; the backward *pointwise* half is
clean; the backward *uniform* half is the documented constructive wall, closed
honestly by carrying the modulus as data.
-/

namespace E213.Lib.Math.Geometry.Topology.ContinuityOpenSet

open E213.Lib.Math.Analysis.UniformLimitContinuous
  (MetricModulus ContinuousWithModulus)

variable {D V : Type}

/-! ## 1. The dyadic-open notion and preimage -/

/-- **`IsDyadicOpen M U`** — `U` is open in the `1/2^m`-graduated metric `M`:
    every point of `U` has a `close m`-ball that stays inside `U`.  The
    refinement-stable fibre of the resolution reading (`continuity.md`). -/
def IsDyadicOpen {X : Type} (M : MetricModulus X) (U : X → Prop) : Prop :=
  ∀ x, U x → ∃ m, ∀ y, M.close m x y → U y

/-- Preimage of a predicate under `f`. -/
def preimage (f : D → V) (U : V → Prop) : D → Prop := fun x => U (f x)

/-- **Pointwise continuity** (the local, non-uniform form): at each scale `m`
    and each point `x`, some input scale `d` controls the output.  The `∃` is
    *per point* — assembling a single `Nat → Nat` from it is the choice wall. -/
def PointwiseContinuous (MD : MetricModulus D) (MV : MetricModulus V)
    (f : D → V) : Prop :=
  ∀ m x, ∃ d, ∀ y, MD.close d x y → MV.close m (f x) (f y)

/-! ## 2. Forward direction — continuous ⟹ preimage of open is open (∅-axiom) -/

/-- ★ **`continuous_preimage_dyadicopen`** — if `f` is (uniformly) continuous
    with modulus `ω`, the preimage of every dyadic-open set is dyadic-open.
    The clean half of the topological characterisation, unconditional. -/
theorem continuous_preimage_dyadicopen
    (MD : MetricModulus D) (MV : MetricModulus V)
    (f : D → V) (ω : Nat → Nat)
    (hf : ContinuousWithModulus MD MV f ω)
    (U : V → Prop) (hU : IsDyadicOpen MV U) :
    IsDyadicOpen MD (preimage f U) := by
  intro x hx
  -- hx : U (f x).  Open gives a close m-ball around f x inside U.
  obtain ⟨m, hm⟩ := hU (f x) hx
  -- continuity pulls that ball back to a close (ω m)-ball around x.
  refine ⟨ω m, ?_⟩
  intro y hxy
  -- hxy : MD.close (ω m) x y ⇒ MV.close m (f x) (f y) ⇒ U (f y).
  exact hm (f y) (hf m x y hxy)

/-! ## 3. The canonical open neighbourhood (interior of the closed ball) -/

/-- **`nbhd M v₀ m`** — the interior of the closed `1/2^m`-ball around `v₀`:
    points `v` carrying a `close k`-ball that lands inside the `m`-ball of
    `v₀`.  This is the canonical genuinely-open neighbourhood used to probe
    continuity from the open-set side. -/
def nbhd {X : Type} (M : MetricModulus X) (v₀ : X) (m : Nat) : X → Prop :=
  fun v => ∃ k, ∀ w, M.close k v w → M.close m v₀ w

/-- `v₀` lies in its own neighbourhood (witness `k = m`, identity). -/
theorem mem_nbhd_self {X : Type} (M : MetricModulus X) (v₀ : X) (m : Nat) :
    nbhd M v₀ m v₀ :=
  ⟨m, fun _ h => h⟩

/-- ★ **`nbhd_isDyadicOpen`** — the neighbourhood is genuinely dyadic-open.
    Interiors are open: a `close (k+1)`-ball around an interior point `v`
    (witness `k`) stays interior, via one halving triangle (`ctri`). -/
theorem nbhd_isDyadicOpen {X : Type} (M : MetricModulus X) (v₀ : X) (m : Nat) :
    IsDyadicOpen M (nbhd M v₀ m) := by
  intro v hv
  obtain ⟨k, hk⟩ := hv
  -- ball of radius k+1 around v keeps points interior with witness k+1.
  refine ⟨k + 1, ?_⟩
  intro z hvz
  refine ⟨k + 1, ?_⟩
  intro w hzw
  -- close (k+1) v z and close (k+1) z w ⇒ close k v w ⇒ close m v₀ w.
  exact hk w (M.ctri k v z w hvz hzw)

/-! ## 4. Backward, pointwise — preimage of open is open ⟹ pointwise continuous
       (∅-axiom) -/

/-- ★ **`preimage_dyadicopen_pointwise_continuous`** — if the preimage of every
    dyadic-open set is dyadic-open, then `f` is **pointwise** continuous.

    Fully ∅-axiom: the canonical open neighbourhood `nbhd (f x) m` is open
    (`nbhd_isDyadicOpen`), its preimage is open and contains `x`, and reading
    that openness at `x` (instantiated at `w = f y` via `crefl`) hands back the
    local input scale.  The *uniform* modulus — one `ω` for all `x` — is the
    documented choice wall (see module header). -/
theorem preimage_dyadicopen_pointwise_continuous
    (MD : MetricModulus D) (MV : MetricModulus V) (f : D → V)
    (H : ∀ U : V → Prop, IsDyadicOpen MV U → IsDyadicOpen MD (preimage f U)) :
    PointwiseContinuous MD MV f := by
  intro m x
  -- the open neighbourhood of f x at scale m; its preimage is open.
  have hopen : IsDyadicOpen MD (preimage f (nbhd MV (f x) m)) :=
    H (nbhd MV (f x) m) (nbhd_isDyadicOpen MV (f x) m)
  -- x is in the preimage (f x is in its own neighbourhood).
  have hx : preimage f (nbhd MV (f x) m) x := mem_nbhd_self MV (f x) m
  -- openness at x gives the local input scale d.
  obtain ⟨d, hd⟩ := hopen x hx
  refine ⟨d, ?_⟩
  intro y hxy
  -- hd y hxy : nbhd MV (f x) m (f y), i.e. ∃ k, ∀ w, close k (f y) w → close m (f x) w.
  obtain ⟨k, hk⟩ := hd y hxy
  -- instantiate at w = f y; close k (f y) (f y) by reflexivity.
  exact hk (f y) (MV.crefl k (f y))

/-! ## 5. Backward, uniform — the modulus-as-data closure (∅-axiom) -/

/-- A **uniform open-set witness** for `f`: a single `ω : Nat → Nat` such that
    at every scale `m` and point `x`, inputs within `1/2^(ω m)` of `x` map into
    the `m`-neighbourhood of `f x`.  This is the modulus carried *as data* (the
    Bishop / `HasModulus` move) — exactly the datum the choice wall forbids us
    to *extract* from the bare open-preimage hypothesis. -/
def UniformOpenWitness (MD : MetricModulus D) (MV : MetricModulus V)
    (f : D → V) (ω : Nat → Nat) : Prop :=
  ∀ m x y, MD.close (ω m) x y → nbhd MV (f x) m (f y)

/-- ★ **`preimage_dyadicopen_uniform_continuous_of_modulus`** — given a uniform
    open-set witness `ω` (modulus as data), `f` is uniformly continuous with
    that very `ω`.  Closes the backward direction at the uniform level
    *honestly*: ∅-axiom, with the modulus supplied rather than choice-extracted
    (mirrors `banach_fixed_point`'s computed-vs-assumed modulus). -/
theorem preimage_dyadicopen_uniform_continuous_of_modulus
    (MD : MetricModulus D) (MV : MetricModulus V) (f : D → V) (ω : Nat → Nat)
    (hω : UniformOpenWitness MD MV f ω) :
    ContinuousWithModulus MD MV f ω := by
  intro m x y hxy
  -- hω m x y hxy : nbhd MV (f x) m (f y) = ∃ k, ∀ w, close k (f y) w → close m (f x) w.
  obtain ⟨k, hk⟩ := hω m x y hxy
  exact hk (f y) (MV.crefl k (f y))

/-- The forward direction also supplies a uniform open-set witness, but **one
    output level finer**: from `ContinuousWithModulus MD MV f ω` we get a
    `UniformOpenWitness` at the shifted modulus `fun m => ω (m + 1)`.  The `+1`
    is not slack to be removed — it is the graduated metric's structural cost:
    the `nbhd` witness needs a halving-triangle (`ctri`) step, which consumes
    one refinement level.  (So `UniformOpenWitness` and `ContinuousWithModulus`
    are interderivable *up to a one-level output shift*, never verbatim — the
    same `+1`-budget that forbids open balls from being open at their own
    radius.) -/
theorem continuous_uniform_open_witness_shift
    (MD : MetricModulus D) (MV : MetricModulus V) (f : D → V) (ω : Nat → Nat)
    (hf : ContinuousWithModulus MD MV f ω) :
    UniformOpenWitness MD MV f (fun m => ω (m + 1)) := by
  intro m x y hxy
  -- continuity at the finer output level m+1: hxy : close (ω (m+1)) x y, so
  -- hf (m+1) gives close (m+1) (f x) (f y).
  have hfxfy : MV.close (m + 1) (f x) (f y) := hf (m + 1) x y hxy
  -- witness k = m+1: for w with close (m+1) (f y) w, halving triangle gives
  -- close m (f x) w.
  refine ⟨m + 1, ?_⟩
  intro w hyw
  exact MV.ctri m (f x) (f y) w hfxfy hyw
