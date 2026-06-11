import E213.Lib.Math.NumberSystems.Real213.RateModulus
import E213.Meta.Nat.PolyNat
import E213.Meta.Nat.PolyNatMTactic

/-!
# RateStratification — completeness as a layer-by-layer growth-axis comparison

`RateModulus.Htel_of_crossdet` reduced the rate certificate `Htel` to a *smallness*
law on the cross-determinant `W_i = a_{i+1}·d_i − a_i·d_{i+1}`:

    i(i+1)·W_i + i·d_i ≤ (i+1)·d_{i+1}.

That smallness law is a comparison of **two tower-internal growth axes** — the
cross-determinant `W` (the divergence ladder's central object) against the
denominator `d`'s discrete growth quantum.  This file makes the comparison the
primitive object and reads completeness off it *layer by layer*, with no irrationality
measure, no LEM, no quantification over "all reals" — only trajectories and their
coordinates, the tower-native reframing of completeness.

## The stratification

`DominatesS W d ρ i` is the per-layer predicate "`W` stays below `d`'s growth
quantum at layer `i`, measured under the probe schedule `ρ`" — the ladder note's
`Dominates_s`; `Dominates W d i` is its identity-schedule (degree-1) instance.
The results:

  * ★★★ `htelS_iff_dominatesS` — the graded rate certificate `HtelS a d ρ` holds
    **iff** every layer `i ≥ 1` is `ρ`-dominated, for *any* schedule; the binary
    `htel_iff_dominates` is the `ρ = id` instance.  Completability is exactly the
    W-vs-d comparison, read at every layer, at every grade.
  * ★★ `dominated_free_modulus` / `dominatedS_graded_modulus` — domination
    everywhere yields the constructed total modulus: `N(m,k) = k+2` at the
    identity schedule, `N(m,k) = k^s + 1` at the degree-`s` root schedule (via
    `RateModulus.graded_total_modulus`).
  * ★★★ `overtakeS_breaks_layer` — conversely, any layer where `W` overtakes the
    scheduled denominator quantum (`ρ_{i+1}·d_{i+1} < W_i`) is **not** dominated:
    the margin increases there and the certificate breaks.  The abstract
    exponential-overtake boundary, negative direction, at every grade.
  * ★★★ `sep_dominatesS_all` / `sep_breaks_unit_schedule` — **the grading is
    strict**: the presentation `d_{i+1} = (⌊√i⌋+2)·d_i` with `W = d` fails
    `Dominates` at layer 4 yet is root-2-dominated at *every* layer.  The
    degree-2 schedule rescues what the degree-1 schedule breaks; "rescue" is
    graded the way `CompletabilityGrade` grades "break", and the two axes are
    symmetric.
  * ★★★ `sep_graded_modulus` — the rescue end to end: `sepNum/sepDen` (the
    numerators `a_{i+1} = (⌊√i⌋+2)·a_i + 1` realize the cross-det `W = d`
    exactly) completes through the degree-2 schedule with the constructed
    total modulus `N(m,k) = k² + 1` — an actual real outside the degree-1
    class, carried by the graded generator.

## The unimodular floor sits at the bottom

The det-1 floor (`DepthFloorDetOne`: the convergent cross-determinant of the P-orbit
is the constant `W ≡ 1`) is dominated at *every* layer against the denominator
`d_i = (i+1)(i+2)` (`floor_dominates_all`, the comparison collapses to `i ≤ i+2`).  So
`floor_carries_Htel`: any presentation whose cross-determinant is the unimodular floor
carries its own rate certificate unconditionally — the atomic `T = [[2,1],[1,1]]`
floor is the trivially-free bottom of the stratification, and the overtake regime is
the genuine content above it.

`tower_stratification` bundles the degree-1 facts; `graded_stratification` bundles
the graded characterization with the strict-separation witness.

Narrative: `theory/math/analysis/holonomic_modulus.md` §4.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.RateStratification

open E213.Lib.Math.NumberSystems.Real213.RateModulus
  (Htel HtelS rcut rate_total_modulus graded_total_modulus Htel_of_crossdet
   hmono_of_hmonoS)
open E213.Meta.Nat.PolyNat (PE poly_id)
open E213.Meta.Nat.RootFloor (rootFloor rootFloor_mono)
open E213.Tactic.NatHelper
  (add_mul mul_assoc mul_mul_mul_comm_213 le_of_add_le_add_left le_of_mul_le_mul_right)

/-- The **scheduled domination predicate** at layer `i`: the cross-determinant
    `W_i` stays below the denominator's growth quantum, measured under the probe
    schedule `ρ` — the per-layer content of the graded rate certificate
    (`Dominates_s` of the modulus-degree ladder). -/
def DominatesS (W d ρ : Nat → Nat) (i : Nat) : Prop :=
  ρ i * ρ (i+1) * W i + ρ i * d i ≤ ρ (i+1) * d (i+1)

/-- The identity-schedule domination predicate — `DominatesS` at `ρ = id`,
    exactly the per-layer content of `Htel_of_crossdet`'s smallness law. -/
def Dominates (W d : Nat → Nat) (i : Nat) : Prop :=
  i*(i+1)*W i + i*d i ≤ (i+1)*d (i+1)

variable {a d ρ : Nat → Nat}

/-! ## §1 — the layer-by-layer characterization -/

/-- ★ **Single-layer biconditional, any schedule.**  Given the cross-determinant
    relation `hW`, the `HtelS` inequality at layer `i` holds **iff** layer `i` is
    `ρ`-dominated.  Both margin sides share the common term
    `ρ_i·ρ_{i+1}·(a_i·d_{i+1})`; cancelling it leaves exactly the W-vs-d
    comparison. -/
theorem htelS_layer_iff_dominatesS (W : Nat → Nat)
    (hW : ∀ i, a (i+1) * d i = a i * d (i+1) + W i) (i : Nat) :
    ((a (i+1)*ρ (i+1)+1)*(ρ i*d i) ≤ (a i*ρ i+1)*(ρ (i+1)*d (i+1)))
      ↔ DominatesS W d ρ i := by
  have hLHS : (a (i+1)*ρ (i+1)+1)*(ρ i*d i)
      = ρ i*ρ (i+1)*(a (i+1)*d i) + ρ i*d i := by
    rw [add_mul, Nat.one_mul]; congr 1
    rw [mul_mul_mul_comm_213, Nat.mul_comm (a (i+1)) (ρ i), ← mul_mul_mul_comm_213]
  have hRHS : (a i*ρ i+1)*(ρ (i+1)*d (i+1))
      = ρ i*ρ (i+1)*(a i*d (i+1)) + ρ (i+1)*d (i+1) := by
    rw [add_mul, Nat.one_mul]; congr 1
    rw [mul_mul_mul_comm_213, Nat.mul_comm (a i) (ρ (i+1)), mul_mul_mul_comm_213,
        Nat.mul_comm (ρ (i+1)) (ρ i)]
  have hLHSfull : (a (i+1)*ρ (i+1)+1)*(ρ i*d i)
      = ρ i*ρ (i+1)*(a i*d (i+1)) + (ρ i*ρ (i+1)*W i + ρ i*d i) := by
    rw [hLHS, hW i, Nat.mul_add, Nat.add_assoc]
  constructor
  · intro h
    rw [hLHSfull, hRHS] at h
    exact le_of_add_le_add_left h
  · intro h
    rw [hLHSfull, hRHS]
    exact Nat.add_le_add_left h _

/-- ★ Single-layer biconditional at the identity schedule. -/
theorem htel_layer_iff_dominates (W : Nat → Nat)
    (hW : ∀ i, a (i+1) * d i = a i * d (i+1) + W i) (i : Nat) :
    ((a (i+1)*(i+1)+1)*(i*d i) ≤ (a i*i+1)*((i+1)*d (i+1)))
      ↔ Dominates W d i :=
  htelS_layer_iff_dominatesS (ρ := fun n => n) W hW i

/-- ★★★ **The graded stratification characterization.**  The rate certificate
    `HtelS a d ρ` holds **iff** every layer `i ≥ 1` is `ρ`-dominated —
    completability is exactly the W-vs-d comparison read at every layer, at
    every grade. -/
theorem htelS_iff_dominatesS (W : Nat → Nat)
    (hW : ∀ i, a (i+1) * d i = a i * d (i+1) + W i) :
    HtelS a d ρ ↔ ∀ i, 1 ≤ i → DominatesS W d ρ i := by
  constructor
  · intro h i hi; exact (htelS_layer_iff_dominatesS W hW i).mp (h i hi)
  · intro h i hi; exact (htelS_layer_iff_dominatesS W hW i).mpr (h i hi)

/-- ★★★ The stratification characterization at the identity schedule: `Htel a d`
    holds **iff** every layer `i ≥ 1` is dominated.  Upgrades `Htel_of_crossdet`
    (implication) to a biconditional. -/
theorem htel_iff_dominates (W : Nat → Nat)
    (hW : ∀ i, a (i+1) * d i = a i * d (i+1) + W i) :
    Htel a d ↔ ∀ i, 1 ≤ i → Dominates W d i :=
  htelS_iff_dominatesS (ρ := fun n => n) W hW

/-- Domination at every layer yields the rate certificate (the convenient forward
    direction; definitionally `Htel_of_crossdet`). -/
theorem htel_of_dominates_all (W : Nat → Nat)
    (hW : ∀ i, a (i+1) * d i = a i * d (i+1) + W i)
    (hdom : ∀ i, 1 ≤ i → Dominates W d i) : Htel a d :=
  Htel_of_crossdet W hW hdom

/-- ★★ **Domination everywhere ⟹ free completion.**  A monotone convergent
    presentation whose every layer is dominated has a total ∅-axiom modulus
    `N(m,k)=k+2`. -/
theorem dominated_free_modulus (W : Nat → Nat)
    (hd : ∀ i, 1 ≤ d i)
    (hW : ∀ i, a (i+1) * d i = a i * d (i+1) + W i)
    (hdom : ∀ i, 1 ≤ i → Dominates W d i)
    (hmono : ∀ N i, N ≤ i → a N * d i ≤ a i * d N)
    (hmonoS : ∀ i, a i * d (i+1) < a (i+1) * d i)
    (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N → rcut a d i m k = rcut a d j m k :=
  rate_total_modulus hd (htel_of_dominates_all W hW hdom) hmono hmonoS m k hk

/-- ★★ **Scheduled domination everywhere ⟹ graded completion.**  A monotone
    convergent presentation whose every layer is dominated under the degree-`s`
    root schedule has a total ∅-axiom modulus `N(m,k) = k^s + 1` — the graded
    rescue: a bigger cross-determinant is forgiven, a deeper modulus is paid. -/
theorem dominatedS_graded_modulus (s : Nat) (hs : 1 ≤ s) (W : Nat → Nat)
    (hd : ∀ i, 1 ≤ d i)
    (hW : ∀ i, a (i+1) * d i = a i * d (i+1) + W i)
    (hdom : ∀ i, 1 ≤ i → DominatesS W d (rootFloor s) i)
    (hmono : ∀ N i, N ≤ i → a N * d i ≤ a i * d N)
    (hmonoS : ∀ i, a i * d (i+1) < a (i+1) * d i)
    (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N → rcut a d i m k = rcut a d j m k :=
  graded_total_modulus s hs hd
    ((htelS_iff_dominatesS W hW).mpr hdom) hmono hmonoS m k hk

/-! ## §2 — the overtake boundary (negative direction) -/

/-- ★★★ **Overtake breaks the layer, any schedule.**  If the cross-determinant
    overtakes the scheduled denominator quantum at layer `i`
    (`ρ_{i+1}·d_{i+1} < W_i`, schedule positive there), that layer is **not**
    `ρ`-dominated: the margin increases there and the certificate fails.  The
    `W`-axis crossing the scheduled `d`-axis is exactly the boundary where the
    graded completion breaks. -/
theorem overtakeS_breaks_layer (W : Nat → Nat) (i : Nat)
    (hρi : 1 ≤ ρ i) (hρi1 : 1 ≤ ρ (i+1))
    (hover : ρ (i+1) * d (i+1) < W i) : ¬ DominatesS W d ρ i := by
  intro hdom
  have hpos : 0 < ρ i * ρ (i+1) := Nat.mul_pos hρi hρi1
  have h2 : W i ≤ ρ i*ρ (i+1)*W i := Nat.le_mul_of_pos_left (W i) hpos
  have h3 : ρ i*ρ (i+1)*W i ≤ ρ i*ρ (i+1)*W i + ρ i*d i := Nat.le_add_right _ _
  have hchain : ρ (i+1) * d (i+1) < ρ (i+1) * d (i+1) :=
    Nat.lt_of_lt_of_le hover (Nat.le_trans h2 (Nat.le_trans h3 hdom))
  exact Nat.lt_irrefl _ hchain

/-- ★★★ Overtake breaks the layer, identity schedule. -/
theorem overtake_breaks_layer (W : Nat → Nat) (i : Nat) (hi : 1 ≤ i)
    (hover : (i+1) * d (i+1) < W i) : ¬ Dominates W d i :=
  overtakeS_breaks_layer (ρ := fun n => n) W i hi
    (Nat.succ_le_succ (Nat.zero_le i)) hover

/-! ## §3 — the unimodular floor is the trivially-free bottom -/

/-- The det-1 floor's cross-determinant: the constant `W ≡ 1` (`DepthFloorDetOne`:
    the P-orbit's convergent cross-determinant is the unimodular invariant). -/
def floorW : Nat → Nat := fun _ => 1

/-- A denominator that dominates the unimodular floor at every layer: `d_i =
    (i+1)(i+2)`.  Positive everywhere, and the comparison collapses to `i ≤ i+2`. -/
def floorDen : Nat → Nat := fun i => (i+1)*(i+2)

/-- `floorDen` is positive everywhere (`(i+1)(i+2) ≥ 1`). -/
theorem floorDen_pos (i : Nat) : 1 ≤ floorDen i :=
  Nat.mul_pos (Nat.succ_pos i) (Nat.succ_pos (i+1))

/-- ★★ **The unimodular floor is dominated at every layer.**  With `W ≡ 1` and
    `d_i = (i+1)(i+2)`, the smallness law `i(i+1)·1 + i·d_i ≤ (i+1)·d_{i+1}` becomes
    `(i+1)(i+2)(i+3) = [i(i+1) + i(i+1)(i+2)] + 2(i+1)(i+3)`, i.e. the comparison
    collapses to `i ≤ i+2`.  (The polynomial identity is discharged by the `PolyNat`
    reflection ring.) -/
theorem floor_dominates_all (i : Nat) : Dominates floorW floorDen i := by
  show i*(i+1)*1 + i*((i+1)*(i+2)) ≤ (i+1)*((i+2)*(i+3))
  have heq : (i+1)*((i+2)*(i+3))
      = (i*(i+1)*1 + i*((i+1)*(i+2))) + 2*(i+1)*(i+3) :=
    poly_id
      (.mul (.add .X (.C 1)) (.mul (.add .X (.C 2)) (.add .X (.C 3))))
      (.add (.add (.mul (.mul .X (.add .X (.C 1))) (.C 1))
                  (.mul .X (.mul (.add .X (.C 1)) (.add .X (.C 2)))))
            (.mul (.mul (.C 2) (.add .X (.C 1))) (.add .X (.C 3))))
      rfl i
  rw [heq]; exact Nat.le_add_right _ _

/-- ★★★ **The floor carries its own rate certificate.**  Any convergent presentation
    whose cross-determinant against `floorDen` is the unimodular floor (`W ≡ 1`)
    satisfies `Htel` unconditionally — the atomic `T = [[2,1],[1,1]]` det-1 floor is
    the trivially-free bottom of the stratification. -/
theorem floor_carries_Htel
    (hW : ∀ i, a (i+1) * floorDen i = a i * floorDen (i+1) + 1) : Htel a floorDen :=
  htel_of_dominates_all floorW hW (fun i _ => floor_dominates_all i)

/-! ## §4 — the grading is strict: a root-2 rescue the identity schedule breaks -/

/-- The schedule-separation denominator: `d_{i+1} = (⌊√i⌋ + 2)·d_i`, paired with
    the cross-determinant `W = d` itself — growth tuned so the root-2 schedule's
    per-layer budget just absorbs it. -/
def sepDen : Nat → Nat
  | 0 => 1
  | i+1 => (rootFloor 2 i + 2) * sepDen i

/-- ★★★ **The root-2 schedule rescues `sepDen`.**  With `W = d = sepDen`, every
    layer is dominated under `ρ = rootFloor 2`: the comparison reduces to
    `⌊√i⌋ ≤ 2·⌊√(i+1)⌋`, which monotonicity of the root supplies. -/
theorem sep_dominatesS_all (i : Nat) : DominatesS sepDen sepDen (rootFloor 2) i := by
  show rootFloor 2 i * rootFloor 2 (i+1) * sepDen i + rootFloor 2 i * sepDen i
      ≤ rootFloor 2 (i+1) * sepDen (i+1)
  have hmono : rootFloor 2 i ≤ rootFloor 2 (i+1) := rootFloor_mono 2 (Nat.le_succ i)
  have hcoef : rootFloor 2 i * rootFloor 2 (i+1) + rootFloor 2 i
      ≤ rootFloor 2 (i+1) * (rootFloor 2 i + 2) := by
    rw [Nat.mul_add, Nat.mul_comm (rootFloor 2 (i+1)) (rootFloor 2 i)]
    exact Nat.add_le_add_left
      (Nat.le_trans hmono (by rw [Nat.mul_two]; exact Nat.le_add_right _ _)) _
  calc rootFloor 2 i * rootFloor 2 (i+1) * sepDen i + rootFloor 2 i * sepDen i
      = (rootFloor 2 i * rootFloor 2 (i+1) + rootFloor 2 i) * sepDen i :=
        (add_mul _ _ _).symm
    _ ≤ (rootFloor 2 (i+1) * (rootFloor 2 i + 2)) * sepDen i :=
        Nat.mul_le_mul_right _ hcoef
    _ = rootFloor 2 (i+1) * ((rootFloor 2 i + 2) * sepDen i) := mul_assoc _ _ _
    _ = rootFloor 2 (i+1) * sepDen (i+1) := rfl

/-- ★★★ **The identity schedule breaks `sepDen`.**  At layer 4 the unscheduled
    comparison `4·5·W_4 + 4·d_4 ≤ 5·d_5` reads `1296 ≤ 1080` — overtake.
    Together with `sep_dominatesS_all` this separates the grades: the degree-2
    rescue is strictly larger than the degree-1 rescue. -/
theorem sep_breaks_unit_schedule : ¬ Dominates sepDen sepDen 4 := by
  intro h
  have h' : 4*(4+1)*sepDen 4 + 4*sepDen 4 ≤ (4+1)*sepDen (4+1) := h
  exact absurd h' (by decide)

/-- The convergent numerators realizing `sepDen` as an actual presentation:
    `a_{i+1} = (⌊√i⌋+2)·a_i + 1` makes the cross-determinant exactly `sepDen`
    (no division — the recurrence is the cross-det relation solved over ℕ). -/
def sepNum : Nat → Nat
  | 0 => 0
  | i+1 => (rootFloor 2 i + 2) * sepNum i + 1

theorem sepDen_pos (i : Nat) : 1 ≤ sepDen i := by
  induction i with
  | zero => exact Nat.le_refl 1
  | succ i ih =>
    exact Nat.mul_pos (Nat.succ_le_succ (Nat.zero_le _)) ih

/-- The presentation's cross-determinant is `sepDen` itself (`W = d`). -/
theorem sep_cross_det (i : Nat) :
    sepNum (i+1) * sepDen i = sepNum i * sepDen (i+1) + sepDen i := by
  show ((rootFloor 2 i + 2) * sepNum i + 1) * sepDen i
      = sepNum i * ((rootFloor 2 i + 2) * sepDen i) + sepDen i
  rw [add_mul, Nat.one_mul, ← mul_assoc, Nat.mul_comm (sepNum i) (rootFloor 2 i + 2)]

/-- The convergents are strictly increasing (the cross-det is positive). -/
theorem sep_hmonoS (i : Nat) : sepNum i * sepDen (i+1) < sepNum (i+1) * sepDen i := by
  rw [sep_cross_det i]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.add_le_add_left (sepDen_pos i) _)

/-- ★★★ **An actual real rescued at degree 2.**  The presentation
    `sepNum/sepDen` — whose identity-schedule certificate is *broken*
    (`sep_breaks_unit_schedule`) — completes through the degree-2 root schedule
    with the constructed total ∅-axiom modulus `N(m,k) = k² + 1`: the graded
    generator, end to end, on a witness outside the degree-1 class. -/
theorem sep_graded_modulus (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N →
      rcut sepNum sepDen i m k = rcut sepNum sepDen j m k :=
  dominatedS_graded_modulus 2 (Nat.le_succ 1) sepDen sepDen_pos sep_cross_det
    (fun i _ => sep_dominatesS_all i)
    (hmono_of_hmonoS sepDen_pos sep_hmonoS) sep_hmonoS m k hk

/-! ## §5 — the schedule comparison law (the order structure on the ladder) -/

private theorem rearrange (a b x y : Nat) (hab : a ≤ b) (hxy : x ≤ y) :
    a*y + b*x ≤ a*x + b*y := by
  obtain ⟨u, hu⟩ := Nat.le.dest hab
  obtain ⟨v, hv⟩ := Nat.le.dest hxy
  subst hu; subst hv
  have hid : a*x + (a+u)*(x+v) = (a*(x+v) + (a+u)*x) + u*v := by ring_nat
  rw [hid]
  exact Nat.le_add_right _ _

/-- ★★ **Schedule comparison, sufficient condition.**  A slower schedule `ρ'`
    inherits domination at layer `i` from `ρ` when (1) the denominator does not
    shrink (`d_i ≤ d_{i+1}`), (2) `ρ'_i ≤ ρ_i`, and (3) the **gap law** holds —
    the slack difference `1/ρ' − 1/ρ` is non-increasing across the layer,
    cross-multiplied:

        ρ'_i·ρ'_{i+1}·ρ_{i+1} + ρ'_i·ρ_i·ρ_{i+1} ≤ ρ_i·ρ'_{i+1}·ρ_{i+1} + ρ'_i·ρ_i·ρ'_{i+1}.

    The gap law is the genuine content: `schedule_comparison_needs_gap` shows
    (1)+(2) alone do **not** suffice — pointwise, the ladder is *not* a chain;
    rungs are independent comparisons, ordered only where the gap law holds. -/
theorem dominatesS_schedule_mono (W : Nat → Nat) {ρ' : Nat → Nat} (i : Nat)
    (hρi : 1 ≤ ρ i) (hρi1 : 1 ≤ ρ (i+1))
    (hd : d i ≤ d (i+1)) (h1 : ρ' i ≤ ρ i)
    (hgap : ρ' i * ρ' (i+1) * ρ (i+1) + ρ' i * ρ i * ρ (i+1)
      ≤ ρ i * ρ' (i+1) * ρ (i+1) + ρ' i * ρ i * ρ' (i+1))
    (hdom : DominatesS W d ρ i) : DominatesS W d ρ' i := by
  -- A1: (d_{i+1} − d_i)·(ρ_i − ρ'_i) ≥ 0, cleared and ×(ρ'_{i+1}·ρ_{i+1})
  have hxy : ρ' i * (ρ' (i+1) * ρ (i+1)) ≤ ρ i * (ρ' (i+1) * ρ (i+1)) :=
    Nat.mul_le_mul_right _ h1
  have hA1 : d i * (ρ i * (ρ' (i+1) * ρ (i+1))) + d (i+1) * (ρ' i * (ρ' (i+1) * ρ (i+1)))
      ≤ d i * (ρ' i * (ρ' (i+1) * ρ (i+1))) + d (i+1) * (ρ i * (ρ' (i+1) * ρ (i+1))) :=
    rearrange (d i) (d (i+1)) _ _ hd hxy
  -- A2: the gap law × d_i
  have hA2 : d i * (ρ' i * ρ' (i+1) * ρ (i+1) + ρ' i * ρ i * ρ (i+1))
      ≤ d i * (ρ i * ρ' (i+1) * ρ (i+1) + ρ' i * ρ i * ρ' (i+1)) :=
    Nat.mul_le_mul_left _ hgap
  -- (★): B' + C ≤ C' + B, by summing A1 + A2 and cancelling the common junk J
  have hsum := Nat.add_le_add hA1 hA2
  have hstar : (ρ i * ρ (i+1)) * (ρ' i * d i) + ρ' i * ρ' (i+1) * (ρ (i+1) * d (i+1))
      ≤ (ρ i * ρ (i+1)) * (ρ' (i+1) * d (i+1)) + ρ' i * ρ' (i+1) * (ρ i * d i) := by
    have eL : d i * (ρ i * (ρ' (i+1) * ρ (i+1))) + d (i+1) * (ρ' i * (ρ' (i+1) * ρ (i+1)))
        + d i * (ρ' i * ρ' (i+1) * ρ (i+1) + ρ' i * ρ i * ρ (i+1))
        = (d i * (ρ i * (ρ' (i+1) * ρ (i+1))) + d i * (ρ' i * (ρ' (i+1) * ρ (i+1))))
          + ((ρ i * ρ (i+1)) * (ρ' i * d i)
              + ρ' i * ρ' (i+1) * (ρ (i+1) * d (i+1))) := by ring_nat
    have eR : d i * (ρ' i * (ρ' (i+1) * ρ (i+1))) + d (i+1) * (ρ i * (ρ' (i+1) * ρ (i+1)))
        + d i * (ρ i * ρ' (i+1) * ρ (i+1) + ρ' i * ρ i * ρ' (i+1))
        = (d i * (ρ i * (ρ' (i+1) * ρ (i+1))) + d i * (ρ' i * (ρ' (i+1) * ρ (i+1))))
          + ((ρ i * ρ (i+1)) * (ρ' (i+1) * d (i+1))
              + ρ' i * ρ' (i+1) * (ρ i * d i)) := by ring_nat
    rw [eL, eR] at hsum
    exact le_of_add_le_add_left hsum
  -- assemble: G′ = hdom × (ρ'_i·ρ'_{i+1}), then cancel C and divide by ρ_i·ρ_{i+1}
  have hG' : ρ' i * ρ' (i+1) * (ρ i * ρ (i+1) * W i + ρ i * d i)
      ≤ ρ' i * ρ' (i+1) * (ρ (i+1) * d (i+1)) :=
    Nat.mul_le_mul_left _ hdom
  have hfinal : (ρ' i * ρ' (i+1) * W i + ρ' i * d i) * (ρ i * ρ (i+1))
      ≤ (ρ' (i+1) * d (i+1)) * (ρ i * ρ (i+1)) := by
    have key : (ρ' i * ρ' (i+1) * (ρ (i+1) * d (i+1)) + ρ' i * ρ' (i+1) * (ρ i * d i))
        + (ρ' i * ρ' (i+1) * W i + ρ' i * d i) * (ρ i * ρ (i+1))
        ≤ (ρ' i * ρ' (i+1) * (ρ (i+1) * d (i+1)) + ρ' i * ρ' (i+1) * (ρ i * d i))
        + (ρ' (i+1) * d (i+1)) * (ρ i * ρ (i+1)) := by
      have eL' : (ρ' i * ρ' (i+1) * (ρ (i+1) * d (i+1)) + ρ' i * ρ' (i+1) * (ρ i * d i))
          + (ρ' i * ρ' (i+1) * W i + ρ' i * d i) * (ρ i * ρ (i+1))
          = ρ' i * ρ' (i+1) * (ρ i * ρ (i+1) * W i + ρ i * d i)
            + ((ρ i * ρ (i+1)) * (ρ' i * d i)
                + ρ' i * ρ' (i+1) * (ρ (i+1) * d (i+1))) := by ring_nat
      have eR' : (ρ' i * ρ' (i+1) * (ρ (i+1) * d (i+1)) + ρ' i * ρ' (i+1) * (ρ i * d i))
          + (ρ' (i+1) * d (i+1)) * (ρ i * ρ (i+1))
          = ρ' i * ρ' (i+1) * (ρ (i+1) * d (i+1))
            + ((ρ i * ρ (i+1)) * (ρ' (i+1) * d (i+1))
                + ρ' i * ρ' (i+1) * (ρ i * d i)) := by ring_nat
      rw [eL', eR']
      exact Nat.add_le_add hG' hstar
    exact le_of_add_le_add_left key
  exact le_of_mul_le_mul_right (Nat.mul_pos hρi hρi1) hfinal

/-- ★★ **The gap law is not dispensable**: with `W ≡ 1`, `d ≡ 6` at layer 2,
    the identity schedule dominates (`18 ≤ 18`) while the root-2 schedule does
    not (`7 ≤ 6` fails) — even though the denominator is non-decreasing and the
    root schedule is pointwise slower.  Pointwise, rung 1 does not imply
    rung 2: the schedule axis is a genuine new dial, not a refinement chain. -/
theorem schedule_comparison_needs_gap :
    Dominates (fun _ => 1) (fun _ => 6) 2
    ∧ ¬ DominatesS (fun _ => 1) (fun _ => 6) (rootFloor 2) 2 := by
  constructor
  · show 2*(2+1)*1 + 2*6 ≤ (2+1)*6
    decide
  · intro h
    have h' : rootFloor 2 2 * rootFloor 2 (2+1) * 1 + rootFloor 2 2 * 6
        ≤ rootFloor 2 (2+1) * 6 := h
    exact absurd h' (by decide)

/-! ## §6 — capstones -/

/-- ★★★ **Tower stratification capstone (degree 1).**  The three facts of the
    W-vs-d comparison:

    1. the unimodular det-1 floor (`W ≡ 1`) is rate-carrying for any presentation
       (the trivially-free bottom);
    2. the rate certificate `Htel a d` is *exactly* domination at every layer (given
       the cross-determinant `W`);
    3. any layer where `W` overtakes the denominator quantum breaks domination
       (the boundary).

    Completability is a stratified comparison of two tower-internal growth axes, not a
    yes/no fact about individual reals. -/
theorem tower_stratification :
    (∀ a : Nat → Nat,
        (∀ i, a (i+1) * floorDen i = a i * floorDen (i+1) + 1) → Htel a floorDen)
    ∧ (∀ (a d W : Nat → Nat), (∀ i, a (i+1) * d i = a i * d (i+1) + W i) →
        (Htel a d ↔ ∀ i, 1 ≤ i → Dominates W d i))
    ∧ (∀ (d W : Nat → Nat) (i : Nat), 1 ≤ i → (i+1) * d (i+1) < W i →
        ¬ Dominates W d i) :=
  ⟨fun _ hW => floor_carries_Htel hW,
   fun _ _ W hW => htel_iff_dominates W hW,
   fun _ W i hi hover => overtake_breaks_layer W i hi hover⟩

/-- ★★★ **Graded stratification capstone.**  The schedule axis is real:

    1. at *every* schedule `ρ`, the graded certificate is exactly per-layer
       scheduled domination;
    2. the root-2 schedule dominates `sepDen` at every layer — rescue;
    3. the identity schedule breaks `sepDen` at layer 4 — the same presentation,
       one grade down, overtakes.

    "Completes" is not refined by a single binary comparison but by a ladder of
    them, one per probe schedule; the modulus degree is the price of the rung. -/
theorem graded_stratification :
    (∀ (a d W ρ : Nat → Nat), (∀ i, a (i+1) * d i = a i * d (i+1) + W i) →
        (HtelS a d ρ ↔ ∀ i, 1 ≤ i → DominatesS W d ρ i))
    ∧ (∀ i, DominatesS sepDen sepDen (rootFloor 2) i)
    ∧ ¬ Dominates sepDen sepDen 4 :=
  ⟨fun _ _ W ρ hW => htelS_iff_dominatesS (ρ := ρ) W hW,
   sep_dominatesS_all,
   sep_breaks_unit_schedule⟩

end E213.Lib.Math.NumberSystems.Real213.RateStratification
