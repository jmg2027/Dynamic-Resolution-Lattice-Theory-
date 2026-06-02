import E213.Lib.Math.Real213.RateModulus
import E213.Meta.Nat.PolyNat

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

`Dominates W d i` is the per-layer predicate "`W` stays below `d`'s growth quantum at
layer `i`".  The results:

  * ★★★ `htel_iff_dominates` — the rate certificate `Htel a d` holds **iff** every
    layer `i ≥ 1` is dominated.  This upgrades `Htel_of_crossdet` from an implication
    to a *characterization*: completability is exactly the W-vs-d comparison, read at
    every layer.  (`htel_layer_iff_dominates` is the single-layer biconditional.)
  * ★★ `dominated_free_modulus` — when every layer is dominated, the convergent
    presentation gets a total ∅-axiom modulus `N(m,k)=k+2` (via `rate_total_modulus`):
    domination everywhere ⟹ free completion.
  * ★★★ `overtake_breaks_layer` — conversely, *any* layer where `W` overtakes the
    denominator quantum (`(i+1)·d_{i+1} < W_i`) is **not** dominated: the margin
    increases there and the rate certificate breaks.  This is the abstract
    exponential-overtake boundary, negative direction — no measure, just the two-axis
    comparison flipping sign.

## The unimodular floor sits at the bottom

The det-1 floor (`DepthFloorDetOne`: the convergent cross-determinant of the P-orbit
is the constant `W ≡ 1`) is dominated at *every* layer against the denominator
`d_i = (i+1)(i+2)` (`floor_dominates_all`, the comparison collapses to `i ≤ i+2`).  So
`floor_carries_Htel`: any presentation whose cross-determinant is the unimodular floor
carries its own rate certificate unconditionally — the atomic `T = [[2,1],[1,1]]`
floor is the trivially-free bottom of the stratification, and the overtake regime is
the genuine content above it.

`tower_stratification` bundles the three facts: the floor is rate-carrying, domination
everywhere is exactly `Htel`, and overtake breaks any layer.

Narrative: `theory/math/analysis/holonomic_modulus.md` §4.

All zero-axiom.
-/

namespace E213.Lib.Math.Real213.RateStratification

open E213.Lib.Math.Real213.RateModulus (Htel rcut rate_total_modulus Htel_of_crossdet)
open E213.Meta.Nat.PolyNat (PE poly_id)
open E213.Tactic.NatHelper (add_mul mul_mul_mul_comm_213 le_of_add_le_add_left)

/-- The **free-modulus domination predicate** at layer `i`: the cross-determinant
    `W_i` stays below the denominator's discrete growth quantum.  This is exactly the
    per-layer content of `Htel_of_crossdet`'s smallness law. -/
def Dominates (W d : Nat → Nat) (i : Nat) : Prop :=
  i*(i+1)*W i + i*d i ≤ (i+1)*d (i+1)

variable {a d : Nat → Nat}

/-! ## §1 — the layer-by-layer characterization -/

/-- ★ **Single-layer biconditional.**  Given the cross-determinant relation `hW`, the
    `Htel` inequality at layer `i` holds **iff** layer `i` is dominated.  Both margin
    sides share the common term `i(i+1)·(a_i·d_{i+1})`; cancelling it leaves exactly
    the W-vs-d comparison. -/
theorem htel_layer_iff_dominates (W : Nat → Nat)
    (hW : ∀ i, a (i+1) * d i = a i * d (i+1) + W i) (i : Nat) :
    ((a (i+1)*(i+1)+1)*(i*d i) ≤ (a i*i+1)*((i+1)*d (i+1)))
      ↔ Dominates W d i := by
  have hLHS : (a (i+1)*(i+1)+1)*(i*d i) = i*(i+1)*(a (i+1)*d i) + i*d i := by
    rw [add_mul, Nat.one_mul]; congr 1
    rw [mul_mul_mul_comm_213, Nat.mul_comm (a (i+1)) i, ← mul_mul_mul_comm_213]
  have hRHS : (a i*i+1)*((i+1)*d (i+1)) = i*(i+1)*(a i*d (i+1)) + (i+1)*d (i+1) := by
    rw [add_mul, Nat.one_mul]; congr 1
    rw [mul_mul_mul_comm_213, Nat.mul_comm (a i) (i+1), mul_mul_mul_comm_213,
        Nat.mul_comm (i+1) i]
  have hLHSfull : (a (i+1)*(i+1)+1)*(i*d i)
      = i*(i+1)*(a i*d (i+1)) + (i*(i+1)*W i + i*d i) := by
    rw [hLHS, hW i, Nat.mul_add, Nat.add_assoc]
  constructor
  · intro h
    rw [hLHSfull, hRHS] at h
    exact le_of_add_le_add_left h
  · intro h
    rw [hLHSfull, hRHS]
    exact Nat.add_le_add_left h _

/-- ★★★ **The stratification characterization.**  The rate certificate `Htel a d`
    holds **iff** every layer `i ≥ 1` is dominated — completability is exactly the
    W-vs-d comparison read at every layer.  Upgrades `Htel_of_crossdet` (implication)
    to a biconditional. -/
theorem htel_iff_dominates (W : Nat → Nat)
    (hW : ∀ i, a (i+1) * d i = a i * d (i+1) + W i) :
    Htel a d ↔ ∀ i, 1 ≤ i → Dominates W d i := by
  constructor
  · intro h i hi; exact (htel_layer_iff_dominates W hW i).mp (h i hi)
  · intro h i hi; exact (htel_layer_iff_dominates W hW i).mpr (h i hi)

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

/-! ## §2 — the overtake boundary (negative direction) -/

/-- ★★★ **Overtake breaks the layer.**  If the cross-determinant overtakes the
    denominator quantum at layer `i ≥ 1` (`(i+1)·d_{i+1} < W_i`), that layer is
    **not** dominated: the margin increases there and the rate certificate fails.
    The `W`-axis crossing the `d`-axis is exactly the boundary where free completion
    breaks — no irrationality measure, just the two growth axes flipping order. -/
theorem overtake_breaks_layer (W : Nat → Nat) (i : Nat) (hi : 1 ≤ i)
    (hover : (i+1) * d (i+1) < W i) : ¬ Dominates W d i := by
  intro hdom
  have hpos : 0 < i * (i+1) := Nat.mul_pos hi (Nat.succ_pos i)
  have h2 : W i ≤ i*(i+1)*W i := Nat.le_mul_of_pos_left (W i) hpos
  have h3 : i*(i+1)*W i ≤ i*(i+1)*W i + i*d i := Nat.le_add_right _ _
  have hchain : (i+1) * d (i+1) < (i+1) * d (i+1) :=
    Nat.lt_of_lt_of_le hover (Nat.le_trans h2 (Nat.le_trans h3 hdom))
  exact Nat.lt_irrefl _ hchain

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

/-- ★★★ **Tower stratification capstone.**  The three facts of the W-vs-d comparison:

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

end E213.Lib.Math.Real213.RateStratification
