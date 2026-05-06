import E213.Math.Infinity.Countable
import E213.Kernel.Tactic.Nat213
import E213.Math.Infinity.Cantor
import E213.Math.Infinity.Godel
import E213.HypervisorCore
import E213.Hypervisor.Characterisation.Catalog
import E213.Hypervisor.Instances.Bool
import E213.Hypervisor.Instances.Parity
import E213.Hypervisor.Instances.Max
import E213.Prelude

/-!
# Infinity.LensCardinality: Σ4 — Lens-image cardinalities

**What different Lens choices extract from the same Raw.**

Image-cardinality data for the catalogue Lenses, formalised as
surjectivity / image-characterisation theorems:

| Lens           | Image                   | Class                     |
|----------------|-------------------------|---------------------------|
| `boolAndLens`  | `{true}`                | cardinality 1             |
| `boolOrLens`   | `{true}`                | cardinality 1             |
| `parityLens`   | `{true, false}`         | cardinality 2             |
| `maxLens`      | `{0, 1}`                | cardinality 2             |
| `Lens.leaves`  | `{n : ℕ | n ≥ 1}`       | countably infinite        |
| `Lens.depth`   | `ℕ`                     | countably infinite        |
| `signedLens`   | contains `{-1, 0, 1, …}`| countably infinite        |
| *(higher)*     | up to Cantor tower      | uncountable (via Tower)   |

The **same Raw** — an axiom-level object that makes no
cardinality claim — supplies images of cardinality 1, 2, ℕ,
and, when lifted to `Raw → Bool` and beyond, arbitrarily
high through the Cantor tower (`Infinity.Tower`).  This is
the precise content of "cardinality is Lens-output".
-/

namespace E213.Infinity

open E213.Firmware E213.Hypervisor

-- ═══ leaves surjective onto ℕ≥1 ═══

theorem leaves_surjective_pos :
    ∀ n : Nat, 1 ≤ n → ∃ r : Raw, Lens.leaves.view r = n := by
  intro n hn
  have ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
    have h := E213.Tactic.Nat213.add_sub_of_le hn
    rw [Nat.add_comm 1 (n - 1)] at h
    exact h.symm⟩
  refine ⟨rawTower m, ?_⟩
  show Raw.fold 1 1 (· + ·) (rawTower m) = n
  rw [Raw.fold_eq_leaves, rawTower_leaves, hm]

end E213.Infinity

namespace E213.Firmware.Internal

/-- Depth of the tree tower: equals `n` at every level. -/
theorem treeTower_depth : ∀ n, (treeTower n).depth = n := by
  intro n; induction n with
  | zero => rfl
  | succ m ih =>
      show (Tree.slash Tree.a (treeTower m)).depth = m + 1
      show 1 + Nat.max Tree.a.depth (treeTower m).depth = m + 1
      rw [ih]
      show 1 + Nat.max 0 m = m + 1
      have hzm : Nat.max 0 m = m := Nat.zero_max m
      rw [hzm, Nat.add_comm 1 m]

end E213.Firmware.Internal

namespace E213.Infinity

open E213.Firmware E213.Firmware.Internal E213.Hypervisor

-- ═══ depth surjective onto ℕ ═══

theorem depth_surjective :
    ∀ n : Nat, ∃ r : Raw, Lens.depth.view r = n := by
  intro n
  refine ⟨rawTower n, ?_⟩
  show Raw.fold 0 0 (fun a b => 1 + Nat.max a b) (rawTower n) = n
  rw [Raw.fold_eq_depth]
  exact treeTower_depth n

end E213.Infinity

namespace E213.Infinity

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Instances.Bool
open E213.Hypervisor.Instances.Parity
open E213.Hypervisor.Instances.Max
open E213.Hypervisor.Characterisation.Catalog

-- ═══ Finite-image Lenses ═══

/-- **`boolAndLens` image = `{true}`**: the view is constantly
    `true` on every Raw.  Already proved in
    `Meta.BoolLens.boolAndLens_view_const`. -/
theorem boolAndLens_image :
    ∀ r : Raw, boolAndLens.view r = true := boolAndLens_view_const

/-- **`boolOrLens` image = `{true}`**. -/
theorem boolOrLens_image :
    ∀ r : Raw, boolOrLens.view r = true := boolOrLens_view_const

/-- **`parityLens` image covers both booleans.** -/
theorem parityLens_image_true : ∃ r : Raw, parityLens.view r = true :=
  ⟨Raw.a, rfl⟩

theorem parityLens_image_false : ∃ r : Raw, parityLens.view r = false :=
  ⟨parityLens_sample_even, parityLens_sample_even_view⟩

/-- **`maxLens` image covers both 0 and 1.** -/
theorem maxLens_image_zero : ∃ r : Raw, maxLens.view r = 0 :=
  ⟨Raw.a, rfl⟩

theorem maxLens_image_one : ∃ r : Raw, maxLens.view r = 1 :=
  ⟨Raw.b, rfl⟩

/-- **`maxLens` image is contained in `{0, 1}`.**  Since base
    values are 0,1 and `max` preserves this set. -/
theorem maxLens_image_binary :
    ∀ r : Raw, maxLens.view r = 0 ∨ maxLens.view r = 1 := by
  intro r
  show Raw.fold 0 1 max r = 0 ∨ Raw.fold 0 1 max r = 1
  induction r using Raw.rec with
  | a => left; rfl
  | b => right; rfl
  | slash x y h ihx ihy =>
      rw [Raw.fold_slash _ _ _
           (fun u v => by show max u v = max v u; omega) x y h]
      rcases ihx with hx | hx <;> rcases ihy with hy | hy <;>
        rw [hx, hy] <;> decide

end E213.Infinity

namespace E213.Firmware.Internal

/-- Signed-view of the tree tower: `view(treeTower n) = n - 1`
    as an Int.  tower_0 = Tree.b → -1; each slash adds `1`. -/
theorem treeTower_signed :
    ∀ n, Tree.fold (1 : Int) (-1) (· + ·) (treeTower n) = (n : Int) - 1 := by
  intro n; induction n with
  | zero => rfl
  | succ m ih =>
      show (1 : Int) + Tree.fold (1 : Int) (-1) (· + ·) (treeTower m)
             = (m + 1 : Int) - 1
      rw [ih]; push_cast; omega

end E213.Firmware.Internal

namespace E213.Infinity

open E213.Firmware E213.Firmware.Internal E213.Hypervisor
open E213.Hypervisor.Characterisation.Catalog

/-- **signedLens surjective onto `{z : ℤ | z ≥ -1}`** via
    `rawTower`.  The full `ℤ` surjectivity (covering `z ≤ -2`)
    would require a dual "b-tower"; skipped here since
    unboundedness of the image is enough for the Σ4
    cardinality claim. -/
theorem signedLens_image_ge_neg_one :
    ∀ z : Int, -1 ≤ z → ∃ r : Raw, signedLens.view r = z := by
  intro z hz
  have ⟨n, hn⟩ : ∃ n : Nat, z = (n : Int) - 1 := by
    refine ⟨(z + 1).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  refine ⟨rawTower n, ?_⟩
  show Raw.fold (1 : Int) (-1) (· + ·) (rawTower n) = z
  rw [hn]
  exact treeTower_signed n

/-- **signedLens image is unbounded above.**  For every
    `N : ℕ`, some Raw term has signed view `≥ N`. -/
theorem signedLens_unbounded_above :
    ∀ N : Nat, ∃ r : Raw, (N : Int) ≤ signedLens.view r := by
  intro N
  obtain ⟨r, hr⟩ := signedLens_image_ge_neg_one (N : Int) (by omega)
  exact ⟨r, by rw [hr]; exact Int.le_refl _⟩

end E213.Infinity

namespace E213.Infinity

open E213.Firmware E213.Hypervisor

-- ═══ Σ7 summary — cardinality spectrum ═══

/-- **Σ7 (summary formal statement).**  The Raw axiom is
    syntactic-finite and has no cardinality clause; yet
    observation via Lens / function-space lifts exhibits a
    full Cantor ladder of cardinalities.  This theorem
    packages the four structural witnesses:

    (i) Raw ≤ ℕ (Σ2); (ii) Raw ≥ ℕ (Σ3); (iii) `Raw → Bool`
    strictly larger than Raw (Σ5); (iv) `X → Bool` strictly
    larger than `X` for every `X` (Cantor general), giving
    a tower of any depth. -/
theorem sigma7_cardinality_is_lens_output :
    (∃ g : Raw → Nat, Function.Injective g)
      ∧ (∃ f : Nat → Raw, Function.Injective f)
      ∧ (¬ ∃ h : Raw → (Raw → Bool), Function.Surjective h)
      ∧ (∀ X : Type, ¬ ∃ k : X → (X → Bool), Function.Surjective k) := by
  refine ⟨raw_at_most_countable, raw_at_least_countable,
          cantor_raw_bool, ?_⟩
  intro _; exact cantor_general

end E213.Infinity
