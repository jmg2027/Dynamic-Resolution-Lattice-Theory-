import E213.Lens.LensCore
import E213.Lens.Compose.Factoring
import E213.Lib.Math.Infinity.LensCardinality
import E213.Lib.Math.NatHelpers.AddMod213

/-!
# LeavesModNat: divisibility → refinement for leaves mod m

Unified form of the mod m family of Lenses.  For any m ≥ 2,
observes leaves mod m via a Lens Nat.

**Key**: `k ∣ m → leavesModNat m refines leavesModNat k`.  That is,
the mod m family is isomorphic to the divisibility lattice (as a
reflection of the refines preorder).

Concrete structure of the countably infinite lower bound from note 41 §4.
-/

namespace E213.Lens.Leaves.ModNat

open E213.Theory E213.Lens E213.Lens.Compose.Factoring

/-- Leaves mod m Lens (m ≥ 2).  view r = leaves r % m. -/
def leavesModNat (m : Nat) : Lens Nat where
  base_a := 1 % m
  base_b := 1 % m
  combine u v := (u + v) % m

private theorem mod_add_comm (m a b : Nat) :
    (a + b) % m = (b + a) % m := by rw [Nat.add_comm]

/-- View of leavesModNat m = leaves r % m. -/
theorem leavesModNat_view_eq (m : Nat) :
    ∀ r : Raw, (leavesModNat m).view r = Lens.leaves.view r % m := by
  intro r
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfsM : (leavesModNat m).view (Raw.slash x y h)
                    = (leavesModNat m).combine
                        ((leavesModNat m).view x) ((leavesModNat m).view y) :=
        Raw.fold_slash _ _ _ (mod_add_comm m) x y h
      have hfsL : Lens.leaves.view (Raw.slash x y h)
                    = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      rw [hfsM, hfsL]
      show (((leavesModNat m).view x) + ((leavesModNat m).view y)) % m
           = (Lens.leaves.view x + Lens.leaves.view y) % m
      rw [ihx, ihy]
      exact (E213.Lib.Math.NatHelpers.AddMod213.add_mod_gen _ _ m).symm

end E213.Lens.Leaves.ModNat

namespace E213.Lens.Leaves.ModNat

open E213.Theory E213.Lens E213.Lens.Compose.Factoring

/-- divisibility → refinement: k ∣ m ⟹ mod m refines mod k. -/
theorem divides_refines (m k : Nat) (hmk : k ∣ m) :
    (leavesModNat m).refines (leavesModNat k) := by
  apply refines_of_factor (leavesModNat m) (leavesModNat k)
    (fun n => n % k)
  intro r
  rw [leavesModNat_view_eq m, leavesModNat_view_eq k]
  obtain ⟨q, hq⟩ := hmk
  have : Lens.leaves.view r % m % k = Lens.leaves.view r % k := by
    rw [hq]
    exact E213.Lib.Math.NatHelpers.AddMod213.mod_mod_of_dvd _ ⟨q, rfl⟩
  exact this.symm

end E213.Lens.Leaves.ModNat

namespace E213.Lens.Leaves.ModNat

open E213.Theory E213.Lens

/-- Converse (k ≥ 2): mod m refines mod k ⟹ k ∣ m.  Witness:
    leaves = m+1 (exists — leaves_surjective_pos) vs leaves = 1
    (= Raw.a). -/
theorem refines_implies_divides (m k : Nat) (hm : m ≥ 2) (hk : k ≥ 2)
    (hrefines : (leavesModNat m).refines (leavesModNat k)) :
    k ∣ m := by
  obtain ⟨r, hr⟩ := E213.Infinity.leaves_surjective_pos (m + 1) (by omega)
  have h_leaves_a : Lens.leaves.view Raw.a = 1 := rfl
  -- In mod m, Raw.a and r are equal (both have leaves ≡ 1 mod m)
  have hm_eq : (leavesModNat m).view Raw.a = (leavesModNat m).view r := by
    rw [leavesModNat_view_eq, leavesModNat_view_eq, h_leaves_a, hr]
    show 1 % m = (m + 1) % m
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  -- By refines, they are also equal under mod k
  have hk_eq : (leavesModNat k).view Raw.a = (leavesModNat k).view r :=
    hrefines Raw.a r hm_eq
  rw [leavesModNat_view_eq, leavesModNat_view_eq, h_leaves_a, hr] at hk_eq
  -- hk_eq : 1 % k = (m + 1) % k
  -- k ≥ 2 → 1 % k = 1
  rw [Nat.mod_eq_of_lt (show 1 < k from hk)] at hk_eq
  -- hk_eq : 1 = (m + 1) % k
  -- (m + 1) % k = (m % k + 1) % k
  have hstep : (m + 1) % k = (m % k + 1) % k := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show (1 : Nat) < k from hk)]
  rw [hstep] at hk_eq
  -- hk_eq : 1 = (m % k + 1) % k
  have hmk : m % k < k := Nat.mod_lt _ (by omega)
  have hm_zero : m % k = 0 := by
    by_cases h : m % k + 1 < k
    · rw [Nat.mod_eq_of_lt h] at hk_eq; omega
    · have h_eq : m % k + 1 = k := by omega
      rw [h_eq, Nat.mod_self] at hk_eq
      exact absurd hk_eq (by decide)
  exact Nat.dvd_of_mod_eq_zero hm_zero

end E213.Lens.Leaves.ModNat

namespace E213.Lens.Leaves.ModNat

open E213.Theory E213.Lens

/-- **General upper bound (∅-axiom).** For any common divisor `d`
    of `m` and `k`, both `L_m` and `L_k` refine `L_d`.  The
    lattice-theoretic "gcd as least upper bound" is the maximum
    such `d`; this generic form drops the maximality and stays
    `Nat.gcd`-free. -/
theorem common_divisor_upper_bound (m k d : Nat)
    (hdm : d ∣ m) (hdk : d ∣ k) :
    (leavesModNat m).refines (leavesModNat d) ∧
    (leavesModNat k).refines (leavesModNat d) :=
  ⟨divides_refines m d hdm, divides_refines k d hdk⟩

/-- **General lower bound (∅-axiom).** For any common multiple `N`
    of `m` and `k`, `L_N` refines both `L_m` and `L_k`.  The
    lattice-theoretic "lcm as greatest lower bound" is the minimum
    such `N`; this generic form drops the minimality and stays
    `Nat.lcm`-free.  Specialised to `N := m * k` below. -/
theorem common_multiple_lower_bound (m k N : Nat)
    (hmN : m ∣ N) (hkN : k ∣ N) :
    (leavesModNat N).refines (leavesModNat m) ∧
    (leavesModNat N).refines (leavesModNat k) :=
  ⟨divides_refines N m hmN, divides_refines N k hkN⟩

/-- **Trivial-common-multiple lower bound (∅-axiom).**  At
    `N := m * k` the common-multiple form holds without external
    hypotheses — `m ∣ m * k = ⟨k, rfl⟩` and `k ∣ m * k` by
    `Nat.mul_comm`.  Drop-in ∅-axiom replacement for prior
    `lcm_lower_bound`. -/
theorem product_lower_bound (m k : Nat) :
    (leavesModNat (m * k)).refines (leavesModNat m) ∧
    (leavesModNat (m * k)).refines (leavesModNat k) :=
  common_multiple_lower_bound m k (m * k)
    ⟨k, rfl⟩ ⟨m, Nat.mul_comm m k⟩

/-- L_gcd(m, k) is an upper bound of both L_m and L_k (in the refines order).
    Direct consequence of divides_refines.

    DIRTY-by-design (`[propext]`): the statement mentions `Nat.gcd m k`
    whose well-founded termination proof brings `propext`.  Use
    `common_divisor_upper_bound` for a generic ∅-axiom alternative. -/
theorem gcd_upper_bound (m k : Nat) :
    (leavesModNat m).refines (leavesModNat (Nat.gcd m k)) ∧
    (leavesModNat k).refines (leavesModNat (Nat.gcd m k)) :=
  common_divisor_upper_bound m k (Nat.gcd m k)
    (Nat.gcd_dvd_left m k) (Nat.gcd_dvd_right m k)

/-! ## Converse (least upper bound / greatest lower bound) direction

**Least upper bound** (gcd is least upper bound): if an arbitrary N
is refined by both L_m and L_k, then N is refined by L_gcd.
Requires Bezout chain — future work.

**Greatest lower bound** (lcm is greatest lower bound): analogous.
Can be derived indirectly from the universal property of prodLens = meet.
-/

end E213.Lens.Leaves.ModNat
