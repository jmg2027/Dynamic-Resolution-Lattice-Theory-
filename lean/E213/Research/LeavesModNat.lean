import E213.Hypervisor.Lens
import E213.Research.LensFactoring
import E213.Infinity.LensCardinality

/-!
# Research.LeavesModNat: leaves mod m 의 divisibility → refinement

mod m 계열 Lens 의 통합 form.  임의의 m ≥ 2 에 대해 Lens Nat
으로 leaves mod m 관측.

**핵심**: `k ∣ m → leavesModNat m refines leavesModNat k`.  즉
mod m family 는 divisibility lattice 와 동형 (refines preorder
의 반영).

note 41 §4 의 countable 무한 하한의 구체 구조.
-/

namespace E213.Research.LeavesModNat

open E213.Firmware E213.Hypervisor E213.Research.LensFactoring

/-- Leaves mod m Lens (m ≥ 2).  view r = leaves r % m. -/
def leavesModNat (m : Nat) : Lens Nat where
  base_a := 1 % m
  base_b := 1 % m
  combine u v := (u + v) % m

private theorem mod_add_comm (m a b : Nat) :
    (a + b) % m = (b + a) % m := by rw [Nat.add_comm]

/-- leavesModNat m 의 view = leaves r % m. -/
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
      exact Nat.add_mod _ _ m |>.symm

end E213.Research.LeavesModNat

namespace E213.Research.LeavesModNat

open E213.Firmware E213.Hypervisor E213.Research.LensFactoring

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
    exact Nat.mod_mod_of_dvd _ ⟨q, rfl⟩
  exact this.symm

end E213.Research.LeavesModNat

namespace E213.Research.LeavesModNat

open E213.Firmware E213.Hypervisor

/-- Converse (k ≥ 2): mod m refines mod k ⟹ k ∣ m.  Witness는
    leaves = m+1 (존재 — leaves_surjective_pos) vs leaves = 1
    (= Raw.a). -/
theorem refines_implies_divides (m k : Nat) (hm : m ≥ 2) (hk : k ≥ 2)
    (hrefines : (leavesModNat m).refines (leavesModNat k)) :
    k ∣ m := by
  obtain ⟨r, hr⟩ := E213.Infinity.leaves_surjective_pos (m + 1) (by omega)
  have h_leaves_a : Lens.leaves.view Raw.a = 1 := rfl
  -- mod m 에서 Raw.a 와 r 은 같음 (둘 다 leaves ≡ 1 mod m)
  have hm_eq : (leavesModNat m).view Raw.a = (leavesModNat m).view r := by
    rw [leavesModNat_view_eq, leavesModNat_view_eq, h_leaves_a, hr]
    show 1 % m = (m + 1) % m
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  -- refines 로 mod k 에서도 같음
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

end E213.Research.LeavesModNat

namespace E213.Research.LeavesModNat

open E213.Firmware E213.Hypervisor

/-- L_gcd(m, k) 는 L_m, L_k 양쪽의 upper bound (refines 관점).
    divides_refines 의 직접 귀결. -/
theorem gcd_upper_bound (m k : Nat) :
    (leavesModNat m).refines (leavesModNat (Nat.gcd m k)) ∧
    (leavesModNat k).refines (leavesModNat (Nat.gcd m k)) :=
  ⟨divides_refines m (Nat.gcd m k) (Nat.gcd_dvd_left m k),
   divides_refines k (Nat.gcd m k) (Nat.gcd_dvd_right m k)⟩

/-- L_lcm(m, k) 는 L_m, L_k 양쪽의 lower bound (refines 관점).
    divides_refines 의 귀결. -/
theorem lcm_lower_bound (m k : Nat) :
    (leavesModNat (Nat.lcm m k)).refines (leavesModNat m) ∧
    (leavesModNat (Nat.lcm m k)).refines (leavesModNat k) :=
  ⟨divides_refines (Nat.lcm m k) m (Nat.dvd_lcm_left m k),
   divides_refines (Nat.lcm m k) k (Nat.dvd_lcm_right m k)⟩

/-! ## Converse (least upper bound / greatest lower bound) 방향

**Least upper bound** (gcd is least upper bound): 임의의 N 이
L_m, L_k 에 의해 refine 되면, N 은 L_gcd 에 의해 refine 됨.
Bezout chain 필요 — 향후 작업.

**Greatest lower bound** (lcm is greatest lower bound): 유사.
prodLens = meet 의 universal property 로부터 간접 도출 가능.
-/

end E213.Research.LeavesModNat
