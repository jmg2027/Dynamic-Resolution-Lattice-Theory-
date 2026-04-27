import E213.Research.LeavesModNat
import E213.Infinity.LensCardinality

/-!
# Research.KernelCardinalityLB: Lens kernel 공간 lower bound (≥ ℵ₀)

`leavesModNat m` family 가 m 별로 구별되는 kernel 을 제공.
즉 Lens kernel 공간은 **countable infinite 이상**.

Upper bound 𝔠 (Raw 가 countable 이고 equivalence 관계는
2^(Raw²) = 𝔠) 와 합쳐: ℵ₀ ≤ |kernel space| ≤ 𝔠.

정확한 cardinality 는 open conjecture (note 47).  하지만
**lower bound 가 확정** = mod family 로부터.

## 주 정리

`leavesModNat_injective_kernel`: m ≠ k (둘 다 ≥ 2) → 두 Lens
의 kernel 이 서로 다름 (∃ r, r' 에서 분리).
-/

namespace E213.Research.KernelCardinalityLB

open E213.Firmware E213.Hypervisor E213.Research.LeavesModNat

/-- m ≠ k (둘 다 ≥ 2) 이면 leavesModNat m 의 kernel ≠
    leavesModNat k 의 kernel.  Witness: Raw.a (leaves=1) 와
    leaves = m+1 인 Raw.

    leavesModNat m: Raw.a (1 mod m) vs r (m+1 mod m = 1) — 같음.
    leavesModNat k: 1 mod k vs (m+1) mod k — m % k = 0 인 경우만
    같음.  m ≠ k, m ≥ 2 이고 k ∤ m 이면 다름. -/
private theorem mod_kernel_separates (m k : Nat) (hm : m ≥ 2) (hk : k ≥ 2)
    (hnotdvd : ¬ k ∣ m) :
    ∃ r r' : Raw,
      (leavesModNat m).view r = (leavesModNat m).view r' ∧
      (leavesModNat k).view r ≠ (leavesModNat k).view r' := by
  obtain ⟨r', hr'⟩ := E213.Infinity.leaves_surjective_pos (m + 1) (by omega)
  refine ⟨Raw.a, r', ?_, ?_⟩
  · -- leavesModNat m: 1 % m = (m+1) % m = 1
    show (leavesModNat m).view Raw.a = (leavesModNat m).view r'
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hr']
    show 1 % m = (m + 1) % m
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  · -- leavesModNat k: 1 % k vs (m+1) % k.  k ≥ 2 → 1 % k = 1.
    -- (m+1) % k = (m % k + 1) % k.  k ∤ m → m % k ≠ 0 → m % k ≥ 1 → m % k + 1 ≥ 2.
    show (leavesModNat k).view Raw.a ≠ (leavesModNat k).view r'
    rw [leavesModNat_view_eq, leavesModNat_view_eq, hr']
    show 1 % k ≠ (m + 1) % k
    rw [Nat.mod_eq_of_lt (show (1 : Nat) < k from hk)]
    have h_mk_pos : m % k > 0 := by
      by_cases h : m % k = 0
      · exfalso
        exact hnotdvd (Nat.dvd_of_mod_eq_zero h)
      · omega
    have h_mk_lt : m % k < k := Nat.mod_lt _ (by omega)
    -- (m+1) % k = ((m % k) + 1) % k
    have hstep : (m + 1) % k = (m % k + 1) % k := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show (1 : Nat) < k from hk)]
    rw [hstep]
    by_cases hcase : m % k + 1 < k
    · rw [Nat.mod_eq_of_lt hcase]
      omega
    · -- m % k + 1 = k → mod = 0
      have heq : m % k + 1 = k := by omega
      rw [heq, Nat.mod_self]
      -- 1 ≠ 0
      decide

end E213.Research.KernelCardinalityLB

namespace E213.Research.KernelCardinalityLB

open E213.Firmware E213.Hypervisor E213.Research.LeavesModNat

/-- **Distinct mod kernels for distinct moduli (m ≠ k, both ≥ 2)**.
    적어도 한 방향에서 k ∤ m 이므로 위 lemma 적용. -/
theorem leavesModNat_kernel_neq (m k : Nat) (hm : m ≥ 2) (hk : k ≥ 2)
    (hne : m ≠ k) :
    ∃ r r' : Raw,
      ¬ ((leavesModNat m).view r = (leavesModNat m).view r' ↔
          (leavesModNat k).view r = (leavesModNat k).view r') := by
  -- WLOG m > k OR k > m.  In each case, the larger one is not divided by the smaller.
  -- m > k: m % k ≠ 0 (since k < m and m ≠ multiple of k).  Hmm, m might be a multiple.
  -- Actually we need: ¬ k ∣ m OR ¬ m ∣ k.
  rcases Nat.lt_or_ge m k with hlt | hge
  · -- m < k: m ∤ k? not always true.  Try the other side: ¬ k ∣ m.  k > m → k ∤ m
    -- (since k ∤ m would require m ≥ k or m = 0).  Here m ≥ 2 > 0, so k ∤ m.
    have hnotdvd : ¬ k ∣ m := by
      intro ⟨q, hq⟩
      -- m = k * q.  k > m and m ≥ 2.  q ≥ 1 (else m = 0).  Then m = k*q ≥ k > m, contradiction.
      cases q with
      | zero => omega
      | succ n =>
        have : k ≤ m := by
          calc k = k * 1 := (Nat.mul_one k).symm
               _ ≤ k * (n + 1) := Nat.mul_le_mul_left k (by omega)
               _ = m := hq.symm
        omega
    obtain ⟨r, r', heqm, hneqk⟩ := mod_kernel_separates m k hm hk hnotdvd
    exact ⟨r, r', fun h => hneqk (h.mp heqm)⟩
  · -- m ≥ k.  m > k since m ≠ k.
    have hgt : m > k := by omega
    -- Same: ¬ m ∣ k (since m > k and k ≥ 2).
    have hnotdvd : ¬ m ∣ k := by
      intro ⟨q, hq⟩
      cases q with
      | zero => omega
      | succ n =>
        have : m ≤ k := by
          calc m = m * 1 := (Nat.mul_one m).symm
               _ ≤ m * (n + 1) := Nat.mul_le_mul_left m (by omega)
               _ = k := hq.symm
        omega
    obtain ⟨r, r', heqk, hneqm⟩ := mod_kernel_separates k m hk hm hnotdvd
    exact ⟨r, r', fun h => hneqm (h.mpr heqk)⟩

end E213.Research.KernelCardinalityLB
