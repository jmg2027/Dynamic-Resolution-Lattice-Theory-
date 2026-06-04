import E213.Lib.Math.ModArith.PureNatMod3
import E213.Lib.Math.ModArith.PureNatMod5
import E213.Meta.Nat.PureNat
import E213.Meta.Tactic.NatHelper

/-!
# Irrational.SqrtPure — √N irrationality, truly axiom-free

Zero-axiom proof of √N irrationality via infinite descent on the
squaring map mod N.  Concrete instances at N ∈ {2, 3, 5}.

Pattern (same template, abstracted over `N`):
  1. Assume √N = a/b in lowest terms
  2. N divides b² (from b² = N · k² some k)
  3. N divides b (by squaring map analysis mod N)
  4. N divides a (similarly)
  5. a, b both divisible by N — contradicts "lowest terms"

`DescentBase N` packages the per-N witness `N · (k²) = m² → N | m` plus
`N ≥ 2`; the parametric `sqrtN_no_rational_aux_generic` proves bounded
descent uniformly.  Per-prime namespaces (`Sqrt{p}Pure`) supply
`descentBase` + a thin corollary `sqrt{p}_no_rational_aux`.
-/

namespace E213.Lib.Math.NumberSystems.Irrational

open E213.Meta.Nat.PureNat

/-! ## §0.  Generic descent infrastructure. -/

/-- Witness for "N is squarefree enough to admit infinite descent
    on `m² = N · k²`": `N ≥ 2` plus the divisibility-by-N pullback. -/
structure DescentBase (N : Nat) where
  ge_two : 2 ≤ N
  divides_of_mul_sq : ∀ m k : Nat, m * m = N * (k * k) → ∃ m', m = N * m'

namespace DescentBase

variable {N : Nat}

/-- `0 < N`, derived from `2 ≤ N`. -/
theorem pos (D : DescentBase N) : 0 < N :=
  Nat.lt_of_lt_of_le (by decide : 0 < 2) D.ge_two

/-- Scaled-square identity: `(N · k)² = N · (N · k²)`.  PURE; uniform
    over N, generalises the per-prime `even_sq` / `three_mul_sq` /
    `five_mul_sq` rewrites. -/
theorem scaled_sq (N k : Nat) : (N * k) * (N * k) = N * (N * (k * k)) := by
  rw [mul_mul_mul_comm N k N k, mul_assoc]

/-- The descent step: from `m² = N · k²` and `m = N · m'`, derive
    `N · m'² = k²`.  Uses only `N > 0` and `scaled_sq`. -/
theorem descent_step (D : DescentBase N)
    (m k : Nat) (heq : m * m = N * (k * k))
    (m' : Nat) (hm : m = N * m') :
    N * (m' * m') = k * k := by
  rw [hm, scaled_sq] at heq
  exact Nat.eq_of_mul_eq_mul_left D.pos heq

end DescentBase

open E213.Tactic.NatHelper renaming one_le_of_ne_zero → ne_zero_imp_ge_one

/-- ★ Parametric bounded descent.  Given a `DescentBase N`, the
    equation `m² = N · k²` forces `k = 0` (bounded by induction on
    a search budget `s ≥ k`). -/
theorem sqrtN_no_rational_aux_generic {N : Nat} (D : DescentBase N) :
    ∀ s k m : Nat, k ≤ s → m * m = N * (k * k) → k = 0 := by
  intro s
  induction s with
  | zero =>
      intro k _ hkn _
      exact Nat.le_zero.mp hkn
  | succ n ih =>
      intro k m hkn heq
      by_cases hk : k = 0
      · exact hk
      · exfalso
        have hk_pos : 1 ≤ k := ne_zero_imp_ge_one k hk
        obtain ⟨m', hm_eq⟩ := D.divides_of_mul_sq m k heq
        have h2 : N * (m' * m') = k * k := D.descent_step m k heq m' hm_eq
        obtain ⟨k', hk_eq⟩ := D.divides_of_mul_sq k m' h2.symm
        have h3 : m' * m' = N * (k' * k') := by
          have hstep := D.descent_step k m' h2.symm k' hk_eq
          exact hstep.symm
        by_cases hk'_zero : k' = 0
        · exact hk (by rw [hk_eq, hk'_zero, Nat.mul_zero])
        · have hk'_pos : 1 ≤ k' := ne_zero_imp_ge_one k' hk'_zero
          have hbnd : N * k' ≤ n + 1 := by rw [← hk_eq]; exact hkn
          have hk'_le : k' ≤ n := by
            have h_step : k' + 1 ≤ 2 * k' := by
              rw [Nat.two_mul]
              exact Nat.add_le_add_left hk'_pos k'
            have h_2k_Nk : 2 * k' ≤ N * k' := Nat.mul_le_mul_right k' D.ge_two
            exact Nat.le_of_succ_le_succ
              (Nat.le_trans h_step (Nat.le_trans h_2k_Nk hbnd))
          exact hk'_zero (ih k' m' hk'_le h3)

end E213.Lib.Math.NumberSystems.Irrational

namespace E213.Lib.Math.NumberSystems.Irrational.Sqrt2Pure

open E213.Meta.Nat.PureNat
open E213.Lib.Math.NumberSystems.Irrational (DescentBase sqrtN_no_rational_aux_generic)

/-- m^2 = 2*(k*k) → m even. -/
theorem m_even_of_sq (m k : Nat) (heq : m * m = 2 * (k * k)) :
    isEven m = true := by
  have h1 : isEven (m * m) = isEven m := isEven_self_mul m
  rw [heq] at h1
  rw [isEven_two_mul] at h1
  exact h1.symm

/-- isEven m = true → ∃ m', m = 2 * m'. -/
theorem even_split (m : Nat) (h : isEven m = true) : ∃ m', m = 2 * m' := by
  cases nat_dichotomy m with
  | inl h' => exact h'
  | inr h' =>
      obtain ⟨k, hk⟩ := h'
      exfalso
      rw [hk, isEven_two_mul_succ] at h
      exact Bool.noConfusion h

/-- `DescentBase 2` instance: divisibility-by-2 pulls back through
    squaring (`m² = 2·k² → ∃ m', m = 2·m'`) and `2 ≥ 2`. -/
def descentBase : DescentBase 2 where
  ge_two := Nat.le_refl 2
  divides_of_mul_sq m k heq := even_split m (m_even_of_sq m k heq)

/-- Bounded descent at N = 2, thin corollary of the generic. -/
theorem sqrt2_no_rational_aux :
    ∀ s k m : Nat, k ≤ s → m * m = 2 * (k * k) → k = 0 :=
  sqrtN_no_rational_aux_generic descentBase

/-- **√2 irrationality, truly axiom-free**. -/
theorem sqrt2_irrational (k : Nat) (hk : k ≥ 1) (m : Nat) :
    m * m ≠ 2 * (k * k) := by
  intro heq
  have h := sqrt2_no_rational_aux k k m (Nat.le_refl _) heq
  rw [h] at hk
  exact Nat.not_succ_le_zero 0 hk

end E213.Lib.Math.NumberSystems.Irrational.Sqrt2Pure

namespace E213.Lib.Math.NumberSystems.Irrational.Sqrt3Pure

open E213.Meta.Nat.PureNat
open E213.Lib.Math.ModArith.PureNatMod3
open E213.Lib.Math.NumberSystems.Irrational (DescentBase sqrtN_no_rational_aux_generic)

/-- m^2 = 3*(k*k) → mod3 m = 0. -/
theorem m_mod3_zero_of_sq (m k : Nat) (heq : m * m = 3 * (k * k)) :
    mod3 m = 0 := by
  apply mod3_self_mul_zero
  rw [heq]
  exact mod3_three_mul (k * k)

/-- mod3 m = 0 → ∃ m', m = 3 * m'. -/
theorem three_split (m : Nat) (h : mod3 m = 0) : ∃ m', m = 3 * m' := by
  cases nat_trichotomy m with
  | inl h' => exact h'
  | inr h' =>
      cases h' with
      | inl h'' =>
          obtain ⟨k, hk⟩ := h''
          exfalso; rw [hk, mod3_three_mul_one] at h
          exact Nat.noConfusion h
      | inr h'' =>
          obtain ⟨k, hk⟩ := h''
          exfalso; rw [hk, mod3_three_mul_two] at h
          exact Nat.noConfusion h

/-- `DescentBase 3` instance. -/
def descentBase : DescentBase 3 where
  ge_two := by decide
  divides_of_mul_sq m k heq := three_split m (m_mod3_zero_of_sq m k heq)

/-- Bounded descent at N = 3, thin corollary of the generic. -/
theorem sqrt3_no_rational_aux :
    ∀ s k m : Nat, k ≤ s → m * m = 3 * (k * k) → k = 0 :=
  sqrtN_no_rational_aux_generic descentBase

/-- **√3 irrationality, truly axiom-free**. -/
theorem sqrt3_irrational (k : Nat) (hk : k ≥ 1) (m : Nat) :
    m * m ≠ 3 * (k * k) := by
  intro heq
  have h := sqrt3_no_rational_aux k k m (Nat.le_refl _) heq
  rw [h] at hk
  exact Nat.not_succ_le_zero 0 hk

end E213.Lib.Math.NumberSystems.Irrational.Sqrt3Pure

namespace E213.Lib.Math.NumberSystems.Irrational.Sqrt5Pure

open E213.Meta.Nat.PureNat
open E213.Lib.Math.ModArith.PureNatMod5
open E213.Lib.Math.NumberSystems.Irrational (DescentBase sqrtN_no_rational_aux_generic)

/-- m^2 = 5*(k*k) → mod5 m = 0. -/
theorem m_mod5_zero_of_sq (m k : Nat) (heq : m * m = 5 * (k * k)) :
    mod5 m = 0 := by
  apply mod5_self_mul_zero
  rw [heq]; exact mod5_five_mul (k * k)

/-- mod5 m = 0 → ∃ m', m = 5 * m'. -/
theorem five_split (m : Nat) (h : mod5 m = 0) : ∃ m', m = 5 * m' := by
  rcases nat_quintichotomy m with h' | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
  · exact h'
  · exfalso; rw [hk, mod5_five_mul_one] at h; exact Nat.noConfusion h
  · exfalso; rw [hk, mod5_five_mul_two] at h; exact Nat.noConfusion h
  · exfalso; rw [hk, mod5_five_mul_three] at h; exact Nat.noConfusion h
  · exfalso; rw [hk, mod5_five_mul_four] at h; exact Nat.noConfusion h

/-- `DescentBase 5` instance. -/
def descentBase : DescentBase 5 where
  ge_two := by decide
  divides_of_mul_sq m k heq := five_split m (m_mod5_zero_of_sq m k heq)

/-- Bounded descent at N = 5, thin corollary of the generic. -/
theorem sqrt5_no_rational_aux :
    ∀ s k m : Nat, k ≤ s → m * m = 5 * (k * k) → k = 0 :=
  sqrtN_no_rational_aux_generic descentBase

/-- **√5 irrationality, truly axiom-free**. -/
theorem sqrt5_irrational (k : Nat) (hk : k ≥ 1) (m : Nat) :
    m * m ≠ 5 * (k * k) := by
  intro heq
  have h := sqrt5_no_rational_aux k k m (Nat.le_refl _) heq
  rw [h] at hk
  exact Nat.not_succ_le_zero 0 hk

end E213.Lib.Math.NumberSystems.Irrational.Sqrt5Pure
