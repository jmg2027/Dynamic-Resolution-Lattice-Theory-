import E213.Clean213

/-!
# Atomicity: d = 5 as a theorem (not an axiom)

Given atoms `{2, 3}`, the unique n ∈ ℕ such that
  (a) n admits exactly one decomposition n = 2a + 3b with a,b ∈ ℕ, and
  (b) that decomposition is "alive" (both a,b odd)
is n = 5.

Proof idea: Bézout shift (a, b) ↦ (a±3, b∓2) preserves the sum, so
uniqueness forces a < 3 ∧ b < 2. Combined with a,b odd and ≥ 1 gives
a = b = 1, hence n = 5.
-/

namespace E213.Atomicity

/-- n decomposes as 2a + 3b. -/
def Decomp (n a b : Nat) : Prop := n = 2 * a + 3 * b

/-- Alive: both parts odd (survive swap annihilation). -/
def IsAlive (a b : Nat) : Prop := a % 2 = 1 ∧ b % 2 = 1

/-- n is atomic: has a unique decomposition, and it is alive. -/
def Atomic (n : Nat) : Prop :=
  ∃ a b, Decomp n a b ∧ IsAlive a b ∧
         ∀ a' b', Decomp n a' b' → a' = a ∧ b' = b

/-- Existence: n = 5 has the unique alive decomposition (1, 1). -/
theorem atomic_five : Atomic 5 := by
  refine ⟨1, 1, rfl, ⟨rfl, rfl⟩, ?_⟩
  intro a b h
  simp [Decomp] at h
  refine ⟨?_, ?_⟩ <;> omega

/-- Uniqueness: Atomic n implies n = 5 (Bézout shift argument). -/
theorem atomic_implies_five (n : Nat) (h : Atomic n) : n = 5 := by
  obtain ⟨a, b, hdec, ⟨ha_odd, hb_odd⟩, huniq⟩ := h
  -- If a ≥ 3, shift (a, b) ↦ (a-3, b+2) yields another decomposition.
  have ha_lt : a < 3 := by
    rcases Nat.lt_or_ge a 3 with h | h
    · exact h
    · exfalso
      have hdec' : Decomp n (a - 3) (b + 2) := by
        simp [Decomp] at hdec ⊢; omega
      have := huniq (a - 3) (b + 2) hdec'
      omega
  -- If b ≥ 2, shift (a, b) ↦ (a+3, b-2) yields another decomposition.
  have hb_lt : b < 2 := by
    rcases Nat.lt_or_ge b 2 with h | h
    · exact h
    · exfalso
      have hdec' : Decomp n (a + 3) (b - 2) := by
        simp [Decomp] at hdec ⊢; omega
      have := huniq (a + 3) (b - 2) hdec'
      omega
  -- a % 2 = 1 ∧ a < 3 ⟹ a = 1; similarly b = 1.
  have ha1 : a = 1 := by omega
  have hb1 : b = 1 := by omega
  subst ha1; subst hb1
  simp [Decomp] at hdec
  omega

/-- Main theorem: atomicity singles out n = 5. -/
theorem atomic_iff_five (n : Nat) : Atomic n ↔ n = 5 :=
  ⟨atomic_implies_five n, fun h => h ▸ atomic_five⟩

/-- Corollary: partition labels are canonical — one 3-atom, one 2-atom. -/
theorem canonical_partition :
    ∀ a b, Decomp 5 a b ∧ IsAlive a b → a = 1 ∧ b = 1 := by
  intro a b ⟨h, _⟩
  simp [Decomp] at h
  refine ⟨?_, ?_⟩ <;> omega

end E213.Atomicity
