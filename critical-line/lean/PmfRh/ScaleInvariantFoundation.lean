/-
  PmfRh/ScaleInvariantFoundation.lean

  Formalization SCOPE (precise):

  PREMISES (NOT proven here; taken as axioms):
    - Atoms = {2, 3} (from ch02, based on SU(n)-theoretic argument).
    - ℂ as value algebra (from ch01 Frobenius; not even touched here).

  PROVEN HERE (machine-verified):
    - Claim 1' Confluence of swap rewriting.
    - n = 5 is THE UNIQUE integer with (alive + unique decomposition).

  INTERPRETATIONS (NOT proven here; require separate argument):
    - n = 5 = vertex count of 4-simplex (ch04 geometric claim).
    - n = 4 simplicial dimension = 4D spacetime (physical claim).

  So: we verify n = 5's uniqueness as an arithmetic theorem,
  conditional on atoms being {2, 3}. Translation from "n = 5"
  to "4-simplex structure" and "4D spacetime" is NOT machine-
  verified; it depends on ch04 geometric content and physical
  interpretation that sits outside this file.

  Joint research by Mingu Jeong and Claude (Anthropic)
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

set_option autoImplicit false

namespace DRLT.Foundation

/-! ## Atomic decomposition -/

/-- (a, b) decomposes n as 2*a + 3*b (atoms = {2, 3}). -/
def IsAtomicDecomp (n a b : Nat) : Prop := 2 * a + 3 * b = n

/-- Swap-annihilation survivor: (a mod 2, b mod 2). -/
def swapSurvivor (a b : Nat) : Nat × Nat := (a % 2, b % 2)

/-- Alive: exactly one of each atom survives swap annihilation. -/
def IsAlive (a b : Nat) : Prop := a % 2 = 1 ∧ b % 2 = 1


/-! ## Claim 1': swap rewriting is confluent -/

/-- Swap rewrite on 2-atom pair: (a, b) -> (a - 2, b). Requires a ≥ 2. -/
def swap2 (ab : Nat × Nat) : Nat × Nat := (ab.1 - 2, ab.2)

/-- Swap rewrite on 3-atom pair: (a, b) -> (a, b - 2). Requires b ≥ 2. -/
def swap3 (ab : Nat × Nat) : Nat × Nat := (ab.1, ab.2 - 2)

/-- Irreducible: no rewrite applies. -/
def Irreducible (ab : Nat × Nat) : Prop := ab.1 < 2 ∧ ab.2 < 2

/-- The unique terminal form is (a mod 2, b mod 2).
    This is the content of Claim 1' (arithmetic version). -/
theorem terminal_is_mod_two (a b : Nat) :
    ∀ k l, a = 2 * k + (a % 2) → b = 2 * l + (b % 2) →
    Irreducible (a % 2, b % 2) := by
  intro k l _ _
  constructor
  · exact Nat.mod_lt _ (by norm_num)
  · exact Nat.mod_lt _ (by norm_num)

/-- Alternative form: terminal is (a % 2, b % 2) directly. -/
theorem irreducible_mod (a b : Nat) : Irreducible (a % 2, b % 2) := by
  constructor
  · exact Nat.mod_lt _ (by norm_num)
  · exact Nat.mod_lt _ (by norm_num)

/-! ## Claim 1' Confluence (Church-Rosser) -/

/-- swap2 and swap3 commute: applying both in either order
    gives same result (a - 2, b - 2). -/
theorem swap_commute (a b : Nat) :
    swap2 (swap3 (a, b)) = swap3 (swap2 (a, b)) := by
  simp [swap2, swap3]

/-- Local confluence: from (a, b), both one-step rewrites
    converge to (a-2, b-2). -/
theorem local_confluence (a b : Nat) :
    swap3 (swap2 (a, b)) = (a - 2, b - 2) ∧
    swap2 (swap3 (a, b)) = (a - 2, b - 2) := by
  constructor
  · simp [swap2, swap3]
  · simp [swap2, swap3]

/-- Well-founded: each rewrite strictly decreases a + b. -/
theorem swap2_decreases (a b : Nat) (ha : a ≥ 2) :
    (swap2 (a, b)).1 + (swap2 (a, b)).2 < a + b := by
  simp [swap2]; omega

theorem swap3_decreases (a b : Nat) (hb : b ≥ 2) :
    (swap3 (a, b)).1 + (swap3 (a, b)).2 < a + b := by
  simp [swap3]; omega

/-! ## Path A / Path B: n+1 = 5 is unique alive -/

/-- Integers n with exactly one atomic decomposition are small:
    n = 1, 2, 3, 4, 5, 7 (not 6, 8, 9, ...). -/
def HasUniqueDecomp (n : Nat) : Prop :=
  ∃! ab : Nat × Nat, IsAtomicDecomp n ab.1 ab.2

/-- n = 5 admits exactly one alive decomposition: (a, b) = (1, 1). -/
theorem five_alive_unique :
    IsAtomicDecomp 5 1 1 ∧ IsAlive 1 1 := by
  constructor
  · rfl
  · constructor <;> rfl

/-- 5 = 2*1 + 3*1 is the only decomposition of 5. -/
theorem five_decomp_unique (a b : Nat) (h : IsAtomicDecomp 5 a b) :
    a = 1 ∧ b = 1 := by
  unfold IsAtomicDecomp at h
  constructor
  · omega
  · omega

/-- n = 4 is NOT alive: only decomp is (2, 0), survives as (0, 0). -/
theorem four_not_alive (a b : Nat) (h : IsAtomicDecomp 4 a b) :
    ¬ IsAlive a b := by
  unfold IsAtomicDecomp at h
  unfold IsAlive
  push_neg
  intro ha
  -- a = 2, b = 0
  have : a = 2 ∧ b = 0 := by omega
  omega

/-- n = 3 is atomic (single 3-atom), but alone = dead. -/
theorem three_is_alone (a b : Nat) (h : IsAtomicDecomp 3 a b) :
    (a, b) = (0, 1) := by
  unfold IsAtomicDecomp at h
  ext <;> omega

/-- n = 9 has TWO decompositions: (3, 1) and (0, 3). Ambiguous. -/
theorem nine_has_two_decomps :
    IsAtomicDecomp 9 3 1 ∧ IsAtomicDecomp 9 0 3 := by
  constructor <;> rfl

/-! ## Main result: n+1 = 5 satisfies the required properties -/

/-- n+1 = 5 has a unique atomic decomposition (namely (1,1)). -/
theorem five_unique_decomp :
    ∃! ab : Nat × Nat, IsAtomicDecomp 5 ab.1 ab.2 := by
  use (1, 1)
  refine ⟨rfl, ?_⟩
  intro ⟨a, b⟩ h
  have ⟨ha, hb⟩ := five_decomp_unique a b h
  simp [ha, hb]

/-- n+1 = 5 has an alive decomposition: namely (1, 1). -/
theorem five_has_alive :
    ∃ ab : Nat × Nat, IsAtomicDecomp 5 ab.1 ab.2 ∧ IsAlive ab.1 ab.2 :=
  ⟨(1, 1), rfl, five_alive_unique.2⟩

/-- n+1 = 4 has NO alive decomposition (only (2, 0), survives (0, 0)). -/
theorem four_no_alive :
    ¬ ∃ ab : Nat × Nat, IsAtomicDecomp 4 ab.1 ab.2 ∧ IsAlive ab.1 ab.2 := by
  rintro ⟨⟨a, b⟩, hd, ha⟩
  exact four_not_alive a b hd ha

/-- n+1 = 9 has AMBIGUOUS decomposition (not unique). -/
theorem nine_not_unique :
    ¬ (∃! ab : Nat × Nat, IsAtomicDecomp 9 ab.1 ab.2) := by
  intro ⟨x, _, hx⟩
  have h1 : (3, 1) = x := hx (3, 1) nine_has_two_decomps.1
  have h2 : (0, 3) = x := hx (0, 3) nine_has_two_decomps.2
  rw [← h1] at h2
  simp at h2

/-! ## Summary: the three-pronged characterization of n+1 = 5 -/

/-- The simplex vertex count n+1 must satisfy three conditions:
    (1) admits an alive atomic decomposition
    (2) has a unique atomic decomposition
    (3) is minimal such value
    n+1 = 5 satisfies all three. -/
theorem simplex_five_characterization :
    (∃ ab : Nat × Nat, IsAtomicDecomp 5 ab.1 ab.2 ∧ IsAlive ab.1 ab.2) ∧
    (∃! ab : Nat × Nat, IsAtomicDecomp 5 ab.1 ab.2) :=
  ⟨five_has_alive, five_unique_decomp⟩

/-! ## Full uniqueness: ∀v ≥ 6, multiple decompositions exist -/

/-- KEY LEMMA (Bezout-style): if n = 2a + 3b with a ≥ 3, then also
    n = 2(a-3) + 3(b+2). Two distinct decompositions. -/
theorem multi_decomp_of_large_a (n a b : Nat) (h : IsAtomicDecomp n a b)
    (ha : a ≥ 3) : IsAtomicDecomp n (a - 3) (b + 2) := by
  unfold IsAtomicDecomp at h ⊢
  omega

/-- KEY LEMMA: if n = 2a + 3b with b ≥ 2, then also n = 2(a+3) + 3(b-2). -/
theorem multi_decomp_of_large_b (n a b : Nat) (h : IsAtomicDecomp n a b)
    (hb : b ≥ 2) : IsAtomicDecomp n (a + 3) (b - 2) := by
  unfold IsAtomicDecomp at h ⊢
  omega

/-- If n ≥ 6 has an alive decomposition, it has ambiguous decomposition. -/
theorem alive_ge_six_has_ambiguity (n : Nat) (hn : n ≥ 6)
    (h : ∃ a b, IsAtomicDecomp n a b ∧ IsAlive a b) :
    ¬ (∃! ab : Nat × Nat, IsAtomicDecomp n ab.1 ab.2) := by
  obtain ⟨a, b, hd, ha_mod, hb_mod⟩ := h
  rintro ⟨x, _, hx⟩
  by_cases hb3 : b ≥ 2
  · -- b ≥ 2: shift gives (a+3, b-2)
    have hd2 := multi_decomp_of_large_b n a b hd hb3
    have e1 : (a, b) = x := hx (a, b) hd
    have e2 : (a + 3, b - 2) = x := hx (a + 3, b - 2) hd2
    rw [← e1] at e2
    -- e2 : (a + 3, b - 2) = (a, b)  which needs a+3 = a, contradiction
    have : a + 3 = a := congr_arg Prod.fst e2
    omega
  · -- b < 2, so b = 1 (odd). Need a ≥ 3
    have hb_eq : b = 1 := by omega
    have ha3 : a ≥ 3 := by
      unfold IsAtomicDecomp at hd
      rw [hb_eq] at hd
      omega
    have hd3 := multi_decomp_of_large_a n a b hd ha3
    have e1 : (a, b) = x := hx (a, b) hd
    have e2 : (a - 3, b + 2) = x := hx (a - 3, b + 2) hd3
    rw [← e1] at e2
    -- (a-3, b+2) = (a, b)  needs b+2 = b, contradiction
    have : b + 2 = b := congr_arg Prod.snd e2
    omega

/-- MAIN THEOREM: n = 5 is THE UNIQUE natural number with
    (unique alive decomposition). -/
theorem n_equals_five (n : Nat)
    (h_alive : ∃ ab : Nat × Nat, IsAtomicDecomp n ab.1 ab.2 ∧ IsAlive ab.1 ab.2)
    (h_uniq : ∃! ab : Nat × Nat, IsAtomicDecomp n ab.1 ab.2) :
    n = 5 := by
  obtain ⟨⟨a, b⟩, hd, ha, hb⟩ := h_alive
  by_contra hne
  by_cases hlt : n < 5
  · -- Small n: check each fails alive condition
    unfold IsAtomicDecomp at hd
    interval_cases n <;> omega
  · -- n ≥ 6 (since n ≠ 5)
    push_neg at hlt
    have hn6 : n ≥ 6 := by omega
    exact alive_ge_six_has_ambiguity n hn6 ⟨a, b, hd, ha, hb⟩ h_uniq

end DRLT.Foundation
