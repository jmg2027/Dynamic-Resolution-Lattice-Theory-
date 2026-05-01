/-!
# Non-decomposable integers: {2, 3}

Proposition 6.5 of PAPER.md: an integer `n ≥ 2` cannot be expressed
as a sum `n = n_1 + … + n_k` with `k ≥ 2` and each `n_i ≥ 2` iff
`n ∈ {2, 3}`.

Any `k`-part decomposition (`k ≥ 2`, parts `≥ 2`) collapses to a
2-part decomposition by taking the first part and the sum of the
rest (the rest has `k-1 ≥ 1` parts each `≥ 2`, so its sum is `≥ 2`).
Hence decomposability as stated is equivalent to the 2-part form,
which we use below.
-/

namespace E213.Firmware.Atomicity.NonDecomposable
/-- Expressible as `a + b` with `a, b ≥ 2` (two-part decomposition). -/
def Decomposable (n : Nat) : Prop :=
  ∃ a b : Nat, a ≥ 2 ∧ b ≥ 2 ∧ a + b = n

/-- Non-decomposable and `≥ 2` (the "atoms"). -/
def NonDecomposable (n : Nat) : Prop :=
  n ≥ 2 ∧ ¬ Decomposable n

/-- **Characterization of atoms.** The non-decomposable integers
    `≥ 2` are exactly `{2, 3}`. -/
theorem non_decomposable_iff (n : Nat) :
    NonDecomposable n ↔ n = 2 ∨ n = 3 := by
  constructor
  · rintro ⟨hge, hnd⟩
    rcases Nat.lt_or_ge n 4 with h | h
    · -- n ∈ {2, 3} from 2 ≤ n < 4.
      omega
    · -- n ≥ 4 ⟹ n = 2 + (n-2) with both parts ≥ 2: decomposable.
      exfalso
      exact hnd ⟨2, n - 2, by omega, by omega, by omega⟩
  · rintro (rfl | rfl)
    · -- n = 2: any a, b ≥ 2 has a + b ≥ 4 > 2.
      refine ⟨by omega, ?_⟩
      rintro ⟨a, b, ha, hb, hab⟩
      omega
    · -- n = 3: any a, b ≥ 2 has a + b ≥ 4 > 3.
      refine ⟨by omega, ?_⟩
      rintro ⟨a, b, ha, hb, hab⟩
      omega

end E213.Firmware.Atomicity.NonDecomposable