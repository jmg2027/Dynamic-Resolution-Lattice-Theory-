import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid
import E213.Meta.Tactic.Pow213
import E213.Meta.Int213.Core
import E213.Meta.Int213.Order

/-!
# PolyRoot/ResidueList — the nonzero residues `[1, p)` as distinct-mod-`p` roots

To apply Lagrange's bound (`RootBound.eval_zero`) to `Tᵐ − 1`, we need the list of nonzero
residues `1, 2, …, p−1` (as `Int`), proved pairwise-distinct mod `p`: their differences have
absolute value `< p`, hence are not divisible by `p`.

  * `intRangeFrom lo n` — `[lo, lo+1, …, lo+n−1]` as a `List Int`.
  * `intRangeFrom_length`, `mem_intRangeFrom_nat` — length `n`; every element is `↑a` with
    `lo ≤ a < lo+n`.
  * ★ `intRangeFrom_pairwise` — `n ≤ p` ⟹ pairwise `¬ ↑p ∣ (a − b)`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.PolyRoot

open E213.Tactic.Pow213 (le_of_dvd_pos)

/-- `[lo, lo+1, …, lo+n−1]` as a list of `Int`. -/
def intRangeFrom (lo : Int) : Nat → List Int
  | 0 => []
  | n + 1 => lo :: intRangeFrom (lo + 1) n

theorem intRangeFrom_length (lo : Int) : ∀ n, (intRangeFrom lo n).length = n
  | 0 => rfl
  | n + 1 => by
      show (intRangeFrom (lo + 1) n).length + 1 = n + 1
      rw [intRangeFrom_length]

/-- `(↑(a+1) : Int) = ↑a + 1` (pure cast-of-successor). -/
theorem natCast_succ (a : Nat) : ((a + 1 : Nat) : Int) = (a : Int) + 1 := rfl

/-- `(↑(m+n) : Int) = ↑m + ↑n` (pure cast-of-sum). -/
theorem natCast_add (m n : Nat) : ((m + n : Nat) : Int) = (m : Int) + (n : Int) := rfl

/-- Every element of `intRangeFrom ↑lo n` is `↑a` for a `Nat` `a` with `lo ≤ a < lo + n`. -/
theorem mem_intRangeFrom_nat : ∀ (n : Nat) (lo : Nat) {x : Int},
    x ∈ intRangeFrom (lo : Int) n → ∃ a : Nat, lo ≤ a ∧ a < lo + n ∧ x = (a : Int) := by
  intro n
  induction n with
  | zero => intro lo x h; exact absurd h (List.not_mem_nil x)
  | succ n ih =>
    intro lo x h
    have h' : x ∈ (lo : Int) :: intRangeFrom ((lo : Int) + 1) n := h
    cases h' with
    | head => exact ⟨lo, Nat.le_refl lo, Nat.lt_add_of_pos_right (Nat.succ_pos n), rfl⟩
    | tail _ hm =>
      have hcast : ((lo : Int) + 1) = ((lo + 1 : Nat) : Int) := (natCast_succ lo).symm
      rw [hcast] at hm
      obtain ⟨a, hge, hlt, hx⟩ := ih (lo + 1) hm
      refine ⟨a, Nat.le_of_succ_le hge, ?_, hx⟩
      have e1 : (lo + 1) + n = lo + (n + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 n]
      rw [← e1]; exact hlt

/-- `0 < (a−b).natAbs`, `(a−b).natAbs < p` ⟹ `¬ ↑p ∣ (a − b)`. -/
theorem not_dvd_of_natAbs_lt (p : Nat) {d : Int} (h0 : 0 < d.natAbs) (hlt : d.natAbs < p) :
    ¬ (p : Int) ∣ d := by
  intro hd
  have hnat : p ∣ d.natAbs := int_dvd_to_nat p d hd
  have hle : p ≤ d.natAbs := le_of_dvd_pos p d.natAbs h0 hnat
  exact absurd hle (Nat.not_le.mpr hlt)

/-- ★ The nonzero-residue window is pairwise-distinct mod `p`: for `n ≤ p`,
    `intRangeFrom ↑lo n` is `Pairwise (fun a b => ¬ ↑p ∣ (a − b))`. -/
theorem intRangeFrom_pairwise (p : Nat) : ∀ (n : Nat) (lo : Nat), n ≤ p →
    (intRangeFrom (lo : Int) n).Pairwise (fun a b => ¬ (p : Int) ∣ (a - b)) := by
  intro n
  induction n with
  | zero => intro lo _; exact List.Pairwise.nil
  | succ n ih =>
    intro lo hn
    have hcast : ((lo : Int) + 1) = ((lo + 1 : Nat) : Int) := (natCast_succ lo).symm
    have hshow : intRangeFrom (lo : Int) (n + 1)
        = (lo : Int) :: intRangeFrom ((lo : Int) + 1) n := rfl
    rw [hshow]
    refine List.pairwise_cons.mpr ⟨?_, ?_⟩
    · intro y hy
      rw [hcast] at hy
      obtain ⟨a, hge, hlt, hya⟩ := mem_intRangeFrom_nat n (lo + 1) hy
      have hloa : lo ≤ a := Nat.le_of_succ_le hge
      obtain ⟨k, hak⟩ : ∃ k, a = lo + k :=
        ⟨a - lo, (E213.Tactic.NatHelper.add_sub_of_le hloa).symm⟩
      have hk1 : 1 ≤ k := by
        have h2 := hge; rw [hak] at h2
        exact E213.Tactic.NatHelper.le_of_add_le_add_left h2
      have hkn : k < n + 1 := by
        have h3 := hlt; rw [hak] at h3
        have e1 : (lo + 1) + n = lo + (n + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 n]
        rw [e1] at h3
        exact Nat.lt_of_add_lt_add_left h3
      have hkp : k < p := Nat.lt_of_le_of_lt (Nat.le_of_lt_succ hkn) (Nat.lt_of_succ_le hn)
      have hval : (lo : Int) - y = -(k : Int) := by
        rw [hya, hak, natCast_add]; ring_intZ
      rw [hval]
      exact not_dvd_of_natAbs_lt p
        (by rw [Int.natAbs_neg, Int.natAbs_ofNat]; exact hk1)
        (by rw [Int.natAbs_neg, Int.natAbs_ofNat]; exact hkp)
    · rw [hcast]
      exact ih (lo + 1) (Nat.le_of_succ_le hn)

end E213.Lib.Math.NumberTheory.PolyRoot
