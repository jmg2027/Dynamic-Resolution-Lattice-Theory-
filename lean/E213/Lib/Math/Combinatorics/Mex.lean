/-!
# `mex` — the minimal excludant (least non-member), ∅-axiom

The **minimal excludant** `mex S` of a finite set of naturals is the least `Nat`
*not* in `S`.  It is the engine of the Sprague–Grundy / nim-value reading in
combinatorial game theory (`research-notes/decomposition/practice/game_theory.md`):
the nim-value of a position is `mex` of its options' nim-values.

Read through the 213 decomposition calculus, `mex` is a **bounded diagonal** — the
finite-resolution cousin of the Lawvere/Cantor diagonal `no_surjection_of_fixedpointfree`
(`Lens/Foundations/OneDiagonal.lean`): it returns *the first value the set misses*,
"the value outside the image" read on a *finite* set, so it lands at a finite `Nat`
(the first gap) instead of escaping to an uncountable residue.

The construction mirrors the corpus's `findFrom` least-witness search
(`Lib/Math/Logic/BolzanoWeierstrass.lean`): a single linear scan, structural recursion
on the budget, **no `Nat.find`, no `omega`-driven termination, no `Classical`**.  The
set is presented by its membership reading `p : Nat → Bool` (`p c = true` ≙ "`c` is in
the set").  `mexFrom p c k` scans the budget `c, c+1, …, c+k` and returns the first
non-member, or `c + k` if every candidate is a member.
-/

namespace E213.Lib.Math.Combinatorics.Mex

/-- `mexFrom p c k`: scan candidates `c, c+1, …` within budget `k` and return the
    first non-member (`p = false`); if all `k` candidates are members, return `c + k`. -/
def mexFrom (p : Nat → Bool) : Nat → Nat → Nat
  | c, 0     => c
  | c, k + 1 => match p c with
    | false => c
    | true  => mexFrom p (c + 1) k

/-- Unfolding at a successor budget when the head is a non-member. -/
theorem mexFrom_succ_false (p : Nat → Bool) (c k : Nat) (h : p c = false) :
    mexFrom p c (k + 1) = c := by
  show (match p c with | false => c | true => mexFrom p (c + 1) k) = c
  rw [h]

/-- Unfolding at a successor budget when the head is a member. -/
theorem mexFrom_succ_true (p : Nat → Bool) (c k : Nat) (h : p c = true) :
    mexFrom p c (k + 1) = mexFrom p (c + 1) k := by
  show (match p c with | false => c | true => mexFrom p (c + 1) k) = mexFrom p (c + 1) k
  rw [h]

/-- The excludant is at least the start of the scan. -/
theorem mexFrom_ge (p : Nat → Bool) : ∀ k c, c ≤ mexFrom p c k
  | 0,     c => Nat.le_refl c
  | k + 1, c => by
    cases hpc : p c with
    | false => rw [mexFrom_succ_false p c k hpc]; exact Nat.le_refl c
    | true  =>
      rw [mexFrom_succ_true p c k hpc]
      exact Nat.le_trans (Nat.le_succ c) (mexFrom_ge p k (c + 1))

/-- The excludant never exceeds the scanned budget. -/
theorem mexFrom_le (p : Nat → Bool) : ∀ k c, mexFrom p c k ≤ c + k
  | 0,     c => Nat.le_of_eq (Nat.add_zero c).symm
  | k + 1, c => by
    cases hpc : p c with
    | false =>
      rw [mexFrom_succ_false p c k hpc]
      exact Nat.le_trans (Nat.le_succ c) (Nat.succ_le_succ (Nat.le_add_right c k))
    | true  =>
      rw [mexFrom_succ_true p c k hpc]
      have := mexFrom_le p k (c + 1)
      calc mexFrom p (c + 1) k ≤ (c + 1) + k := this
        _ = c + (k + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 k]

/-- **Minimality.**  Everything strictly below the excludant (and ≥ the start) is a
    member.  This is the "least" in *least* non-member: the scan only advances past
    members. -/
theorem mexFrom_lt_mem (p : Nat → Bool) :
    ∀ k c j, c ≤ j → j < mexFrom p c k → p j = true
  | 0,     c, j, hcj, hjm => by
    -- `mexFrom p c 0 = c`, so `j < c` contradicts `c ≤ j`.
    exact absurd hjm (Nat.not_lt.mpr hcj)
  | k + 1, c, j, hcj, hjm => by
    cases hpc : p c with
    | false =>
      -- excludant is `c`; `j < c` contradicts `c ≤ j`.
      rw [mexFrom_succ_false p c k hpc] at hjm
      exact absurd hjm (Nat.not_lt.mpr hcj)
    | true  =>
      rw [mexFrom_succ_true p c k hpc] at hjm
      -- either `j = c` (a member by `hpc`) or `j ≥ c+1` (by IH)
      cases Nat.lt_or_ge j (c + 1) with
      | inl hjc =>
        have : j = c := Nat.le_antisymm (Nat.le_of_lt_succ hjc) hcj
        rw [this]; exact hpc
      | inr hjc => exact mexFrom_lt_mem p k (c + 1) j hjc hjm

/-- **Search succeeds.**  If some candidate in `[c, c+k)` is a non-member, the scan
    lands on a non-member, and strictly inside the budget.  Stated jointly so the
    recursion carries both facts (mirrors `findFrom_succeeds`). -/
theorem mexFrom_finds (p : Nat → Bool) :
    ∀ k c j, c ≤ j → j < c + k → p j = false →
      p (mexFrom p c k) = false ∧ mexFrom p c k < c + k
  | 0,     c, j, hcj, hjk, _ => by
    exact absurd hjk (Nat.not_lt.mpr (Nat.le_trans (Nat.le_of_eq (Nat.add_zero c).symm) hcj))
  | k + 1, c, j, hcj, hjk, hpj => by
    cases hpc : p c with
    | false =>
      rw [mexFrom_succ_false p c k hpc]
      exact ⟨hpc, Nat.lt_of_lt_of_le (Nat.lt_succ_self c)
        (Nat.succ_le_succ (Nat.le_add_right c k))⟩
    | true  =>
      rw [mexFrom_succ_true p c k hpc]
      -- `j ≠ c` since `p c = true` but `p j = false`; so `c+1 ≤ j < (c+1)+k`.
      have hjne : j ≠ c := by
        intro h; rw [h] at hpj; rw [hpc] at hpj; exact Bool.noConfusion hpj
      have hcj' : c + 1 ≤ j := Nat.lt_of_le_of_ne hcj (fun h => hjne h.symm)
      have hjk' : j < (c + 1) + k := by
        have : c + (k + 1) = (c + 1) + k := by
          rw [Nat.add_assoc, Nat.add_comm 1 k]
        rw [← this]; exact hjk
      have ⟨hres, hlt⟩ := mexFrom_finds p k (c + 1) j hcj' hjk' hpj
      refine ⟨hres, ?_⟩
      calc mexFrom p (c + 1) k < (c + 1) + k := hlt
        _ = c + (k + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 k]

/-- **`mex` proper.**  Given a budget `B` (a known bound such that some value `≤ B` is a
    non-member — always true for a finite option-set, where `B` = number of options),
    `mex p B := mexFrom p 0 (B + 1)`. -/
def mex (p : Nat → Bool) (B : Nat) : Nat := mexFrom p 0 (B + 1)

/-- `mex` lands on a non-member, given any non-member witness within the budget. -/
theorem mex_not_mem (p : Nat → Bool) (B j : Nat)
    (hjB : j < B + 1) (hpj : p j = false) : p (mex p B) = false :=
  (mexFrom_finds p (B + 1) 0 j (Nat.zero_le j)
    (by rw [Nat.zero_add]; exact hjB) hpj).1

/-- `mex` is minimal: every value strictly below it is a member. -/
theorem mex_lt_mem (p : Nat → Bool) (B j : Nat) (hj : j < mex p B) : p j = true :=
  mexFrom_lt_mem p (B + 1) 0 j (Nat.zero_le j) hj

/-- `mex` is bounded by the budget. -/
theorem mex_le (p : Nat → Bool) (B : Nat) : mex p B ≤ B + 1 := by
  have := mexFrom_le p (B + 1) 0
  rw [Nat.zero_add] at this; exact this

/-! ## The decomposition reading (game theory)

For an impartial game position `g` with options `g'`, the option-readout set is
`{ G(g') }`; `p c := (c ∈ {G(g')})` is the membership reading and `G(g) = mex p B`
with `B` = the number of options.  `mex_not_mem` is "the nim-value escapes the option
set" (the q=−1 *escape*, read at finite resolution — the **bounded diagonal**), and
`mex_lt_mem` is "every smaller value is reachable" (minimality).  `G(g) = 0` ⟺ every
option is a non-zero member, i.e. `p 0 = false` ⟺ the **P-position** (q=+1 sink):
the least excludant is `0` exactly when the set of option-values misses `0`. -/

/-- A position is a **P-position** (nim-value `0`, second-player win) iff `0` is a
    non-member of the option set — the least excludant bottoms out at `0`. -/
theorem mex_eq_zero_iff_zero_excluded (p : Nat → Bool) (B : Nat) :
    mex p B = 0 ↔ p 0 = false := by
  constructor
  · intro h
    cases hp0 : p 0 with
    | false => rfl
    | true =>
      -- if `0` is a member, `mex ≥ 1`, contradicting `mex = 0`
      exfalso
      have hge : (1 : Nat) ≤ mex p B := by
        show mexFrom p 0 (B + 1) ≥ 1
        rw [mexFrom_succ_true p 0 B hp0]
        exact mexFrom_ge p B 1
      rw [h] at hge; exact absurd hge (Nat.not_succ_le_zero 0)
  · intro h
    show mexFrom p 0 (B + 1) = 0
    exact mexFrom_succ_false p 0 B h

end E213.Lib.Math.Combinatorics.Mex
