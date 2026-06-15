/-!
# Delannoy numbers `D(m,n)` (∅-axiom)

`D(m,n)` counts lattice paths from `(0,0)` to `(m,n)` using steps E, N, NE (OEIS
A008288; central diagonal A001850: `1, 3, 13, 63, 321, …`).  Recurrence
`D(m,0)=1`, `D(0,n)=1`, `D(m+1,n+1) = D(m,n+1) + D(m+1,n) + D(m,n)`.

  * ★ `delannoy_rec` — the defining recurrence (general).
  * `delannoy_row0` / `delannoy_col0` — the boundary `= 1` (general).
  * ★ `delannoy_symm'` — `D(m,n) = D(n,m)` (general, strong induction on `m+n`).
  * `delannoy_table` — incl. the central Delannoy `1,3,13,63,321`.

`delannoy` is fuel-based (`Nat.strongRecOn` fuel-irrelevance; the naive 2-arg def
is well-founded but does not reduce under `decide`).  Genuinely absent.  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.DelannoyNumbers

def delannoyF : Nat → Nat → Nat → Nat
  | _,     _,     0     => 1
  | _,     0,     _ + 1 => 1
  | f + 1, m + 1, n + 1 =>
      delannoyF f m (n + 1) + delannoyF f (m + 1) n + delannoyF f m n
  | 0,     _ + 1, _ + 1 => 0

def delannoy (m n : Nat) : Nat := delannoyF (m + n) m n

theorem delannoyF_eq :
    ∀ s m n f g, m + n = s → s ≤ f → s ≤ g → delannoyF f m n = delannoyF g m n := by
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro m n f g hsum hf hg
    match m, n with
    | m, 0 =>
      rw [delannoyF.eq_1, delannoyF.eq_1]
    | 0, n + 1 =>
      rw [delannoyF.eq_2, delannoyF.eq_2]
    | m + 1, n + 1 =>
      have hge1 : 1 ≤ s := by rw [← hsum]; exact Nat.succ_le_succ (Nat.zero_le _)
      have hfpos : 1 ≤ f := Nat.le_trans hge1 hf
      have hgpos : 1 ≤ g := Nat.le_trans hge1 hg
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 :=
        ⟨f - 1, (Nat.succ_pred_eq_of_pos hfpos).symm⟩
      obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 :=
        ⟨g - 1, (Nat.succ_pred_eq_of_pos hgpos).symm⟩
      rw [delannoyF.eq_3, delannoyF.eq_3]
      have e1 : m + (n + 1) = m + n + 1 := by rw [Nat.add_succ]
      have e2 : (m + 1) + n = m + n + 1 := by rw [Nat.add_right_comm]
      have hssucc : s = (m + n + 1) + 1 := by
        rw [← hsum]; rw [Nat.add_succ, Nat.succ_add]
      have hs1 : m + n + 1 < s := by rw [hssucc]; exact Nat.lt_succ_self _
      have hs3 : m + n < s := Nat.lt_of_succ_lt hs1
      have hf1 : m + n + 1 ≤ f := Nat.le_of_succ_le_succ (Nat.le_trans hs1 hf)
      have hg1 : m + n + 1 ≤ g := Nat.le_of_succ_le_succ (Nat.le_trans hs1 hg)
      have hf0 : m + n ≤ f := Nat.le_trans (Nat.le_succ _) hf1
      have hg0 : m + n ≤ g := Nat.le_trans (Nat.le_succ _) hg1
      have r1 : delannoyF f m (n + 1) = delannoyF g m (n + 1) :=
        ih (m + n + 1) hs1 m (n + 1) f g e1 hf1 hg1
      have r2 : delannoyF f (m + 1) n = delannoyF g (m + 1) n :=
        ih (m + n + 1) hs1 (m + 1) n f g e2 hf1 hg1
      have r3 : delannoyF f m n = delannoyF g m n :=
        ih (m + n) hs3 m n f g rfl hf0 hg0
      rw [r1, r2, r3]

/-- `delannoyF f m n = delannoy m n` whenever `fuel ≥ m + n`. -/
theorem delannoyF_eq_delannoy (f m n : Nat) (h : m + n ≤ f) :
    delannoyF f m n = delannoy m n :=
  delannoyF_eq (m + n) m n f (m + n) rfl h (Nat.le_refl _)

/-- ★ **Defining recurrence**:
    `D(m+1, n+1) = D(m, n+1) + D(m+1, n) + D(m, n)`. -/
theorem delannoy_rec (m n : Nat) :
    delannoy (m + 1) (n + 1)
      = delannoy m (n + 1) + delannoy (m + 1) n + delannoy m n := by
  show delannoyF ((m + 1) + (n + 1)) (m + 1) (n + 1)
      = delannoy m (n + 1) + delannoy (m + 1) n + delannoy m n
  have hf : (m + 1) + (n + 1) = (m + n + 1) + 1 := by
    rw [Nat.add_succ, Nat.succ_add]
  rw [hf, delannoyF.eq_3]
  have h1 : m + (n + 1) ≤ m + n + 1 := by rw [Nat.add_succ]; exact Nat.le_refl _
  have h2 : (m + 1) + n ≤ m + n + 1 := by rw [Nat.add_right_comm]; exact Nat.le_refl _
  have h3 : m + n ≤ m + n + 1 := Nat.le_succ _
  rw [delannoyF_eq_delannoy (m + n + 1) m (n + 1) h1,
      delannoyF_eq_delannoy (m + n + 1) (m + 1) n h2,
      delannoyF_eq_delannoy (m + n + 1) m n h3]

/-- `D(m, 0) = 1`. -/
theorem delannoy_row0 (m : Nat) : delannoy m 0 = 1 := by
  show delannoyF (m + 0) m 0 = 1
  rw [delannoyF.eq_1]

/-- `D(0, n) = 1`. -/
theorem delannoy_col0 (n : Nat) : delannoy 0 n = 1 := by
  show delannoyF (0 + n) 0 n = 1
  cases n with
  | zero => rw [delannoyF.eq_1]
  | succ k => rw [delannoyF.eq_2]

/-- **Value table** including the central Delannoy numbers `1, 3, 13, 63, 321`. -/
theorem delannoy_table :
    delannoy 0 0 = 1 ∧ delannoy 1 0 = 1 ∧ delannoy 0 1 = 1
    ∧ delannoy 1 1 = 3 ∧ delannoy 2 1 = 5 ∧ delannoy 1 2 = 5
    ∧ delannoy 2 2 = 13 ∧ delannoy 2 3 = 25 ∧ delannoy 3 2 = 25
    ∧ delannoy 3 3 = 63 ∧ delannoy 4 4 = 321 := by
  decide

/-- ★ **Symmetry** `D(m, n) = D(n, m)` — by strong induction on `m + n`,
    using the boundary values and the recurrence. -/
theorem delannoy_symm : ∀ s m n, m + n = s → delannoy m n = delannoy n m := by
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro m n hsum
    match m, n with
    | 0, n =>
      rw [delannoy_col0, delannoy_row0]
    | m + 1, 0 =>
      rw [delannoy_row0, delannoy_col0]
    | m + 1, n + 1 =>
      rw [delannoy_rec, delannoy_rec]
      -- LHS terms: D(m,n+1) + D(m+1,n) + D(m,n)
      -- RHS terms: D(n,m+1) + D(n+1,m) + D(n,m)
      have hssucc : s = (m + n + 1) + 1 := by
        rw [← hsum]; rw [Nat.add_succ, Nat.succ_add]
      have hs1 : m + n + 1 < s := by rw [hssucc]; exact Nat.lt_succ_self _
      have hs3 : m + n < s := Nat.lt_of_succ_lt hs1
      -- D(m, n+1) = D(n+1, m)
      have e1 : m + (n + 1) = m + n + 1 := by rw [Nat.add_succ]
      have r1 : delannoy m (n + 1) = delannoy (n + 1) m :=
        ih (m + n + 1) hs1 m (n + 1) e1
      -- D(m+1, n) = D(n, m+1)
      have e2 : (m + 1) + n = m + n + 1 := by rw [Nat.add_right_comm]
      have r2 : delannoy (m + 1) n = delannoy n (m + 1) :=
        ih (m + n + 1) hs1 (m + 1) n e2
      -- D(m, n) = D(n, m)
      have r3 : delannoy m n = delannoy n m :=
        ih (m + n) hs3 m n rfl
      rw [r1, r2, r3]
      -- goal: (D(n+1,m) + D(n,m+1)) + D(n,m) = (D(n,m+1) + D(n+1,m)) + D(n,m)
      rw [Nat.add_comm (delannoy (n + 1) m) (delannoy n (m + 1))]

/-- Symmetry, packaged at `s := m + n`. -/
theorem delannoy_symm' (m n : Nat) : delannoy m n = delannoy n m :=
  delannoy_symm (m + n) m n rfl

end E213.Lib.Math.Combinatorics.DelannoyNumbers
