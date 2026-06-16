import E213.Lib.Math.Combinatorics.Pigeonhole
import E213.Meta.Nat.Max213
import E213.Meta.Nat.EncodePair213

/-!
# Erdős–Szekeres via the constructive label-box pigeonhole (∅-axiom)

`inc a i` / `dec a i` = length of the longest strictly increasing /
decreasing subsequence ending at index `i`.  The box-pigeonhole forces a
**computed** colliding label pair through `exists_collision_lt`.
-/

open E213.Lib.Math.Combinatorics.Pigeonhole
open E213.Meta.Nat.Max213
open E213.Meta.Nat.EncodePair213
open E213.Tactic.NatHelper (sub_add_cancel sub_lt_sub_right le_sub_of_add_le)

namespace E213.Lib.Math.Combinatorics.ErdosSzekeres

/-! ## Bounded max over the first `m` indices

`bmax f m` = `max { f k : k < m }` with the empty max = 0.  Pure fold. -/

/-- `bmax f m = max_{k<m} f k`, empty = 0. -/
def bmax (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m+1 => Nat.max (bmax f m) (f m)

/-- Every `f k` with `k < m` is `≤ bmax f m`. -/
theorem le_bmax (f : Nat → Nat) :
    ∀ (m k : Nat), k < m → f k ≤ bmax f m
  | 0, _, hk => absurd hk (Nat.not_lt_zero _)
  | m+1, k, hk => by
    show f k ≤ Nat.max (bmax f m) (f m)
    rcases Nat.lt_or_ge k m with hlt | hge
    · exact Nat.le_trans (le_bmax f m k hlt) (le_max_left _ _)
    · have hkm : k = m := Nat.le_antisymm (Nat.le_of_lt_succ hk) hge
      exact hkm ▸ le_max_right (bmax f m) (f m)

/-! ## `inc` / `dec` labels by strong recursion on the position

`incVal a m = 1 + max { incVal a k : k < m ∧ a k < a m }`.  The bounded
max ranges only over `k < m`, so the recursion is well-founded.  We model
`a` as `Nat → Nat` (extended); on `Fin n` we apply with `a ∘ Fin.val`.

`maxBelow g j hj` folds `g k _` over `k < j` (where `j ≤ m`), carrying the
`k < m` proof into each call, so the recursion is structurally visible. -/

/-- `max_{k<j} g k`, with the `k < m` witness supplied to `g`.  Empty = 0. -/
def maxBelow {m : Nat} (g : (k : Nat) → k < m → Nat) :
    (j : Nat) → j ≤ m → Nat
  | 0, _ => 0
  | j+1, hj =>
    Nat.max (maxBelow g j (Nat.le_of_lt hj))
            (g j (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj))

/-- Increasing-label value at position `m`.  Strong recursion via `maxBelow`,
    which only ever calls `incVal a k` for `k < m`. -/
def incVal (a : Nat → Nat) (m : Nat) : Nat :=
  1 + maxBelow (m := m)
    (fun k hk => if a k < a m then incVal a k else 0) m (Nat.le_refl m)
  decreasing_by exact hk

/-- Decreasing-label value at position `m`: same recursion with `a m < a k`. -/
def decVal (a : Nat → Nat) (m : Nat) : Nat :=
  1 + maxBelow (m := m)
    (fun k hk => if a m < a k then decVal a k else 0) m (Nat.le_refl m)
  decreasing_by exact hk

/-! ## `maxBelow` lower bound -/

/-- Any in-range entry `g k hk` (with `k < j`) is `≤ maxBelow g j hj`. -/
theorem le_maxBelow {m : Nat} (g : (k : Nat) → k < m → Nat) :
    ∀ (j : Nat) (hj : j ≤ m) (k : Nat) (hk : k < m) (hkj : k < j),
      g k hk ≤ maxBelow g j hj
  | 0, _, _, _, hkj => absurd hkj (Nat.not_lt_zero _)
  | j+1, hj, k, hk, hkj => by
    show g k hk ≤ Nat.max (maxBelow g j (Nat.le_of_lt hj)) _
    rcases Nat.lt_or_ge k j with hlt | hge
    · exact Nat.le_trans (le_maxBelow g j (Nat.le_of_lt hj) k hk hlt)
        (le_max_left _ _)
    · have hkj' : k = j := Nat.le_antisymm (Nat.le_of_lt_succ hkj) hge
      -- g k hk = g j _ since k = j (proof irrelevance on the bound)
      have : g k hk = g j (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj) := by
        subst hkj'; rfl
      rw [this]
      exact le_max_right _ _

/-- `maxBelow` is attained: it is either `0` or equals some in-range `g k`. -/
theorem maxBelow_attained {m : Nat} (g : (k : Nat) → k < m → Nat) :
    ∀ (j : Nat) (hj : j ≤ m),
      maxBelow g j hj = 0 ∨ ∃ (k : Nat) (hk : k < m), k < j ∧ g k hk = maxBelow g j hj
  | 0, _ => Or.inl rfl
  | j+1, hj => by
    show (Nat.max (maxBelow g j (Nat.le_of_lt hj))
            (g j (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj)) = 0)
         ∨ _
    let hjm : j < m := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
    let mb := maxBelow g j (Nat.le_of_lt hj)
    let gj := g j hjm
    -- compare mb and gj
    rcases Nat.lt_or_ge mb gj with hlt | hge
    · -- max = gj, attained at j
      have hmax : Nat.max mb gj = gj := by
        rw [E213.Meta.Nat.AddMod213.max_comm]
        exact max_eq_left (Nat.le_of_lt hlt)
      refine Or.inr ⟨j, hjm, Nat.lt_succ_self j, ?_⟩
      show gj = Nat.max mb gj
      rw [hmax]
    · -- max = mb
      have hmax : Nat.max mb gj = mb := max_eq_left hge
      rcases maxBelow_attained g j (Nat.le_of_lt hj) with h0 | ⟨k, hk, hkj, hgk⟩
      · -- mb = 0 ⟹ max = gj (since gj ≥ mb = 0), attained at j
        refine Or.inr ⟨j, hjm, Nat.lt_succ_self j, ?_⟩
        show gj = Nat.max mb gj
        have hgj0 : gj = 0 := Nat.le_antisymm (h0 ▸ hge) (Nat.zero_le _)
        have : gj = mb := hgj0.trans h0.symm
        rw [hmax]; exact this
      · -- attained at k < j ≤ j+1
        refine Or.inr ⟨k, hk, Nat.lt_succ_of_lt hkj, ?_⟩
        show g k hk = Nat.max mb gj
        rw [hmax]; exact hgk

/-! ## Key monotonicity: a strict step raises the label -/

/-- `1 ≤ incVal a m` always. -/
theorem one_le_incVal (a : Nat → Nat) (m : Nat) : 1 ≤ incVal a m := by
  rw [incVal.eq_def]
  exact Nat.le_add_right 1 _

/-- `1 ≤ decVal a m` always. -/
theorem one_le_decVal (a : Nat → Nat) (m : Nat) : 1 ≤ decVal a m := by
  rw [decVal.eq_def]
  exact Nat.le_add_right 1 _

/-- **Increasing-label monotonicity.** If `k < m` and `a k < a m` then
    `incVal a k < incVal a m`. -/
theorem inc_lt_of_lt (a : Nat → Nat) {k m : Nat}
    (hkm : k < m) (halt : a k < a m) : incVal a k < incVal a m := by
  -- incVal a m = 1 + maxBelow g m, and g k hkm = incVal a k (since a k < a m).
  have hunfold : incVal a m =
      1 + maxBelow (m := m)
        (fun k' hk' => if a k' < a m then incVal a k' else 0) m
        (Nat.le_refl m) := by
    rw [incVal.eq_def]
  let g : (k' : Nat) → k' < m → Nat :=
    fun k' _ => if a k' < a m then incVal a k' else 0
  have hgk : g k hkm = incVal a k := by
    show (if a k < a m then incVal a k else 0) = incVal a k
    rw [if_pos halt]
  have hle : incVal a k ≤ maxBelow (m := m) g m (Nat.le_refl m) := by
    rw [← hgk]
    exact le_maxBelow g m (Nat.le_refl m) k hkm hkm
  rw [hunfold]
  -- incVal a k ≤ M  ⟹  incVal a k < 1 + M  (= M + 1)
  have h1M : 1 + maxBelow (m := m) g m (Nat.le_refl m)
           = maxBelow (m := m) g m (Nat.le_refl m) + 1 :=
    Nat.add_comm 1 _
  rw [h1M]
  exact Nat.lt_succ_of_le hle

/-- **Decreasing-label monotonicity.** If `k < m` and `a m < a k` then
    `decVal a k < decVal a m`. -/
theorem dec_lt_of_lt (a : Nat → Nat) {k m : Nat}
    (hkm : k < m) (halt : a m < a k) : decVal a k < decVal a m := by
  have hunfold : decVal a m =
      1 + maxBelow (m := m)
        (fun k' hk' => if a m < a k' then decVal a k' else 0) m
        (Nat.le_refl m) := by
    rw [decVal.eq_def]
  let g : (k' : Nat) → k' < m → Nat :=
    fun k' _ => if a m < a k' then decVal a k' else 0
  have hgk : g k hkm = decVal a k := by
    show (if a m < a k then decVal a k else 0) = decVal a k
    rw [if_pos halt]
  have hle : decVal a k ≤ maxBelow (m := m) g m (Nat.le_refl m) := by
    rw [← hgk]
    exact le_maxBelow g m (Nat.le_refl m) k hkm hkm
  rw [hunfold]
  have h1M : 1 + maxBelow (m := m) g m (Nat.le_refl m)
           = maxBelow (m := m) g m (Nat.le_refl m) + 1 :=
    Nat.add_comm 1 _
  rw [h1M]
  exact Nat.lt_succ_of_le hle

/-! ## Data-valued attainment (for the explicit subsequence, choice-free)

`maxBelow_attained` lives in `Prop` — extracting the witnessing index from
it would need choice.  `maxBelowArg` returns the index *as data* (a
`Subtype`), so the predecessor function is choice-free. -/

/-- Data-valued max attainment: returns the maximizing index `< j` (when the
    max is positive) as a `PSigma`, together with `k < m`, `k < j`, and the
    value-attainment equation. -/
def maxBelowArg {m : Nat} (g : (k : Nat) → k < m → Nat) :
    (j : Nat) → (hj : j ≤ m) →
      (Σ' (k : Nat) (hk : k < m), k < j ∧ g k hk = maxBelow g j hj)
        ⊕ PLift (maxBelow g j hj = 0)
  | 0, _ => Sum.inr (PLift.up rfl)
  | j+1, hj => by
    have hjm : j < m := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
    by_cases hlt : maxBelow g j (Nat.le_of_lt hj) < g j hjm
    · -- max attained at j
      refine Sum.inl ⟨j, hjm, Nat.lt_succ_self j, ?_⟩
      show g j hjm = Nat.max (maxBelow g j (Nat.le_of_lt hj)) (g j hjm)
      rw [E213.Meta.Nat.AddMod213.max_comm]
      exact (max_eq_left (Nat.le_of_lt hlt)).symm
    · -- max = maxBelow g j; recurse
      have hge : g j hjm ≤ maxBelow g j (Nat.le_of_lt hj) := Nat.le_of_not_lt hlt
      have hmax : maxBelow g (j+1) hj = maxBelow g j (Nat.le_of_lt hj) := by
        show Nat.max (maxBelow g j (Nat.le_of_lt hj)) (g j hjm)
              = maxBelow g j (Nat.le_of_lt hj)
        exact max_eq_left hge
      match maxBelowArg g j (Nat.le_of_lt hj) with
      | Sum.inl ⟨k, hk, hkj, hgk⟩ =>
        exact Sum.inl ⟨k, hk, Nat.lt_succ_of_lt hkj, by rw [hmax]; exact hgk⟩
      | Sum.inr h0 =>
        exact Sum.inr (PLift.up (by rw [hmax]; exact h0.down))

/-! ## Data-valued predecessor (choice-free) -/

/-- Choice-free predecessor: from `2 ≤ incVal A m` compute `k < m` with
    `A k < A m` and `incVal A k + 1 = incVal A m`, *as data*. -/
def incPredData (A : Nat → Nat) (m : Nat) (hm : 2 ≤ incVal A m) :
    Σ' (k : Nat), k < m ∧ A k < A m ∧ incVal A k + 1 = incVal A m := by
  have hunfold : incVal A m =
      1 + maxBelow (m := m)
        (fun k' hk' => if A k' < A m then incVal A k' else 0) m
        (Nat.le_refl m) := by
    rw [incVal.eq_def]
  let g : (k' : Nat) → k' < m → Nat :=
    fun k' _ => if A k' < A m then incVal A k' else 0
  have hmb_eq : maxBelow (m := m) g m (Nat.le_refl m) + 1 = incVal A m := by
    rw [hunfold]; exact Nat.add_comm _ 1
  have hmb_pos : 1 ≤ maxBelow (m := m) g m (Nat.le_refl m) := by
    have h2 : 2 ≤ maxBelow (m := m) g m (Nat.le_refl m) + 1 := hmb_eq ▸ hm
    exact Nat.le_of_succ_le_succ h2
  match maxBelowArg g m (Nat.le_refl m) with
  | Sum.inr h0 =>
    exact absurd (by rw [← h0.down]; exact hmb_pos : (1:Nat) ≤ 0)
      (Nat.not_succ_le_zero 0)
  | Sum.inl ⟨k, hk, _, hgk⟩ =>
    have hge1 : 1 ≤ g k hk := by rw [hgk]; exact hmb_pos
    -- branch must be true (else g k = 0)
    have hak : A k < A m := by
      rcases Nat.lt_or_ge (A k) (A m) with h | h
      · exact h
      · exfalso
        have hgk0 : g k hk = 0 := by
          show (if A k < A m then incVal A k else 0) = 0
          rw [if_neg (Nat.not_lt_of_le h)]
        exact absurd (by rw [← hgk0]; exact hge1 : (1:Nat) ≤ 0)
          (Nat.not_succ_le_zero 0)
    refine ⟨k, hk, hak, ?_⟩
    have hgk' : g k hk = incVal A k := by
      show (if A k < A m then incVal A k else 0) = incVal A k
      rw [if_pos hak]
    have hik : incVal A k = maxBelow (m := m) g m (Nat.le_refl m) := by
      rw [← hgk']; exact hgk
    rw [hik]; exact hmb_eq

/-! ## Predecessor step: peel one element off an increasing run -/

/-- If `incVal A m ≥ 2` there is an earlier `k < m` with `a k < a m` and
    `incVal A k + 1 = incVal A m`.  This is the argmax witness inside the
    bounded max; iterating it reconstructs the increasing subsequence. -/
theorem inc_pred (A : Nat → Nat) {m : Nat} (hm : 2 ≤ incVal A m) :
    ∃ (k : Nat), k < m ∧ A k < A m ∧ incVal A k + 1 = incVal A m := by
  have hunfold : incVal A m =
      1 + maxBelow (m := m)
        (fun k' hk' => if A k' < A m then incVal A k' else 0) m
        (Nat.le_refl m) := by
    rw [incVal.eq_def]
  let g : (k' : Nat) → k' < m → Nat :=
    fun k' _ => if A k' < A m then incVal A k' else 0
  -- maxBelow g m = incVal A m - 1 ≥ 1
  have hmb_eq : maxBelow (m := m) g m (Nat.le_refl m) + 1 = incVal A m := by
    rw [hunfold]; exact Nat.add_comm _ 1
  have hmb_pos : 1 ≤ maxBelow (m := m) g m (Nat.le_refl m) := by
    have : 2 ≤ maxBelow (m := m) g m (Nat.le_refl m) + 1 := hmb_eq ▸ hm
    exact Nat.le_of_succ_le_succ this
  -- the max is attained at some k
  rcases maxBelow_attained g m (Nat.le_refl m) with h0 | ⟨k, hk, _, hgk⟩
  · have : (1 : Nat) ≤ 0 := by rw [← h0]; exact hmb_pos
    exact absurd this (Nat.not_succ_le_zero 0)
  · -- g k hk = maxBelow ≥ 1, so the `if` is the true branch
    have hge1 : 1 ≤ g k hk := by rw [hgk]; exact hmb_pos
    -- decide the branch
    rcases Nat.lt_or_ge (A k) (A m) with hak | hak
    · refine ⟨k, hk, hak, ?_⟩
      have hgk' : g k hk = incVal A k := by
        show (if A k < A m then incVal A k else 0) = incVal A k
        rw [if_pos hak]
      -- incVal A k = maxBelow, and maxBelow + 1 = incVal A m
      have : incVal A k = maxBelow (m := m) g m (Nat.le_refl m) :=
        hgk' ▸ hgk
      rw [this]; exact hmb_eq
    · -- a k ≥ a m ⟹ if-false ⟹ g k hk = 0, contradicting ≥ 1
      exfalso
      have hgk0 : g k hk = 0 := by
        show (if A k < A m then incVal A k else 0) = 0
        rw [if_neg (Nat.not_lt_of_le hak)]
      have : (1 : Nat) ≤ 0 := by rw [← hgk0]; exact hge1
      exact absurd this (Nat.not_succ_le_zero 0)

/-! ## Extending `a : Fin n → Nat` to `Nat → Nat` -/

/-- Extend a finite sequence to `Nat → Nat` (0 outside range). -/
def ext {n : Nat} (a : Fin n → Nat) : Nat → Nat :=
  fun k => if h : k < n then a ⟨k, h⟩ else 0

/-- On its range, `ext a` agrees with `a`. -/
theorem ext_apply {n : Nat} (a : Fin n → Nat) (i : Fin n) :
    ext a i.val = a i := by
  show (if h : i.val < n then a ⟨i.val, h⟩ else 0) = a i
  rw [dif_pos i.isLt]

/-! ## The pairing `(p,q) ↦ p*(s-1) + q` is injective for `q < s-1`

Reuses `EncodePair213.encode_div` / `encode_mod` as the decoder. -/

/-- Pairing injectivity: `p₁*S + q₁ = p₂*S + q₂` with `q₁,q₂ < S` (and `0 < S`)
    forces `p₁ = p₂` and `q₁ = q₂`. -/
theorem pack_inj {S p₁ q₁ p₂ q₂ : Nat} (hS : 0 < S)
    (hq₁ : q₁ < S) (hq₂ : q₂ < S)
    (heq : p₁ * S + q₁ = p₂ * S + q₂) : p₁ = p₂ ∧ q₁ = q₂ := by
  have hp : p₁ = p₂ := by
    have e₁ : (p₁ * S + q₁) / S = p₁ := encode_div hS p₁ q₁ hq₁
    have e₂ : (p₂ * S + q₂) / S = p₂ := encode_div hS p₂ q₂ hq₂
    rw [heq] at e₁
    exact e₁.symm.trans e₂
  have hq : q₁ = q₂ := by
    have e₁ : (p₁ * S + q₁) % S = q₁ := encode_mod hS p₁ q₁ hq₁
    have e₂ : (p₂ * S + q₂) % S = q₂ := encode_mod hS p₂ q₂ hq₂
    rw [heq] at e₁
    exact e₁.symm.trans e₂
  exact ⟨hp, hq⟩

/-- `p < P` and `q < S` ⟹ `p*S + q < P*S`. -/
theorem pack_lt {p q P S : Nat} (hp : p < P) (hq : q < S) :
    p * S + q < P * S := by
  have h1 : p * S + q < p * S + S :=
    Nat.add_lt_add_left hq (p * S)
  have h2 : p * S + S = (p + 1) * S := by
    rw [Nat.succ_mul]
  have h3 : (p + 1) * S ≤ P * S :=
    Nat.mul_le_mul_right S (Nat.succ_le_of_lt hp)
  exact Nat.lt_of_lt_of_le (h2 ▸ h1) h3

/-! ## Box-pigeonhole helper — the forcing heart

If every label is boxed (`incVal < r` and `decVal < s`) while
`(r-1)*(s-1) < n`, the constructive collision finder returns a colliding
pair whose strict order contradicts equal labels. -/

/-- **Box pigeonhole (forcing heart).**  With distinct values and the box
    `∀ i, incVal < r ∧ decVal < s`, having more than `(r-1)*(s-1)` indices is
    impossible. -/
theorem box_pigeonhole {n : Nat} (r s : Nat) (a : Fin n → Nat)
    (hn : (r - 1) * (s - 1) < n)
    (hdist : ∀ i j : Fin n, i ≠ j → a i ≠ a j)
    (hbox : ∀ i : Fin n, incVal (ext a) i.val < r ∧ decVal (ext a) i.val < s) :
    False := by
  -- Abbreviation (definitional).
  let A : Nat → Nat := ext a
  have hA : A = ext a := rfl
  -- r ≥ 1 and s ≥ 1 from the box together with `1 ≤ incVal`.
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- n = 0 : but then (r-1)*(s-1) < 0 impossible
      exact absurd (hn0 ▸ hn) (Nat.not_lt_zero _)
    · have i0 : Fin n := ⟨0, hnpos⟩
      exact Nat.le_trans (one_le_incVal A i0.val) (Nat.le_of_lt (hbox i0).1)
  -- Build the label map into Fin ((r-1)*(s-1)).
  let S := s - 1
  let g : Fin n → Fin ((r - 1) * (s - 1)) := fun i =>
    ⟨(incVal A i.val - 1) * S + (decVal A i.val - 1),
     by
       have hinc : incVal A i.val < r := (hbox i).1
       have hdec : decVal A i.val < s := (hbox i).2
       -- incVal - 1 < r - 1
       have hp : incVal A i.val - 1 < r - 1 :=
         sub_lt_sub_right 1 (one_le_incVal A i.val) hinc
       -- decVal - 1 < s - 1 = S
       have hq : decVal A i.val - 1 < S :=
         sub_lt_sub_right 1 (one_le_decVal A i.val) hdec
       exact pack_lt hp hq⟩
  -- Constructive collision.
  obtain ⟨i, j, hij, hgij⟩ := exists_collision_lt hn g
  -- Equal labels ⟹ equal packed values ⟹ equal incVal, equal decVal.
  have hval : (incVal A i.val - 1) * S + (decVal A i.val - 1)
            = (incVal A j.val - 1) * S + (decVal A j.val - 1) :=
    congrArg Fin.val hgij
  -- S > 0:  from s ≥ 1 we need s ≥ 2 actually (decVal ≥ 1 < s ⟹ s ≥ 2 ⟹ S ≥ 1).
  have hs2 : 2 ≤ s := by
    have i0 : Fin n := ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) hn⟩
    have : 1 ≤ decVal A i0.val := one_le_decVal A i0.val
    exact Nat.lt_of_le_of_lt this (hbox i0).2
  have hSpos : 0 < S := Nat.lt_of_lt_of_le (Nat.zero_lt_one)
    (le_sub_of_add_le hs2)
  -- bounds q < S for both:
  have hqi : decVal A i.val - 1 < S :=
    sub_lt_sub_right 1 (one_le_decVal A i.val) (hbox i).2
  have hqj : decVal A j.val - 1 < S :=
    sub_lt_sub_right 1 (one_le_decVal A j.val) (hbox j).2
  obtain ⟨hpeq, hqeq⟩ := pack_inj hSpos hqi hqj hval
  -- recover incVal i = incVal j and decVal i = decVal j
  have hinc_eq : incVal A i.val = incVal A j.val := by
    have ci : incVal A i.val - 1 + 1 = incVal A i.val :=
      sub_add_cancel (one_le_incVal A i.val)
    have cj : incVal A j.val - 1 + 1 = incVal A j.val :=
      sub_add_cancel (one_le_incVal A j.val)
    rw [← ci, ← cj, hpeq]
  have hdec_eq : decVal A i.val = decVal A j.val := by
    have ci : decVal A i.val - 1 + 1 = decVal A i.val :=
      sub_add_cancel (one_le_decVal A i.val)
    have cj : decVal A j.val - 1 + 1 = decVal A j.val :=
      sub_add_cancel (one_le_decVal A j.val)
    rw [← ci, ← cj, hqeq]
  -- distinctness:  a i ≠ a j
  have haij : a i ≠ a j := hdist i j hij
  -- WLOG i.val < j.val.
  have hvalne : i.val ≠ j.val := fun e => hij (Fin.ext e)
  rcases Nat.lt_or_ge i.val j.val with hlt | hge
  · -- i.val < j.val : split on a i < a j or a i > a j
    rcases Nat.lt_or_ge (a i) (a j) with hai | hai
    · -- a i < a j ⟹ incVal i < incVal j, contradicting hinc_eq
      have : incVal A i.val < incVal A j.val :=
        inc_lt_of_lt A hlt (by rw [hA, ext_apply, ext_apply]; exact hai)
      exact Nat.lt_irrefl _ (hinc_eq ▸ this)
    · -- a i ≥ a j and a i ≠ a j ⟹ a j < a i ⟹ decVal i < decVal j
      have hgt : a j < a i := Nat.lt_of_le_of_ne hai (fun e => haij e.symm)
      have : decVal A i.val < decVal A j.val :=
        dec_lt_of_lt A hlt (by rw [hA, ext_apply, ext_apply]; exact hgt)
      exact Nat.lt_irrefl _ (hdec_eq ▸ this)
  · -- j.val ≤ i.val and i.val ≠ j.val ⟹ j.val < i.val (symmetric)
    have hlt : j.val < i.val := Nat.lt_of_le_of_ne hge (fun e => hvalne e.symm)
    rcases Nat.lt_or_ge (a j) (a i) with haj | haj
    · have hlt2 : incVal A j.val < incVal A i.val :=
        inc_lt_of_lt A hlt (by rw [hA, ext_apply, ext_apply]; exact haj)
      exact Nat.lt_irrefl _ (hinc_eq ▸ hlt2)
    · have hgt : a i < a j := Nat.lt_of_le_of_ne haj haij
      have hlt2 : decVal A j.val < decVal A i.val :=
        dec_lt_of_lt A hlt (by rw [hA, ext_apply, ext_apply]; exact hgt)
      exact Nat.lt_irrefl _ (hdec_eq ▸ hlt2)

/-! ## Constructive bounded search → the outer `Or`

`scanBox` walks positions `0..m` deciding each `incVal < r` / `decVal < s`
(both `Nat.decLt`); it returns a label-violating witness, or a pointwise
in-box proof.  No `Classical`, no decidable-`∃` instance. -/

/-- Bounded search over the first `m` positions. -/
theorem scanBox {n : Nat} (A : Nat → Nat) (r s : Nat) :
    ∀ (m : Nat), m ≤ n →
      (∃ i : Fin n, r ≤ incVal A i.val)
      ∨ (∃ i : Fin n, s ≤ decVal A i.val)
      ∨ (∀ i : Fin n, i.val < m → incVal A i.val < r ∧ decVal A i.val < s)
  | 0, _ => Or.inr (Or.inr (fun i hi => absurd hi (Nat.not_lt_zero _)))
  | m+1, hm => by
    have hmn : m < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm
    let p : Fin n := ⟨m, hmn⟩
    rcases scanBox A r s m (Nat.le_of_lt hmn) with hinc | hdec | hball
    · exact Or.inl hinc
    · exact Or.inr (Or.inl hdec)
    · -- decide the two bounds at position p
      rcases Nat.lt_or_ge (incVal A p.val) r with hpi | hpi
      · rcases Nat.lt_or_ge (decVal A p.val) s with hpd | hpd
        · -- both in box at p : extend hball to m+1
          refine Or.inr (Or.inr (fun i hi => ?_))
          rcases Nat.lt_or_ge i.val m with hlt | hge
          · exact hball i hlt
          · have hieq : i.val = m :=
              Nat.le_antisymm (Nat.le_of_lt_succ hi) hge
            have hip : i = p := Fin.ext hieq
            exact hip ▸ ⟨hpi, hpd⟩
        · exact Or.inr (Or.inl ⟨p, hpd⟩)
      · exact Or.inl ⟨p, hpi⟩

/-! ## Explicit decreasing-index chain (the strictly-monotone subsequence)

`idxChain A m t` walks `t` predecessor steps from `m`.  Reversed, it is the
strictly-increasing subsequence of length `incVal A m` ending at `m`. -/

/-- Total predecessor step: peel one element if the label allows, else fix. -/
def idxStep (A : Nat → Nat) (m : Nat) : Nat :=
  if h : 2 ≤ incVal A m then (incPredData A m h).1 else m

/-- `idxChain A m t` = index after `t` predecessor steps from `m`. -/
def idxChain (A : Nat → Nat) (m : Nat) : Nat → Nat
  | 0 => m
  | t+1 => idxStep A (idxChain A m t)

/-- Label invariant: after `t < incVal A m` steps the label is `incVal A m - t`. -/
theorem idxChain_label (A : Nat → Nat) (m : Nat) :
    ∀ t, t < incVal A m → incVal A (idxChain A m t) = incVal A m - t
  | 0, _ => by show incVal A m = incVal A m - 0; rw [Nat.sub_zero]
  | t+1, ht => by
    have htlt : t < incVal A m := Nat.lt_of_succ_lt ht
    have ih : incVal A (idxChain A m t) = incVal A m - t :=
      idxChain_label A m t htlt
    -- since t+1 < incVal A m, incVal A m - t ≥ 2
    have hge2 : 2 ≤ incVal A (idxChain A m t) := by
      rw [ih]
      -- t+1 < V ⟹ V - t ≥ 2
      have h2 : t + 2 ≤ incVal A m := ht
      exact le_sub_of_add_le (by rw [Nat.add_comm]; exact h2)
    show incVal A (idxStep A (idxChain A m t)) = incVal A m - (t+1)
    have hstep : idxStep A (idxChain A m t) = (incPredData A (idxChain A m t) hge2).1 := by
      show (if h : 2 ≤ incVal A (idxChain A m t) then _ else _) = _
      rw [dif_pos hge2]
    rw [hstep]
    have hpred := (incPredData A (idxChain A m t) hge2).2.2.2
    -- incVal pred + 1 = incVal (idxChain t) = V - t
    have : incVal A (incPredData A (idxChain A m t) hge2).1 + 1 = incVal A m - t := by
      rw [hpred]; exact ih
    -- so incVal pred = V - t - 1 = V - (t+1)
    have hsub : incVal A (incPredData A (idxChain A m t) hge2).1 = incVal A m - t - 1 := by
      rw [← this]
      exact (E213.Tactic.NatHelper.add_sub_cancel_right _ 1).symm
    -- incVal m - t - 1 = incVal m - (t+1)  (definitional: Nat.sub _ (t+1) = pred (Nat.sub _ t))
    rw [hsub]
    show incVal A m - t - 1 = incVal A m - (t + 1)
    rfl

/-- One chain step strictly drops both the index and the value, when in range. -/
theorem idxChain_step (A : Nat → Nat) (m : Nat) (t : Nat) (ht : t + 1 < incVal A m) :
    idxChain A m (t+1) < idxChain A m t
    ∧ A (idxChain A m (t+1)) < A (idxChain A m t) := by
  have htlt : t < incVal A m := Nat.lt_of_succ_lt ht
  have hlabel : incVal A (idxChain A m t) = incVal A m - t :=
    idxChain_label A m t htlt
  have hge2 : 2 ≤ incVal A (idxChain A m t) := by
    rw [hlabel]
    exact le_sub_of_add_le (by rw [Nat.add_comm]; exact (ht : t + 2 ≤ incVal A m))
  have hstep : idxChain A m (t+1) = (incPredData A (idxChain A m t) hge2).1 := by
    show idxStep A (idxChain A m t) = _
    show (if h : 2 ≤ incVal A (idxChain A m t) then _ else _) = _
    rw [dif_pos hge2]
  have hpd := (incPredData A (idxChain A m t) hge2).2
  rw [hstep]
  exact ⟨hpd.1, hpd.2.1⟩

/-- Every chain index is `≤ m` (so reversing into `Fin n` is safe). -/
theorem idxChain_le (A : Nat → Nat) (m : Nat) :
    ∀ t, t < incVal A m → idxChain A m t ≤ m
  | 0, _ => Nat.le_refl m
  | t+1, ht => by
    have htlt : t < incVal A m := Nat.lt_of_succ_lt ht
    have hlt : idxChain A m (t+1) < idxChain A m t := (idxChain_step A m t ht).1
    exact Nat.le_trans (Nat.le_of_lt hlt) (idxChain_le A m t htlt)

/-- Strict antitone comparison: `t < t'` (in range) ⟹ chain index and value
    both strictly drop from `t` to `t'`. -/
theorem idxChain_anti (A : Nat → Nat) (m : Nat) :
    ∀ (d t : Nat), t + (d+1) < incVal A m →
      idxChain A m (t + (d+1)) < idxChain A m t
      ∧ A (idxChain A m (t + (d+1))) < A (idxChain A m t)
  | 0, t, ht => by
    have : t + 1 < incVal A m := ht
    exact idxChain_step A m t this
  | d+1, t, ht => by
    -- t + (d+2) < V.  Step from t to t+1, then anti from t+1 by d+1.
    have ht1 : t + 1 < incVal A m :=
      Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le _)) t) ht
    have hstep : idxChain A m (t+1) < idxChain A m t
               ∧ A (idxChain A m (t+1)) < A (idxChain A m t) :=
      idxChain_step A m t ht1
    have hassoc : t + (d + 2) = (t + 1) + (d + 1) := by
      rw [Nat.add_assoc t 1 (d+1)]
      have : (1 : Nat) + (d + 1) = d + 2 := by
        rw [Nat.add_comm 1 (d+1)]
      rw [this]
    have hrec : (t+1) + (d+1) < incVal A m := by rw [← hassoc]; exact ht
    have hanti := idxChain_anti A m d (t+1) hrec
    rw [hassoc]
    exact ⟨Nat.lt_trans hanti.1 hstep.1, Nat.lt_trans hanti.2 hstep.2⟩

/-! ## Erdős–Szekeres (label form) — the deliverable -/

/-- **Erdős–Szekeres.**  With `(r-1)*(s-1) < n` distinct values, some index
    carries an increasing label `≥ r` or a decreasing label `≥ s`.

    `r ≤ incVal (ext a) i.val` *is* the existence of a strictly increasing
    subsequence of length `r` ending at `i` (by the definition of `incVal`);
    likewise `dec`/`s`. -/
theorem erdos_szekeres {n : Nat} (r s : Nat) (a : Fin n → Nat)
    (hn : (r - 1) * (s - 1) < n)
    (hdist : ∀ i j : Fin n, i ≠ j → a i ≠ a j) :
    (∃ i : Fin n, r ≤ incVal (ext a) i.val)
    ∨ (∃ i : Fin n, s ≤ decVal (ext a) i.val) := by
  rcases scanBox (ext a) r s n (Nat.le_refl n) with hinc | hdec | hball
  · exact Or.inl hinc
  · exact Or.inr hdec
  · -- full box ⟹ box_pigeonhole gives False
    exact (box_pigeonhole r s a hn hdist (fun i => hball i i.isLt)).elim

/-! ## Stretch goal: explicit strictly-increasing subsequence `Fin r → Fin n`

From `r ≤ incVal (ext a) i.val` we read off the actual length-`r` increasing
subsequence: `f p = idxChain (ext a) i.val (r-1-p)`.  `f` is strictly
monotone (as an index map) and `a` is strictly increasing along it. -/

/-- `a + c = b ⟹ b - a = c` (∅-axiom, via `add_sub_cancel_right`). -/
private theorem diff_of_add {a b c : Nat} (h : a + c = b) : b - a = c := by
  rw [← h, Nat.add_comm]
  exact E213.Tactic.NatHelper.add_sub_cancel_right c a

/-- Pure split: `a < b ≤ x` ⟹ `x - a = (x - b) + ((b-a-1) + 1)` — exactly the
    chain-arg gap (`d+1`) that `idxChain_anti` consumes. -/
theorem sub_split {a b x : Nat} (hab : a < b) (hbx : b ≤ x) :
    x - a = (x - b) + ((b - a - 1) + 1) := by
  have hba1 : (b - a - 1) + 1 = b - a := by
    have hpos : 1 ≤ b - a := le_sub_of_add_le (by rw [Nat.add_comm]; exact hab)
    exact sub_add_cancel hpos
  rw [hba1]
  -- decompose:  a + c = b  and  b + e = x
  obtain ⟨c, hc⟩ := Nat.le.dest (Nat.le_of_lt hab)   -- a + c = b
  obtain ⟨e, he⟩ := Nat.le.dest hbx                  -- b + e = x
  have hbma : b - a = c := diff_of_add hc
  have hxmb : x - b = e := diff_of_add he
  -- x - a = e + c
  have hxa : a + (e + c) = x := by
    -- a + (e + c) = (a + c) + e = b + e = x
    have : a + (e + c) = (a + c) + e := by
      rw [Nat.add_comm e c, ← Nat.add_assoc]
    rw [this, hc, he]
  have hxma : x - a = e + c := diff_of_add hxa
  rw [hbma, hxmb, hxma]

/-- **Explicit increasing subsequence.**  If `incVal (ext a) i.val ≥ r` with
    `1 ≤ r`, there is a strictly-monotone index map `f : Fin r → Fin n` along
    which `a` is strictly increasing — a genuine length-`r` increasing
    subsequence ending at `i`. -/
def inc_subseq {n : Nat} (a : Fin n → Nat) (i : Fin n) (r : Nat)
    (hr : 1 ≤ r) (hri : r ≤ incVal (ext a) i.val) :
    Σ' (f : Fin r → Fin n),
      (∀ p q : Fin r, p.val < q.val → (f p).val < (f q).val)
      ∧ (∀ p q : Fin r, p.val < q.val → a (f p) < a (f q)) := by
  let A := ext a
  have hr1lt : r - 1 < incVal A i.val :=
    Nat.lt_of_lt_of_le
      (Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hr) Nat.zero_lt_one) hri
  have hrange : ∀ p : Fin r, r - 1 - p.val < incVal A i.val := fun p =>
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hr1lt
  have hle : ∀ p : Fin r, idxChain A i.val (r - 1 - p.val) ≤ i.val := fun p =>
    idxChain_le A i.val (r - 1 - p.val) (hrange p)
  let f : Fin r → Fin n := fun p =>
    ⟨idxChain A i.val (r - 1 - p.val), Nat.lt_of_le_of_lt (hle p) i.isLt⟩
  have core : ∀ p q : Fin r, p.val < q.val →
      idxChain A i.val (r - 1 - p.val) < idxChain A i.val (r - 1 - q.val)
      ∧ A (idxChain A i.val (r - 1 - p.val))
          < A (idxChain A i.val (r - 1 - q.val)) := by
    intro p q hpq
    have hqle : q.val ≤ r - 1 := Nat.le_sub_one_of_lt q.isLt
    -- chain-arg gap:  r-1-p = (r-1-q) + (d+1),  d = q-p-1
    have heq : r - 1 - p.val
             = (r - 1 - q.val) + (((q.val - p.val) - 1) + 1) :=
      sub_split (a := p.val) (b := q.val) (x := r - 1) hpq hqle
    have hrec : (r - 1 - q.val) + (((q.val - p.val) - 1) + 1) < incVal A i.val := by
      rw [← heq]; exact hrange p
    have hanti :=
      idxChain_anti A i.val ((q.val - p.val) - 1) (r - 1 - q.val) hrec
    rw [← heq] at hanti
    exact hanti
  refine ⟨f, ?_, ?_⟩
  · intro p q hpq; exact (core p q hpq).1
  · intro p q hpq
    -- a (f p) = A (idxChain ...) via ext_apply, since idxChain ≤ i.val < n
    have hfp : a (f p) = A (idxChain A i.val (r - 1 - p.val)) :=
      (ext_apply a (f p)).symm
    have hfq : a (f q) = A (idxChain A i.val (r - 1 - q.val)) :=
      (ext_apply a (f q)).symm
    rw [hfp, hfq]
    exact (core p q hpq).2

end E213.Lib.Math.Combinatorics.ErdosSzekeres
