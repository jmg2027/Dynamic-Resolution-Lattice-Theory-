import E213.Meta.Int213.PolyIntMTactic

/-!
# ∅-axiom integer ordering

Lean-core `Int.lt`/`Int.le` lemmas (`Int.le_trans`, `Int.lt_trichotomy`, …) route through
`propext`/`Quot.sound`.  This module rebuilds exactly the ordering layer needed for the
finite-difference monotonicity bridge directly from the inductive `Int.NonNeg` and the ∅-axiom
ring lemmas of `Core` (constant-free regroupings discharged by `ring_intZ`).

Definitions (Lean core): `a ≤ b := (b - a).NonNeg`, `a < b := a + 1 ≤ b`, `a - b := a + -b`,
`NonNeg` inductive with single constructor `⟨n⟩ : NonNeg (Int.ofNat n)`.
-/

namespace E213.Meta.Int213.Order

open E213.Meta.Int213

/-! ## Constant helpers (where `ring_intZ` cannot normalise literals) -/

theorem sub_zero (a : Int) : a - 0 = a := by
  show a + -0 = a; rw [Int.neg_zero, Int.add_zero]

theorem sub_self_zero (a : Int) : a - a = 0 := add_neg_cancel a

theorem ofNat_succ_sub_one (k : Nat) : Int.ofNat (k + 1) - 1 = Int.ofNat k := by
  show Int.subNatNat (k + 1) 1 = Int.ofNat k
  exact subNatNat_of_le (Nat.le_add_left 1 k)

/-! ## `NonNeg` ↔ `0 ≤` collapse -/

theorem nonneg_of_le_zero {a : Int} (h : (0 : Int) ≤ a) : a.NonNeg := sub_zero a ▸ h

theorem le_zero_of_nonneg {a : Int} (h : a.NonNeg) : (0 : Int) ≤ a :=
  show (a - 0).NonNeg from (sub_zero a).symm ▸ h

theorem le_of_sub_nonneg {a b : Int} (h : (b - a).NonNeg) : a ≤ b := h

theorem sub_nonneg_of_le {a b : Int} (h : a ≤ b) : (b - a).NonNeg := h

/-! ## `≤` -/

theorem le_refl (a : Int) : a ≤ a :=
  show (a - a).NonNeg from (sub_self_zero a).symm ▸ (⟨0⟩ : (0 : Int).NonNeg)

theorem le_trans {a b c : Int} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  have h := add_nonneg (le_zero_of_nonneg hbc) (le_zero_of_nonneg hab)
  rw [show (c - b) + (b - a) = c - a by ring_intZ] at h
  exact nonneg_of_le_zero h

/-! ## `<` ↔ `0 < b - a`, and `<`/`≤` interaction -/

theorem sub_one_nonneg_of_lt {a b : Int} (h : a < b) : (b - a - 1).NonNeg :=
  (show b - (a + 1) = b - a - 1 by ring_intZ) ▸ h

theorem lt_of_sub_one_nonneg {a b : Int} (h : (b - a - 1).NonNeg) : a < b :=
  show (b - (a + 1)).NonNeg from (show b - (a + 1) = b - a - 1 by ring_intZ).symm ▸ h

theorem lt_of_sub_pos {a b : Int} (h : (0 : Int) < b - a) : a < b :=
  lt_of_sub_one_nonneg ((show b - a - 0 - 1 = b - a - 1 by rw [sub_zero]) ▸ sub_one_nonneg_of_lt h)

theorem sub_pos_of_lt {a b : Int} (h : a < b) : (0 : Int) < b - a :=
  lt_of_sub_one_nonneg ((show b - a - 1 = b - a - 0 - 1 by rw [sub_zero]) ▸ sub_one_nonneg_of_lt h)

theorem le_of_lt {a b : Int} (h : a < b) : a ≤ b := by
  have h2 : (0 : Int) ≤ (b - a - 1) + 1 :=
    add_nonneg (le_zero_of_nonneg (sub_one_nonneg_of_lt h)) (le_zero_of_nonneg ⟨1⟩)
  rw [show (b - a - 1) + 1 = b - a by ring_intZ] at h2
  exact nonneg_of_le_zero h2

theorem lt_of_le_of_lt {a b c : Int} (hab : a ≤ b) (hbc : b < c) : a < c := by
  apply lt_of_sub_one_nonneg
  have h := add_nonneg (le_zero_of_nonneg (sub_one_nonneg_of_lt hbc))
    (le_zero_of_nonneg (sub_nonneg_of_le hab))
  rw [show (c - b - 1) + (b - a) = c - a - 1 by ring_intZ] at h
  exact nonneg_of_le_zero h

theorem lt_of_lt_of_le {a b c : Int} (hab : a < b) (hbc : b ≤ c) : a < c := by
  apply lt_of_sub_one_nonneg
  have h := add_nonneg (le_zero_of_nonneg (sub_nonneg_of_le hbc))
    (le_zero_of_nonneg (sub_one_nonneg_of_lt hab))
  rw [show (c - b) + (b - a - 1) = c - a - 1 by ring_intZ] at h
  exact nonneg_of_le_zero h

theorem lt_trans {a b c : Int} (hab : a < b) (hbc : b < c) : a < c :=
  lt_of_lt_of_le hab (le_of_lt hbc)

/-! ## Irreflexivity — the contradiction engine -/

theorem lt_irrefl (a : Int) : ¬ a < a := by
  intro h
  have he : a - a - 1 = -1 := by rw [sub_self_zero]; show (0 : Int) + -1 = -1; rw [zero_add]
  have h1 : ((-1 : Int)).NonNeg := he ▸ sub_one_nonneg_of_lt h
  cases h1

theorem not_le_of_lt {a b : Int} (h : a < b) : ¬ b ≤ a := fun hle => lt_irrefl a (lt_of_lt_of_le h hle)

theorem not_lt_of_lt {a b : Int} (h : a < b) : ¬ b < a := fun h' => lt_irrefl a (lt_trans h h')

/-! ## Addition is order-preserving -/

theorem add_le_add_right {a b : Int} (h : a ≤ b) (c : Int) : a + c ≤ b + c := by
  apply le_of_sub_nonneg
  rw [show (b + c) - (a + c) = b - a by ring_intZ]
  exact sub_nonneg_of_le h

theorem add_lt_add_right {a b : Int} (h : a < b) (c : Int) : a + c < b + c := by
  apply lt_of_sub_one_nonneg
  rw [show (b + c) - (a + c) - 1 = b - a - 1 by ring_intZ]
  exact sub_one_nonneg_of_lt h

theorem succ_le_succ {a b : Int} (h : a ≤ b) : a + 1 ≤ b + 1 := add_le_add_right h 1

theorem add_le_add_left {b c : Int} (h : b ≤ c) (a : Int) : a + b ≤ a + c := by
  apply le_of_sub_nonneg
  rw [show (a + c) - (a + b) = c - b by ring_intZ]
  exact sub_nonneg_of_le h

/-- `0 ≤ x + |x|` — the magnitude dominates the negative part. -/
theorem nonneg_add_natAbs (x : Int) : (0 : Int) ≤ x + Int.ofNat x.natAbs := by
  match x with
  | Int.ofNat p =>
    exact le_zero_of_nonneg
      ((show Int.ofNat p + Int.ofNat (Int.ofNat p).natAbs = Int.ofNat (p + p) from rfl).symm
        ▸ (⟨p + p⟩ : (Int.ofNat (p + p)).NonNeg))
  | Int.negSucc q =>
    have he : Int.negSucc q + Int.ofNat (Int.negSucc q).natAbs = 0 := add_left_neg (Int.ofNat (q + 1))
    rw [he]; exact le_refl 0

/-! ## Sign trichotomy on a single integer, and `sub = 0` -/

theorem pos_zero_or_neg (a : Int) : (0 : Int) < a ∨ a = 0 ∨ a < 0 := by
  match a with
  | Int.ofNat 0 => exact Or.inr (Or.inl rfl)
  | Int.ofNat (k + 1) =>
    refine Or.inl (lt_of_sub_one_nonneg ?_)
    have he : Int.ofNat (k + 1) - 0 - 1 = Int.ofNat k := by rw [sub_zero, ofNat_succ_sub_one]
    exact he ▸ (⟨k⟩ : (Int.ofNat k).NonNeg)
  | Int.negSucc k =>
    refine Or.inr (Or.inr (lt_of_sub_one_nonneg ?_))
    have he : (0 : Int) - Int.negSucc k - 1 = Int.ofNat k := by
      rw [show (0 : Int) - Int.negSucc k = Int.ofNat (k + 1) by
            show (0 : Int) + Int.ofNat (k + 1) = Int.ofNat (k + 1); exact zero_add _,
          ofNat_succ_sub_one]
    exact he ▸ (⟨k⟩ : (Int.ofNat k).NonNeg)

theorem eq_of_sub_eq_zero {a b : Int} (h : a - b = 0) : a = b := by
  have h2 : a - b + b = 0 + b := by rw [h]
  rw [sub_add_cancel_int, zero_add] at h2
  exact h2

/-! ## Negation reverses order -/

theorem zero_sub (a : Int) : (0 : Int) - a = -a := by show (0 : Int) + -a = -a; exact zero_add (-a)

theorem neg_pos_of_neg {c : Int} (h : c < 0) : (0 : Int) < -c := by
  apply lt_of_sub_one_nonneg
  exact (show (0 : Int) - c - 1 = -c - 0 - 1 by rw [zero_sub, sub_zero]) ▸ sub_one_nonneg_of_lt h

theorem lt_of_neg_lt_neg {a b : Int} (h : -b < -a) : a < b := by
  apply lt_of_sub_one_nonneg
  exact (show -a - -b - 1 = b - a - 1 by ring_intZ) ▸ sub_one_nonneg_of_lt h

theorem le_of_neg_le_neg {a b : Int} (h : -b ≤ -a) : a ≤ b := by
  apply le_of_sub_nonneg
  exact (show -a - -b = b - a by ring_intZ) ▸ sub_nonneg_of_le h

/-! ## `ofNat` order embedding -/

theorem ofNat_sub_ofNat (b a : Nat) : Int.ofNat b - Int.ofNat a = Int.subNatNat b a := by
  cases a with
  | zero =>
    show Int.ofNat b - Int.ofNat 0 = Int.subNatNat b 0
    rw [subNatNat_zero]; exact sub_zero (Int.ofNat b)
  | succ j => rfl

theorem ofNat_le {a b : Nat} (h : a ≤ b) : Int.ofNat a ≤ Int.ofNat b := by
  apply le_of_sub_nonneg
  rw [ofNat_sub_ofNat, subNatNat_of_le h]; exact ⟨b - a⟩

theorem le_of_ofNat_le {a b : Nat} (h : Int.ofNat a ≤ Int.ofNat b) : a ≤ b := by
  rcases Nat.lt_or_ge b a with hlt | hge
  · exfalso
    have hnn : (Int.ofNat b - Int.ofNat a).NonNeg := sub_nonneg_of_le h
    rw [ofNat_sub_ofNat, subNatNat_of_lt hlt] at hnn
    cases hnn
  · exact hge

end E213.Meta.Int213.Order
