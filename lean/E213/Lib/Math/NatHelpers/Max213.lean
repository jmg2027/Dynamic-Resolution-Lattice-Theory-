import E213.Lib.Math.NatHelpers.AddMod213

/-!
# Max213 — `Nat.max` helpers (∅-axiom)

213-native replacements for Lean-core `Nat.max_*` lemmas that
leak `propext`.  Every theorem here is `#print axioms`-clean.

Used pervasively in Real213 for `LocallyDeterminedData.N` field
proofs (modulus combiners) and in `IsSmooth` / `ResolutionDepth`.

Lean-core leak status (probed):
  - `Nat.le_max_left`         DIRTY (propext)
  - `Nat.le_max_right`        DIRTY (propext)
  - `Nat.max_eq_left`         DIRTY (propext)
  - `Nat.max_comm`            DIRTY (propext)
  - `Nat.max_eq_right`        PURE
  - `Nat.max_self`            PURE
  - `Nat.le_total`            PURE
-/

namespace E213.Lib.Math.NatHelpers.Max213

/-- ∅-axiom replacement for `Nat.max_eq_left` (when `b ≤ a`). -/
theorem max_eq_left {a b : Nat} (h : b ≤ a) : Nat.max a b = a :=
  match Nat.le_total a b with
  | Or.inl hab =>
    -- a ≤ b ∧ b ≤ a → a = b → max = b = a
    let h1 : Nat.max a b = b := Nat.max_eq_right hab
    let h2 : a = b := Nat.le_antisymm hab h
    h1.trans h2.symm
  | Or.inr hba =>
    -- b ≤ a from le_total — chain via Nat.max_self when a = b
    -- General case: use bridge via 213-native max_comm.
    let h1 : Nat.max a b = Nat.max b a := E213.Lib.Math.NatHelpers.AddMod213.max_comm a b
    h1.trans (Nat.max_eq_right hba)

/-- ∅-axiom replacement for `Nat.le_max_left`. -/
theorem le_max_left (a b : Nat) : a ≤ Nat.max a b :=
  match Nat.le_total a b with
  | Or.inl hab =>
    -- a ≤ b → max a b = b → a ≤ b = max a b
    let h1 : Nat.max a b = b := Nat.max_eq_right hab
    h1.symm ▸ hab
  | Or.inr hba =>
    -- b ≤ a → max a b = a → a ≤ a
    let h1 : Nat.max a b = a := max_eq_left hba
    h1.symm ▸ Nat.le_refl a

/-- ∅-axiom replacement for `Nat.le_max_right`. -/
theorem le_max_right (a b : Nat) : b ≤ Nat.max a b :=
  match Nat.le_total a b with
  | Or.inl hab =>
    -- a ≤ b → max a b = b → b ≤ b
    let h1 : Nat.max a b = b := Nat.max_eq_right hab
    h1.symm ▸ (Nat.le_refl b)
  | Or.inr hba =>
    -- b ≤ a → max a b = a ≥ b
    let h1 : Nat.max a b = a := max_eq_left hba
    h1.symm ▸ hba

end E213.Lib.Math.NatHelpers.Max213
