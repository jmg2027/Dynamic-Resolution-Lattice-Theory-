import E213.Lens.Number.Nat213.Chain
import E213.Lens.Number.Nat213.Core

/-!
# Lens.Number.Nat213.ChainCoreBridge — Chain (Raw-subtype) ↔ Core (Nat-subtype)

ℕ₊ has two complementary subtype carriers in this directory:

  - **Core**: `Nat213 := { n : Nat // 1 ≤ n }` — Nat-subtype side
    (`Core.lean`).
  - **Chain**: `Chain := { r : Raw // IsMethodAChain r }` — Raw-subtype
    side (`Chain.lean`).

This file is the bijection between them, with both round-trips
proved.  The bridge witnesses that the two subtypes are
*isomorphic* representations of the same abstract ℕ₊.

∅-axiom standard.
-/

namespace E213.Lens.Number.Nat213

open E213.Theory

/-! ### Forward: Chain → Core -/

/-- Project a `Chain` element to its `Nat213` (Core) counterpart. -/
def Chain.toCore (c : Chain) : Nat213 :=
  ⟨c.toNat, c.toNat_ge_one⟩

theorem Chain.toCore_val (c : Chain) : c.toCore.val = c.toNat := rfl

/-! ### Backward: Core → Chain -/

/-- Construct a `Chain` element from a `Nat213` (Core) value. -/
def Nat213.toChain (n : Nat213) : Chain :=
  Chain.numeral (n.val - 1)

theorem Nat213.toChain_val (n : Nat213) :
    (Nat213.toChain n).val = Raw.numeral (n.val - 1) := rfl

/-! ### Round-trips -/

/-- Core → Chain → Core is identity. -/
theorem Chain.toCore_ofCore (n : Nat213) : (Nat213.toChain n).toCore = n := by
  apply Subtype.ext
  show (Chain.numeral (n.val - 1)).toNat = n.val
  rw [Chain.toNat_numeral]
  exact Nat.succ_pred_eq_of_pos n.property

/-- Structure-extensionality for `Chain`: equal `val` ⇒ equal `Chain`. -/
theorem Chain.ext_val {c₁ c₂ : Chain} (h : c₁.val = c₂.val) : c₁ = c₂ := by
  obtain ⟨v₁, p₁⟩ := c₁
  obtain ⟨v₂, p₂⟩ := c₂
  cases h
  rfl

/-- Chain → Core → Chain is identity. -/
theorem Chain.ofCore_toCore (c : Chain) : Nat213.toChain c.toCore = c := by
  apply Chain.ext_val
  obtain ⟨m, hm⟩ := c.property
  -- `c.val = Raw.numeral m`, so `c.toNat = m + 1`,
  -- hence `Nat213.toChain c.toCore = Chain.numeral m`, whose val is `Raw.numeral m = c.val`.
  show Raw.numeral (c.toCore.val - 1) = c.val
  rw [hm]
  show Raw.numeral (c.toCore.val - 1) = Raw.numeral m
  -- Need: c.toCore.val - 1 = m
  -- c.toCore.val = c.toNat = Raw.value c.val = Raw.value (Raw.numeral m) = m + 1
  -- so c.toCore.val - 1 = m
  have hval : c.toCore.val = m + 1 := by
    show Raw.value c.val = m + 1
    rw [hm, Raw.value_numeral]
  rw [hval]
  rfl

end E213.Lens.Number.Nat213
