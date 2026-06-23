import E213.Meta.Nat.UnitList

/-!
# UnitOrder — the order `≤`, born as unit-list extension

`UnitList`/`UnitGrid`/`UnitBox`/`UnitDistrib` generated the commutative semiring
`(ℕ, +, ·, 0, 1)` as the count-shadow of unit-structure double-counts. This file
adds the **order**: `a ≤ b` is born as "`fromNat a` is a *prefix* of `fromNat b`"
— `b`'s unit list extends `a`'s. The order is the extension relation on the count
carrier; counting reads it back as `Nat.le`.

Its compatibility with `+` (`a ≤ b → a + c ≤ b + c`) is generated from the *same*
indistinguishability that gave `+`-commutativity: on unit lists the suffix and the
added block commute (`UnitList.append_comm`), so the extension survives adding `c`.
∅-axiom; the order content comes from list prefix/append facts, not from `Nat.le`'s
own order lemmas.
-/

namespace E213.Meta.Nat.UnitOrder

open E213.Meta.Nat.UnitList
  (count fromNat count_fromNat count_append_fwd append_nil append_assoc append_comm)

/-- `fromNat` is additive over `++`: `fromNat (a+b) = fromNat a ++ fromNat b`
    (the count-list analogue of `replicate_add`). -/
theorem fromNat_add : ∀ (a b : Nat), fromNat (a + b) = fromNat a ++ fromNat b
  | 0,     b => by rw [Nat.zero_add]; rfl
  | a + 1, b => by
      rw [Nat.succ_add]
      show () :: fromNat (a + b) = () :: (fromNat a ++ fromNat b)
      rw [fromNat_add a b]

/-- ★★★★★ **The order is born as unit-list extension**: `a ≤ b` iff `b`'s unit
    list extends `a`'s by some suffix. `Nat.le` is the count-readout of the
    prefix relation. -/
theorem le_iff_unit_extension (a b : Nat) :
    a ≤ b ↔ ∃ l : List Unit, fromNat a ++ l = fromNat b := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := Nat.le.dest h
    exact ⟨fromNat d, by rw [← fromNat_add, hd]⟩
  · rintro ⟨l, hl⟩
    have hc : count (fromNat a ++ l) = count (fromNat b) := congrArg count hl
    rw [count_append_fwd, count_fromNat, count_fromNat] at hc
    exact Nat.le.intro hc

/-- ★ **`+`-monotonicity, generated**: `a ≤ b → a + c ≤ b + c`. The extension
    suffix `l` witnessing `a ≤ b` still witnesses `a + c ≤ b + c` after the added
    `c`-block, because on unit lists the suffix and the block commute
    (`append_comm`) — the same indistinguishability that births `+`-commutativity.
    No `Nat.add_le_add_right`. -/
theorem add_le_add_right {a b : Nat} (h : a ≤ b) (c : Nat) : a + c ≤ b + c := by
  obtain ⟨l, hl⟩ := (le_iff_unit_extension a b).mp h
  refine (le_iff_unit_extension (a + c) (b + c)).mpr ⟨l, ?_⟩
  -- fromNat (a+c) ++ l = fromNat a ++ fromNat c ++ l
  --                    = fromNat a ++ (l ++ fromNat c)   [append_comm on unit lists]
  --                    = (fromNat a ++ l) ++ fromNat c = fromNat b ++ fromNat c = fromNat (b+c)
  rw [fromNat_add, fromNat_add, append_assoc, append_comm (fromNat c) l,
      ← append_assoc, hl]

end E213.Meta.Nat.UnitOrder
