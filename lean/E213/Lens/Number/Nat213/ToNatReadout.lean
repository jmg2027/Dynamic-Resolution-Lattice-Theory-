import E213.Lens.Number.Nat213.Divisibility

/-!
# Lens.Number.Nat213.ToNatReadout — the depth readout is a faithful ordered-semiring embedding (∅-axiom)

The **descent leg**: `Nat213` is the Raw-generated carrier; Lean's `Nat` enters only as the **depth
readout** `toNat` (a Lens reading *out*, the legitimate direction — `naturals_from_the_spine.md`).
This file collects the bridge lemmas that make that readout *faithful*: `toNat` is an injective
`+`/`×` homomorphism onto `ℕ₊` (`Peano.toNat_{add,mul,injective,ge_one}`), and it transports the
order and divisibility structure *exactly* — `lt`/`le`/`Dvd` over `Nat213` each read as their native
counterpart on the readout, both directions. The ⟸ directions lift a native witness back through
`toNat`'s **surjectivity onto ℕ₊** (`toNat_surj`).

These are the reusable carrier-readout API (used by `Valuation.vp_eq_vpSub` to weld the generated
`p`-adic valuation to the native `vpSub`). ∅-axiom throughout.
-/

namespace E213.Lens.Number.Nat213.ToNatReadout

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213
  (mul one succ add toNat toNat_add toNat_mul toNat_ge_one toNat_injective powNat)
open E213.Lens.Number.Nat213.Order (lt le)
open E213.Lens.Number.Nat213.Divisibility (Dvd)

/-- `toNat` is surjective onto `ℕ₊` — every count `≥ 1` is some `Nat213`'s depth. -/
theorem toNat_surj : ∀ m : Nat, 1 ≤ m → ∃ c : Nat213, c.toNat = m
  | 0     => fun h => absurd h (by decide)
  | 1     => fun _ => ⟨one, rfl⟩
  | m + 2 => fun _ => by
      obtain ⟨c, hc⟩ := toNat_surj (m + 1) (Nat.le_add_left 1 m)
      exact ⟨succ c, by show c.toNat + 1 = m + 2; rw [hc]⟩

/-- `(p^k).toNat = (p.toNat)^k` — the `Nat`-exponent power commutes with the depth readout. -/
theorem toNat_powNat (p : Nat213) : ∀ k : Nat, (powNat p k).toNat = p.toNat ^ k
  | 0     => rfl
  | k + 1 => by
      show (mul p (powNat p k)).toNat = p.toNat ^ (k + 1)
      rw [toNat_mul, toNat_powNat p k, Nat.pow_succ, Nat.mul_comm]

/-- ★ **Divisibility carrier bridge** — `Dvd a b ⟺ a.toNat ∣ b.toNat`.  ⟹ via `toNat_mul`; ⟸
    lifts the native quotient back through `toNat`'s surjectivity (the quotient is `≥ 1` since
    `b.toNat ≥ 1`). -/
theorem dvd_toNat_iff {a b : Nat213} : Dvd a b ↔ a.toNat ∣ b.toNat := by
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c.toNat, toNat_mul a c⟩
  · rintro ⟨m, hm⟩
    have hm1 : 1 ≤ m := by
      cases m with
      | zero => rw [Nat.mul_zero] at hm; exact absurd (hm ▸ toNat_ge_one b) (by decide)
      | succ k => exact Nat.succ_le_succ (Nat.zero_le k)
    obtain ⟨c, hc⟩ := toNat_surj m hm1
    exact ⟨c, toNat_injective (by rw [toNat_mul, hc]; exact hm)⟩

/-- ★ **Strict-order carrier bridge** — `lt a b ⟺ a.toNat < b.toNat`. -/
theorem lt_toNat_iff {a b : Nat213} : lt a b ↔ a.toNat < b.toNat := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [toNat_add]
    exact Nat.lt_add_of_pos_right (toNat_ge_one c)
  · intro h
    obtain ⟨d, hd⟩ := Nat.le.dest (Nat.le_of_lt h)
    have hd1 : 1 ≤ d := by
      cases d with
      | zero => rw [Nat.add_zero] at hd; exact absurd (hd ▸ h) (Nat.lt_irrefl _)
      | succ k => exact Nat.succ_le_succ (Nat.zero_le k)
    obtain ⟨c, hc⟩ := toNat_surj d hd1
    exact ⟨c, toNat_injective (by rw [toNat_add, hc]; exact hd)⟩

/-- ★ **Non-strict-order carrier bridge** — `le a b ⟺ a.toNat ≤ b.toNat`. -/
theorem le_toNat_iff {a b : Nat213} : le a b ↔ a.toNat ≤ b.toNat := by
  constructor
  · rintro (rfl | hlt)
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (lt_toNat_iff.mp hlt)
  · intro h
    rcases Nat.lt_or_ge a.toNat b.toNat with hlt | hge
    · exact Or.inr (lt_toNat_iff.mpr hlt)
    · exact Or.inl (toNat_injective (Nat.le_antisymm h hge))

/-- ★★★ **The depth readout is a faithful order/divisibility embedding** — `toNat` transports
    `lt`, `le`, and `Dvd` exactly onto their native counterparts (both directions), and is
    surjective onto `ℕ₊`.  `Nat213` *is* `ℕ₊` read out, structure and all. -/
theorem toNat_faithful :
    (∀ a b : Nat213, lt a b ↔ a.toNat < b.toNat)
    ∧ (∀ a b : Nat213, le a b ↔ a.toNat ≤ b.toNat)
    ∧ (∀ a b : Nat213, Dvd a b ↔ a.toNat ∣ b.toNat)
    ∧ (∀ m : Nat, 1 ≤ m → ∃ c : Nat213, c.toNat = m) :=
  ⟨fun _ _ => lt_toNat_iff, fun _ _ => le_toNat_iff, fun _ _ => dvd_toNat_iff, toNat_surj⟩

end E213.Lens.Number.Nat213.ToNatReadout
