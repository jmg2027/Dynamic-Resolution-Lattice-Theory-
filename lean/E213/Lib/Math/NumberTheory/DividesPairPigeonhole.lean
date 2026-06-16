import E213.Lib.Math.NumberTheory.OddPartDecomposition
import E213.Lib.Math.Combinatorics.Pigeonhole
import E213.Meta.Nat.Iterate213
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.AddMod213

/-!
# Divisibility pigeonhole on `[1,2n]` (∅-axiom, constructive dividing pair)

**Among any `n+1` distinct numbers in `{1,…,2n}`, one divides another.**

## The forcing
Classically this is pigeonhole asserting a *non-constructive* `∃` (two of the
`n+1` chosen numbers share an odd part — but *which* pair is never exhibited).
∅-axiom forces the **explicit** collision via the computable `oddPart` map, and
`same_oddpart_dvd` reads the divisibility *straight off* the comparison of 2-adic
valuations `v2 a` vs `v2 b`: the smaller one's value divides the other, because
both equal `2^v · (common odd part)`.  **The dividing pair is computed (odd-part
map + v2 comparison), not asserted by an abstract pigeonhole existence.**
-/

namespace E213.Lib.Math.NumberTheory.DividesPairPigeonhole

open E213.Lib.Math.NumberTheory.OddPartDecomposition
  (oddPart v2 decomp oddPart_odd oddPart_pos)
open E213.Lib.Math.Combinatorics.Pigeonhole (no_inj_lt)
open E213.Meta.Nat.Iterate213 (pow_add_from_iter)

/-! ## §1 — ★★★ the constructive divisibility core -/

/-- If `v2 a ≤ v2 b` and `oddPart a = oddPart b` (both positive), then `a ∣ b`.
    Write `v2 b = v2 a + d`; then `b = 2^(v2 a)·2^d·oddPart b = a·2^d` (using
    `a = 2^(v2 a)·oddPart a`), so `a ∣ b` with explicit cofactor `2^d`. -/
theorem dvd_of_v2_le {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (hle : v2 a ≤ v2 b) (hop : oddPart a = oddPart b) : a ∣ b := by
  -- d with v2 a + d = v2 b
  obtain ⟨d, hd⟩ : ∃ d, v2 a + d = v2 b := Nat.le.dest hle
  -- b = 2^(v2 b) * oddPart b
  have hbdec : b = 2 ^ v2 b * oddPart b := decomp hb
  -- a = 2^(v2 a) * oddPart a
  have hadec : a = 2 ^ v2 a * oddPart a := decomp ha
  -- witness cofactor: 2^d
  refine ⟨2 ^ d, ?_⟩
  -- b = a * 2^d
  calc b = 2 ^ v2 b * oddPart b := hbdec
    _ = 2 ^ (v2 a + d) * oddPart b := by rw [hd]
    _ = (2 ^ v2 a * 2 ^ d) * oddPart b := by rw [pow_add_from_iter]
    _ = (2 ^ v2 a * oddPart b) * 2 ^ d := by
          rw [E213.Tactic.NatHelper.mul_assoc, E213.Tactic.NatHelper.mul_assoc,
              Nat.mul_comm (2 ^ d) (oddPart b)]
    _ = (2 ^ v2 a * oddPart a) * 2 ^ d := by rw [hop]
    _ = a * 2 ^ d := by rw [← hadec]

/-- ★★★ **Same odd part ⟹ one divides the other.**  With equal odd parts, compare
    the 2-adic valuations: the smaller-valuation number divides the larger.  This is
    the load-bearing constructive content — explicit divisibility from `v2`. -/
theorem same_oddpart_dvd {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (h : oddPart a = oddPart b) : a ∣ b ∨ b ∣ a := by
  rcases Nat.le_total (v2 a) (v2 b) with hle | hle
  · exact Or.inl (dvd_of_v2_le ha hb hle h)
  · exact Or.inr (dvd_of_v2_le hb ha hle h.symm)

/-! ## §2 — counting: only `n` odd numbers in `[1,2n]`, indexed into `Fin n` -/

/-- The odd part of any `m ∈ [1,2n]` is an odd number `< 2n`; its index `(o-1)/2`
    lands in `Fin n`.  Bound: `oddPart m ≤ m ≤ 2n` and `oddPart m` odd, so it is
    `≤ 2n-1`, giving `(oddPart m - 1)/2 < n`. -/
theorem oddPart_index_lt {n m : Nat} (h1 : 1 ≤ m) (h2 : m ≤ 2 * n) :
    (oddPart m - 1) / 2 < n := by
  have hmpos : 0 < m := h1
  -- oddPart m ≤ m : since m = 2^(v2 m) * oddPart m and oddPart m > 0
  have hopos : 0 < oddPart m := oddPart_pos hmpos
  have hdec : m = 2 ^ v2 m * oddPart m := decomp hmpos
  have hple : oddPart m ≤ m := by
    have h2pos : 0 < 2 ^ v2 m := Nat.pos_pow_of_pos (v2 m) (by decide)
    calc oddPart m = 1 * oddPart m := (Nat.one_mul _).symm
      _ ≤ 2 ^ v2 m * oddPart m := Nat.mul_le_mul_right _ h2pos
      _ = m := hdec.symm
  -- oddPart m ≤ 2n
  have hop2n : oddPart m ≤ 2 * n := Nat.le_trans hple h2
  -- oddPart m is odd
  have hodd : oddPart m % 2 = 1 := oddPart_odd hmpos
  -- since oddPart m is odd it cannot equal 2n (which is even): oddPart m < 2n
  have hlt2n : oddPart m < 2 * n := by
    rcases Nat.lt_or_ge (oddPart m) (2 * n) with hlt | hge
    · exact hlt
    · -- oddPart m ≥ 2n and ≤ 2n ⇒ = 2n, contradicting oddness
      have heq : oddPart m = 2 * n := Nat.le_antisymm hop2n hge
      have : (2 * n) % 2 = 1 := heq ▸ hodd
      rw [E213.Meta.Nat.NatDiv213.mul_mod_self_pure 2 n] at this
      exact absurd this (by decide)
  -- oddPart m ≥ 1
  have h1op : 1 ≤ oddPart m := hopos
  -- (oddPart m - 1) < 2n - 1 < 2n ; want (oddPart m - 1)/2 < n
  -- oddPart m - 1 + 1 = oddPart m  (oddPart m ≥ 1)
  -- from oddPart m < 2n : oddPart m - 1 < 2n - 1, and 2n - 1 < 2n, so (oddPart m -1) ≤ 2n-1 < 2n
  -- (oddPart m -1)/2 < n  ⟺  oddPart m - 1 < 2n  (div_lt)
  have hsub_lt : oddPart m - 1 < 2 * n := Nat.lt_of_le_of_lt (Nat.sub_le _ 1) hlt2n
  -- (oddPart m -1)/2 < (2n)/2 = n  via div monotonicity is awkward; use: x/2 < n ⟸ x < 2n
  exact E213.Meta.Nat.NatDiv213.div_lt_of_lt_mul hsub_lt

/-! ## §3 — ★★★ the divisibility pigeonhole, packaged -/

/-- ★★★ **Divisibility pigeonhole on `[1,2n]`.**  Given an injection
    `f : Fin (n+1) → Nat` with every `f i ∈ [1,2n]`, there are two distinct indices
    whose values stand in a divisibility relation — and the witnessing pair is
    *computed*: the odd-part map collides (pigeonhole over the `n` odd numbers `< 2n`),
    and `same_oddpart_dvd` reads off the divisibility. -/
theorem exists_dvd_pair (n : Nat) (f : Fin (n + 1) → Nat)
    (hf : ∀ i, 1 ≤ f i ∧ f i ≤ 2 * n) (hinj : ∀ i j, i ≠ j → f i ≠ f j) :
    ∃ i j, i ≠ j ∧ (f i ∣ f j ∨ f j ∣ f i) := by
  -- the index map i ↦ Fin n carrying the odd part of f i
  let g : Fin (n + 1) → Fin n := fun i =>
    ⟨(oddPart (f i) - 1) / 2, oddPart_index_lt (hf i).1 (hf i).2⟩
  -- constructive pigeonhole: `exists_collision` *produces* the colliding pair
  -- (n+1 inputs, Fin n outputs) — no `Classical`, the witness is computed.
  obtain ⟨i, j, hij, hgij⟩ :=
    E213.Lib.Math.Combinatorics.Pigeonhole.exists_collision n g
  -- g i = g j  ⟹  (oddPart (f i) - 1)/2 = (oddPart (f j) - 1)/2
  have hval : (oddPart (f i) - 1) / 2 = (oddPart (f j) - 1) / 2 :=
    congrArg Fin.val hgij
  -- recover oddPart (f i) = oddPart (f j):
  -- odd o ⟹ o = 2*((o-1)/2) + 1
  have hrec : ∀ m : Nat, 1 ≤ m → m ≤ 2 * n →
      oddPart m = 2 * ((oddPart m - 1) / 2) + 1 := by
    intro m h1 _
    have hmpos : 0 < m := h1
    have hodd : oddPart m % 2 = 1 := oddPart_odd hmpos
    have hopos : 0 < oddPart m := oddPart_pos hmpos
    -- oddPart m - 1 is even: (oddPart m - 1) % 2 = 0
    -- oddPart m = (oddPart m - 1) + 1 ; ((o-1)+1) % 2 = 1 ⟹ (o-1)%2 = 0
    have hsucc : oddPart m - 1 + 1 = oddPart m := Nat.succ_pred_eq_of_pos hopos
    have heven : (oddPart m - 1) % 2 = 0 := by
      have : (oddPart m - 1 + 1) % 2 = 1 := hsucc ▸ hodd
      -- (x+1)%2 = 1 ⟹ x%2 = 0
      rcases E213.Meta.Nat.AddMod213.mod_two_zero_or_one (oddPart m - 1) with h0 | h1'
      · exact h0
      · exfalso
        rw [E213.Meta.Nat.AddMod213.add_mod_gen (oddPart m - 1) 1 2, h1'] at this
        exact absurd this (by decide)
    -- even x ⟹ x = 2*(x/2)
    have hdm : 2 * ((oddPart m - 1) / 2) + (oddPart m - 1) % 2 = oddPart m - 1 :=
      E213.Meta.Nat.AddMod213.div_add_mod (oddPart m - 1) 2
    rw [heven, Nat.add_zero] at hdm
    calc oddPart m = oddPart m - 1 + 1 := hsucc.symm
      _ = 2 * ((oddPart m - 1) / 2) + 1 := by rw [hdm]
  have hoi : oddPart (f i) = 2 * ((oddPart (f i) - 1) / 2) + 1 :=
    hrec (f i) (hf i).1 (hf i).2
  have hoj : oddPart (f j) = 2 * ((oddPart (f j) - 1) / 2) + 1 :=
    hrec (f j) (hf j).1 (hf j).2
  have hopeq : oddPart (f i) = oddPart (f j) := by
    rw [hoi, hoj, hval]
  exact ⟨i, j, hij, same_oddpart_dvd (hf i).1 (hf j).1 hopeq⟩

/-! ## §4 — smoke tests (closed numerics, axiom-clean `decide`) -/

/-- `same_oddpart_dvd` smoke: 12 and 40 both... no, different odd parts.
    Use 6 (=2·3) and 24 (=8·3): both oddPart 3, v2 6 = 1 ≤ v2 24 = 3 ⟹ 6 ∣ 24. -/
theorem same_oddpart_smoke : (6 : Nat) ∣ 24 ∨ (24 : Nat) ∣ 6 :=
  same_oddpart_dvd (by decide) (by decide) (by decide)

/-- Same odd part 3: 12 = 4·3 and 6 = 2·3, oddPart equal ⟹ 6 ∣ 12. -/
theorem same_oddpart_smoke2 : (12 : Nat) ∣ 6 ∨ (6 : Nat) ∣ 12 :=
  same_oddpart_dvd (by decide) (by decide) (by decide)

/-- Index bound smoke: oddPart 6 = 3, (3-1)/2 = 1 < 3 (n=3). -/
theorem index_smoke : (oddPart 6 - 1) / 2 < 3 := by decide

end E213.Lib.Math.NumberTheory.DividesPairPigeonhole
