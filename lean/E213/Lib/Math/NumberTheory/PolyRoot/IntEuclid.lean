import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Meta.Int213.Core
import E213.Meta.Int213.PolyIntMTactic

/-!
# PolyRoot/IntEuclid — Euclid's lemma over `ℤ` for a prime modulus

The root bound's peel step needs: `↑p ∣ (s−r)·g(s)`, `↑p ∤ (s−r)`, `p` prime ⟹ `↑p ∣ g(s)`
over `ℤ`.  The repo's `euclid_of_coprime` is over `ℕ`; this file bridges via `natAbs`
(pure `natAbs_mul`, avoiding the `propext`-dirty `Int.natAbs_mul`).

  * `natAbs_mul` — `(a·b).natAbs = a.natAbs · b.natAbs` (constructor cases + `negOfNat`).
  * `nat_dvd_to_int` / `int_dvd_to_nat` — `↑p ∣ z ⟺ p ∣ z.natAbs`.
  * ★★★ `int_euclid` — `p` prime, `↑p ∣ a·b`, `↑p ∤ a` ⟹ `↑p ∣ b` over `ℤ`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.PolyRoot

open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (euclid_of_coprime prime_coprime)
open E213.Meta.Nat.Gcd213 (gcd213_comm)
open E213.Tactic.NatHelper (gcd213)

/-- Pure `ℤ`-divisibility closure (the core `Int.dvd_*` are `propext`-dirty). -/
theorem dvd_add' {a b c : Int} (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b + c := by
  obtain ⟨u, hu⟩ := h1; obtain ⟨v, hv⟩ := h2
  exact ⟨u + v, by rw [hu, hv]; ring_intZ⟩

theorem dvd_sub' {a b c : Int} (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b - c := by
  obtain ⟨u, hu⟩ := h1; obtain ⟨v, hv⟩ := h2
  exact ⟨u - v, by rw [hu, hv]; ring_intZ⟩

theorem dvd_mul_left' {a d : Int} (h : a ∣ d) (e : Int) : a ∣ e * d := by
  obtain ⟨u, hu⟩ := h
  exact ⟨e * u, by rw [hu]; ring_intZ⟩

/-- `(negOfNat k).natAbs = k`. -/
theorem natAbs_negOfNat (k : Nat) : (Int.negOfNat k).natAbs = k := by
  cases k with
  | zero => rfl
  | succ n => rfl

/-- ★★ **Pure `natAbs` multiplicativity** (`Int.natAbs_mul` is `propext`-dirty). -/
theorem natAbs_mul (a b : Int) : (a * b).natAbs = a.natAbs * b.natAbs := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => rfl
    | negSucc n => exact natAbs_negOfNat (m * Nat.succ n)
  | negSucc m =>
    cases b with
    | ofNat n => exact natAbs_negOfNat (Nat.succ m * n)
    | negSucc n => rfl

/-- `p ∣ z.natAbs ⟹ ↑p ∣ z` over `ℤ`. -/
theorem nat_dvd_to_int (p : Nat) (z : Int) (h : p ∣ z.natAbs) : (p : Int) ∣ z := by
  obtain ⟨k, hk⟩ := h
  have h1 : ((z.natAbs : Nat) : Int) = (p : Int) * (k : Int) := by rw [hk, Int.ofNat_mul]
  rcases Int.natAbs_eq z with hz | hz
  · exact ⟨(k : Int), by rw [hz, h1]⟩
  · exact ⟨-(k : Int), by rw [hz, h1, E213.Meta.Int213.mul_neg]⟩

/-- `↑p ∣ z ⟹ p ∣ z.natAbs`. -/
theorem int_dvd_to_nat (p : Nat) (z : Int) (h : (p : Int) ∣ z) : p ∣ z.natAbs := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c.natAbs, by rw [hc, natAbs_mul, Int.natAbs_ofNat]⟩

/-- ★★★ **Euclid's lemma over `ℤ` for a prime.**  `p` prime, `↑p ∣ a·b`, `↑p ∤ a` ⟹ `↑p ∣ b`. -/
theorem int_euclid (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) (a b : Int)
    (hdvd : (p : Int) ∣ a * b) (hna : ¬ (p : Int) ∣ a) : (p : Int) ∣ b := by
  have h1 : p ∣ a.natAbs * b.natAbs := by rw [← natAbs_mul]; exact int_dvd_to_nat p (a * b) hdvd
  have h2 : ¬ p ∣ a.natAbs := fun hd => hna (nat_dvd_to_int p a hd)
  have hco : gcd213 a.natAbs p = 1 := by rw [gcd213_comm]; exact prime_coprime p a.natAbs hpr h2
  exact nat_dvd_to_int p b (euclid_of_coprime a.natAbs b.natAbs p hp hco h1)

end E213.Lib.Math.NumberTheory.PolyRoot
