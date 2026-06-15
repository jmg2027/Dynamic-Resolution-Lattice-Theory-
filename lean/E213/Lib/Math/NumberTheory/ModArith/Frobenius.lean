import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.AddMod213
import E213.Meta.Tactic.NatHelper

/-!
# The Frobenius / Chicken-McNugget theorem for two coprime values (∅-axiom)

For coprime `a, b ≥ 1`, every `n ≥ (a−1)·(b−1)` is representable as `n = a·x + b·y`
with `x, y : ℕ` (`frobenius_representable`).  Equivalently, the Frobenius number
`a·b − a − b` is the largest non-representable value — this file proves the
representability (everything past the threshold) direction.

The proof is the classical modular-inverse argument, all PURE:

  * **`residue_hit`** — for coprime `a,b`, the multiples `j·a (mod b)` cover all
    residues, so some `j < b` has `n ≡ j·a (mod b)` (witness `j = (n·s) % b`,
    `s` = inverse of `a` mod `b`, from `MarkovPrimeFactor.inverse_of_coprime`).
  * **`residue_le`** — the threshold `(a−1)(b−1) ≤ n` forces `j·a ≤ n` (else
    `b ∣ (j·a − n) > 0` ⟹ `j·a ≥ n + b`, contradicting `j ≤ b−1`).
  * lift `n ≡ j·a (mod b)` with `j·a ≤ n` to `n = j·a + q·b` (`mod_eq_exists_mul_add`).

All the modular-inverse / gcd / mod infra was already present and PURE.  A
signed Bézout is *not* needed — the modular-inverse route stays in `ℕ`.
(`Nat.sub_pos_of_lt` leaks `propext`; replaced by the local PURE `sub_pos_pure`.)
-/

namespace E213.Lib.Math.NumberTheory.ModArith.Frobenius

open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (inverse_of_coprime)
open E213.Lib.Math.NumberTheory.ModArith.ModBezout (modBezout)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure)
open E213.Meta.Nat.Gcd213 (mod_eq_exists_mul_add)

/-- **Residue-hit lemma.**  For coprime `a, b` with `0 < b`, there is a residue
    `j < b` with `(j * a) % b = n % b`, i.e. `n ≡ j·a (mod b)`.  `j = (n·s) % b`
    with `s` the modular inverse of `a` mod `b`. -/
theorem residue_hit (a b : Nat) (hb : 0 < b) (hcop : gcd213 a b = 1) (n : Nat) :
    ∃ j, j < b ∧ (j * a) % b = n % b := by
  let s := (modBezout a b).2
  have hs : (a * s) % b = 1 % b := inverse_of_coprime a b hb hcop
  refine ⟨(n * s) % b, Nat.mod_lt _ hb, ?_⟩
  have e1 : ((n * s) % b * a) % b = (n * s * a) % b :=
    (mul_mod_left_pure (n * s) a b).symm
  rw [e1]
  have e2 : n * s * a = n * (a * s) := by
    rw [E213.Tactic.NatHelper.mul_assoc n s a, Nat.mul_comm s a]
  rw [e2]
  rw [mul_mod_right_pure n (a * s) b, hs, ← mul_mod_right_pure n 1 b, Nat.mul_one]

/-- PURE replacement for `Nat.sub_pos_of_lt` (Lean-core leaks `propext`). -/
private theorem sub_pos_pure (n m : Nat) (h : n < m) : 0 < m - n := by
  have h1 : m - n + n = m := E213.Tactic.NatHelper.sub_add_cancel (Nat.le_of_lt h)
  cases hmn : m - n with
  | zero => rw [hmn, Nat.zero_add] at h1; rw [h1] at h; exact absurd h (Nat.lt_irrefl m)
  | succ k => exact Nat.succ_pos k

/-- The threshold bound: if `j·a ≡ n (mod b)`, `j < b`, and `(a−1)(b−1) ≤ n`
    (with `a,b ≥ 1`), then `j·a ≤ n`. -/
theorem residue_le (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (n : Nat)
    (hn : (a - 1) * (b - 1) ≤ n) (j : Nat) (hj : j < b)
    (hmod : (j * a) % b = n % b) : j * a ≤ n := by
  rcases Nat.le_total (j * a) n with hok | hlt'
  · exact hok
  rcases Nat.eq_or_lt_of_le hlt' with heq | hlt
  · exact Nat.le_of_eq heq.symm
  exfalso
  have hnle : n ≤ j * a := Nat.le_of_lt hlt
  have hbpos : 0 < b := hb
  have hdvd : b ∣ (j * a - n) :=
    E213.Meta.Nat.Gcd213.mod_eq_dvd_sub (j * a) n b hbpos hnle hmod
  have hpos_sub : 0 < j * a - n := sub_pos_pure n (j * a) hlt
  obtain ⟨q, hq⟩ := hdvd
  have hq_pos : 0 < q := by
    cases q with
    | zero =>
      exfalso
      rw [Nat.mul_zero] at hq
      exact absurd hq (Nat.ne_of_gt hpos_sub)
    | succ q' => exact Nat.succ_pos q'
  have hb_le_sub : b ≤ j * a - n := by
    rw [hq]
    calc b = b * 1 := (Nat.mul_one b).symm
      _ ≤ b * q := Nat.mul_le_mul_left b hq_pos
  have hja_ge : n + b ≤ j * a := by
    have h1 : (j * a - n) + n = j * a := E213.Tactic.NatHelper.sub_add_cancel hnle
    have h2 : b + n ≤ (j * a - n) + n := Nat.add_le_add_right hb_le_sub n
    rw [h1] at h2
    rw [Nat.add_comm n b]; exact h2
  have hj_le : j ≤ b - 1 := Nat.le_sub_one_of_lt hj
  have hja_ub : j * a ≤ (b - 1) * a := Nat.mul_le_mul_right a hj_le
  have key : (a - 1) * (b - 1) + b ≤ (b - 1) * a :=
    Nat.le_trans (Nat.add_le_add_right hn b) (Nat.le_trans hja_ge hja_ub)
  have ha_ne : a ≠ 0 := Nat.ne_of_gt ha
  have ha1 : (a - 1) + 1 = a := E213.Tactic.NatHelper.sub_one_add_one ha_ne
  have expand : (b - 1) * a = (b - 1) * (a - 1) + (b - 1) := by
    calc (b - 1) * a = (b - 1) * ((a - 1) + 1) := by rw [ha1]
      _ = (b - 1) * (a - 1) + (b - 1) * 1 := Nat.mul_add (b - 1) (a - 1) 1
      _ = (b - 1) * (a - 1) + (b - 1) := by rw [Nat.mul_one]
  rw [expand, Nat.mul_comm (b - 1) (a - 1)] at key
  have hb_le_bsub1 : b ≤ b - 1 := E213.Tactic.NatHelper.le_of_add_le_add_left key
  have hbb : b - 1 < b := Nat.sub_lt hbpos (by decide)
  have hbb' : b < b := Nat.lt_of_le_of_lt hb_le_bsub1 hbb
  exact absurd hbb' (Nat.lt_irrefl b)

/-- ★★★ **Frobenius / Chicken-McNugget representability.**
    For coprime `a, b ≥ 1`, every `n ≥ (a−1)·(b−1)` is representable as
    `n = a·x + b·y` (`x, y : ℕ`).  (So `a·b − a − b` is the largest
    non-representable value — the Frobenius number of `{a,b}`.) -/
theorem frobenius_representable (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hcop : gcd213 a b = 1) (n : Nat) (hn : (a - 1) * (b - 1) ≤ n) :
    ∃ x y : Nat, n = a * x + b * y := by
  have hbpos : 0 < b := hb
  obtain ⟨j, hj_lt, hj_mod⟩ := residue_hit a b hbpos hcop n
  have hle : j * a ≤ n := residue_le a b ha hb n hn j hj_lt hj_mod
  obtain ⟨q, hq⟩ := mod_eq_exists_mul_add n (j * a) b hbpos hle hj_mod.symm
  refine ⟨j, q, ?_⟩
  rw [hq, Nat.mul_comm j a, Nat.mul_comm q b]

end E213.Lib.Math.NumberTheory.ModArith.Frobenius
