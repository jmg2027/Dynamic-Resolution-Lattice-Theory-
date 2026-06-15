import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor

/-!
# General quadratic-residue descent frame (∅-axiom)

The reusable engine common to both supplement frames (`SqPlusOneFrame`,
`SqMinusTwoFrame`): for a fixed natural `a` and odd prime modulus `p`,
the *existence of an unbounded root* of `x² ≡ a (mod p)` is equivalent
to the *existence of a bounded nonzero residue root* `0 < r < p`.

This strips away the QR-symbol-specific RHS (`p%4=1`, `(m−m/2)%2`) and
keeps only the descent bridge: a root in `ℕ` descends to the fundamental
domain `0 < r < p`.  Both supplement frames factor through this iff
(compose the bounded root with `euler_criterion_m` / `second_supplement_m`).

The hypothesis `¬ p ∣ a` (`a` is a unit mod `p`) is exactly the regime
of the QR criteria: it rules out the degenerate `a ≡ 0` case in which an
unbounded root `x ≡ 0` exists but no *nonzero* bounded residue root does.

All ∅-axiom: `omega`/`simp`/propext-leaking `rw…at` are avoided; the
NatHelper / AddMod213 PURE twins carry the subtraction & mod algebra.
This proof is structurally simpler than the `SqMinusTwoFrame` template
(which relied on `a = 2` being small for an ordering step that does not
generalize): everything routes through `mod_eq_of_dvd_sub`.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.QRDescentFrame

open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (dvd_sq_sub_mod_sq)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero mod_diff_eq_zero_of_le)
open E213.Tactic.NatHelper (sub_add_cancel add_mul_mod_self_pure zero_mod)

/-- Congruence from divisibility of the difference: if `a ≤ b` and
    `p ∣ (b - a)` then `b % p = a % p`.  ∅-axiom. -/
private theorem mod_eq_of_dvd_sub {a b p : Nat} (hle : a ≤ b)
    (hdvd : p ∣ (b - a)) : b % p = a % p := by
  obtain ⟨w, hw⟩ := hdvd
  have hb : b = a + w * p := by
    have hcancel : (b - a) + a = b := sub_add_cancel hle
    calc b = (b - a) + a := hcancel.symm
      _ = p * w + a := by rw [hw]
      _ = a + w * p := by ring_nat
  calc b % p = (a + w * p) % p := by rw [hb]
    _ = a % p := add_mul_mod_self_pure a p w

/-- The lifted witness `x = r + a*p` is large enough: `a ≤ (r + a*p)²`
    whenever `1 ≤ p`.  ∅-axiom. -/
private theorem le_sq_lift (a r p : Nat) (hp1 : 1 ≤ p) :
    a ≤ (r + a * p) * (r + a * p) := by
  have hxge : a ≤ r + a * p := by
    have h2 : a * 1 ≤ a * p := Nat.mul_le_mul_left a hp1
    have h3 : a * p ≤ r + a * p := Nat.le_add_left (a * p) r
    calc a = a * 1 := (Nat.mul_one a).symm
      _ ≤ a * p := h2
      _ ≤ r + a * p := h3
  have hxle : r + a * p ≤ (r + a * p) * (r + a * p) := by
    rcases Nat.eq_zero_or_pos (r + a * p) with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · calc r + a * p = (r + a * p) * 1 := (Nat.mul_one _).symm
        _ ≤ (r + a * p) * (r + a * p) := Nat.mul_le_mul_left (r + a * p) hpos
  exact Nat.le_trans hxge hxle

/-- Bridge: an unbounded root `x` of `x² ≡ a (mod p)` descends to the bounded
    residue `x % p`, which satisfies `(x%p)² ≡ a (mod p)`.  Generalizes
    `SqMinusTwoFrame.root_mod_P_sub_two` (the `a = 2` instance) — same descent,
    with the output kept as `a % p` rather than a literal value. -/
theorem root_mod_P_sub (a p x : Nat) (_hp2 : 2 < p) (hax : a ≤ x * x)
    (hpx : p ∣ (x * x - a)) : (x % p) * (x % p) % p = a % p := by
  -- x*x % p = a % p  (from p ∣ x*x - a)
  have hxa : x * x % p = a % p := mod_eq_of_dvd_sub hax hpx
  -- x*x % p = (x%p)*(x%p) % p  (from p ∣ x*x - (x%p)²)
  have hrle : (x % p) * (x % p) ≤ x * x :=
    Nat.mul_le_mul (Nat.mod_le x p) (Nat.mod_le x p)
  have hxr : x * x % p = (x % p) * (x % p) % p :=
    mod_eq_of_dvd_sub hrle (dvd_sq_sub_mod_sq p x)
  exact hxr.symm.trans hxa

/-- ★ **General quadratic-residue descent frame**: for an odd prime modulus
    `p` (`2 < p`) and `a` a unit mod `p` (`¬ p ∣ a`), the existence of an
    *unbounded* root of `x² ≡ a (mod p)` (with `a ≤ x²`) is equivalent to
    the existence of a *bounded nonzero* residue root `0 < r < p`.

    Both supplement frames are instances: `SqMinusTwoFrame` is `a = 2`
    (then compose the bounded root with `second_supplement_m`); the `x²+1`
    first supplement is the `−1`-shift variant.  This iff is the shared
    descent engine — the part that has nothing to do with the QR symbol. -/
theorem qr_descent_iff (a p : Nat) (hp2 : 2 < p) (hpa : ¬ p ∣ a) :
    (∃ x : Nat, a ≤ x * x ∧ p ∣ (x * x - a))
      ↔ (∃ r : Nat, 0 < r ∧ r < p ∧ r * r % p = a % p) := by
  have hppos : 0 < p := Nat.lt_trans (by decide) hp2
  constructor
  · rintro ⟨x, hax, hx⟩
    have hroot := root_mod_P_sub a p x hp2 hax hx
    refine ⟨x % p, ?_, Nat.mod_lt x hppos, hroot⟩
    rcases Nat.eq_zero_or_pos (x % p) with h0 | hpos
    · exfalso
      have e : (x % p) * (x % p) % p = 0 := by
        rw [h0, Nat.zero_mul]; exact zero_mod p
      have ha0 : a % p = 0 := hroot.symm.trans e
      exact hpa (dvd_of_mod_eq_zero ha0)
    · exact hpos
  · rintro ⟨r, _, hrlt, hrsq⟩
    -- A bounded root `r` may have `r*r < a`; lift it to `x = r + a*p`, which
    -- is `≡ r (mod p)` and large enough that `a ≤ x*x`.
    have hp1 : 1 ≤ p := hppos
    refine ⟨r + a * p, le_sq_lift a r p hp1, ?_⟩
    · -- p ∣ (r + a*p)² - a, via congruence mod p
      -- (r + a*p) % p = r % p = r, so its square ≡ r*r ≡ a (mod p).
      have hxmod : (r + a * p) % p = r := by
        calc (r + a * p) % p = r % p := add_mul_mod_self_pure r p a
          _ = r := Nat.mod_eq_of_lt hrlt
      -- ((r+a*p)%p)*((r+a*p)%p) % p = (r+a*p)*(r+a*p) % p  (dvd_sq_sub_mod_sq)
      have hsqmod : (r + a * p) * (r + a * p) % p = a % p := by
        have hbridge : (r + a * p) * (r + a * p) % p
            = ((r + a * p) % p) * ((r + a * p) % p) % p := by
          have hrle : ((r + a * p) % p) * ((r + a * p) % p)
              ≤ (r + a * p) * (r + a * p) :=
            Nat.mul_le_mul (Nat.mod_le _ p) (Nat.mod_le _ p)
          exact (mod_eq_of_dvd_sub hrle (dvd_sq_sub_mod_sq p (r + a * p)))
        calc (r + a * p) * (r + a * p) % p
            = ((r + a * p) % p) * ((r + a * p) % p) % p := hbridge
          _ = r * r % p := by rw [hxmod]
          _ = a % p := hrsq
      -- p ∣ (r+a*p)² - a  from  (r+a*p)² % p = a % p  and  a ≤ (r+a*p)²
      exact dvd_of_mod_eq_zero
        (mod_diff_eq_zero_of_le hppos (le_sq_lift a r p hp1) hsqmod.symm)

end E213.Lib.Math.NumberTheory.ModArith.QRDescentFrame
