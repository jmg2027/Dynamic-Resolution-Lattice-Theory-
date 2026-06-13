import E213.Lib.Math.NumberTheory.ModArith.PureNatMod3
import E213.Meta.Nat.PolyNatMTactic

/-!
# EisensteinFormCharacter — the disc-`−3` form represents only `{0,1} mod 3` (the χ₋₃ fingerprint)

The Eisenstein period (the real period of the `j = 0` curve `y² = x³ − 1`, a `Γ(1/3)`
value, CM by `ℤ[ω]`) is the disc-`−3` analog of `ϖ` (the lemniscate constant, disc `−4`,
a `Γ(1/4)` value).  Its arithmetic skeleton is the **Epstein zeta function of the
Eisenstein form**

  `Z(s) = Σ'_{(a,b)≠0} 1 / (a² + ab + b²)^s`,

which factors as `Z(s) = 6 · ζ(s) · L(s, χ₋₃)` — the disc-`−3` `L`-function attached to
the quadratic character `χ₋₃` mod 3 (the same mod-3 structure the repo carries in
`Mod213`'s 6th-root walk).  This factorization is *why* the Eisenstein period is a
`Γ(1/3)` value (Chowla–Selberg / Lerch), exactly as the disc-`−4` `Σ 1/(a²+b²)^s =
4 ζ(s) L(s,χ₋₄)` makes `ϖ` a `Γ(1/4)` value.

This file pins the part of that picture reachable by pure `ℕ`-arithmetic: the **character
constraint**, i.e. *which residues the form can represent*.

  * ★★★ `eisCyc_mod3_ne_two` — the disc-`−3` form `a² + ab + b²` is **never `≡ 2 (mod 3)`**;
    it represents only the residues `{0, 1}` mod 3.  This is the `χ₋₃` fingerprint: the
    Loeschian numbers (values of the form) avoid the non-residue class `2 mod 3` exactly as
    sums of two squares avoid `3 mod 4`.  `a² + ab + b²` is `formEval (fixForm U)` — the
    fixed-point form of the order-6 elliptic generator `U` (`Real213.CrossDet.CrossDetTraceField`),
    so the period's governing form is the elliptic CM point's own form.

  * `mod3_add` / `mod3_mul` — the custom `mod3` is a ring homomorphism (additive and
    multiplicative); the structural tools behind the fingerprint.

**The wall (honest scope).**  Only the *necessary* character condition is `∅`-axiom here.
The full Loeschian theorem (`a²+ab+b² = n` solvable ⟺ every prime `≡ 2 (mod 3)` divides
`n` to an even power) needs unique factorization in `ℤ[ω]`; the *value* of the period
itself — the real number `Z(1)`-regulator / the `Γ(1/3)` constant — needs either the cube
`AGM` (whose geometric-mean step is exactly `b·(a²+ab+b²)/3`, the disc-`−3` form again, but
with a cube root that leaves clean `ℤ`-arithmetic) or the analytic value `L(1,χ₋₃) = π/√27`.
Neither is reached from inside the `ℕ`/`ℤ` reflection provers; the reachable handle is the
form's arithmetic — the character — and that is what is pinned.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.EisensteinFormCharacter

open E213.Lib.Math.NumberTheory.ModArith.PureNatMod3
  (mod3 mod3_three_mul mod3_three_mul_add mod3_three_mul_one mod3_three_mul_two
   nat_trichotomy)

/-! ## §1 — `mod3` is a ring homomorphism: range, decomposition, additive, multiplicative -/

/-- Every residue is `0`, `1`, or `2`. -/
theorem mod3_range (n : Nat) : mod3 n = 0 ∨ mod3 n = 1 ∨ mod3 n = 2 := by
  rcases nat_trichotomy n with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk, mod3_three_mul]; exact Or.inl rfl
  · rw [hk, mod3_three_mul_one]; exact Or.inr (Or.inl rfl)
  · rw [hk, mod3_three_mul_two]; exact Or.inr (Or.inr rfl)

/-- The division decomposition `n = 3k + (n mod 3)`. -/
theorem mod3_decomp (n : Nat) : ∃ k, n = 3 * k + mod3 n := by
  rcases nat_trichotomy n with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k, by rw [hk, mod3_three_mul, Nat.add_zero]⟩
  · exact ⟨k, by rw [hk, mod3_three_mul_one]⟩
  · exact ⟨k, by rw [hk, mod3_three_mul_two]⟩

/-- The packed additive law `mod3 (3a+r + (3b+s)) = mod3 (r+s)`. -/
theorem mod3_add_pack (a r b s : Nat) :
    mod3 (3 * a + r + (3 * b + s)) = mod3 (r + s) := by
  have h : 3 * a + r + (3 * b + s) = 3 * (a + b) + (r + s) := by ring_nat
  rw [h, mod3_three_mul_add]

/-- ★★ **`mod3` is additive**: `mod3 (x+y) = mod3 (mod3 x + mod3 y)`. -/
theorem mod3_add (x y : Nat) : mod3 (x + y) = mod3 (mod3 x + mod3 y) := by
  obtain ⟨a, ha⟩ := mod3_decomp x
  obtain ⟨b, hb⟩ := mod3_decomp y
  generalize mod3 x = r at ha
  generalize mod3 y = s at hb
  rw [ha, hb]; exact mod3_add_pack a r b s

/-- The packed multiplicative law `mod3 ((3a+r)(3b+s)) = mod3 (r·s)`. -/
theorem mod3_mul_pack (a r b s : Nat) :
    mod3 ((3 * a + r) * (3 * b + s)) = mod3 (r * s) := by
  have h : (3 * a + r) * (3 * b + s) = 3 * (3 * a * b + a * s + b * r) + r * s := by ring_nat
  rw [h, mod3_three_mul_add]

/-- ★★ **`mod3` is multiplicative**: `mod3 (x·y) = mod3 (mod3 x · mod3 y)`. -/
theorem mod3_mul (x y : Nat) : mod3 (x * y) = mod3 (mod3 x * mod3 y) := by
  obtain ⟨a, ha⟩ := mod3_decomp x
  obtain ⟨b, hb⟩ := mod3_decomp y
  generalize mod3 x = r at ha
  generalize mod3 y = s at hb
  rw [ha, hb]; exact mod3_mul_pack a r b s

/-! ## §2 — the χ₋₃ fingerprint of the disc-`−3` Eisenstein form -/

/-- The positive-definite disc-`−3` Eisenstein form `a² + ab + b²` (the Loeschian-number
    form; `= formEval (fixForm U)` over `ℤ`, the order-6 elliptic CM point's own form). -/
def eisCyc (a b : Nat) : Nat := a * a + a * b + b * b

/-- The packed form reduction: `a² + ab + b²` modulo 3 depends only on `(a mod 3, b mod 3)`.
    Expanding `a = 3i+r`, `b = 3j+s` factors out a multiple of 3, leaving `r² + rs + s²`. -/
theorem eisCyc_pack (i r j s : Nat) :
    mod3 ((3 * i + r) * (3 * i + r) + (3 * i + r) * (3 * j + s)
            + (3 * j + s) * (3 * j + s))
      = mod3 (r * r + r * s + s * s) := by
  have h : (3 * i + r) * (3 * i + r) + (3 * i + r) * (3 * j + s)
            + (3 * j + s) * (3 * j + s)
      = 3 * (3 * i * i + 3 * i * j + 3 * j * j + 2 * i * r + i * s + j * r + 2 * j * s)
        + (r * r + r * s + s * s) := by ring_nat
  rw [h, mod3_three_mul_add]

/-- ★★★ **The χ₋₃ fingerprint.**  The disc-`−3` Eisenstein form `a² + ab + b²` is **never
    `≡ 2 (mod 3)`** — it represents only the residues `{0, 1}` mod 3.  This is the necessary
    character condition behind the Epstein-zeta factorization `Σ 1/(a²+ab+b²)^s = 6 ζ L(·,χ₋₃)`
    that makes the Eisenstein period a `Γ(1/3)` value: the Loeschian numbers avoid the
    non-residue class `2 mod 3`, the disc-`−3` analog of sums of two squares avoiding `3 mod
    4`.  Proved by the `mod3` ring-hom reduction to the nine residue pairs, each `decide`d. -/
theorem eisCyc_mod3_ne_two (a b : Nat) : mod3 (a * a + a * b + b * b) ≠ 2 := by
  obtain ⟨i, ha⟩ := mod3_decomp a
  obtain ⟨j, hb⟩ := mod3_decomp b
  have hra := mod3_range a
  have hrb := mod3_range b
  generalize mod3 a = r at ha hra
  generalize mod3 b = s at hb hrb
  rw [ha, hb, eisCyc_pack]
  rcases hra with h | h | h <;> rcases hrb with h' | h' | h' <;> rw [h, h'] <;> decide

/-- ★★★ **The form hits both allowed residues** (so the fingerprint is sharp): `0` at
    `(1,1)` (`eisCyc 1 1 = 3 ≡ 0`) and `1` at `(1,0)` (`eisCyc 1 0 = 1`).  With
    `eisCyc_mod3_ne_two` this is the full image `{0,1}` mod 3. -/
theorem eisCyc_hits_zero_and_one :
    mod3 (eisCyc 1 1) = 0 ∧ mod3 (eisCyc 1 0) = 1 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ★★★ **`2 mod 3` is not representable.**  Any `n ≡ 2 (mod 3)` — `2, 5, 8, 11, …` — is not
    a value of the Eisenstein form (contrapositive of `eisCyc_mod3_ne_two`): no `a, b` give
    `a² + ab + b² = n`.  The character obstruction, `∅`-axiom. -/
theorem mod3_two_not_eisenstein (n : Nat) (hn : mod3 n = 2) :
    ∀ a b : Nat, a * a + a * b + b * b ≠ n := by
  intro a b h
  exact eisCyc_mod3_ne_two a b ((congrArg mod3 h).trans hn)

end E213.Lib.Math.NumberTheory.ModArith.EisensteinFormCharacter
