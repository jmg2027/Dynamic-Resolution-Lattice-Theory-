import E213.Meta.Nat.PolyNatMTactic

/-!
# LambertMinor — the minor-sign system of the convergent polynomials (weld, final piece)

`cross_le` (the Chebyshev engine, `LambertWeld` §9) consumes the **minor condition**
on the convergent-polynomial pair `(Ã, B̃)`: the coefficient ratios increase along
positions.  This file proves the underlying sign system at the position-function
level (`apF/bpF n i` = the `i`-th coefficient of `Ã_{n−1}/B̃_{n−1}`, totalized by `0`
off the support — so there are **no list edge cases**):

  * `m₁` — adjacent minors:        `aₙ(t)·bₙ(t+1) ≤ bₙ(t)·aₙ(t+1)`;
  * `D`  — same-position cross-level: `aₙ₊₁(t)·bₙ(t) ≤ bₙ₊₁(t)·aₙ(t)`;
  * `F`  — one-apart cross-level:  `aₙ(t)·bₙ₊₁(t+1) ≤ bₙ(t)·aₙ₊₁(t+1)`;
  * `G`  — reverse one-apart:      `aₙ₊₁(t)·bₙ(t+1) ≤ bₙ₊₁(t)·aₙ(t+1)`,

a **closed system** under the three-term recursion: the two-apart cross (`E`) that
`m₁`'s step needs is *derived* by ratio-chaining `F` with `m₁` through the pivot
`bₙ₊₁(t+1)` — with the zero-pivot case discharged by **prefix-support** (`bpF`'s
support is an initial segment, so a vanishing pivot kills the whole tail).  Each
step inequality closes **termwise** (no cancellation): the bilinear expansion of
the recursion sends each product to a `c²·`, `c·`, or constant multiple of a
lower-level family member.

This is the continuant-total-positivity core of the weld; chaining it to all gaps
(`MinorLE`) and assembling the order transfer is the remaining plumbing.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertMinor

/-! ## §1 — the coefficient functions -/

/-- Coefficients of `Ã_{n−1}` (= `AP n`), totalized: `apF n i = 0` off the support. -/
def apF : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | 1, 0 => 1
  | 1, _ + 1 => 0
  | n + 2, 0 => (2 * n + 3) * apF (n + 1) 0
  | n + 2, i + 1 => (2 * n + 3) * apF (n + 1) (i + 1) + apF n i

/-- Coefficients of `B̃_{n−1}` (= `BP n`), totalized. -/
def bpF : Nat → Nat → Nat
  | 0, _ => 0
  | 1, 0 => 1
  | 1, _ + 1 => 0
  | n + 2, 0 => (2 * n + 3) * bpF (n + 1) 0
  | n + 2, i + 1 => (2 * n + 3) * bpF (n + 1) (i + 1) + bpF n i

/-! ## §2 — prefix support: a zero entry kills the tail -/

private theorem eq_zero_of_le_zero : ∀ {n : Nat}, n ≤ 0 → n = 0
  | 0, _ => rfl
  | _ + 1, h => absurd h (Nat.not_succ_le_zero _)

private theorem factor_zero {c x : Nat} (hc : 1 ≤ c) (h : c * x = 0) : x = 0 := by
  apply eq_zero_of_le_zero
  calc x = 1 * x := (Nat.one_mul x).symm
    _ ≤ c * x := Nat.mul_le_mul hc (Nat.le_refl x)
    _ = 0 := h

private theorem left_zero_of_add_eq_zero {a b : Nat} (h : a + b = 0) : a = 0 := by
  apply eq_zero_of_le_zero
  calc a ≤ a + b := Nat.le_add_right a b
    _ = 0 := h

private theorem right_zero_of_add_eq_zero {a b : Nat} (h : a + b = 0) : b = 0 := by
  apply eq_zero_of_le_zero
  calc b ≤ a + b := Nat.le_add_left b a
    _ = 0 := h

/-- `bpF`'s support is a prefix: a zero entry forces the next entry to vanish. -/
theorem bpF_support : ∀ (n s : Nat), bpF n s = 0 → bpF n (s + 1) = 0
  | 0, _, _ => rfl
  | 1, 0, h => absurd h (by decide)
  | 1, _ + 1, _ => rfl
  | n + 2, 0, h => by
    show (2 * n + 3) * bpF (n + 1) 1 + bpF n 0 = 0
    have h1 : bpF (n + 1) 0 = 0 :=
      factor_zero (Nat.le_add_left 1 _) h
    have h2 : bpF (n + 1) 1 = 0 := bpF_support (n + 1) 0 h1
    have h3 : bpF n 0 = 0 := by
      cases n with
      | zero => rfl
      | succ k =>
        exact factor_zero (Nat.le_add_left 1 _)
          (show (2 * k + 3) * bpF (k + 1) 0 = 0 from h1)
    rw [h2, h3, Nat.mul_zero]
  | n + 2, s + 1, h => by
    show (2 * n + 3) * bpF (n + 1) (s + 2) + bpF n (s + 1) = 0
    have h1 : bpF (n + 1) (s + 1) = 0 :=
      factor_zero (Nat.le_add_left 1 _) (left_zero_of_add_eq_zero h)
    have h2 : bpF n s = 0 := right_zero_of_add_eq_zero h
    rw [bpF_support (n + 1) (s + 1) h1, bpF_support n s h2, Nat.mul_zero]

/-! ## §3 — the ratio chain -/

/-- Cross-multiplied ratio transitivity through a positive pivot:
    `a/b ≤ u/v` and `u/v ≤ u'/v'` give `a/b ≤ u'/v'` (`v ≥ 1`). -/
theorem ratio_chain {a b u v u' v' : Nat} (h1 : a * v ≤ b * u) (h2 : u * v' ≤ v * u')
    (hv : 1 ≤ v) : a * v' ≤ b * u' := by
  have h3 : v * (a * v') ≤ v * (b * u') := by
    calc v * (a * v') = a * v * v' := by ring_nat
      _ ≤ b * u * v' := Nat.mul_le_mul h1 (Nat.le_refl v')
      _ = b * (u * v') := by ring_nat
      _ ≤ b * (v * u') := Nat.mul_le_mul (Nat.le_refl b) h2
      _ = v * (b * u') := by ring_nat
  exact Nat.le_of_mul_le_mul_left h3 hv

/-! ## §4 — the four-family sign system -/

/-- The closed minor-sign system at level `n` (`a := apF`, `b := bpF`):
    adjacent minors `m₁`, same-position cross-level `D`, one-apart `F`, and
    reverse one-apart `G`. -/
structure MinorSys (n : Nat) : Prop where
  m1 : ∀ t, apF n t * bpF n (t + 1) ≤ bpF n t * apF n (t + 1)
  d  : ∀ t, apF (n + 1) t * bpF n t ≤ bpF (n + 1) t * apF n t
  f  : ∀ t, apF n t * bpF (n + 1) (t + 1) ≤ bpF n t * apF (n + 1) (t + 1)
  g  : ∀ t, apF (n + 1) t * bpF n (t + 1) ≤ bpF (n + 1) t * apF n (t + 1)

/-- The two-apart cross-level inequality (`E`), **derived**: chain `F` with the
    next-level adjacent minor through the pivot `bpF (n+1) (t+1)`; if the pivot
    vanishes, prefix-support kills `bpF (n+1) (t+2)` and the claim is free. -/
theorem e_of_sys {n : Nat} (S : MinorSys n) (S' : MinorSys (n + 1)) (t : Nat) :
    apF n t * bpF (n + 1) (t + 2) ≤ bpF n t * apF (n + 1) (t + 2) := by
  cases hpiv : bpF (n + 1) (t + 1) with
  | zero =>
    rw [bpF_support (n + 1) (t + 1) hpiv]
    rw [Nat.mul_zero]
    exact Nat.zero_le _
  | succ p =>
    exact ratio_chain (S.f t) (S'.m1 (t + 1))
      (by rw [hpiv]; exact Nat.succ_le_succ (Nat.zero_le p))

/-- Base: level 0 (`B̃₋₁ = 0`, everything degenerate). -/
theorem minorSys_zero : MinorSys 0 where
  m1 := fun t => by
    show apF 0 t * bpF 0 (t + 1) ≤ bpF 0 t * apF 0 (t + 1)
    rw [show bpF 0 (t + 1) = 0 from rfl, show bpF 0 t = 0 from rfl,
        Nat.mul_zero, Nat.zero_mul]
    exact Nat.le_refl 0
  d := fun t => by
    rw [show bpF 0 t = 0 from rfl, Nat.mul_zero]
    exact Nat.zero_le _
  f := fun t => by
    cases t with
    | zero =>
      show apF 0 0 * bpF 1 1 ≤ bpF 0 0 * apF 1 1
      decide
    | succ s =>
      show apF 0 (s + 1) * bpF 1 (s + 2) ≤ bpF 0 (s + 1) * apF 1 (s + 2)
      rw [show apF 0 (s + 1) = 0 from rfl, Nat.zero_mul]
      exact Nat.zero_le _
  g := fun t => by
    rw [show bpF 0 (t + 1) = 0 from rfl, Nat.mul_zero]
    exact Nat.zero_le _

/-- Base: level 1 (`Ã₀ = B̃₀ = 1`). -/
theorem minorSys_one : MinorSys 1 where
  m1 := fun t => by
    cases t with
    | zero => decide
    | succ s =>
      rw [show apF 1 (s + 1) = 0 from rfl, Nat.zero_mul]
      exact Nat.zero_le _
  d := fun t => by
    cases t with
    | zero => decide
    | succ s =>
      rw [show bpF 1 (s + 1) = 0 from rfl, Nat.mul_zero]
      exact Nat.zero_le _
  f := fun t => by
    cases t with
    | zero => decide
    | succ s =>
      rw [show apF 1 (s + 1) = 0 from rfl, Nat.zero_mul]
      exact Nat.zero_le _
  g := fun t => by
    cases t with
    | zero => decide
    | succ s =>
      rw [show bpF 1 (s + 1 + 1) = 0 from rfl, Nat.mul_zero]
      exact Nat.zero_le _

/-- ★★★★★ **The minor-sign system holds at every level** — the
    continuant-total-positivity induction.  Each component of level `n+2` closes
    **termwise** from levels `n+1` and `n` through the bilinear expansion of the
    three-term recursion; the two-apart cross (`E`) is chained on demand. -/
theorem minorSys : ∀ n, MinorSys n
  | 0 => minorSys_zero
  | 1 => minorSys_one
  | n + 2 => by
    have S0 := minorSys n
    have S1 := minorSys (n + 1)
    have hE0 := e_of_sys S0 S1
    -- m₁ at level n+2
    have hm1 : ∀ t, apF (n + 2) t * bpF (n + 2) (t + 1)
        ≤ bpF (n + 2) t * apF (n + 2) (t + 1) := by
      intro t
      cases t with
      | zero =>
        show (2 * n + 3) * apF (n + 1) 0
              * ((2 * n + 3) * bpF (n + 1) 1 + bpF n 0)
            ≤ (2 * n + 3) * bpF (n + 1) 0
              * ((2 * n + 3) * apF (n + 1) 1 + apF n 0)
        rw [show (2 * n + 3) * apF (n + 1) 0
              * ((2 * n + 3) * bpF (n + 1) 1 + bpF n 0)
            = (2 * n + 3) * (2 * n + 3) * (apF (n + 1) 0 * bpF (n + 1) 1)
              + (2 * n + 3) * (apF (n + 1) 0 * bpF n 0) from by ring_nat,
            show (2 * n + 3) * bpF (n + 1) 0
              * ((2 * n + 3) * apF (n + 1) 1 + apF n 0)
            = (2 * n + 3) * (2 * n + 3) * (bpF (n + 1) 0 * apF (n + 1) 1)
              + (2 * n + 3) * (bpF (n + 1) 0 * apF n 0) from by ring_nat]
        exact Nat.add_le_add
          (Nat.mul_le_mul_left _ (S1.m1 0))
          (Nat.mul_le_mul_left _ (S0.d 0))
      | succ s =>
        show ((2 * n + 3) * apF (n + 1) (s + 1) + apF n s)
              * ((2 * n + 3) * bpF (n + 1) (s + 2) + bpF n (s + 1))
            ≤ ((2 * n + 3) * bpF (n + 1) (s + 1) + bpF n s)
              * ((2 * n + 3) * apF (n + 1) (s + 2) + apF n (s + 1))
        rw [show ((2 * n + 3) * apF (n + 1) (s + 1) + apF n s)
              * ((2 * n + 3) * bpF (n + 1) (s + 2) + bpF n (s + 1))
            = (2 * n + 3) * (2 * n + 3) * (apF (n + 1) (s + 1) * bpF (n + 1) (s + 2))
              + ((2 * n + 3) * (apF (n + 1) (s + 1) * bpF n (s + 1))
                + ((2 * n + 3) * (apF n s * bpF (n + 1) (s + 2))
                  + apF n s * bpF n (s + 1))) from by ring_nat,
            show ((2 * n + 3) * bpF (n + 1) (s + 1) + bpF n s)
              * ((2 * n + 3) * apF (n + 1) (s + 2) + apF n (s + 1))
            = (2 * n + 3) * (2 * n + 3) * (bpF (n + 1) (s + 1) * apF (n + 1) (s + 2))
              + ((2 * n + 3) * (bpF (n + 1) (s + 1) * apF n (s + 1))
                + ((2 * n + 3) * (bpF n s * apF (n + 1) (s + 2))
                  + bpF n s * apF n (s + 1))) from by ring_nat]
        exact Nat.add_le_add (Nat.mul_le_mul_left _ (S1.m1 (s + 1)))
          (Nat.add_le_add (Nat.mul_le_mul_left _ (S0.d (s + 1)))
            (Nat.add_le_add (Nat.mul_le_mul_left _ (hE0 s)) (S0.m1 s)))
    -- E at level n+1 (chained from F(n+1) and the just-proven m₁(n+2))
    have hE1 : ∀ t, apF (n + 1) t * bpF (n + 2) (t + 2)
        ≤ bpF (n + 1) t * apF (n + 2) (t + 2) := by
      intro t
      cases hpiv : bpF (n + 2) (t + 1) with
      | zero =>
        rw [bpF_support (n + 2) (t + 1) hpiv, Nat.mul_zero]
        exact Nat.zero_le _
      | succ p =>
        exact ratio_chain (S1.f t) (hm1 (t + 1))
          (by rw [hpiv]; exact Nat.succ_le_succ (Nat.zero_le p))
    refine ⟨hm1, ?_, ?_, ?_⟩
    -- D at level n+2: the c-heads cancel termwise; the rest is F(n+1)
    · intro t
      cases t with
      | zero =>
        show (2 * n + 5) * apF (n + 2) 0 * ((2 * n + 3) * bpF (n + 1) 0)
            ≤ (2 * n + 5) * bpF (n + 2) 0 * ((2 * n + 3) * apF (n + 1) 0)
        rw [show (2 * n + 5) * apF (n + 2) 0 * ((2 * n + 3) * bpF (n + 1) 0)
              = (2 * n + 5) * (2 * n + 3)
                * (apF (n + 2) 0 * bpF (n + 1) 0) from by ring_nat,
            show (2 * n + 5) * bpF (n + 2) 0 * ((2 * n + 3) * apF (n + 1) 0)
              = (2 * n + 5) * (2 * n + 3)
                * (bpF (n + 2) 0 * apF (n + 1) 0) from by ring_nat]
        refine Nat.mul_le_mul_left _ ?_
        show apF (n + 2) 0 * bpF (n + 1) 0 ≤ bpF (n + 2) 0 * apF (n + 1) 0
        rw [show apF (n + 2) 0 = (2 * n + 3) * apF (n + 1) 0 from rfl,
            show bpF (n + 2) 0 = (2 * n + 3) * bpF (n + 1) 0 from rfl,
            show (2 * n + 3) * apF (n + 1) 0 * bpF (n + 1) 0
              = (2 * n + 3) * (apF (n + 1) 0 * bpF (n + 1) 0) from by ring_nat,
            show (2 * n + 3) * bpF (n + 1) 0 * apF (n + 1) 0
              = (2 * n + 3) * (apF (n + 1) 0 * bpF (n + 1) 0) from by ring_nat]
        exact Nat.le_refl _
      | succ s =>
        show ((2 * n + 5) * apF (n + 2) (s + 1) + apF (n + 1) s)
              * ((2 * n + 3) * bpF (n + 1) (s + 1) + bpF n s)
            ≤ ((2 * n + 5) * bpF (n + 2) (s + 1) + bpF (n + 1) s)
              * ((2 * n + 3) * apF (n + 1) (s + 1) + apF n s)
        -- apF (n+2) (s+1) = (2n+3)·apF (n+1) (s+1) + apF n s (defeq), so both sides
        -- share the structure; expand fully and compare termwise.
        rw [show apF (n + 2) (s + 1)
              = (2 * n + 3) * apF (n + 1) (s + 1) + apF n s from rfl,
            show bpF (n + 2) (s + 1)
              = (2 * n + 3) * bpF (n + 1) (s + 1) + bpF n s from rfl,
            show ((2 * n + 5) * ((2 * n + 3) * apF (n + 1) (s + 1) + apF n s)
                  + apF (n + 1) s)
                * ((2 * n + 3) * bpF (n + 1) (s + 1) + bpF n s)
              = (2 * n + 5) * ((2 * n + 3) * apF (n + 1) (s + 1) + apF n s)
                  * ((2 * n + 3) * bpF (n + 1) (s + 1) + bpF n s)
                + ((2 * n + 3) * (apF (n + 1) s * bpF (n + 1) (s + 1))
                  + apF (n + 1) s * bpF n s) from by ring_nat,
            show ((2 * n + 5) * ((2 * n + 3) * bpF (n + 1) (s + 1) + bpF n s)
                  + bpF (n + 1) s)
                * ((2 * n + 3) * apF (n + 1) (s + 1) + apF n s)
              = (2 * n + 5) * ((2 * n + 3) * apF (n + 1) (s + 1) + apF n s)
                  * ((2 * n + 3) * bpF (n + 1) (s + 1) + bpF n s)
                + ((2 * n + 3) * (bpF (n + 1) s * apF (n + 1) (s + 1))
                  + bpF (n + 1) s * apF n s) from by ring_nat]
        refine Nat.add_le_add_left ?_ _
        exact Nat.add_le_add (Nat.mul_le_mul_left _ (S1.m1 s)) (S0.d s)
    -- F at level n+2: c-heads are m₁(n+2); the rest is D(n+1)
    · intro t
      show apF (n + 2) t * ((2 * n + 5) * bpF (n + 2) (t + 1) + bpF (n + 1) t)
          ≤ bpF (n + 2) t * ((2 * n + 5) * apF (n + 2) (t + 1) + apF (n + 1) t)
      rw [show apF (n + 2) t * ((2 * n + 5) * bpF (n + 2) (t + 1) + bpF (n + 1) t)
            = (2 * n + 5) * (apF (n + 2) t * bpF (n + 2) (t + 1))
              + apF (n + 2) t * bpF (n + 1) t from by ring_nat,
          show bpF (n + 2) t * ((2 * n + 5) * apF (n + 2) (t + 1) + apF (n + 1) t)
            = (2 * n + 5) * (bpF (n + 2) t * apF (n + 2) (t + 1))
              + bpF (n + 2) t * apF (n + 1) t from by ring_nat]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ (hm1 t)) (S1.d t)
    -- G at level n+2: expand the (n+3)-entry; c-heads are m₁(n+2), rest is E(n+1)
    · intro t
      cases t with
      | zero =>
        show (2 * n + 5) * apF (n + 2) 0 * bpF (n + 2) 1
            ≤ (2 * n + 5) * bpF (n + 2) 0 * apF (n + 2) 1
        rw [show (2 * n + 5) * apF (n + 2) 0 * bpF (n + 2) 1
              = (2 * n + 5) * (apF (n + 2) 0 * bpF (n + 2) 1) from by ring_nat,
            show (2 * n + 5) * bpF (n + 2) 0 * apF (n + 2) 1
              = (2 * n + 5) * (bpF (n + 2) 0 * apF (n + 2) 1) from by ring_nat]
        exact Nat.mul_le_mul_left _ (hm1 0)
      | succ s =>
        show ((2 * n + 5) * apF (n + 2) (s + 1) + apF (n + 1) s) * bpF (n + 2) (s + 2)
            ≤ ((2 * n + 5) * bpF (n + 2) (s + 1) + bpF (n + 1) s) * apF (n + 2) (s + 2)
        rw [show ((2 * n + 5) * apF (n + 2) (s + 1) + apF (n + 1) s)
                * bpF (n + 2) (s + 2)
              = (2 * n + 5) * (apF (n + 2) (s + 1) * bpF (n + 2) (s + 2))
                + apF (n + 1) s * bpF (n + 2) (s + 2) from by ring_nat,
            show ((2 * n + 5) * bpF (n + 2) (s + 1) + bpF (n + 1) s)
                * apF (n + 2) (s + 2)
              = (2 * n + 5) * (bpF (n + 2) (s + 1) * apF (n + 2) (s + 2))
                + bpF (n + 1) s * apF (n + 2) (s + 2) from by ring_nat]
        exact Nat.add_le_add (Nat.mul_le_mul_left _ (hm1 (s + 1))) (hE1 s)

/-- The two-apart cross at every level (the `E`-family, packaged). -/
theorem minor_e (n t : Nat) :
    apF n t * bpF (n + 1) (t + 2) ≤ bpF n t * apF (n + 1) (t + 2) :=
  e_of_sys (minorSys n) (minorSys (n + 1)) t

/-- ★★★★ **All-gap minors**: the coefficient ratios increase across *every* gap,
    not just adjacent positions — chain the adjacent minors through positive
    pivots (`ratio_chain`); a vanishing pivot kills the tail (`bpF_support`). -/
theorem minor_all (n : Nat) : ∀ (j i : Nat), i < j →
    apF n i * bpF n j ≤ bpF n i * apF n j
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | j + 1, i, h => by
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h) with heq | hlt
    · rw [heq]
      exact (minorSys n).m1 j
    · cases hpiv : bpF n j with
      | zero =>
        rw [bpF_support n j hpiv, Nat.mul_zero]
        exact Nat.zero_le _
      | succ p =>
        exact ratio_chain (minor_all n j i hlt) ((minorSys n).m1 j)
          (by rw [hpiv]; exact Nat.succ_le_succ (Nat.zero_le p))

/-! ## §5 — the halving system: coefficients at least halve along the lists

The dominance blueprint's geometric input.  The exact strengthening
`2·f(n+1)(s+1) + f(n)(s) ≤ f(n+1)(s)` (equality at the head: `2·420 + 105 =
945`) is what the three-term recursion propagates — the plain halving
`2·f(s+1) ≤ f(s)` follows. -/

theorem apF_level_mono : ∀ (n s : Nat), apF n s ≤ apF (n + 1) s
  | 0, 0 => Nat.le_refl 1
  | 0, _ + 1 => Nat.le_refl 0
  | n + 1, 0 => by
    show apF (n + 1) 0 ≤ (2 * n + 3) * apF (n + 1) 0
    exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  | n + 1, s + 1 => by
    show apF (n + 1) (s + 1) ≤ (2 * n + 3) * apF (n + 1) (s + 1) + apF n s
    exact Nat.le_trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      (Nat.le_add_right _ _)

theorem bpF_level_mono : ∀ (n s : Nat), bpF n s ≤ bpF (n + 1) s
  | 0, _ => Nat.zero_le _
  | n + 1, 0 => by
    show bpF (n + 1) 0 ≤ (2 * n + 3) * bpF (n + 1) 0
    exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  | n + 1, s + 1 => by
    show bpF (n + 1) (s + 1) ≤ (2 * n + 3) * bpF (n + 1) (s + 1) + bpF n s
    exact Nat.le_trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      (Nat.le_add_right _ _)

/-- The head recursion in closed form: `apF (n+1) 0 = (2n+1)·apF n 0`. -/
theorem apF_head : ∀ n, apF (n + 1) 0 = (2 * n + 1) * apF n 0
  | 0 => (Nat.one_mul 1).symm
  | _ + 1 => rfl

theorem apF_step_le : ∀ (n s : Nat),
    apF (n + 1) (s + 1) ≤ (2 * n + 1) * apF n (s + 1) + apF n s
  | 0, _ => Nat.zero_le _
  | n + 1, s => by
    show (2 * n + 3) * apF (n + 1) (s + 1) + apF n s
        ≤ (2 * n + 3) * apF (n + 1) (s + 1) + apF (n + 1) s
    exact Nat.add_le_add_left (apF_level_mono n s) _

theorem bpF_step_le : ∀ (n s : Nat),
    bpF (n + 1) (s + 1) ≤ (2 * n + 1) * bpF n (s + 1) + bpF n s
  | 0, _ => Nat.zero_le _
  | n + 1, s => by
    show (2 * n + 3) * bpF (n + 1) (s + 1) + bpF n s
        ≤ (2 * n + 3) * bpF (n + 1) (s + 1) + bpF (n + 1) s
    exact Nat.add_le_add_left (bpF_level_mono n s) _

/-- ★★★ **Strengthened halving, `A`-side**: `2·apF (n+1) (s+1) + apF n s ≤
    apF (n+1) s` — the absorption `2 + (2n+1) = 2n+3` closes the head, the
    level shift closes the tail. -/
theorem apF_halving_strong : ∀ (n s : Nat),
    2 * apF (n + 1) (s + 1) + apF n s ≤ apF (n + 1) s
  | 0, 0 => by decide
  | 0, s + 1 => by
    show 2 * apF 1 (s + 2) + apF 0 (s + 1) ≤ apF 1 (s + 1)
    exact Nat.le_refl 0
  | n + 1, 0 => by
    have ih := apF_halving_strong n 0
    show 2 * ((2 * n + 3) * apF (n + 1) 1 + apF n 0) + apF (n + 1) 0
        ≤ (2 * n + 3) * apF (n + 1) 0
    calc 2 * ((2 * n + 3) * apF (n + 1) 1 + apF n 0) + apF (n + 1) 0
        = 2 * ((2 * n + 3) * apF (n + 1) 1 + apF n 0) + (2 * n + 1) * apF n 0 := by
          rw [apF_head n]
      _ = (2 * n + 3) * (2 * apF (n + 1) 1 + apF n 0) := by ring_nat
      _ ≤ (2 * n + 3) * apF (n + 1) 0 := Nat.mul_le_mul_left _ ih
  | n + 1, s + 1 => by
    have ih := apF_halving_strong n (s + 1)
    show 2 * ((2 * n + 3) * apF (n + 1) (s + 2) + apF n (s + 1)) + apF (n + 1) (s + 1)
        ≤ (2 * n + 3) * apF (n + 1) (s + 1) + apF n s
    calc 2 * ((2 * n + 3) * apF (n + 1) (s + 2) + apF n (s + 1)) + apF (n + 1) (s + 1)
        ≤ 2 * ((2 * n + 3) * apF (n + 1) (s + 2) + apF n (s + 1))
          + ((2 * n + 1) * apF n (s + 1) + apF n s) :=
          Nat.add_le_add_left (apF_step_le n s) _
      _ = (2 * n + 3) * (2 * apF (n + 1) (s + 2) + apF n (s + 1)) + apF n s := by
          ring_nat
      _ ≤ (2 * n + 3) * apF (n + 1) (s + 1) + apF n s :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ ih) _

/-- ★★★ **Strengthened halving, `B`-side** (two bases: `bpF`'s head identity
    starts one level later). -/
theorem bpF_halving_strong : ∀ (n s : Nat),
    2 * bpF (n + 1) (s + 1) + bpF n s ≤ bpF (n + 1) s
  | 0, 0 => by decide
  | 0, s + 1 => by
    show 2 * bpF 1 (s + 2) + bpF 0 (s + 1) ≤ bpF 1 (s + 1)
    exact Nat.le_refl 0
  | 1, 0 => by decide
  | 1, s + 1 => by
    show 2 * ((2 * 0 + 3) * bpF 1 (s + 2) + bpF 0 (s + 1)) + bpF 1 (s + 1)
        ≤ (2 * 0 + 3) * bpF 1 (s + 1) + bpF 0 s
    exact Nat.zero_le _
  | n + 2, 0 => by
    have ih := bpF_halving_strong (n + 1) 0
    show 2 * ((2 * n + 5) * bpF (n + 2) 1 + bpF (n + 1) 0) + bpF (n + 2) 0
        ≤ (2 * n + 5) * bpF (n + 2) 0
    calc 2 * ((2 * n + 5) * bpF (n + 2) 1 + bpF (n + 1) 0) + bpF (n + 2) 0
        = 2 * ((2 * n + 5) * bpF (n + 2) 1 + bpF (n + 1) 0)
          + (2 * n + 3) * bpF (n + 1) 0 := rfl
      _ = (2 * n + 5) * (2 * bpF (n + 2) 1 + bpF (n + 1) 0) := by ring_nat
      _ ≤ (2 * n + 5) * bpF (n + 2) 0 := Nat.mul_le_mul_left _ ih
  | n + 2, s + 1 => by
    have ih := bpF_halving_strong (n + 1) (s + 1)
    show 2 * ((2 * n + 5) * bpF (n + 2) (s + 2) + bpF (n + 1) (s + 1))
          + bpF (n + 2) (s + 1)
        ≤ (2 * n + 5) * bpF (n + 2) (s + 1) + bpF (n + 1) s
    calc 2 * ((2 * n + 5) * bpF (n + 2) (s + 2) + bpF (n + 1) (s + 1))
          + bpF (n + 2) (s + 1)
        ≤ 2 * ((2 * n + 5) * bpF (n + 2) (s + 2) + bpF (n + 1) (s + 1))
          + ((2 * (n + 1) + 1) * bpF (n + 1) (s + 1) + bpF (n + 1) s) :=
          Nat.add_le_add_left (bpF_step_le (n + 1) s) _
      _ = (2 * n + 5) * (2 * bpF (n + 2) (s + 2) + bpF (n + 1) (s + 1))
          + bpF (n + 1) s := by ring_nat
      _ ≤ (2 * n + 5) * bpF (n + 2) (s + 1) + bpF (n + 1) s :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ ih) _

/-- Plain halving: every coefficient is at least twice its successor. -/
theorem apF_halving : ∀ (n s : Nat), 2 * apF n (s + 1) ≤ apF n s
  | 0, 0 => by decide
  | 0, s + 1 => by
    show 2 * apF 0 (s + 2) ≤ apF 0 (s + 1)
    exact Nat.le_refl 0
  | n + 1, s =>
    Nat.le_trans (Nat.le_add_right _ (apF n s)) (apF_halving_strong n s)

theorem bpF_halving : ∀ (n s : Nat), 2 * bpF n (s + 1) ≤ bpF n s
  | 0, _ => Nat.zero_le _
  | n + 1, s =>
    Nat.le_trans (Nat.le_add_right _ (bpF n s)) (bpF_halving_strong n s)

/-- Numeric anchors (level 5: `Ã₄ = [945, 420, 15]`, `B̃₄ = [945, 105, 1]`): the
    adjacent minors and cross-level families check arithmetically. -/
theorem minor_anchors :
    apF 5 0 = 945 ∧ apF 5 1 = 420 ∧ apF 5 2 = 15
    ∧ bpF 5 0 = 945 ∧ bpF 5 1 = 105 ∧ bpF 5 2 = 1
    ∧ apF 5 0 * bpF 5 1 ≤ bpF 5 0 * apF 5 1
    ∧ apF 5 1 * bpF 5 2 ≤ bpF 5 1 * apF 5 2 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
   by decide⟩

end E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertMinor
