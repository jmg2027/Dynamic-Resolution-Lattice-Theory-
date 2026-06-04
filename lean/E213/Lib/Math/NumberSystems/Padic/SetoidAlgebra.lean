import E213.Lib.Math.NumberSystems.Padic.SetoidFramework
/-!
# Setoid Algebra — Zp ring operations respect ZpSeqEquiv

Extends `SetoidFramework.lean` to the full ring structure on
ZpSeq: every ring operation (add, neg, mul) **respects the
digit-pointwise equivalence** `ZpSeqEquiv`.

This gives the full algebraic Setoid structure on `ZpSeq p`:

  · `add_respects` — `Zp.add` respects equivalence in both args
  · `neg_respects` — `Zp.neg` respects equivalence
  · `mul_respects` — `Zp.mul` respects equivalence in both args

Together with `SetoidFramework`'s involution result, this lifts
all ring identities (commutativity, associativity, distributivity)
to the Setoid level, **without funext**.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.Padic.SetoidAlgebra

open E213.Lib.Math.NumberSystems.Padic.SetoidFramework
  (ZpSeqEquiv ZpSeqEquiv.refl ZpSeqEquiv.symm ZpSeqEquiv.trans
   complement_respects)

/-! ## §1 — Carry respects ZpSeqEquiv -/

/-- Carry function of `x + y` depends only on x.digits and y.digits;
    equivalent inputs produce equal carries. -/
theorem carry_respects (p : Nat) (x₁ y₁ x₂ y₂ : ZpSeq p)
    (hx : ZpSeqEquiv x₁ x₂) (hy : ZpSeqEquiv y₁ y₂) :
    ∀ k, Zp.carry p x₁ y₁ k = Zp.carry p x₂ y₂ k
  | 0 => rfl
  | k + 1 => by
    rw [Zp.carry_succ, Zp.carry_succ]
    rw [hx k, hy k]
    rw [carry_respects p x₁ y₁ x₂ y₂ hx hy k]

/-! ## §2 — Zp.add respects ZpSeqEquiv -/

/-- ★★★★ **Zp.add respects ZpSeqEquiv** in both arguments. -/
theorem add_respects (p : Nat) (hp : 0 < p) (x₁ y₁ x₂ y₂ : ZpSeq p)
    (hx : ZpSeqEquiv x₁ x₂) (hy : ZpSeqEquiv y₁ y₂) :
    ZpSeqEquiv (Zp.add p hp x₁ y₁) (Zp.add p hp x₂ y₂) := by
  intro k
  apply Fin.ext
  -- Both sides reduce to ((x.digit_k).val + (y.digit_k).val + carry_k) % p
  show ((Zp.add p hp x₁ y₁).digits k).val
       = ((Zp.add p hp x₂ y₂).digits k).val
  rw [Zp.add_digit_val p hp x₁ y₁ k]
  rw [Zp.add_digit_val p hp x₂ y₂ k]
  rw [hx k, hy k]
  rw [carry_respects p x₁ y₁ x₂ y₂ hx hy k]

/-! ## §3 — Zp.neg respects ZpSeqEquiv -/

/-- ★★★★ **Zp.neg respects ZpSeqEquiv**. -/
theorem neg_respects (p : Nat) (hp : 1 < p) (x y : ZpSeq p)
    (h : ZpSeqEquiv x y) :
    ZpSeqEquiv (Zp.neg p hp x) (Zp.neg p hp y) := by
  -- Zp.neg x = Zp.add (complement x) one
  show ZpSeqEquiv (Zp.add p (Nat.lt_of_succ_lt hp)
                      (Zp.complement p (Nat.lt_of_succ_lt hp) x)
                      (ZpSeq.one p hp))
                  (Zp.add p (Nat.lt_of_succ_lt hp)
                      (Zp.complement p (Nat.lt_of_succ_lt hp) y)
                      (ZpSeq.one p hp))
  apply add_respects p (Nat.lt_of_succ_lt hp)
  · exact complement_respects p (Nat.lt_of_succ_lt hp) x y h
  · exact ZpSeqEquiv.refl (ZpSeq.one p hp)

/-! ## §4 — Helper for Zp.mul: mulRawSum / mulCarry respect equivalence -/

/-- mulRawSum at position k, upper bound u, respects equivalence in
    both arguments. -/
theorem mulRawSum_respects (p : Nat) (x₁ y₁ x₂ y₂ : ZpSeq p)
    (hx : ZpSeqEquiv x₁ x₂) (hy : ZpSeqEquiv y₁ y₂) :
    ∀ k u, Zp.mulRawSum p x₁ y₁ k u = Zp.mulRawSum p x₂ y₂ k u
  | _, 0 => rfl
  | k, u + 1 => by
    show Zp.mulRawSum p x₁ y₁ k u
            + (x₁.digits u).val * (y₁.digits (k - u)).val
        = Zp.mulRawSum p x₂ y₂ k u
            + (x₂.digits u).val * (y₂.digits (k - u)).val
    rw [mulRawSum_respects p x₁ y₁ x₂ y₂ hx hy k u]
    rw [hx u, hy (k - u)]

/-- mulRaw respects equivalence. -/
theorem mulRaw_respects (p : Nat) (x₁ y₁ x₂ y₂ : ZpSeq p)
    (hx : ZpSeqEquiv x₁ x₂) (hy : ZpSeqEquiv y₁ y₂) (k : Nat) :
    Zp.mulRaw p x₁ y₁ k = Zp.mulRaw p x₂ y₂ k := by
  show Zp.mulRawSum p x₁ y₁ k (k + 1) = Zp.mulRawSum p x₂ y₂ k (k + 1)
  exact mulRawSum_respects p x₁ y₁ x₂ y₂ hx hy k (k + 1)

/-- mulCarry respects equivalence (by induction on k). -/
theorem mulCarry_respects (p : Nat) (x₁ y₁ x₂ y₂ : ZpSeq p)
    (hx : ZpSeqEquiv x₁ x₂) (hy : ZpSeqEquiv y₁ y₂) :
    ∀ k, Zp.mulCarry p x₁ y₁ k = Zp.mulCarry p x₂ y₂ k
  | 0 => rfl
  | k + 1 => by
    rw [Zp.mulCarry_succ, Zp.mulCarry_succ]
    rw [mulRaw_respects p x₁ y₁ x₂ y₂ hx hy k]
    rw [mulCarry_respects p x₁ y₁ x₂ y₂ hx hy k]

/-! ## §5 — Zp.mul respects ZpSeqEquiv -/

/-- ★★★★ **Zp.mul respects ZpSeqEquiv** in both arguments. -/
theorem mul_respects (p : Nat) (hp : 0 < p) (x₁ y₁ x₂ y₂ : ZpSeq p)
    (hx : ZpSeqEquiv x₁ x₂) (hy : ZpSeqEquiv y₁ y₂) :
    ZpSeqEquiv (Zp.mul p hp x₁ y₁) (Zp.mul p hp x₂ y₂) := by
  intro k
  apply Fin.ext
  show ((Zp.mul p hp x₁ y₁).digits k).val
       = ((Zp.mul p hp x₂ y₂).digits k).val
  rw [Zp.mul_digit_val p hp x₁ y₁ k]
  rw [Zp.mul_digit_val p hp x₂ y₂ k]
  rw [mulRaw_respects p x₁ y₁ x₂ y₂ hx hy k]
  rw [mulCarry_respects p x₁ y₁ x₂ y₂ hx hy k]

/-! ## §6 — Capstone -/

/-- ★★★★★ **Setoid Algebra capstone**: all Zp ring operations
    respect ZpSeqEquiv.

    Bundles: (a) `add_respects` (both args), (b) `neg_respects`,
    (c) `mul_respects` (both args), (d) carry-level helpers
    (`carry_respects`, `mulCarry_respects`).

    Reading: the Setoid `(ZpSeq p, ZpSeqEquiv)` is a **ring up to
    pointwise digit equivalence**.  All algebraic identities
    (commutativity, associativity, distributivity) lift to the
    Setoid level via these respects-theorems + the existing
    digit-by-digit identities.  Funext-free, propext-free. -/
theorem setoid_algebra_capstone
    (p : Nat) (hp : 1 < p) (x₁ y₁ x₂ y₂ : ZpSeq p)
    (hx : ZpSeqEquiv x₁ x₂) (hy : ZpSeqEquiv y₁ y₂) :
    -- (a) add respects in both args
    ZpSeqEquiv (Zp.add p (Nat.lt_of_succ_lt hp) x₁ y₁)
                (Zp.add p (Nat.lt_of_succ_lt hp) x₂ y₂)
    -- (b) neg respects
    ∧ ZpSeqEquiv (Zp.neg p hp x₁) (Zp.neg p hp x₂)
    -- (c) mul respects in both args
    ∧ ZpSeqEquiv (Zp.mul p (Nat.lt_of_succ_lt hp) x₁ y₁)
                  (Zp.mul p (Nat.lt_of_succ_lt hp) x₂ y₂) := by
  refine ⟨?_, ?_, ?_⟩
  · exact add_respects p (Nat.lt_of_succ_lt hp) x₁ y₁ x₂ y₂ hx hy
  · exact neg_respects p hp x₁ x₂ hx
  · exact mul_respects p (Nat.lt_of_succ_lt hp) x₁ y₁ x₂ y₂ hx hy

end E213.Lib.Math.NumberSystems.Padic.SetoidAlgebra
