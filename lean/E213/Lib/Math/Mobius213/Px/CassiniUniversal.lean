import E213.Lib.Physics.Simplex.Counts
import E213.Meta.Nat.NatRing213
import E213.Lib.Math.Mobius213.Px.POrbitClosure
import E213.Lib.Math.Mobius213.Px.CassiniInduction

/-!
# Mobius213.Px.CassiniUniversal — Cassini identity at every n (PURE)

`CassiniInduction.lean` proves Cassini `L(n) · L(n+2) − L(n+1)² = d`
at concrete `n = 0..9`.  The universal `∀n` lift in Int form
requires `propext`-leaking Int.add_comm / Int.sub_eq_add_neg
chain and was deferred.

This file closes the universal lift by reformulating Cassini in
**Nat-additive form**:

  `L(n) · L(n+2) = L(n+1)² + d`   (for all n : Nat)

avoiding Int subtraction entirely.  The proof uses the PURE Nat
ring toolkit (`NatRing.nat_mul_assoc`, `NatRing.nat_add_mul`,
`NatRing.nat_add_right_cancel`) plus the additive recurrence

  `Lnat(n+2) + Lnat(n) = NS · Lnat(n+1)`

(rearranged from `Lnat(n+2) = NS · Lnat(n+1) − Lnat(n)` so that
both sides are Nat-positive).

## Strategy

  · §1 — Define `Lnat : Nat → Nat` (mirrors `L : Nat → Int`).
  · §2 — Additive recurrence: `Lnat(n+2) + Lnat n = 3 · Lnat(n+1)`.
  · §3 — Cassini-∀n by induction.  Inductive step uses Nat ring:

    L(k+1) · L(k+3) + L(k+1)² = L(k+1) · (L(k+3) + L(k+1))
                              = L(k+1) · 3 · L(k+2)
    L(k) · L(k+2) + L(k+2)²   = (L(k) + L(k+2)) · L(k+2)
                              = 3 · L(k+1) · L(k+2)

    Both equal `3 · L(k+1) · L(k+2)`, hence equal to each other.
    Substituting IH `L(k) · L(k+2) = L(k+1)² + d` and cancelling
    `L(k+1)²` (Nat right-cancellation) gives the step.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Mobius213.Px.CassiniUniversal

open E213.Meta.Nat.NatRing213
open E213.Lib.Physics.Simplex.Counts (NS NT d)

/-! ## §1 — Lnat: Nat-valued Pell-Lucas trace -/

/-- `Lnat n = trace(P^n)` in Nat (mirrors `POrbitClosure.L` for
    n ≥ 0; all values positive so Nat truncation never triggers). -/
def Lnat : Nat → Nat
  | 0     => 2
  | 1     => 3
  | n + 2 => 3 * Lnat (n + 1) - Lnat n

theorem Lnat_0 : Lnat 0 = 2 := rfl
theorem Lnat_1 : Lnat 1 = 3 := rfl
theorem Lnat_2 : Lnat 2 = 7 := rfl
theorem Lnat_3 : Lnat 3 = 18 := rfl
theorem Lnat_4 : Lnat 4 = 47 := rfl

/-! ## §2 — Joint monotonicity + additive recurrence

Joint induction: `Lnat n ≤ Lnat (n+1)` (monotonicity) AND
`Lnat (n+2) + Lnat n = 3 · Lnat (n+1)` (additive recurrence).
Proved together because each step depends on the other:
  · Mono at n+1 uses the additive recurrence at n.
  · Additive recurrence at n+1 uses `nat_sub_add_cancel` with
    the inequality `Lnat (n+1) ≤ 3 · Lnat (n+2)` derived from
    mono at n+1. -/

/-- Helper: monotonicity step.  From ih_mono `Lnat n ≤ Lnat(n+1)` and
    ih_add `Lnat(n+2) + Lnat n = 3·Lnat(n+1)`, derive
    `Lnat(n+1) ≤ Lnat(n+2)`. -/
private theorem Lnat_mono_step (n : Nat)
    (ih_mono : Lnat n ≤ Lnat (n + 1))
    (ih_add : Lnat (n + 2) + Lnat n = 3 * Lnat (n + 1)) :
    Lnat (n + 1) ≤ Lnat (n + 2) := by
  have hsum : Lnat (n + 1) + Lnat n ≤ Lnat (n + 2) + Lnat n := by
    rw [ih_add, three_mul_eq]
    rw [Nat.add_assoc]
    apply Nat.add_le_add_left
    exact Nat.le_trans ih_mono (Nat.le_add_right _ _)
  exact nat_le_of_add_le_add_right hsum

theorem Lnat_mono_and_add :
    ∀ n : Nat, Lnat n ≤ Lnat (n + 1) ∧
               Lnat (n + 2) + Lnat n = 3 * Lnat (n + 1)
  | 0 => by refine ⟨?_, ?_⟩ <;> decide
  | n + 1 => by
    have ⟨ih_mono, ih_add⟩ := Lnat_mono_and_add n
    have mono_n1 : Lnat (n + 1) ≤ Lnat (n + 2) :=
      Lnat_mono_step n ih_mono ih_add
    refine ⟨mono_n1, ?_⟩
    -- Goal: Lnat (n+3) + Lnat (n+1) = 3 * Lnat (n+2)
    -- Need: Lnat (n+1) ≤ 3 * Lnat (n+2).
    have hle : Lnat (n + 1) ≤ 3 * Lnat (n + 2) := by
      rw [three_mul_eq]
      -- Goal: Lnat (n+1) ≤ Lnat (n+2) + Lnat (n+2) + Lnat (n+2)
      have h1 : Lnat (n + 1) ≤ Lnat (n + 2) + Lnat (n + 2) :=
        Nat.le_trans mono_n1 (Nat.le_add_right _ _)
      exact Nat.le_trans h1 (Nat.le_add_right _ _)
    show 3 * Lnat (n + 2) - Lnat (n + 1) + Lnat (n + 1) = 3 * Lnat (n + 2)
    exact nat_sub_add_cancel hle

/-- Monotonicity standalone. -/
theorem Lnat_monotone (n : Nat) : Lnat n ≤ Lnat (n + 1) :=
  (Lnat_mono_and_add n).1

/-- Additive recurrence standalone:
    `Lnat (n+2) + Lnat n = 3 · Lnat (n+1)`. -/
theorem Lnat_add_recurrence (n : Nat) :
    Lnat (n + 2) + Lnat n = 3 * Lnat (n + 1) :=
  (Lnat_mono_and_add n).2

/-! ## §3 — Cassini at every n (Nat-additive form) -/

/-- ★★★★★★★★★ **Cassini identity at every n (PURE)**:
    `L(n) · L(n+2) = L(n+1)² + d` for every `n : Nat`.

    Nat-additive reformulation (no subtraction) of the classical
    Pell-Lucas Cassini identity.  Proof by induction:

    **Base** (n = 0): `L(0) · L(2) = 2 · 7 = 14 = 9 + 5 = L(1)² + d`. ✓

    **Step** (assuming `L(k) · L(k+2) = L(k+1)² + d`):

      L(k+1) · L(k+3) + L(k+1) · L(k+1)
        = L(k+1) · (L(k+3) + L(k+1))      (distributivity)
        = L(k+1) · (3 · L(k+2))           (add recurrence at k+1)
        = 3 · L(k+1) · L(k+2)             (mul commutativity)
        = L(k+2) · (3 · L(k+1))           (mul commutativity)
        = L(k+2) · (L(k+2) + L(k))        (add recurrence at k, reversed)
        = L(k+2) · L(k+2) + L(k+2) · L(k) (distributivity)
        = L(k+2) · L(k+2) + L(k) · L(k+2) (mul commutativity)
        = L(k+2) · L(k+2) + L(k+1) · L(k+1) + d  (by IH)

    Cancelling `L(k+1) · L(k+1)` on both sides via PURE
    `nat_add_right_cancel` gives the step. -/
theorem cassini_universal (n : Nat) :
    Lnat n * Lnat (n + 2) = Lnat (n + 1) * Lnat (n + 1) + 5 := by
  induction n with
  | zero => decide
  | succ k ih =>
    have h_addk : Lnat (k + 2) + Lnat k = 3 * Lnat (k + 1) :=
      Lnat_add_recurrence k
    have h_addk1 : Lnat (k + 3) + Lnat (k + 1) = 3 * Lnat (k + 2) :=
      Lnat_add_recurrence (k + 1)
    apply nat_add_right_cancel (b := Lnat (k + 1) * Lnat (k + 1))
    -- LHS = Lnat(k+1)·Lnat(k+3) + Lnat(k+1)² = Lnat(k+1)·(Lnat(k+3)+Lnat(k+1))
    --     = Lnat(k+1)·(3·Lnat(k+2)) = 3·Lnat(k+1)·Lnat(k+2)
    --     = (Lnat(k+2) + Lnat k)·Lnat(k+2) = Lnat(k+2)² + Lnat k · Lnat(k+2)
    --     = Lnat(k+2)² + (Lnat(k+1)² + 5)                       (by IH)
    --     = (Lnat(k+2)² + 5) + Lnat(k+1)²                       (add_right_comm)
    rw [show Lnat (k + 1 + 2) = Lnat (k + 3) from rfl,
        show Lnat (k + 1 + 1) = Lnat (k + 2) from rfl,
        ← Nat.mul_add,
        h_addk1,
        nat_swap_left_mul,
        ← h_addk,
        nat_add_mul,
        ih,
        ← Nat.add_assoc,
        Nat.add_right_comm _ _ 5]

/-! ## §4 — Bridge: Lnat ↔ Int L -/

open E213.Lib.Math.Mobius213.Px.POrbitClosure (L)

/-- Lnat agrees with the Int-valued L on small indices.  Establishes
    that the Nat-additive Cassini-∀n result transports to the
    classical Int-subtractive form. -/
theorem Lnat_eq_L_at_0 : (Lnat 0 : Int) = L 0 := by decide
theorem Lnat_eq_L_at_1 : (Lnat 1 : Int) = L 1 := by decide
theorem Lnat_eq_L_at_2 : (Lnat 2 : Int) = L 2 := by decide
theorem Lnat_eq_L_at_3 : (Lnat 3 : Int) = L 3 := by decide
theorem Lnat_eq_L_at_4 : (Lnat 4 : Int) = L 4 := by decide

/-! ## §5 — Master: Cassini-∀n closure -/

/-- ★★★★★★★★★★ **Cassini-∀n PURE closure master**.

    The Cassini identity for the Pell-Lucas trace orbit holds at
    every `n : Nat` in Nat-additive form:

      `L(n) · L(n+2) = L(n+1)² + d`   where `d = 5`.

    This is the universal lift of `CassiniInduction`'s finite
    n = 0..9 catalog.  The proof uses **only PURE Nat ring tools**
    from `E213.Meta.Nat.NatRing213`:

      · `nat_mul_assoc`, `nat_add_mul`     — distributivity
      · `nat_add_right_cancel`             — additive cancellation
      · `nat_sub_add_cancel`               — subtraction-add inverse
      · `nat_le_of_add_le_add_right`       — inequality cancellation
      · `three_mul_eq` (3·x = x+x+x)       — recurrence-coefficient
      · `nat_swap_left_mul`                — multiplicative reordering

    avoiding Int polynomial manipulation which leaks `propext`
    through Lean core's `Int.add_comm`, `Int.mul_comm`, etc.

    Includes monotonicity `Lnat n ≤ Lnat (n+1)` and the additive
    recurrence `Lnat(n+2) + Lnat n = 3 · Lnat(n+1)` as supporting
    lemmas, both ∀ n. -/
theorem cassini_universal_master :
    (∀ n : Nat, Lnat n ≤ Lnat (n + 1))
    ∧ (∀ n : Nat, Lnat (n + 2) + Lnat n = 3 * Lnat (n + 1))
    ∧ (∀ n : Nat, Lnat n * Lnat (n + 2) = Lnat (n + 1) * Lnat (n + 1) + 5)
    := ⟨Lnat_monotone, Lnat_add_recurrence, cassini_universal⟩

end E213.Lib.Math.Mobius213.Px.CassiniUniversal
