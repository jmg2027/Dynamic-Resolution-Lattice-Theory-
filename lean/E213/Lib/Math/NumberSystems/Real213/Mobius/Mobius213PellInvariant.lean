import E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213SternBrocot
import E213.Meta.Tactic.NatHelper

/-!
# Mobius213PellInvariant — Pell unit invariant on Pseq orbits

The two Möbius P-orbits (`Pseq seedZero`, `Pseq seedInf`) carry
the symplectic cross-product invariant of the matrix
`P = [[2,1],[1,1]]`: the "det = 1" reading lifted to consecutive
convergents.

For `(a, b) := Pseq seedZero n`, the identity

    `a² + 1 = a·b + b²`

holds for every `n` — the Pell unit relation in its Nat form.
Equivalently, viewed across both orbits via `Pseq_seedInf_components`,

    `(Pseq seedZero n).1 · (Pseq seedInf n).2 + 1
      = (Pseq seedZero n).2 · (Pseq seedInf n).1`

— the cross-product `m · k' - m' · k = -1` of the Pell pair
`((a, b), (a+b, a))`.

The Int version of this invariant lives in `Lib/Math/Algebra/Mobius213.lean`
(`mobius_213_pell_unit_invariant_forall`); this file establishes
the corresponding Nat-side identity directly on the Pseq orbits,
without coercion to Int.  All declarations PURE (∅-axiom).

## Significance

This invariant is the "det = 1 algebraic content of P" seen at the
Stern-Brocot mediant level: every Farey-neighbor pair on the
P-orbit chain has cross-product `±1`, exactly the unit of the
quadratic ring `ℤ[φ²]` whose discriminant is `5 = NS + NT`.
The Pell unit value `-1` reads in 213 terms as `NT - NS = 2 - 3`.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213PellInvariant

open E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213Equiv
  (Pstep Pseq seedZero seedInf)
open E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213SternBrocot
  (Pseq_seedInf_components)

/-! ## §1 — Inductive step (pure Nat arithmetic) -/

/-- ★ **The Pell/Cassini norm step** — the one shared atom.  The Möbius P-step
    `(a, b) ↦ (2a+b, a+b)` preserves the Cassini-variant unit norm
    `a² + 1 = a·b + b²`.  Pure Nat arithmetic, no IH-dependent polynomial
    expansion, ∅-axiom.

    This is the single inductive engine behind **both** Pell/Fibonacci invariants:
    the `Pseq seedZero` orbit (§2 below, `Pseq_seedZero_pell_invariant`) and the
    `fib`-indexed convergents `(fib(2n+2), fib(2n+1))`
    (`FibCassiniNat.fib_cassini_norm`) run the same recurrence, so each is just
    "induct + apply this step" over its own couplings. -/
theorem pellNormStep (a b : Nat) (h : a*a + 1 = a*b + b*b) :
    (2*a+b)*(2*a+b) + 1 = (2*a+b)*(a+b) + (a+b)*(a+b) := by
  have e : 2*a + b = a + (a+b) := by rw [Nat.two_mul, Nat.add_assoc]
  rw [e]
  rw [Nat.mul_add (a + (a+b)) a (a+b)]
  rw [Nat.add_right_comm ((a+(a+b))*a) ((a+(a+b))*(a+b)) 1]
  rw [Nat.add_comm ((a + (a+b))*a + 1) ((a + (a+b))*(a+b))]
  apply congrArg ((a + (a+b))*(a+b) + ·)
  rw [E213.Tactic.NatHelper.add_mul a (a+b) a,
      E213.Tactic.NatHelper.add_mul a b a,
      E213.Tactic.NatHelper.add_mul a b (a+b)]
  rw [Nat.mul_add a a b, Nat.mul_add b a b]
  rw [Nat.add_assoc (a*a) (a*a + b*a) 1]
  rw [Nat.add_assoc (a*a) (a*b) (b*a + b*b)]
  apply congrArg (a*a + ·)
  rw [Nat.add_right_comm (a*a) (b*a) 1]
  rw [h]
  rw [Nat.add_assoc (a*b) (b*b) (b*a)]
  apply congrArg (a*b + ·)
  exact Nat.add_comm _ _

/-! ## §2 — Pell unit invariant on Pseq seedZero -/

/-- ★★★★★ **Pell unit identity on the seedZero orbit**: for every
    depth `n`, `(Pseq seedZero n).1² + 1 = (Pseq seedZero n).1 ·
    (Pseq seedZero n).2 + (Pseq seedZero n).2²`.  Verified
    layer-wise:
      n=0: `(0, 1)` — `0 + 1 = 0 + 1` ✓
      n=1: `(1, 1)` — `1 + 1 = 1 + 1` ✓
      n=2: `(3, 2)` — `9 + 1 = 6 + 4` ✓
      n=3: `(8, 5)` — `64 + 1 = 40 + 25` ✓
    The Pell unit identity in Nat form. -/
theorem Pseq_seedZero_pell_invariant (n : Nat) :
    (Pseq seedZero n).1 * (Pseq seedZero n).1 + 1
      = (Pseq seedZero n).1 * (Pseq seedZero n).2
        + (Pseq seedZero n).2 * (Pseq seedZero n).2 := by
  induction n with
  | zero => decide
  | succ k ih =>
    exact pellNormStep _ _ ih

/-! ## §3 — Cross-orbit form (the symplectic cross-product) -/

/-- ★★★★★★ **Cross-orbit Pell unit invariant**: the symplectic
    cross-product of the two P-orbits at the same depth.

      `(Pseq seedZero n).1 · (Pseq seedInf n).2 + 1
        = (Pseq seedZero n).2 · (Pseq seedInf n).1`

    Verified layer-wise:
      n=0: `(0,1)`, `(1,0)` — `0·0 + 1 = 1·1` ✓
      n=1: `(1,1)`, `(2,1)` — `1·1 + 1 = 1·2` ✓
      n=2: `(3,2)`, `(5,3)` — `3·3 + 1 = 2·5` ✓
      n=3: `(8,5)`, `(13,8)` — `8·8 + 1 = 5·13` ✓

    Follows from `Pseq_seedZero_pell_invariant` plus the cross-
    orbit relation `Pseq_seedInf_components`: substitute
    `(Pseq seedInf n).1 = a + b` and `(Pseq seedInf n).2 = a`. -/
theorem Pseq_cross_pell_invariant (n : Nat) :
    (Pseq seedZero n).1 * (Pseq seedInf n).2 + 1
      = (Pseq seedZero n).2 * (Pseq seedInf n).1 := by
  obtain ⟨hc1, hc2⟩ := Pseq_seedInf_components n
  rw [hc2, hc1]
  rw [Nat.mul_add (Pseq seedZero n).2 (Pseq seedZero n).1 (Pseq seedZero n).2]
  rw [Nat.mul_comm (Pseq seedZero n).2 (Pseq seedZero n).1]
  exact Pseq_seedZero_pell_invariant n

end E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213PellInvariant
