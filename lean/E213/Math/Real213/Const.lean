import E213.Math.Real213.Equiv

/-!
# Research.Real213Const: constant embedding of Real213 (D3-A follow-up)

Next step after D3-A in `D3_real213_native_R.md` — embedding of
Raw → Real213 as a constant Cauchy sequence.

## Definition

`Real213.const r` = Cauchy sequence outputting r at every index +
trivial modulus (N = 0).

## Significance

- Elements of Raw *directly embed* into Real213 (each Raw becomes an
  ℝ-element as its own constant).
- `const r ~ const r'` ↔ orderProj m k agrees at *every* (m, k) —
  ratio-equivalence of the (Nat × Nat) view.
- This is the *minimal* element constructor for Real213.
-/

namespace E213.Math.Real213.Const

open E213.Firmware E213.Hypervisor
open E213.Research.HasModulusNS
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy

/-- Constant sequence at single Raw r. -/
def constSeq (r : Raw) : Nat → Raw := fun _ => r

/-- Trivial modulus for constant sequence — N = 0, cauchy_at trivial. -/
def constModulus (r : Raw) : HasModulus (constSeq r) where
  N := fun _ _ => 0
  cauchy_at := fun _ _ _ _ _ _ _ => rfl

/-- Constant embedding of Real213: Raw → Real213. -/
def const (r : Raw) : Real213 :=
  ⟨constSeq r, constModulus r⟩

/-- Equivalence of constant Real213 ↔ orderProj agrees at every (m, k). -/
theorem const_equiv_iff (r r' : Raw) :
    Real213.equiv (const r) (const r')
      ↔ ∀ m k, k ≥ 1 →
          orderProj m k (abLens.view r) = orderProj m k (abLens.view r') := by
  refine ⟨?_, ?_⟩
  · intro h m k hk
    obtain ⟨N, hN⟩ := h m k hk
    exact hN N (Nat.le_refl N)
  · intro h m k hk
    exact ⟨0, fun _ _ => h m k hk⟩

/-- const is equivalent to itself (trivial — special case of equiv_refl). -/
theorem const_equiv_self (r : Raw) : Real213.equiv (const r) (const r) :=
  equiv_refl (const r)

end E213.Math.Real213.Const
