import E213.Math.Cohomology.Universal.Prop51
import E213.Math.Cohomology.Cup.Leibniz

/-!
# Leibniz universal — HONEST NEGATIVE finding

User: hard deferred items 될때까지 고고.  Attempted to lift
Cup Leibniz `δ(α ⌣ β) = δα ⌣ β XOR α ⌣ δβ` to Prop-level
∀ α β : Cochain 5 1 via pattern enumeration (32 × 32 × 10
= 10240 cases).

**Decide proved Leibniz universal is FALSE in current cup
implementation**.

## Diagnosis

Our `cup n k l : Cochain n k × Cochain n l → Cochain n (k+l)`
splits a (k+l)-subset τ at position k:
  front = τ.take k  (k elements, no overlap)
  back  = τ.drop k  (l elements, no overlap)

Standard simplicial cup product (Alexander-Whitney) splits a
(k+l)-simplex with overlap at the shared vertex:
  front = v_0..v_k  (k+1 vertices, a k-simplex)
  back  = v_k..v_{k+l}  (l+1 vertices, an l-simplex)

Our convention has off-by-one: we map "k-subsets" to Bool, but
standard k-cochain is on k-simplex (k+1 vertices).  So our
`Cochain n k` ≃ standard C^{k-1}.

Cup product correct fix would be:
  cup' (a b : Nat) : Cochain n a × Cochain n b → Cochain n (a+b-1)
with `(α ⌣ β)(τ) = α(τ.take a) · β(τ.drop (a-1))` (overlap at
position a-1).

## What this means

  - 4 concrete Leibniz cases in `CupLeibniz.lean` STILL hold
    (they were specific cases where simplified cup happens
     to agree with Leibniz)
  - Universal Leibniz FAILS in current implementation
  - Fix requires re-implementing cup with correct overlap

## Why we keep the current cup

The current cup is still a meaningful XOR-bilinear operation
on cochains.  It's just not the standard Alexander-Whitney
cup product.  Renaming it to `xor_cup` or fixing the convention
is future work.

## Honest negative formalization

This file documents the finding — Leibniz fails universally
in our setup — as a 0-axiom theorem.
-/

namespace E213.Math.Cohomology.LeibnizFinding

open E213.Physics.Simplex.Counts (binom)
open E213.Math.Cohomology.Universal.Prop51 (pattern)
open E213.Math.Cohomology.Cup.Core (cup)
open E213.Math.Cohomology.Delta.Core (delta)

/-- ★ Honest negative: there EXISTS (a, b) ∈ {true, false}^5 ×
    {true, false}^5 and i ∈ Fin (binom 5 3) such that Leibniz
    fails for our cup implementation.  Specific witness via
    decide search. -/
theorem leibniz_universal_false :
    ¬ (∀ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool,
         ∀ i : Fin (binom 5 3),
           delta (cup 5 1 1 (pattern a0 a1 a2 a3 a4)
                             (pattern b0 b1 b2 b3 b4)) i
             = xor (cup 5 2 1 (delta (pattern a0 a1 a2 a3 a4))
                               (pattern b0 b1 b2 b3 b4) i)
                   (cup 5 1 2 (pattern a0 a1 a2 a3 a4)
                               (delta (pattern b0 b1 b2 b3 b4)) i)) := by
  decide

end E213.Math.Cohomology.LeibnizFinding
