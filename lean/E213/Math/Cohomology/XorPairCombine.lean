import E213.Math.Cohomology.Cochain.Core
import E213.Math.Cohomology.CupAW.BasisLeibniz

/-!
# XOR pair combine — structural proof via List.foldr induction

Pure-Bool combinatorial fact:

  XOR_k (a_k ⊕ b_k) = (XOR_k a_k) ⊕ (XOR_k b_k)

over a list of (Bool × Bool) pairs.  Proved by induction on the
list, then specialised to the 10-pair tuple form needed by the
(5, 1, 2) Leibniz algebraic lift.

This is the residual combinatorial step after bilinearity reduces
(5, 1, 2) Leibniz to a pure 20-Bool XOR rearrangement.
-/

namespace E213.Math.Cohomology.XorPairCombine

open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.CupAW.BasisLeibniz (basis)


/-- Generic structural lemma: foldr-XOR of pair sums = pair of foldr-XORs.
    Generalised over starting accumulators a, b for induction. -/
theorem foldr_xor_pair (xs : List (Bool × Bool)) (a b : Bool) :
    xs.foldr (fun p acc => xor (xor p.1 p.2) acc) (xor a b)
      = xor (xs.foldr (fun p acc => xor p.1 acc) a)
            (xs.foldr (fun p acc => xor p.2 acc) b) := by
  induction xs generalizing a b with
  | nil => rfl
  | cons hd tl ih =>
    show xor (xor hd.1 hd.2) (tl.foldr _ (xor a b))
       = xor (xor hd.1 (tl.foldr _ a)) (xor hd.2 (tl.foldr _ b))
    rw [ih a b]
    cases hd.1 <;> cases hd.2 <;>
      cases (tl.foldr (fun p acc => xor p.1 acc) a) <;>
      cases (tl.foldr (fun p acc => xor p.2 acc) b) <;> rfl

/-- Specialised: 10-pair XOR rearrangement (matches simp-expanded
    form from the (5, 1, 2) Leibniz lift). -/
theorem combine_10 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
                    b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) :
    xor (xor a0 b0) (xor (xor a1 b1) (xor (xor a2 b2) (xor (xor a3 b3)
      (xor (xor a4 b4) (xor (xor a5 b5) (xor (xor a6 b6)
        (xor (xor a7 b7) (xor (xor a8 b8) (xor a9 b9)))))))))
      = xor (xor a0 (xor a1 (xor a2 (xor a3 (xor a4 (xor a5
              (xor a6 (xor a7 (xor a8 a9)))))))))
            (xor b0 (xor b1 (xor b2 (xor b3 (xor b4 (xor b5
              (xor b6 (xor b7 (xor b8 b9)))))))))  := by
  have h := foldr_xor_pair
    [(a0, b0), (a1, b1), (a2, b2), (a3, b3), (a4, b4),
     (a5, b5), (a6, b6), (a7, b7), (a8, b8), (a9, b9)] false false
  simp only [List.foldr, Bool.xor_false] at h
  exact h

/-- Specialised: 5-pair XOR rearrangement (for the (5,2,1) lift
    where β : Cochain 5 1 has 5 basis components). -/
theorem combine_5 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool) :
    xor (xor a0 b0) (xor (xor a1 b1) (xor (xor a2 b2)
      (xor (xor a3 b3) (xor a4 b4))))
      = xor (xor a0 (xor a1 (xor a2 (xor a3 a4))))
            (xor b0 (xor b1 (xor b2 (xor b3 b4)))) := by
  have h := foldr_xor_pair
    [(a0, b0), (a1, b1), (a2, b2), (a3, b3), (a4, b4)] false false
  simp only [List.foldr, Bool.xor_false] at h
  exact h

end E213.Math.Cohomology.XorPairCombine
