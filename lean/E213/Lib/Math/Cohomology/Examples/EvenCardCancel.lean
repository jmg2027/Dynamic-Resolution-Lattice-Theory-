import E213.Lib.Math.Cohomology.Examples.XorInvolution
import E213.Lib.Math.Cohomology.Examples.ColexRoundTrip
import E213.Meta.Tactic.List213

/-!
# A third lattice node — even cardinality cancels (running the de-abstraction calculus)

`theory/meta/de_abstraction_calculus.md` opens the program: peel an abstractly-unrelated
result to ∅-axiom, and if it shares a **removal-fingerprint** with one already mapped, that
shared bottom is a lattice edge.  Here that program is *run*, not just stated.

**The peeled result.**  "A non-empty power set has an even number of elements" — i.e. an
even-cardinality set has ℤ/2-sum-of-ones `= 0` (a power set of an `n`-set has `2ⁿ = m+m`
elements with `m = 2ⁿ⁻¹`).  Abstractly this is *combinatorics / parity*, with no visible
tie to a chain-complex law.

**Its fingerprint.**  Peeled, it bottoms out in a **fixed-point-free involution** — the
halving swap `code ↦ code + m` for `code < m`, else `code − m` — fed to
`XorInvolution.xorFold_involution`.  That is the **same engine** as
`DeltaSqZero.delta_sq_zero_general` (δ²=0) and, dually, as the residue
(`object1_not_surjective`, via `bnot_self_ne`).  The swap is the high-half `not` — the
2-element distinguishing once more.

So three results unrelated at the abstract top — **the residue (Cantor), δ²=0, and
even-cardinality cancellation** — share one resolution-bottom: a fixed-point-free involution
on the one distinguishing.  This is the calculus producing a lattice edge, machine-checked.

*(Honest note: `m+m` elements being even is elementary; the point is not its depth but its
**placement** — same `xorFold_involution`, same fixed-point-free-involution bottom.  The
content is the shared generator, exhibited.)*  ∅-axiom throughout.
-/

namespace E213.Lib.Math.Cohomology.Examples.EvenCardCancel

open E213.Lib.Math.Cohomology.Examples.XorInvolution (xorFold xorFold_involution)
open E213.Lib.Math.Cohomology.Examples.ColexRoundTrip (mem_range_lt range_concat)
open E213.Tactic.List213 (nodup_append)

/-! ## Local range facts (re-derived pure, as the calculus requires) -/

private theorem lt_mem_range : ∀ {q b : Nat}, b < q → b ∈ List.range q
  | q + 1, b, hb => by
    refine (range_concat q).symm ▸ ?_
    rcases Nat.lt_or_ge b q with h | h
    · exact E213.Tactic.List213.mem_append_left (lt_mem_range h)
    · have hbq : b = q := Nat.le_antisymm (Nat.le_of_lt_succ hb) h
      exact hbq ▸ E213.Tactic.ListHelper.mem_append_singleton_right (List.range q) q

private theorem range_nodup : ∀ (m : Nat), (List.range m).Nodup
  | 0     => List.Pairwise.nil
  | m + 1 =>
    (range_concat m).symm ▸ nodup_append (range_nodup m)
      (List.Pairwise.cons (fun _ hb => nomatch hb) List.Pairwise.nil)
      (fun a ha hb => by
        have hlt : a < m := mem_range_lt a m ha
        cases hb with
        | head => exact Nat.lt_irrefl m hlt
        | tail _ h => exact nomatch h)

/-! ## The halving involution and the cancellation -/

/-- Swap the two halves of `{0..(m+m)−1}`: `code ↦ code + m` below `m`, else `code − m`.
    The high-half `not` — a fixed-point-free involution. -/
def halfSwap (m code : Nat) : Nat := if code < m then code + m else code - m

/-- ★★★ **Even cardinality cancels (third lattice node).**  The ℤ/2 sum of ones over a set
    of `m+m` elements is `0`, by the fixed-point-free halving involution — fed to the *same*
    `xorFold_involution` engine that closes `δ²=0`.  "Non-empty power set is even" lives here
    (`m+m = 2ⁿ`).  ∅-axiom. -/
theorem even_card_cancel (m : Nat) :
    xorFold (fun _ : Nat => true) (List.range (m + m)) = false := by
  refine xorFold_involution _ (halfSwap m) _ (range_nodup (m + m)) ?_ ?_ ?_ ?_
  · -- closed
    intro code hc
    have hlt : code < m + m := mem_range_lt code (m + m) hc
    by_cases h : code < m
    · have he : halfSwap m code = code + m := if_pos h
      exact he ▸ lt_mem_range (Nat.add_lt_add_right h m)
    · have he : halfSwap m code = code - m := if_neg h
      exact he ▸ lt_mem_range (Nat.lt_of_le_of_lt (Nat.sub_le code m) hlt)
  · -- fixed-point-free
    intro code hc
    have hlt : code < m + m := mem_range_lt code (m + m) hc
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmp
      · exact absurd (hm0 ▸ hlt : code < 0 + 0) (Nat.not_lt_zero code)
      · exact hmp
    by_cases h : code < m
    · have he : halfSwap m code = code + m := if_pos h
      intro heq
      have hcm : code + m = code := he.symm.trans heq
      exact absurd hcm.symm (Nat.ne_of_lt (Nat.lt_add_of_pos_right hm))
    · have he : halfSwap m code = code - m := if_neg h
      have hge : m ≤ code := Nat.le_of_not_lt h
      have hcancel : (code - m) + m = code := E213.Tactic.NatHelper.sub_add_cancel hge
      intro heq
      have hcc : code - m = code := he.symm.trans heq
      have hcm : code + m = code := (congrArg (fun z => z + m) hcc).symm.trans hcancel
      exact absurd hcm.symm (Nat.ne_of_lt (Nat.lt_add_of_pos_right hm))
  · -- involutive
    intro code hc
    have hlt : code < m + m := mem_range_lt code (m + m) hc
    by_cases h : code < m
    · have he : halfSwap m code = code + m := if_pos h
      have hnot : ¬ (code + m < m) :=
        fun hc' => Nat.lt_irrefl m (Nat.lt_of_le_of_lt (Nat.le_add_left m code) hc')
      have he2 : halfSwap m (code + m) = (code + m) - m := if_neg hnot
      have hac : (code + m) - m = code := E213.Tactic.NatHelper.add_sub_cancel_right code m
      exact (congrArg (halfSwap m) he).trans (he2.trans hac)
    · have hge : m ≤ code := Nat.le_of_not_lt h
      have he : halfSwap m code = code - m := if_neg h
      have hcancel : (code - m) + m = code := E213.Tactic.NatHelper.sub_add_cancel hge
      have hsub_lt : code - m < m :=
        Nat.lt_of_add_lt_add_right (hcancel.symm ▸ hlt : (code - m) + m < m + m)
      have he2 : halfSwap m (code - m) = (code - m) + m := if_pos hsub_lt
      exact (congrArg (halfSwap m) he).trans (he2.trans hcancel)
  · -- summand-preserving (constant function)
    intro _ _; rfl

end E213.Lib.Math.Cohomology.Examples.EvenCardCancel
