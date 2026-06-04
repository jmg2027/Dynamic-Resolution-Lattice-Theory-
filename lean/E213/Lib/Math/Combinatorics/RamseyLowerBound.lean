import E213.Lib.Math.Combinatorics.CountExistence

/-!
# Erdős' Ramsey lower bound — the concrete COUNT lift, and its "why"

`CountExistence.erdos_schema` is the probabilistic-method *instruction*: `t`
bad events, each on ≤ `c` of the `2ⁿ` colourings, with `t·c < 2ⁿ`, force a
colouring dodging all.  Making the *named* Erdős theorem `R(k,k) > 2^{k/2}`
concrete needs the per-event count `c = 2·2^{E−C(k,2)}`.  This file builds the
**reason** that count holds — the factorization — and reads off the per-event
count from it.

## Why the per-event count is `2 · 2^{E−m}`

A "monochromatic on `S`" event constrains only the `m = C(k,2)` edges *inside*
`S`; the other `E−m` edges are free.  Two independent facts compose:

  · **free edges double** — `count_factor`: a predicate blind to the `r`
    prepended bits counts `2^r ·` (its count on the suffix).  Each free edge is
    one distinguishing, and a distinguishing doubles the residue.  *This is the
    "why": existence-counting factors because independent distinguishings
    multiply.*
  · **shared colour, twice** — `BoolEnum.bcount_const`: the constrained block is
    constant in exactly `2` ways (all-`false`, all-`true`).

Hence per-event `= 2^r · 2 = 2 · 2^{E−m}` (`mono_event_count`), with
`E = r + m`, the `m` constrained edges placed as the suffix (an arbitrary
`S` reduces to this by relabelling edge positions — a count-invariant
permutation; that relabelling + the `t = C(N,k)` event enumeration are the
remaining mechanical rung).
-/

namespace E213.Lib.Math.Combinatorics.RamseyLowerBound

open E213.Lib.Math.Combinatorics.BoolEnum
open E213.Lib.Math.Combinatorics.CountExistence

/-- ★ **The factorization — the "why" of the per-event count.**  A predicate
    that reads only the length-`m` *suffix* is blind to the `r` prepended bits;
    each prepended bit is a free distinguishing that **doubles** the count, so
    the count factors as `2^r · (count on the suffix block)`. -/
theorem count_factor (p : List Bool → Bool) (m : Nat) :
    ∀ r, bcount (fun l => p (l.drop r)) (allBoolLists (r + m))
          = 2 ^ r * bcount p (allBoolLists m)
  | 0 => by
      rw [Nat.zero_add, Nat.pow_zero, Nat.one_mul]
      exact bcount_congr (fun _ => rfl) (allBoolLists m)
  | r + 1 => by
      rw [Nat.succ_add, bcount_allBoolLists_succ]
      have hcong : ∀ (b : Bool),
          bcount (fun x => (fun l => p (l.drop (r + 1))) (b :: x)) (allBoolLists (r + m))
            = 2 ^ r * bcount p (allBoolLists m) := fun b => by
        rw [bcount_congr (p := fun x => (fun l => p (l.drop (r + 1))) (b :: x))
              (q := fun l => p (l.drop r)) (fun _ => rfl) (allBoolLists (r + m))]
        exact count_factor p m r
      rw [hcong false, hcong true, Nat.pow_succ, Nat.mul_two,
          E213.Tactic.NatHelper.add_mul]

/-- ★ **The per-event count.**  A monochromatic constraint on a size-`(m+1)`
    block of the `r + (m+1)` edges holds on exactly `2^(r+1) = 2 · 2^r`
    colourings — `2` shared colours (`bcount_const`) times `2^r` free edges
    (`count_factor`).  This is Erdős' `2 · 2^{E − C(k,2)}` with `E = r + C(k,2)`
    and `m + 1 = C(k,2)`. -/
theorem mono_event_count (m r : Nat) :
    bcount (fun l => isConst (l.drop r)) (allBoolLists (r + (m + 1)))
      = 2 ^ (r + 1) := by
  rw [count_factor isConst (m + 1) r, bcount_const m, Nat.pow_succ]

end E213.Lib.Math.Combinatorics.RamseyLowerBound
