import E213.Lib.Math.Real213.CutSum

/-!
# `cutSum` — pointwise extensionality (∅-axiom)

`cutSum f g m k` only depends on `f` at indices `i ∈ [0, 2*m]` (paired
with `2*k`) and `g` at indices `2*m - i` (paired with `2*k`).  This
file proves a 213-native pointwise-extensionality lemma that lets us
substitute pointwise-equal `f`, `g` — bypassing `funext`.

Used to migrate downstream `cutSum_*`-using theorems from
function-equality (`cutSum f g = c`) to pointwise (`∀ m k, cutSum f g m k
= c m k`) without re-proving the entire arithmetic body.
-/

namespace E213.Lib.Math.Real213.CutSumPointwise

open E213.Lib.Math.Real213.CutSum (cutSum cutSumAux)

/-- `cutSumAux` is pointwise-extensional in both arguments.  ∅-axiom
    by structural recursion + `Eq.subst` (▸) only. -/
theorem cutSumAux_pointwise_eq
    (f1 g1 f2 g2 : Nat → Nat → Bool)
    (hf : ∀ m' k', f1 m' k' = f2 m' k')
    (hg : ∀ m' k', g1 m' k' = g2 m' k') (k m1Max : Nat) :
    ∀ n, cutSumAux f1 g1 k m1Max n = cutSumAux f2 g2 k m1Max n
  | 0 => by
    show (f1 0 (2*k) && g1 m1Max (2*k)) = (f2 0 (2*k) && g2 m1Max (2*k))
    rw [hf 0 (2*k), hg m1Max (2*k)]
  | n+1 => by
    show ((f1 (n+1) (2*k) && g1 (m1Max - (n+1)) (2*k))
         || cutSumAux f1 g1 k m1Max n)
       = ((f2 (n+1) (2*k) && g2 (m1Max - (n+1)) (2*k))
         || cutSumAux f2 g2 k m1Max n)
    rw [hf (n+1) (2*k), hg (m1Max - (n+1)) (2*k),
        cutSumAux_pointwise_eq f1 g1 f2 g2 hf hg k m1Max n]

/-- ★ `cutSum` is pointwise-extensional in both arguments.  ∅-axiom —
    the `funext`-free building block for pointwise migrations of
    `cutSum_*` theorems.  Use to lift `cutSum_*_at` (pointwise) results
    through compositions like `cutSum (riemannSum_left) (riemannSum_right)`. -/
theorem cutSum_pointwise_eq
    (f1 g1 f2 g2 : Nat → Nat → Bool)
    (hf : ∀ m' k', f1 m' k' = f2 m' k')
    (hg : ∀ m' k', g1 m' k' = g2 m' k') (m k : Nat) :
    cutSum f1 g1 m k = cutSum f2 g2 m k :=
  cutSumAux_pointwise_eq f1 g1 f2 g2 hf hg k (2*m) (2*m)

end E213.Lib.Math.Real213.CutSumPointwise
