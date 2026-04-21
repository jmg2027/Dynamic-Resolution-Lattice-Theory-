import E213.Research.ZIArith
import E213.Research.CDDouble
import E213.Research.Cayley

/-!
# Tactic: `hurwitz_ring`

Closes polynomial identities in Cayley–Dickson algebras
(ZI, Lipschitz, Cayley, Sedenion — structures built from
componentwise-Int via iterated CD doubling).

## Mechanism

1. **Descend**.  Applies `Lipschitz.ext` (if goal is a
   Lipschitz equality), then `ZI.ext`, splitting a single
   Lipschitz `=` into 4 Int `=` goals (or 2 for ZI `=`, or
   1 for raw Int `=`).

2. **Unfold projections**.  `simp only` with the complete
   `.re` / `.im` projection lemmas for all algebraic
   operations (`mul`, `conj`, `add`, `sub`, `neg`, `0`).
   Each side becomes a pure Int polynomial.

3. **AC-normalise and close**.  The same ring-AC simp set as
   `quad_norm` (`mul_add/add_mul/mul_comm/mul_assoc/…`)
   reduces to canonical monomials; `omega` closes linear
   atom-level equations.

## Coverage

- Lipschitz `mul_assoc` (12 Int vars, ≥ 64 monomials per side).
- Lipschitz `normSq_mul` / Hurwitz identity (8 Int vars).
- Any ZI-component polynomial identity of similar size.

## Limitations

- Cayley level (16 Int vars) may exceed omega's practical
  atom count; extension via recursive descent needed.
- Purely polynomial; no division, no transcendentals.
-/

namespace E213.Tactic

scoped macro "hurwitz_ring" : tactic => `(tactic|
  ((try apply E213.Research.Cayley.ext) <;>
   (try apply E213.Research.Lipschitz.ext) <;>
   (try apply E213.Research.ZI.ext) <;>
   simp only [
     E213.Research.Cayley.mul_re, E213.Research.Cayley.mul_im,
     E213.Research.Cayley.conj_re, E213.Research.Cayley.conj_im,
     E213.Research.Cayley.add_re, E213.Research.Cayley.add_im,
     E213.Research.Cayley.sub_re, E213.Research.Cayley.sub_im,
     E213.Research.Cayley.neg_re, E213.Research.Cayley.neg_im,
     E213.Research.Cayley.zero_re, E213.Research.Cayley.zero_im,
     E213.Research.Lipschitz.mul_re, E213.Research.Lipschitz.mul_im,
     E213.Research.Lipschitz.conj_re, E213.Research.Lipschitz.conj_im,
     E213.Research.Lipschitz.add_re, E213.Research.Lipschitz.add_im,
     E213.Research.Lipschitz.sub_re, E213.Research.Lipschitz.sub_im,
     E213.Research.Lipschitz.neg_re, E213.Research.Lipschitz.neg_im,
     E213.Research.Lipschitz.zero_re, E213.Research.Lipschitz.zero_im,
     E213.Research.ZI.mul_re, E213.Research.ZI.mul_im,
     E213.Research.ZI.conj_re, E213.Research.ZI.conj_im,
     E213.Research.ZI.add_re, E213.Research.ZI.add_im,
     E213.Research.ZI.sub_re, E213.Research.ZI.sub_im,
     E213.Research.ZI.neg_re, E213.Research.ZI.neg_im,
     E213.Research.ZI.I_re, E213.Research.ZI.I_im,
     E213.Research.ZI.negI_re, E213.Research.ZI.negI_im,
     E213.Research.ZI.re_zero, E213.Research.ZI.im_zero,
     Int.sub_mul, Int.mul_sub, Int.add_mul, Int.mul_add,
     Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
     Int.sub_eq_add_neg, Int.neg_mul, Int.mul_neg, Int.neg_neg
   ] <;> omega))

end E213.Tactic
