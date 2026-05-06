import E213.Lib.Math.CayleyDickson.ZIArith
import E213.Lib.Math.CayleyDickson.CDDouble
import E213.Lib.Math.CayleyDickson.Cayley
import E213.Lib.Math.CayleyDickson.Sedenion
import E213.Lib.Math.CayleyDickson.Trigintaduonion
import E213.Lib.Math.CayleyDickson.Pathion

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
  ((try apply E213.Lib.Math.CayleyDickson.Pathion.ext) <;>
   (try apply E213.Lib.Math.CayleyDickson.Trigintaduonion.ext) <;>
   (try apply E213.Lib.Math.CayleyDickson.Sedenion.ext) <;>
   (try apply E213.Lib.Math.CayleyDickson.Cayley.ext) <;>
   (try apply E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz.ext) <;>
   (try apply E213.Lib.Math.CayleyDickson.ZI.ext) <;>
   simp only [
     E213.Lib.Math.CayleyDickson.Pathion.mul_re, E213.Lib.Math.CayleyDickson.Pathion.mul_im,
     E213.Lib.Math.CayleyDickson.Pathion.conj_re, E213.Lib.Math.CayleyDickson.Pathion.conj_im,
     E213.Lib.Math.CayleyDickson.Pathion.add_re, E213.Lib.Math.CayleyDickson.Pathion.add_im,
     E213.Lib.Math.CayleyDickson.Pathion.sub_re, E213.Lib.Math.CayleyDickson.Pathion.sub_im,
     E213.Lib.Math.CayleyDickson.Pathion.neg_re, E213.Lib.Math.CayleyDickson.Pathion.neg_im,
     E213.Lib.Math.CayleyDickson.Pathion.zero_re, E213.Lib.Math.CayleyDickson.Pathion.zero_im,
     E213.Lib.Math.CayleyDickson.Trigintaduonion.mul_re, E213.Lib.Math.CayleyDickson.Trigintaduonion.mul_im,
     E213.Lib.Math.CayleyDickson.Trigintaduonion.conj_re, E213.Lib.Math.CayleyDickson.Trigintaduonion.conj_im,
     E213.Lib.Math.CayleyDickson.Trigintaduonion.add_re, E213.Lib.Math.CayleyDickson.Trigintaduonion.add_im,
     E213.Lib.Math.CayleyDickson.Trigintaduonion.sub_re, E213.Lib.Math.CayleyDickson.Trigintaduonion.sub_im,
     E213.Lib.Math.CayleyDickson.Trigintaduonion.neg_re, E213.Lib.Math.CayleyDickson.Trigintaduonion.neg_im,
     E213.Lib.Math.CayleyDickson.Trigintaduonion.zero_re, E213.Lib.Math.CayleyDickson.Trigintaduonion.zero_im,
     E213.Lib.Math.CayleyDickson.Sedenion.mul_re, E213.Lib.Math.CayleyDickson.Sedenion.mul_im,
     E213.Lib.Math.CayleyDickson.Sedenion.conj_re, E213.Lib.Math.CayleyDickson.Sedenion.conj_im,
     E213.Lib.Math.CayleyDickson.Sedenion.add_re, E213.Lib.Math.CayleyDickson.Sedenion.add_im,
     E213.Lib.Math.CayleyDickson.Sedenion.sub_re, E213.Lib.Math.CayleyDickson.Sedenion.sub_im,
     E213.Lib.Math.CayleyDickson.Sedenion.neg_re, E213.Lib.Math.CayleyDickson.Sedenion.neg_im,
     E213.Lib.Math.CayleyDickson.Sedenion.zero_re, E213.Lib.Math.CayleyDickson.Sedenion.zero_im,
     E213.Lib.Math.CayleyDickson.Cayley.mul_re, E213.Lib.Math.CayleyDickson.Cayley.mul_im,
     E213.Lib.Math.CayleyDickson.Cayley.conj_re, E213.Lib.Math.CayleyDickson.Cayley.conj_im,
     E213.Lib.Math.CayleyDickson.Cayley.add_re, E213.Lib.Math.CayleyDickson.Cayley.add_im,
     E213.Lib.Math.CayleyDickson.Cayley.sub_re, E213.Lib.Math.CayleyDickson.Cayley.sub_im,
     E213.Lib.Math.CayleyDickson.Cayley.neg_re, E213.Lib.Math.CayleyDickson.Cayley.neg_im,
     E213.Lib.Math.CayleyDickson.Cayley.zero_re, E213.Lib.Math.CayleyDickson.Cayley.zero_im,
     E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz.mul_re, E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz.mul_im,
     E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz.conj_re, E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz.conj_im,
     E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz.add_re, E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz.add_im,
     E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz.sub_re, E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz.sub_im,
     E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz.neg_re, E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz.neg_im,
     E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz.zero_re, E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz.zero_im,
     E213.Lib.Math.CayleyDickson.ZI.mul_re, E213.Lib.Math.CayleyDickson.ZI.mul_im,
     E213.Lib.Math.CayleyDickson.ZI.conj_re, E213.Lib.Math.CayleyDickson.ZI.conj_im,
     E213.Lib.Math.CayleyDickson.ZI.add_re, E213.Lib.Math.CayleyDickson.ZI.add_im,
     E213.Lib.Math.CayleyDickson.ZI.sub_re, E213.Lib.Math.CayleyDickson.ZI.sub_im,
     E213.Lib.Math.CayleyDickson.ZI.neg_re, E213.Lib.Math.CayleyDickson.ZI.neg_im,
     E213.Lib.Math.CayleyDickson.ZI.I_re, E213.Lib.Math.CayleyDickson.ZI.I_im,
     E213.Lib.Math.CayleyDickson.ZI.negI_re, E213.Lib.Math.CayleyDickson.ZI.negI_im,
     E213.Lib.Math.CayleyDickson.ZI.re_zero, E213.Lib.Math.CayleyDickson.ZI.im_zero,
     Int.sub_mul, Int.mul_sub, Int.add_mul, Int.mul_add,
     Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
     Int.sub_eq_add_neg, Int.neg_mul, Int.mul_neg, Int.neg_neg
   ] <;> omega))

end E213.Tactic
