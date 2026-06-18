import E213.Lens.Number
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial

/-!
# `binom = choose` — the Pascal-recursion bridge (∅-axiom)

The repo carries the binomial coefficient under two names, defined by the **identical**
Pascal recursion: `MultSystem.binom` (the Lens-layer central-binomial / Chebyshev machinery,
via the `Lens.Number` umbrella) and `DyadicFSM.FLT.Binomial.choose` (the Lib-layer
binomial-theorem / `binomSum` / `pascal_row_sum` / `choose_symm` machinery).  They coincide,
so the two toolboxes compose.

Unblocks the **primorial bound** `∏_{p≤N} p ≤ 4ⁿ` (the keystone of Bertrand's postulate):
`odd_central_binom_le` applies the Lib-side
`choose_symm` + row-sum `pascal_row_sum` to the Lens-side central binomial `binom (2m+1) m`.
-/

namespace E213.Lib.Math.NumberTheory.BinomChooseBridge

open E213.Lens.Number.Nat213.MultSystem (binom binom_zero)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose choose_zero_right)

/-- ★ **`binom n k = choose n k`** — the two binomial defs coincide (same Pascal
    recursion `C(n+1,k+1) = C(n,k) + C(n,k+1)`, same bases).  ∅-axiom, by induction. -/
theorem binom_eq_choose : ∀ n k, binom n k = choose n k
  | n,     0     => by rw [binom_zero n, choose_zero_right n]
  | 0,     _ + 1 => rfl
  | n + 1, k + 1 => by
      show binom n k + binom n (k + 1) = choose n k + choose n (k + 1)
      rw [binom_eq_choose n k, binom_eq_choose n (k + 1)]

end E213.Lib.Math.NumberTheory.BinomChooseBridge
