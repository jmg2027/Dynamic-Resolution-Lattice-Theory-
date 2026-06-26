import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum
import E213.Meta.Nat.NatRing213

/-!
# The convolution-associativity index identity (∅-axiom, Phase A3 / route b)

The double-sum reindex behind `conv_assoc` needs

  `(k + p − (l + i) % p) % p = ((k + p − i) % p + p − l) % p`   (`conv_assoc_index`),

i.e. `k − (i+l) ≡ (k−i) − l (mod p)` — modular subtraction is associative.  Both sides reduce to
`(k + (p−i) + (p−l)) % p`; the crux is the "negation is additive" lemma
`((p−i)+(p−l)) % p = (p − (i+l)%p) % p` (`neg_add_mod`), proved via `(p−i)+(p−l) = 2p−(i+l)`
(`sub_sub_two`) and `(2p−s)%p = (p − s%p)%p` (`two_sub_mod`).  Pure `ℕ` arithmetic.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvAssocIndex

open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum (add_p_mod)
open E213.Meta.Nat.AddMod213 (add_mod mod_add_mod)
open E213.Meta.Nat.NatRing213 (nat_sub_add_cancel nat_add_right_cancel nat_add_sub_self_right)
open E213.Tactic.NatHelper (add_sub_assoc)

/-- `(p−i)+(p−l) = 2p−(i+l)` for `i, l ≤ p`. -/
theorem sub_sub_two {p i l : Nat} (hi : i ≤ p) (hl : l ≤ p) : (p - i) + (p - l) = 2 * p - (i + l) := by
  have h2p : i + l ≤ 2 * p := by rw [Nat.two_mul]; exact Nat.add_le_add hi hl
  refine nat_add_right_cancel (b := i + l) ?_
  rw [nat_sub_add_cancel h2p, Nat.add_assoc,
      show (p - l) + (i + l) = ((p - l) + l) + i from by rw [Nat.add_comm i l, ← Nat.add_assoc],
      nat_sub_add_cancel hl, Nat.add_comm p i, ← Nat.add_assoc, nat_sub_add_cancel hi, Nat.two_mul]

/-- `s − p < p` for `p ≤ s < 2p`. -/
private theorem sub_lt_of_lt_two {p s : Nat} (hge : p ≤ s) (hs : s < 2 * p) : s - p < p := by
  have h : (s - p) + p < p + p := by rw [nat_sub_add_cancel hge, ← Nat.two_mul]; exact hs
  exact Nat.lt_of_add_lt_add_right h

/-- `(2p − s) % p = (p − s%p) % p` for `s < 2p`. -/
theorem two_sub_mod {p s : Nat} (hp : 0 < p) (hs : s < 2 * p) : (2 * p - s) % p = (p - s % p) % p := by
  rcases Nat.lt_or_ge s p with hlt | hge
  · -- s < p : both = (p − s) % p
    have h2ps : 2 * p - s = (p - s) + p := by
      refine nat_add_right_cancel (b := s) ?_
      rw [nat_sub_add_cancel (Nat.le_of_lt hs), Nat.add_assoc, Nat.add_comm p s, ← Nat.add_assoc,
          nat_sub_add_cancel (Nat.le_of_lt hlt), Nat.two_mul]
    rw [Nat.mod_eq_of_lt hlt, h2ps, add_p_mod hp]
  · -- p ≤ s : both = (2p − s) % p
    have hsplt : s - p < p := sub_lt_of_lt_two hge hs
    have hsmod : s % p = s - p := by
      have hrw : s % p = ((s - p) + p) % p := by rw [nat_sub_add_cancel hge]
      rw [hrw, add_p_mod hp, Nat.mod_eq_of_lt hsplt]
    have hpsp : p - (s - p) = 2 * p - s := by
      refine nat_add_right_cancel (b := s - p) ?_
      rw [nat_sub_add_cancel (Nat.le_of_lt hsplt),
          show (2 * p - s) + (s - p) = ((2 * p - s) + s) - p from (add_sub_assoc (2 * p - s) hge).symm,
          nat_sub_add_cancel (Nat.le_of_lt hs), Nat.two_mul, nat_add_sub_self_right]
    rw [hsmod, hpsp]

/-- ★★★★ **Negation is additive (mod p)** — `((p−i)+(p−l)) % p = (p − (i+l)%p) % p` for `i, l < p`. -/
theorem neg_add_mod {p i l : Nat} (hp : 0 < p) (hi : i < p) (hl : l < p) :
    ((p - i) + (p - l)) % p = (p - (i + l) % p) % p := by
  rw [sub_sub_two (Nat.le_of_lt hi) (Nat.le_of_lt hl),
      two_sub_mod hp (by rw [Nat.two_mul]; exact Nat.add_lt_add hi hl)]

/-- ★★★★★ **The convolution-associativity index** — `(k+p−(l+i)%p)%p = ((k+p−i)%p+p−l)%p` for
    `i, l < p`.  Both sides reduce to `(k+((p−i)+(p−l)))%p`; `neg_add_mod` bridges.  ∅-axiom. -/
theorem conv_assoc_index {p i l k : Nat} (hp : 0 < p) (hi : i < p) (hl : l < p) :
    (k + p - (l + i) % p) % p = ((k + p - i) % p + p - l) % p := by
  rw [add_sub_assoc k (Nat.le_of_lt hi),
      add_sub_assoc ((k + (p - i)) % p) (Nat.le_of_lt hl),
      mod_add_mod hp (k + (p - i)) (p - l), Nat.add_assoc k (p - i) (p - l),
      add_sub_assoc k (Nat.le_of_lt (Nat.mod_lt _ hp)),
      show (l + i) % p = (i + l) % p from by rw [Nat.add_comm l i],
      add_mod hp k (p - (i + l) % p), ← neg_add_mod hp hi hl,
      ← add_mod hp k ((p - i) + (p - l))]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvAssocIndex
