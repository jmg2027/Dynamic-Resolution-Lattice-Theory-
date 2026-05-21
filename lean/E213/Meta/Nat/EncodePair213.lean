import E213.Meta.Nat.NatDiv213

/-!
# Pair-encoding helpers (∅-axiom, Math layer)

Encoding `(a, b) : Fin n × Fin n` as `a * n + b : Fin (n*n)`,
with axiom-free div/mod decoders.  Used by `ArithFSM.toBitFSM`.
-/

namespace E213.Meta.Nat.EncodePair213

open E213.Meta.Nat.NatDiv213 (add_div_right_pos add_mod_right_pos)

/-- `(a * n + b) / n = a` when `b < n`.  ∅-axiom. -/
theorem encode_div {n : Nat} (hn : 0 < n) :
    ∀ (a : Nat) (b : Nat), b < n → (a * n + b) / n = a
  | 0, b, hb => by
    rw [Nat.zero_mul, Nat.zero_add]
    exact Nat.div_eq_of_lt hb
  | k+1, b, hb => by
    show ((k + 1) * n + b) / n = k + 1
    have hreorder : (k + 1) * n + b = (k * n + b) + n := by
      rw [Nat.succ_mul, Nat.add_right_comm]
    rw [hreorder, add_div_right_pos hn]
    rw [encode_div hn k b hb]

/-- `(a * n + b) % n = b` when `b < n`.  ∅-axiom. -/
theorem encode_mod {n : Nat} (hn : 0 < n) :
    ∀ (a : Nat) (b : Nat), b < n → (a * n + b) % n = b
  | 0, b, hb => by
    rw [Nat.zero_mul, Nat.zero_add]
    exact Nat.mod_eq_of_lt hb
  | k+1, b, hb => by
    show ((k + 1) * n + b) % n = b
    have hreorder : (k + 1) * n + b = (k * n + b) + n := by
      rw [Nat.succ_mul, Nat.add_right_comm]
    rw [hreorder, add_mod_right_pos hn]
    rw [encode_mod hn k b hb]

end E213.Meta.Nat.EncodePair213
