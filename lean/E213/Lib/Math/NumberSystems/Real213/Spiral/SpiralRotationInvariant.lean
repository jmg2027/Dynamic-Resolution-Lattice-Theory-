import E213.Lib.Math.NumberSystems.Real213.ProbeTwist.ProbeTwistConic

/-!
# SpiralRotationInvariant — the golden form is conserved at every turn of the P-spiral

The atomic Möbius shift `Pstep (m,k) = (2m+k, m+k)` (the `P = [[2,1],[1,1]]` orbit) runs
the same self-similar step at every iteration — `Pseq seed (n+1) = Pstep (Pseq seed n)`.
`ProbeTwistConic.Q_preserved` proves the golden form `Q(m,k) = m² − mk − k²` (discriminant
`5 = NS+NT`) is conserved by **one** step.  This file iterates it: `Q` is conserved at
**every** step `n`, so the convergent orbit stays on its own hyperbola `Q = N` as the
spiral turns.

That conserved `Q` is the **rotation invariant** of the spiral: the same form, preserved
identically at every scale of the self-similar shift.  The proof is "induct + apply the
one-step law" — the same shape as `Mobius213PellInvariant.Pseq_seedZero_pell_invariant`
(the `N = −1` orbit), now for *every* `(m,k)`/`N`.

  * `add_cancel_chain` — the pure additive transitivity: a point on `(m,k)`'s hyperbola
    whose `Pstep`-image is on its own hyperbola is again on `(m,k)`'s hyperbola.
  * `qinv_step` — one turn preserves the `(m,k)`-hyperbola membership (`Q_preserved` +
    `add_cancel_chain`).
  * ★★★ `Q_iterate_preserved` — `Q(Pseq (m,k) n) = Q(m,k)` for **every** `n`: the golden
    rotation invariant is scale-invariant across all turns of the spiral.

The form is stated sign-free over `ℕ` (`a² + mk + k² = ab + b² + m²`, i.e. `Q(a,b) =
Q(m,k)` with subtractions moved across), so no `Int` is needed.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.SpiralRotationInvariant

open E213.Lib.Math.NumberSystems.Real213.Mobius213Equiv (Pstep Pseq)
open E213.Lib.Math.NumberSystems.Real213.ProbeTwistConic (Q_preserved)

/-! ## §1 — pure additive transitivity of hyperbola membership -/

/-- The additive transitivity behind "same hyperbola".  If `(a,b)` sits on `(m,k)`'s
    `Q`-hyperbola (`ih`, sign-free) and its `Pstep`-image sits on `(a,b)`'s hyperbola
    (`qp`, sign-free), the image sits on `(m,k)`'s hyperbola.  Purely additive: add the
    two equations and cancel the common `ab + bb` (`NatHelper.add_right_cancel`). -/
theorem add_cancel_chain (P R aa ab bb mk kk mm : Nat)
    (qp : P + ab + bb = R + aa) (ih : aa + mk + kk = ab + bb + mm) :
    P + mk + kk = R + mm := by
  have key : (P + mk + kk) + (ab + bb) = (R + mm) + (ab + bb) := by
    calc (P + mk + kk) + (ab + bb)
        = (P + ab + bb) + (mk + kk) := by
          rw [Nat.add_assoc P mk kk, Nat.add_assoc P ab bb,
              Nat.add_assoc P (mk+kk) (ab+bb), Nat.add_assoc P (ab+bb) (mk+kk)]
          exact congrArg (P + ·) (Nat.add_comm (mk+kk) (ab+bb))
      _ = (R + aa) + (mk + kk) := by rw [qp]
      _ = R + (aa + mk + kk) := by
          rw [Nat.add_assoc R aa (mk+kk), ← Nat.add_assoc aa mk kk]
      _ = R + (ab + bb + mm) := by rw [ih]
      _ = (R + mm) + (ab + bb) := by
          rw [Nat.add_comm (ab+bb) mm, ← Nat.add_assoc R mm (ab+bb)]
  exact E213.Tactic.NatHelper.add_right_cancel key

/-! ## §2 — one turn preserves the hyperbola; iterate to every turn -/

/-- One turn of the spiral preserves `(m,k)`-hyperbola membership: if `(a,b)` is on
    `(m,k)`'s `Q`-hyperbola, so is `Pstep (a,b) = (2a+b, a+b)`.  `Q_preserved a b` gives
    the one-step law from `(a,b)`; `add_cancel_chain` chains it to `(m,k)`. -/
theorem qinv_step (m k a b : Nat)
    (ih : a*a + m*k + k*k = a*b + b*b + m*m) :
    (2*a+b)*(2*a+b) + m*k + k*k = (2*a+b)*(a+b) + (a+b)*(a+b) + m*m :=
  add_cancel_chain ((2*a+b)*(2*a+b)) ((2*a+b)*(a+b) + (a+b)*(a+b))
    (a*a) (a*b) (b*b) (m*k) (k*k) (m*m) (Q_preserved a b) ih

/-- ★★★ **The golden rotation invariant is conserved at every turn of the spiral.**
    For every `n`, the `n`-th convergent `Pseq (m,k) n` sits on the *same* `Q`-hyperbola
    as the seed `(m,k)`: `Q(Pseq (m,k) n) = Q(m,k)`, sign-free as

      `(Pseq (m,k) n).1² + m·k + k² = (Pseq (m,k) n).1·(Pseq (m,k) n).2
                                      + (Pseq (m,k) n).2² + m²`.

    The golden form `m² − mk − k²` (disc `5 = NS+NT`) is the rotation invariant: the same
    form, preserved identically at every scale of the self-similar `P`-shift.  Proof:
    induction on `n` — base is hyperbola membership of the seed (additive comm), step is
    `qinv_step`. -/
theorem Q_iterate_preserved (m k : Nat) : ∀ n,
    (Pseq (m,k) n).1 * (Pseq (m,k) n).1 + m*k + k*k
      = (Pseq (m,k) n).1 * (Pseq (m,k) n).2
        + (Pseq (m,k) n).2 * (Pseq (m,k) n).2 + m*m := by
  intro n
  induction n with
  | zero =>
    show m*m + m*k + k*k = m*k + k*k + m*m
    rw [Nat.add_assoc (m*m) (m*k) (k*k), Nat.add_comm (m*m) (m*k + k*k)]
  | succ i ih =>
    exact qinv_step m k (Pseq (m,k) i).1 (Pseq (m,k) i).2 ih

end E213.Lib.Math.NumberSystems.Real213.SpiralRotationInvariant
