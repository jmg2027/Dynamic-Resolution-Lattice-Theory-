import E213.Lib.Math.NumberSystems.Real213.MarkovUniqueness
import E213.Lib.Math.NumberSystems.Real213.FibCassiniNat
import E213.Meta.Nat.PolyNatMTactic

/-!
# MarkovCassiniBridge — the Markov–Fibonacci spine reads the Cassini unimodular dichotomy

The merged-`main` thread `Lib/Math/CassiniUnimodular` proved that a 2nd-order `Int` orbit's
Cassini determinant `D(n) = s(n)·s(n+2) − s(n+1)²` is governed entirely by its **multiplier**
`q` (the determinant of the shift): `det_closed` gives `D(n) = qⁿ · D(0)`, so the two *unimodular*
multipliers `q = ±1` are exactly the conserved (`q=1`) and sign-alternating (`q=−1`) readings —
the **depth-0 Cassini floor** (`CassiniDepthFloor`).

The Markov–Fibonacci spine — the odd-index Fibonacci numbers `fib(2n+1) = 1, 2, 5, 13, 34, …`,
the Markov numbers along the `(1,1,·)` branch — carries *both* unimodular readings at once, and
each is a genuine Markov fact:

  * **`q = −1` (the standard Fibonacci Cassini).**  `fib_cassini_norm` (main) is exactly
    `fib(2n+2)² + 1 = fib(2n+1)·fib(2n+3)` — the index-1 Cassini at its `+1` value.  So the Markov
    number `c = fib(2n+3)` divides `fib(2n+2)² + 1`: **`fib(2n+2)` is the `√(−1)` mod `c`** that
    the uniqueness machinery (`MarkovUniqueness`) runs on.  The `√(−1)` residue *is* the `q = −1`
    Casoratian value.

  * **`q = +1` (the index-gap-2 Cassini).**  `fib(2n+1)·fib(2n+5) = fib(2n+3)² + 1` — the
    consecutive *spine* triple `(fib(2n+1), fib(2n+3), fib(2n+5))` has conserved Cassini equal to
    the **unit `1`**.  This is the `det_closed` value at `q = 1` for the spine's own trace-`3`
    recurrence `s(n+2) = 3·s(n+1) − s(n)` (`fib_spine_recurrence`): the multiplier of
    `[[3,-1],[1,0]]` is `1`, so `D(n) = D(0) = fib(1)·fib(5) − fib(3)² = 5 − 4 = 1`.

So the `√(−1)` that indexes a Fibonacci-spine Markov number and the unit that conserves its spine
Cassini are the **same Cassini law at the two unimodular multipliers** `q = ∓1` — the Markov-side
instance of `CassiniUnimodular.cassini_law_one_at_two_multipliers`.  Both proofs reduce to the one
norm `fib_cassini_norm` (`a² + ab = b² + 1`, `a = fib(2n+1)`, `b = fib(2n+2)`).
-/

namespace E213.Lib.Math.NumberSystems.Real213.MarkovCassiniBridge

open E213.Lib.Math.Algebra.Mobius213.Px.FibonacciAtomicLock (fib)
open E213.Lib.Math.NumberSystems.Real213.FibCassiniNat (fib_cassini_norm)
open E213.Lib.Math.NumberSystems.Real213.GoldenFormMarkov (add_left_cancel_pure)

/-- ★★★★ **`q = −1` reading: the `√(−1)` of a Fibonacci-spine Markov number is the Cassini value.**
    `fib(2n+3) ∣ fib(2n+2)² + 1`, because `fib(2n+2)² + 1 = fib(2n+1)·fib(2n+3)` is precisely
    `fib_cassini_norm` (the standard index-1 Cassini at `+1`, the `q = −1` Casoratian).  So the
    `MarkovUniqueness` `√(−1)`-residue is the `q = −1` reading of the spine's Cassini. -/
theorem markov_spine_sqrt_neg_one_cassini (n : Nat) :
    fib (2 * n + 3) ∣ (fib (2 * n + 2) * fib (2 * n + 2) + 1) := by
  have hc := fib_cassini_norm n
  have h3 : fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) := rfl
  exact ⟨fib (2 * n + 1), by rw [h3, hc]; ring_nat⟩

/-- ★★★★ **`q = +1` reading: the spine's index-gap-2 Cassini is the conserved unit `1`.**
    `fib(2n+1)·fib(2n+5) = fib(2n+3)² + 1` for every `n` — the Cassini determinant
    `s(n)·s(n+2) − s(n+1)²` of the Markov spine `s(n) = fib(2n+1)` is the constant `1`, the
    `det_closed` value at multiplier `q = 1` of the trace-`3` spine recurrence
    `s(n+2) = 3·s(n+1) − s(n)` (`fib_spine_recurrence`).  Proof: reduce to `fib_cassini_norm`
    (`a² + ab = b² + 1`) by unfolding the recurrence + `ring_nat`, cancelling `b² + 1`. -/
theorem markov_fib_second_cassini (n : Nat) :
    fib (2 * n + 1) * fib (2 * n + 5) = fib (2 * n + 3) * fib (2 * n + 3) + 1 := by
  have hc := fib_cassini_norm n
  have h5' : fib (2 * n + 5) = 2 * fib (2 * n + 1) + 3 * fib (2 * n + 2) := by
    have e5 : fib (2 * n + 5) = fib (2 * n + 4) + fib (2 * n + 3) := rfl
    have e4 : fib (2 * n + 4) = fib (2 * n + 3) + fib (2 * n + 2) := rfl
    have e3 : fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) := rfl
    rw [e5, e4, e3]; ring_nat
  have h3' : fib (2 * n + 3) = fib (2 * n + 1) + fib (2 * n + 2) := by
    have e3 : fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) := rfl
    rw [e3]; ring_nat
  rw [h5', h3']
  have key : fib (2 * n + 1) * fib (2 * n + 1) + fib (2 * n + 1) * fib (2 * n + 2)
           = fib (2 * n + 2) * fib (2 * n + 2) + 1 := by rw [hc]; ring_nat
  have hcancel :
      (fib (2 * n + 2) * fib (2 * n + 2) + 1)
        + fib (2 * n + 1) * (2 * fib (2 * n + 1) + 3 * fib (2 * n + 2))
      = (fib (2 * n + 1) * fib (2 * n + 1) + fib (2 * n + 1) * fib (2 * n + 2))
        + ((fib (2 * n + 1) + fib (2 * n + 2)) * (fib (2 * n + 1) + fib (2 * n + 2)) + 1) := by
    ring_nat
  rw [key] at hcancel
  exact add_left_cancel_pure _ _ _ hcancel

/-- ★★★★★ **The Markov spine's two Cassini readings, bundled** — the `√(−1)` (`q = −1`) and the
    conserved unit (`q = +1`) are one Cassini law at the two unimodular multipliers (the Markov
    instance of `CassiniUnimodular.cassini_law_one_at_two_multipliers`). -/
theorem markov_spine_cassini_dichotomy (n : Nat) :
    fib (2 * n + 3) ∣ (fib (2 * n + 2) * fib (2 * n + 2) + 1)
    ∧ fib (2 * n + 1) * fib (2 * n + 5) = fib (2 * n + 3) * fib (2 * n + 3) + 1 :=
  ⟨markov_spine_sqrt_neg_one_cassini n, markov_fib_second_cassini n⟩

/-- ★★★★ **Consecutive spine `(residue, Markov-number)` pairs are Farey/Stern-Brocot neighbors.**
    With residue `u_n = fib(2n)` (`fib(2n)²+1 = fib(2n−1)·fib(2n+1)`) and Markov number
    `m_n = fib(2n+1)`, the pairs `(fib(2n), fib(2n+1))`, `(fib(2n+2), fib(2n+3))` have unimodular
    cross-determinant: `fib(2n+1)·fib(2n+2) = fib(2n)·fib(2n+3) + 1`.  This is the structural basis
    of Zhang Lemma 2 (the Farey-monotone recovery) *on the Fibonacci spine*: the `(u_n, m_n)` walk a
    Stern-Brocot path (det `±1`), so `u_n/m_n` is a strictly monotone convergent sequence and the
    residue determines the spine position.  (Reduces to `fib_cassini_norm`.) -/
theorem spine_residue_farey (n : Nat) :
    fib (2 * n + 1) * fib (2 * n + 2) = fib (2 * n) * fib (2 * n + 3) + 1 := by
  have hc := fib_cassini_norm n
  have h2 : fib (2 * n + 2) = fib (2 * n + 1) + fib (2 * n) := rfl
  have h3 : fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) := rfl
  rw [h3, h2]
  rw [h2] at hc
  have hcancel :
      ((fib (2*n+1)+fib (2*n))*(fib (2*n+1)+fib (2*n))+1) + fib (2*n+1)*(fib (2*n+1)+fib (2*n))
      = ((fib (2*n+1)+fib (2*n))*fib (2*n+1)+fib (2*n+1)*fib (2*n+1))
        + (fib (2*n)*((fib (2*n+1)+fib (2*n))+fib (2*n+1)) + 1) := by ring_nat
  rw [hc] at hcancel
  exact add_left_cancel_pure _ _ _ hcancel

/-- ★★★★ **Zhang Lemma 2 on the spine: the residue ratio is strictly increasing.**  The convergent
    ratios `u_n/m_n = fib(2n)/fib(2n+1)` strictly increase — cross-multiplied,
    `fib(2n)·fib(2n+3) < fib(2n+1)·fib(2n+2)` — an immediate consequence of `spine_residue_farey`
    (the Farey cross-determinant is `+1`).  So distinct spine positions have distinct residues:
    the Farey-monotone recovery (`SamePairInjective`) holds *on the Fibonacci spine*. -/
theorem spine_residue_strict_mono (n : Nat) :
    fib (2 * n) * fib (2 * n + 3) < fib (2 * n + 1) * fib (2 * n + 2) := by
  rw [spine_residue_farey n]; exact Nat.lt_succ_self _

end E213.Lib.Math.NumberSystems.Real213.MarkovCassiniBridge
