import E213.Lib.Math.Combinatorics.FibonacciDivisibility

/-!
# Lucas–Fibonacci link identities (∅-axiom)

The Lucas numbers `L_n` are the Fibonacci companion (same two-step recurrence,
seed `L_0 = 2`, `L_1 = 1`).  This file proves the deep identities *linking* `L_n`
to `F_n` — none of which existed in the corpus (the existing `LucasCutoff.Lucas`
is used only for cardinality cut-offs, with no Fibonacci-link identity):

  ★ **`luc_eq_fib`** : `L_{n+1} = F_n + F_{n+2}` (`L_n = F_{n-1} + F_{n+1}`,
    subtraction-free shift form), by two-step paired induction.
  ★★ **`fib_doubling`** : `F_{2n+2} = F_{n+1} · L_{n+1}` (the doubling identity
    `F_{2n} = F_n · L_n`), direct from `fib_add` + `luc_eq_fib`.
  ★ **`fib_odd_doubling`** : `F_{2n+1} = F_{n+1}² + F_n²`, immediate from `fib_add n n`.

`luc` is a module-local def (it duplicates `LucasCutoff.Lucas` over in the
Cohomology tree; importing that here would be the wrong dependency direction —
the several local `fib`/`luc` defs are a known consolidation smell, deferred).
All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.LucasFibonacci

open E213.Lib.Math.Combinatorics.FibonacciDivisibility (fib fib_rec fib_add)

/-- Lucas numbers: `luc 0 = 2`, `luc 1 = 1`, `luc (n+2) = luc n + luc (n+1)`. -/
def luc : Nat → Nat
  | 0 => 2
  | 1 => 1
  | n + 2 => luc n + luc (n + 1)

theorem luc_rec (n : Nat) : luc (n + 2) = luc n + luc (n + 1) := rfl

theorem luc_2 : luc 2 = 3 := by decide
theorem luc_5 : luc 5 = 11 := by decide

/-- Pure commutative regrouping over four Nat atoms (no `fib`):
    `(a + c) + (b + e) = (a + b) + (c + e)`.  Universally quantified so `ring_nat`
    sees four genuinely-distinct variables (avoids the `fib`-atom-hash collapse). -/
theorem regroup4 (a b c e : Nat) :
    (a + c) + (b + e) = (a + b) + (c + e) := by ring_nat

/-! ## L1  `luc (n+1) = fib n + fib (n+2)` -/

/-- Pair form: `luc_eq_fib` at `n` AND at `n+1`. -/
theorem luc_eq_fib_pair : ∀ n : Nat,
    (luc (n + 1) = fib n + fib (n + 2)) ∧
    (luc (n + 1 + 1) = fib (n + 1) + fib (n + 1 + 2)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · decide
    · decide
  | succ k ih =>
    obtain ⟨ihk, ihk1⟩ := ih
    refine ⟨ihk1, ?_⟩
    rw [luc_rec (k + 1)]
    rw [ihk, ihk1]
    have rL : fib (k + 1 + 1) = fib k + fib (k + 1) := fib_rec k
    have rR : fib (k + 1 + 1 + 2) = fib (k + 2) + fib (k + 1 + 2) := by
      have h : k + 1 + 1 + 2 = (k + 2) + 2 := by ring_nat
      have h2 : (k + 2) + 1 = k + 1 + 2 := by ring_nat
      rw [h, fib_rec (k + 2), h2]
    rw [rL, rR]
    exact regroup4 (fib k) (fib (k + 1)) (fib (k + 2)) (fib (k + 1 + 2))

/-- ★ **L1 — Lucas–Fibonacci link** : `luc (n+1) = fib n + fib (n+2)`,
    i.e. `L_n = F_{n-1} + F_{n+1}` (subtraction-free shift form). -/
theorem luc_eq_fib (n : Nat) : luc (n + 1) = fib n + fib (n + 2) :=
  (luc_eq_fib_pair n).1

/-! ## L2  Fibonacci doubling `F_{2n+2} = F_{n+1} · L_{n+1}` -/

/-- ★★ **L2 — Fibonacci doubling** : `fib (n + (n+1) + 1) = fib (n+1) * luc (n+1)`,
    i.e. `F_{2n+2} = F_{n+1} · L_{n+1}` (the `F_{2n} = F_n L_n` identity, shift form). -/
theorem fib_doubling (n : Nat) :
    fib (n + (n + 1) + 1) = fib (n + 1) * luc (n + 1) := by
  rw [fib_add n (n + 1)]
  rw [luc_eq_fib n]
  have hidx : n + 1 + 1 = n + 2 := by ring_nat
  rw [hidx]
  ring_nat

/-! ## L3  Odd doubling `F_{2n+1} = F_{n+1}² + F_n²` -/

/-- ★ **L3 — odd-index doubling** : `fib (n + n + 1) = fib (n+1)*fib (n+1) + fib n * fib n`,
    i.e. `F_{2n+1} = F_{n+1}² + F_n²` (immediate from `fib_add n n`). -/
theorem fib_odd_doubling (n : Nat) :
    fib (n + n + 1) = fib (n + 1) * fib (n + 1) + fib n * fib n :=
  fib_add n n

/-! ## Smoke checks -/

theorem fib_doubling_smoke : fib (2 + (2 + 1) + 1) = fib (2 + 1) * luc (2 + 1) :=
  fib_doubling 2
theorem fib_odd_doubling_smoke :
    fib (4 + 4 + 1) = fib (4 + 1) * fib (4 + 1) + fib 4 * fib 4 :=
  fib_odd_doubling 4
theorem luc_eq_fib_smoke : luc (5 + 1) = fib 5 + fib (5 + 2) := luc_eq_fib 5

end E213.Lib.Math.Combinatorics.LucasFibonacci
