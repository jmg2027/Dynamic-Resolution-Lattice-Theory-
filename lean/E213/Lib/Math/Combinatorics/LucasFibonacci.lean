import E213.Lib.Math.Combinatorics.FibonacciDivisibility
import E213.Meta.Int213.PolyIntMTactic
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum

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
open E213.Meta.Int213.PolyIntM (powInt)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)

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

/-! ## Cassini + the Lucas–Fibonacci relation (over `Int`)

Cassini for the cluster's local `fib` (the corpus `cassini_fibZ_eq_altSign` is over
the *different* `fibZ` C-finite witness), then `Lₙ²−5Fₙ²=4(−1)ⁿ` follows. -/

/-- Cast of the recurrence to `Int`: `(fib (n+2) : Int) = fib n + fib (n+1)`. -/
theorem fib_rec_cast (n : Nat) :
    ((fib (n + 2) : Nat) : Int) = (fib n : Int) + (fib (n + 1) : Int) := by
  rw [fib_rec n]
  exact Int.ofNat_add (fib n) (fib (n + 1))

/-- Paired two-step form: Cassini at `n` AND `n+1` (so the recurrence has both
    predecessors and the sign flips each step). -/
theorem cassini_pair : ∀ n : Nat,
    ((fib n : Int) * (fib (n + 2) : Int) - (fib (n + 1) : Int) * (fib (n + 1) : Int)
        = powInt (-1) (n + 1))
    ∧ ((fib (n + 1) : Int) * (fib (n + 1 + 2) : Int)
          - (fib (n + 1 + 1) : Int) * (fib (n + 1 + 1) : Int)
        = powInt (-1) (n + 1 + 1)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · show (fib 0 : Int) * (fib 2 : Int) - (fib 1 : Int) * (fib 1 : Int) = powInt (-1) 1
      rw [show (fib 0 : Int) = 0 from rfl, show (fib 1 : Int) = 1 from rfl,
          show (fib 2 : Int) = 1 from rfl]
      decide
    · show (fib 1 : Int) * (fib 3 : Int) - (fib 2 : Int) * (fib 2 : Int) = powInt (-1) 2
      rw [show (fib 1 : Int) = 1 from rfl, show (fib 2 : Int) = 1 from rfl,
          show (fib 3 : Int) = 2 from rfl]
      decide
  | succ k ih =>
    obtain ⟨_, ih1⟩ := ih
    refine ⟨ih1, ?_⟩
    have ek4 : ((fib (k + 1 + 1 + 2) : Nat) : Int)
        = (fib (k + 1 + 1) : Int) + (fib (k + 1 + 1 + 1) : Int) := fib_rec_cast (k + 1 + 1)
    have ek3 : ((fib (k + 1 + 1 + 1) : Nat) : Int)
        = (fib (k + 1) : Int) + (fib (k + 1 + 1) : Int) := fib_rec_cast (k + 1)
    show (fib (k + 1 + 1) : Int) * (fib (k + 1 + 1 + 2) : Int)
          - (fib (k + 1 + 1 + 1) : Int) * (fib (k + 1 + 1 + 1) : Int)
        = powInt (-1) (k + 1 + 1 + 1)
    rw [ek4, ek3]
    have ihaligned : (fib (k + 1) : Int) * ((fib (k + 1) : Int) + (fib (k + 1 + 1) : Int))
          - (fib (k + 1 + 1) : Int) * (fib (k + 1 + 1) : Int)
        = powInt (-1) (k + 1 + 1) := by
      have e : ((fib (k + 1 + 2) : Nat) : Int)
          = (fib (k + 1) : Int) + (fib (k + 1 + 1) : Int) := fib_rec_cast (k + 1)
      rw [← e]; exact ih1
    rw [show powInt (-1 : Int) (k + 1 + 1 + 1) = powInt (-1) (k + 1 + 1) * (-1) from rfl,
        ← ihaligned]
    ring_intZ

/-- ★ **Cassini's identity** (local `fib`, over `Int`):
    `F_n · F_{n+2} − F_{n+1}² = (−1)^{n+1}`. -/
theorem cassini (n : Nat) :
    (fib n : Int) * (fib (n + 2) : Int) - (fib (n + 1) : Int) * (fib (n + 1) : Int)
      = powInt (-1) (n + 1) :=
  (cassini_pair n).1

/-- ★★ **Lucas–Fibonacci relation** over `Int`: `L_n² − 5·F_n² = 4·(−1)ⁿ`, shift form
    `luc(n+1)² − 5·fib(n+1)² = 4·powInt(-1)(n+1)`.  From `luc_eq_fib` + Cassini. -/
theorem lucas_fib_rel (n : Nat) :
    (luc (n + 1) : Int) * (luc (n + 1) : Int)
        - 5 * ((fib (n + 1) : Int) * (fib (n + 1) : Int))
      = 4 * powInt (-1) (n + 1) := by
  have hl : ((luc (n + 1) : Nat) : Int) = (fib n : Int) + (fib (n + 2) : Int) := by
    rw [luc_eq_fib n]; exact Int.ofNat_add (fib n) (fib (n + 2))
  have hf2 : ((fib (n + 2) : Nat) : Int) = (fib n : Int) + (fib (n + 1) : Int) :=
    fib_rec_cast n
  have hc := cassini n
  rw [hf2] at hc
  rw [hl, hf2]
  rw [← hc]
  ring_intZ

/-! ## Lucas doubling `L_{2n} = L_n² − 2·(−1)ⁿ` -/

/-- `L_{2n+2}` as a Nat sum of four Fibonacci squares:
    `L_{2n+2} = F_{2n+1} + F_{2n+3} = (F_{n+1}² + F_n²) + (F_{n+2}² + F_{n+1}²)`. -/
theorem luc_double_nat (n : Nat) :
    luc (n + (n + 1) + 1)
      = (fib (n + 1) * fib (n + 1) + fib n * fib n)
        + (fib (n + 2) * fib (n + 2) + fib (n + 1) * fib (n + 1)) := by
  have hL : luc (n + (n + 1) + 1) = fib (n + (n + 1)) + fib (n + (n + 1) + 2) :=
    luc_eq_fib (n + (n + 1))
  have hi1 : n + (n + 1) = n + n + 1 := by ring_nat
  have hi2 : n + (n + 1) + 2 = (n + 1) + (n + 1) + 1 := by ring_nat
  have hi3 : n + 1 + 1 = n + 2 := by ring_nat
  have hodd1 : fib (n + n + 1) = fib (n + 1) * fib (n + 1) + fib n * fib n :=
    fib_odd_doubling n
  have hodd2 : fib ((n + 1) + (n + 1) + 1)
      = fib (n + 1 + 1) * fib (n + 1 + 1) + fib (n + 1) * fib (n + 1) :=
    fib_odd_doubling (n + 1)
  rw [hi3] at hodd2
  rw [hL]
  rw [hi2, hi1]
  rw [hodd1, hodd2]

/-- ★★ **Lucas doubling** over `Int`: `L_{2n} = L_n² − 2·(−1)ⁿ`, shift form
    `luc(2n+2) = luc(n+1)² − 2·powInt(-1)(n+1)`.  From `luc_double_nat` + Cassini. -/
theorem luc_doubling (n : Nat) :
    (luc (n + (n + 1) + 1) : Int)
      = (luc (n + 1) : Int) * (luc (n + 1) : Int) - 2 * powInt (-1) (n + 1) := by
  have hLZ : ((luc (n + (n + 1) + 1) : Nat) : Int)
      = ((fib (n + 1) : Int) * (fib (n + 1) : Int) + (fib n : Int) * (fib n : Int))
        + ((fib (n + 2) : Int) * (fib (n + 2) : Int)
            + (fib (n + 1) : Int) * (fib (n + 1) : Int)) := by
    rw [luc_double_nat n]
    rw [Int.ofNat_add, Int.ofNat_add, Int.ofNat_add,
        Int.ofNat_mul, Int.ofNat_mul, Int.ofNat_mul]
  have hlucZ : ((luc (n + 1) : Nat) : Int) = (fib n : Int) + (fib (n + 2) : Int) := by
    rw [luc_eq_fib n]; exact Int.ofNat_add (fib n) (fib (n + 2))
  have hc : (fib n : Int) * (fib (n + 2) : Int)
      - (fib (n + 1) : Int) * (fib (n + 1) : Int) = powInt (-1) (n + 1) := cassini n
  rw [hLZ, hlucZ, ← hc]
  ring_intZ

/-! ## Lucas partial sums -/

/-- `sumLuc n = L_0 + … + L_n`. -/
def sumLuc (n : Nat) : Nat := sumTo (n + 1) luc

/-- ★ **Lucas partial-sum identity** `(Σ_{k=0}^{n} L_k) + 1 = L_{n+2}`. -/
theorem sumLuc_succ_one (n : Nat) : sumLuc n + 1 = luc (n + 2) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show sumTo (k + 2) luc + 1 = luc (k + 3)
    rw [sumTo_succ]
    have ih' : sumTo (k + 1) luc + 1 = luc (k + 2) := ih
    have hr : luc (k + 3) = luc (k + 1) + luc (k + 2) := luc_rec (k + 1)
    rw [hr, ← ih']
    ring_nat

/-- `sumLucSq n = L_0² + … + L_n²`. -/
def sumLucSq (n : Nat) : Nat := sumTo (n + 1) (fun k => luc k * luc k)

/-- ★ **Lucas sum-of-squares identity** `Σ_{k=0}^{n} L_k² = L_n · L_{n+1} + 2`.
    (The `+2` is the `L_0 = 2` seed surviving — vs the Fibonacci `Σ F_k² = Fₙ F_{n+1}`.) -/
theorem sumLucSq_eq (n : Nat) : sumLucSq n = luc n * luc (n + 1) + 2 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show sumTo (k + 2) (fun k => luc k * luc k) = luc (k + 1) * luc (k + 2) + 2
    rw [sumTo_succ]
    have ih' : sumTo (k + 1) (fun k => luc k * luc k) = luc k * luc (k + 1) + 2 := ih
    have hr : luc (k + 2) = luc k + luc (k + 1) := luc_rec k
    rw [ih', hr]
    ring_nat

end E213.Lib.Math.Combinatorics.LucasFibonacci
