import E213.Meta.Nat.PolyNatMTactic

/-!
# Fibonacci addition formula + divisibility (∅-axiom)

Two genuinely-absent deep Fibonacci facts (the corpus had sum identities and
mod-5 divisibility, but no addition formula and no index-divisibility):

  ★ **`fib_add`** — the **addition formula** `fib (m+n+1) = fib(m+1)·fib(n+1) +
    fib m·fib n` (the `F_{m+n} = F_m F_{n+1} + F_{m-1} F_n` identity, in the
    subtraction-free shift-by-1 form).  By two-step (paired) induction on `n`.

  ★★ **`fib_dvd_fib_mul`** — `fib m ∣ fib (m·n)`: a Fibonacci number divides every
    Fibonacci at a multiple index.  Induction on `n`: split `fib((j+1)·k + j + 1)`
    via the addition formula into a `·fib(j+1)` term and a `fib((j+1)·k)·fib j`
    term (divisible via the IH).

`fib` is a module-local two-step recurrence (corpus convention; consolidating the
several local `fib` defs is a known smell, deferred).  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.FibonacciDivisibility

/-- Standard Fibonacci: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

theorem fib_rec (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := rfl

/-! ## Local PURE divisibility helpers -/

theorem dvd_refl_n (a : Nat) : a ∣ a := ⟨1, (Nat.mul_one a).symm⟩

/-- `a ∣ b → a ∣ b * c`. -/
theorem dvd_mul_of_dvd {a b : Nat} (h : a ∣ b) (c : Nat) : a ∣ b * c := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w * c, by rw [hw]; ring_nat⟩

/-- `a ∣ x → a ∣ y → a ∣ (x + y)`. -/
theorem dvd_add_n {a x y : Nat} (hx : a ∣ x) (hy : a ∣ y) : a ∣ (x + y) := by
  obtain ⟨w1, h1⟩ := hx
  obtain ⟨w2, h2⟩ := hy
  exact ⟨w1 + w2, by rw [h1, h2]; ring_nat⟩

/-! ## Fibonacci addition formula

`fib (m + n + 1) = fib (m+1) * fib (n+1) + fib m * fib n`, by two-step induction
on `n` (carrying the pair: the formula at `n` AND `n+1`, so the recurrence has
both predecessors). -/

/-- Pair form for two-step induction: the formula at `n` AND at `n+1`. -/
theorem fib_add_pair (m : Nat) : ∀ n : Nat,
    (fib (m + n + 1) = fib (m + 1) * fib (n + 1) + fib m * fib n) ∧
    (fib (m + (n + 1) + 1) = fib (m + 1) * fib (n + 1 + 1) + fib m * fib (n + 1)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · have hidx : m + 0 + 1 = m + 1 := by ring_nat
      have hrhs : fib (m + 1) * fib 1 + fib m * fib 0 = fib (m + 1) := by
        show fib (m + 1) * 1 + fib m * 0 = fib (m + 1)
        rw [Nat.mul_one, Nat.mul_zero, Nat.add_zero]
      rw [hidx, hrhs]
    · have hidx : m + (0 + 1) + 1 = m + 2 := by ring_nat
      have hrhs : fib (m + 1) * fib (0 + 1 + 1) + fib m * fib (0 + 1)
                    = fib m + fib (m + 1) := by
        show fib (m + 1) * 1 + fib m * 1 = fib m + fib (m + 1)
        rw [Nat.mul_one, Nat.mul_one, Nat.add_comm]
      rw [hidx, fib_rec m, hrhs]
  | succ k ih =>
    obtain ⟨ihk, ihk1⟩ := ih
    refine ⟨ihk1, ?_⟩
    have hidxL : m + (k + 1 + 1) + 1 = (m + k + 1) + 2 := by ring_nat
    rw [hidxL, fib_rec (m + k + 1)]
    have e1 : fib (m + k + 1) = fib (m + 1) * fib (k + 1) + fib m * fib k := ihk
    have hshift : m + k + 1 + 1 = m + (k + 1) + 1 := by ring_nat
    have e2 : fib (m + k + 1 + 1)
                = fib (m + 1) * fib (k + 1 + 1) + fib m * fib (k + 1) := by
      rw [hshift]; exact ihk1
    rw [e1, e2]
    have r1 : fib (k + 1 + 1 + 1) = fib (k + 1) + fib (k + 1 + 1) := fib_rec (k + 1)
    have r2 : fib (k + 1 + 1) = fib k + fib (k + 1) := fib_rec k
    rw [r1, r2]
    ring_nat

/-- ★ **Fibonacci addition formula**
    `fib (m + n + 1) = fib (m+1) * fib (n+1) + fib m * fib n`. -/
theorem fib_add (m n : Nat) :
    fib (m + n + 1) = fib (m + 1) * fib (n + 1) + fib m * fib n :=
  (fib_add_pair m n).1

/-! ## Divisibility `fib m ∣ fib (m * n)` -/

/-- ★★ **`fib m ∣ fib (m·n)`** — a Fibonacci number divides every Fibonacci at a
    multiple index.  Induction on `n`; the step splits `fib((j+1)·k + j + 1)` via
    the addition formula into a `·fib(j+1)` part and a `fib((j+1)·k)·fib j` part
    (the latter divisible by `fib(j+1)` via the IH). -/
theorem fib_dvd_fib_mul (m : Nat) : ∀ n : Nat, fib m ∣ fib (m * n) := by
  intro n
  induction n with
  | zero =>
    have hz : m * 0 = 0 := Nat.mul_zero m
    rw [hz]
    show fib m ∣ fib 0
    show fib m ∣ 0
    exact ⟨0, (Nat.mul_zero (fib m)).symm⟩
  | succ k ih =>
    match m with
    | 0 =>
      have hz : (0 : Nat) * (k + 1) = 0 := Nat.zero_mul (k + 1)
      rw [hz]
      exact dvd_refl_n (fib 0)
    | j + 1 =>
      have hidx : (j + 1) * (k + 1) = (j + 1) * k + j + 1 := by ring_nat
      rw [hidx]
      rw [fib_add ((j + 1) * k) j]
      apply dvd_add_n
      · rw [Nat.mul_comm (fib ((j + 1) * k + 1)) (fib (j + 1))]
        exact dvd_mul_of_dvd (dvd_refl_n (fib (j + 1))) _
      · exact dvd_mul_of_dvd ih (fib j)

/-! ## Smoke checks -/

theorem fib_add_smoke : fib (3 + 4 + 1) = fib 4 * fib 5 + fib 3 * fib 4 := by decide
theorem fib_dvd_smoke : fib 3 ∣ fib (3 * 4) := fib_dvd_fib_mul 3 4
theorem fib_dvd_smoke2 : fib 4 ∣ fib (4 * 3) := fib_dvd_fib_mul 4 3

end E213.Lib.Math.Combinatorics.FibonacciDivisibility
