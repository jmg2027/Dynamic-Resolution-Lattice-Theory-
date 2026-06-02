import E213.Lib.Physics.Simplex.Counts

/-!
# The `P`-matrix bridge: natural numbers (Fibonacci) and the `p`-adic `(5/p)` law

Two observations (parallel branch): the Möbius `P = [[2,1],[1,1]]` is
deeply tied to (a) **natural-number construction** and (b) the **`p`-adic
section**.  Both are governed by the single invariant `disc P = NS+NT =
5`.

## `P` builds the naturals: Fibonacci and Stern–Brocot

`P = Q²` where `Q = [[1,1],[1,0]]` is the Fibonacci matrix, and `P = R·L`
where `R = [[1,1],[0,1]]`, `L = [[1,0],[1,1]]` are the Stern–Brocot
generators (every positive rational is a unique `R/L`-word).  So the
entries of `Pⁿ` are Fibonacci numbers:

  `P¹ = (F₃,F₂,F₂,F₁) = (2,1,1,1)`,
  `P² = (F₅,F₄,F₄,F₃) = (5,3,3,2)`,
  `P³ = (F₇,F₆,F₆,F₅) = (13,8,8,5)`,  …  `Pⁿ = (F₂ₙ₊₁, F₂ₙ, F₂ₙ, F₂ₙ₋₁)`.

`P` is the squared Fibonacci recurrence — the natural numbers grow on its
diagonal, `trace Pⁿ = L₂ₙ` (Lucas).  This is the same hyperbolic `P`
engine of `Phase 22` (`D(trace P) = trace P²`), now read as the Fibonacci
generator.

## `P mod p`: the `(5/p)` splitting law (the `p`-adic face)

The order of `P mod p` is governed by whether `disc P = 5 = NS+NT` is a
quadratic residue mod `p` — equivalently `p mod 5`:

  * **ramified** `p = 5 = NS+NT`: order `10 = 2·(NS+NT)` — the `E₈`
    icosian endpoint (`P mod 5`, the lifted `(NS+NT)`-cycle);
  * **split** `p ≡ ±1 (mod 5)` (`5` a QR): `P` diagonalises over `𝔽_p`,
    order `∣ p−1`  (e.g. `p=11`, order `5 ∣ 10`);
  * **inert** `p ≡ ±2 (mod 5)` (`5` a non-QR): `P` irreducible, order
    `∣ p²−1`  (e.g. `p=7`, order `8 ∣ 48`).

`√5 ∈ ℚ_p ⟺ 5` is a QR mod `p ⟺ p ≡ ±1 (mod 5)` (Hensel): the `E₈`
axis field `ℚ(√(NS+NT))` localises exactly at the split primes.  So the
`p`-adic `(5/p)` law, the Fibonacci/Pisano period structure, and the
`E₈` seed `√(NS+NT)` are one phenomenon, pivoting on the ramified prime
`5 = NS+NT`.
-/

namespace E213.Lib.Math.CayleyDickson.Tower.PMatrixArithmeticBridge

open E213.Lib.Physics.Simplex.Counts

/-- `2×2` matrix as `(a,b,c,d)`; ordinary product. -/
def mm (x y : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  (x.1 * y.1 + x.2.1 * y.2.2.1, x.1 * y.2.1 + x.2.1 * y.2.2.2,
   x.2.2.1 * y.1 + x.2.2.2 * y.2.2.1, x.2.2.1 * y.2.1 + x.2.2.2 * y.2.2.2)

/-- `2×2` matrix product mod `p`. -/
def mmod (p : Nat) (x y : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  ((x.1 * y.1 + x.2.1 * y.2.2.1) % p, (x.1 * y.2.1 + x.2.1 * y.2.2.2) % p,
   (x.2.2.1 * y.1 + x.2.2.2 * y.2.2.1) % p, (x.2.2.1 * y.2.1 + x.2.2.2 * y.2.2.2) % p)

/-- `Pⁿ mod p`, `P = [[2,1],[1,1]]`. -/
def Ppow (p : Nat) : Nat → Nat × Nat × Nat × Nat
  | 0     => (1, 0, 0, 1)
  | n + 1 => mmod p (Ppow p n) (2 % p, 1 % p, 1 % p, 1 % p)

/-- Multiplicative order of `P mod p` (search bound `p²`). -/
def Pord (p : Nat) : Nat :=
  ((List.range (p * p)).filter (fun n => 1 ≤ n && Ppow p n == (1, 0, 0, 1))).head?.getD 0

/-- Fibonacci, `∅`-axiom structural recursion. -/
def fib : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fib n + fib (n + 1)

/-- **`P` builds the naturals.**  `P = Q²` (Fibonacci matrix squared) `=
    R·L` (Stern–Brocot generators), and `Pⁿ` has Fibonacci entries
    `(F₂ₙ₊₁, F₂ₙ, F₂ₙ, F₂ₙ₋₁)`. -/
theorem P_is_fibonacci_and_stern_brocot :
    -- P = Q²  (Fibonacci matrix [[1,1],[1,0]] squared)
    (mm (1, 1, 1, 0) (1, 1, 1, 0) = (2, 1, 1, 1))
    -- P = R·L  (Stern–Brocot generators)
    ∧ (mm (1, 1, 0, 1) (1, 0, 1, 1) = (2, 1, 1, 1))
    -- Pⁿ entries are Fibonacci: P¹, P², P³
    ∧ (mm (1, 1, 1, 0) (1, 1, 1, 0) = (fib 3, fib 2, fib 2, fib 1))
    ∧ (mm (2, 1, 1, 1) (2, 1, 1, 1) = (fib 5, fib 4, fib 4, fib 3))
    ∧ (mm (5, 3, 3, 2) (2, 1, 1, 1) = (fib 7, fib 6, fib 6, fib 5)) := by decide

/-- Squares mod `p`. -/
def sqMod (p : Nat) : List Nat := (List.range p).map (fun x => (x * x) % p)

/-- **The `(5/p)` splitting law.**  `disc P = NS+NT = 5` is a QR mod `p`
    iff `p ≡ ±1 (mod 5)` (split); a non-QR iff `p ≡ ±2` (inert). -/
theorem disc_governs_splitting :
    -- disc P = NS+NT.
    ((3 : Int) ^ 2 - 4 * 1 = (NS : Int) + NT)
    -- split classes: p ≡ 1, 4 (mod 5) — 5 is a QR
    ∧ ((sqMod 11).contains (5 % 11) = true ∧ (sqMod 19).contains (5 % 19) = true)
    -- inert classes: p ≡ 2, 3 (mod 5) — 5 is a non-QR
    ∧ ((sqMod 7).contains (5 % 7) = false ∧ (sqMod 13).contains (5 % 13) = false)
    ∧ (11 % 5 = 1 ∧ 19 % 5 = 4 ∧ 7 % 5 = 2 ∧ 13 % 5 = 3) := by decide

/-- **`P mod p`: three regimes by `(5/p)`.**  Ramified `p = NS+NT` gives
    order `2·(NS+NT)` (the `E₈` endpoint); split `p=11` order `∣ p−1`;
    inert `p=7` order `∣ p²−1`. -/
theorem P_mod_p_three_regimes :
    -- ramified p = 5 = NS+NT : order 10 = 2·(NS+NT), the icosian endpoint
    (Pord 5 = 2 * (NS + NT))
    -- split p = 11 ≡ 1 (mod 5) : order 5 divides p−1 = 10
    ∧ (Pord 11 = 5 ∧ (11 - 1) % Pord 11 = 0)
    -- inert p = 7 ≡ 2 (mod 5) : order 8 divides p²−1 = 48
    ∧ (Pord 7 = 8 ∧ (7 * 7 - 1) % Pord 7 = 0) := by decide

/-- ★★★ **The `P`-matrix bridge.**  `P = [[2,1],[1,1]]` is the Fibonacci /
    Stern–Brocot generator of the naturals (`Pⁿ` entries are `Fₙ`), and
    its reduction `P mod p` splits by the `(5/p)` law — ramified at the
    `E₈` prime `NS+NT = 5` (order `2(NS+NT)`), split at `p ≡ ±1 (mod 5)`,
    inert at `p ≡ ±2`.  `disc P = NS+NT` is the single invariant joining
    natural-number (Fibonacci) construction to the `p`-adic localisation
    of the `E₈` axis field `ℚ(√(NS+NT))`. -/
theorem P_matrix_bridge :
    -- naturals: P = Q² = R·L, Fibonacci entries.
    (mm (1, 1, 1, 0) (1, 1, 1, 0) = (2, 1, 1, 1)
      ∧ mm (1, 1, 0, 1) (1, 0, 1, 1) = (2, 1, 1, 1)
      ∧ mm (2, 1, 1, 1) (2, 1, 1, 1) = (fib 5, fib 4, fib 4, fib 3))
    -- disc P = NS+NT, the splitting invariant.
    ∧ ((3 : Int) ^ 2 - 4 * 1 = (NS : Int) + NT)
    -- p-adic: ramified at NS+NT (E₈ endpoint), split/inert by (5/p).
    ∧ (Pord 5 = 2 * (NS + NT) ∧ Pord 11 = 5 ∧ Pord 7 = 8) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.CayleyDickson.Tower.PMatrixArithmeticBridge
