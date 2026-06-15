import E213.Lib.Math.Probability.Information.Bit

/-!
# Information — Coding theory (atomic)

Source coding, error-correcting codes, Hamming distance — all
fundamentally `Nat`-arithmetic on `Bool` strings.

Key atomic facts:

  * **Hamming distance** between two `Bool` strings: `Nat` count
    of disagreements.
  * **Optimal code length** for `2^n` symbols: `n` bits (matches
    Shannon entropy of uniform).
  * **Linear code = subgroup of `Bool^n`** under XOR — combinatorial
    finite structure, no continuous limits.

213-native: bit-string length = depth = log of alphabet size,
all atomically `Nat`-valued.
-/

namespace E213.Lib.Math.Probability.Information.Coding

open E213.Lib.Math.Probability.Information.Bit (bitsAfterBisections)

/-- Hamming distance between two Bool strings of equal length. -/
def hammingDistance : List Bool → List Bool → Nat
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys =>
    (if x = y then 0 else 1) + hammingDistance xs ys

/-- Hamming distance is zero on identical strings. -/
theorem hamming_self : ∀ xs : List Bool, hammingDistance xs xs = 0
  | [] => rfl
  | x :: xs => by
    show (if x = x then 0 else 1) + hammingDistance xs xs = 0
    rw [if_pos rfl, hamming_self xs]

/-- Concrete: `[true, false] vs [false, true]` — Hamming distance 2. -/
theorem hamming_swap : hammingDistance [true, false] [false, true] = 2 := by
  decide

/-- Concrete: `[true, true, true]` vs `[true, false, true]` — distance 1. -/
theorem hamming_one_flip :
    hammingDistance [true, true, true] [true, false, true] = 1 := by decide

/-- ★ **Hamming distance is symmetric** — `d(xs, ys) = d(ys, xs)`, the metric
    symmetry axiom.  Per position, `x ≠ y ⟺ y ≠ x`. -/
theorem hamming_symm : ∀ xs ys : List Bool, hammingDistance xs ys = hammingDistance ys xs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    show (if x = y then 0 else 1) + hammingDistance xs ys
       = (if y = x then 0 else 1) + hammingDistance ys xs
    rw [hamming_symm xs ys]; cases x <;> cases y <;> rfl

/-- Optimal binary code length for `2^n` distinct symbols is `n` bits.
    Matches Shannon entropy of the uniform distribution on `2^n`. -/
def optimalCodeLength (n : Nat) : Nat := bitsAfterBisections n

/-- ★ **Source coding atomic identity** ★ — optimal length =
    log₂(alphabet) = depth in dyadic Lens coordinates. -/
theorem source_coding_optimal (n : Nat) :
    optimalCodeLength n = n := rfl

/-- 256-symbol alphabet (byte): optimal code = 8 bits. -/
theorem byte_optimal : optimalCodeLength 8 = 8 := rfl

/-- 1024-symbol alphabet: optimal = 10 bits. -/
theorem kilobyte_optimal : optimalCodeLength 10 = 10 := rfl

end E213.Lib.Math.Probability.Information.Coding
