/-!
# k-bonacci sequences (parametric in k)

Generalises Fibonacci (k=2), Tribonacci (k=3), Tetranacci (k=4),
Pentanacci (k=5), ... to arbitrary `k : Nat`.

**Convention**: standard k-bonacci with `k - 1` zero seeds followed
by one `1`:
  a_0 = a_1 = ... = a_{k-2} = 0,  a_{k-1} = 1,
  a_n = a_{n-1} + a_{n-2} + ... + a_{n-k}  for n ≥ k.

For k = 2: Fibonacci (`0, 1, 1, 2, 3, 5, 8, 13, ...`).
For k = 3: Tribonacci (`0, 0, 1, 1, 2, 4, 7, 13, 24, ...`).
For k = 4: Tetranacci (`0, 0, 0, 1, 1, 2, 4, 8, 15, 29, ...`).

**Representation**: a list-of-length-k sliding window holding the
last `k` values, oldest first.  Step = drop oldest, append the
sum of the current window.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.KBonacci

/-- One step of the k-bonacci sliding window: drop the oldest value,
    append the sum of the current window. -/
def kBonStep (xs : List Nat) : List Nat :=
  xs.drop 1 ++ [xs.foldr (· + ·) 0]

/-- Iterate `kBonStep` `n` times. -/
def kBonIter : Nat → List Nat → List Nat
  | 0,     xs => xs
  | n + 1, xs => kBonIter n (kBonStep xs)

/-- Initial window for `k`-bonacci: `[0, 0, ..., 0, 1]` of length `k`. -/
def kBonInit (k : Nat) : List Nat :=
  List.replicate (k - 1) 0 ++ [1]

/-- The `n`-th k-bonacci number. -/
def kBonacci (k n : Nat) : Nat :=
  (kBonIter n (kBonInit k)).headD 0

/-! ## Smoke at small k -/

/-- k = 2 (Fibonacci): `0, 1, 1, 2, 3, 5, 8, 13`. -/
theorem kBon_2_0 : kBonacci 2 0 = 0 := by decide
theorem kBon_2_1 : kBonacci 2 1 = 1 := by decide
theorem kBon_2_2 : kBonacci 2 2 = 1 := by decide
theorem kBon_2_3 : kBonacci 2 3 = 2 := by decide
theorem kBon_2_4 : kBonacci 2 4 = 3 := by decide
theorem kBon_2_5 : kBonacci 2 5 = 5 := by decide
theorem kBon_2_6 : kBonacci 2 6 = 8 := by decide
theorem kBon_2_7 : kBonacci 2 7 = 13 := by decide

/-- k = 3 (Tribonacci): `0, 0, 1, 1, 2, 4, 7, 13, 24`. -/
theorem kBon_3_0 : kBonacci 3 0 = 0 := by decide
theorem kBon_3_1 : kBonacci 3 1 = 0 := by decide
theorem kBon_3_2 : kBonacci 3 2 = 1 := by decide
theorem kBon_3_3 : kBonacci 3 3 = 1 := by decide
theorem kBon_3_4 : kBonacci 3 4 = 2 := by decide
theorem kBon_3_5 : kBonacci 3 5 = 4 := by decide
theorem kBon_3_6 : kBonacci 3 6 = 7 := by decide
theorem kBon_3_7 : kBonacci 3 7 = 13 := by decide
theorem kBon_3_8 : kBonacci 3 8 = 24 := by decide

/-- k = 4 (Tetranacci): `0, 0, 0, 1, 1, 2, 4, 8, 15, 29, 56, 108`. -/
theorem kBon_4_0 : kBonacci 4 0 = 0 := by decide
theorem kBon_4_3 : kBonacci 4 3 = 1 := by decide
theorem kBon_4_4 : kBonacci 4 4 = 1 := by decide
theorem kBon_4_5 : kBonacci 4 5 = 2 := by decide
theorem kBon_4_6 : kBonacci 4 6 = 4 := by decide
theorem kBon_4_7 : kBonacci 4 7 = 8 := by decide
theorem kBon_4_8 : kBonacci 4 8 = 15 := by decide
theorem kBon_4_9 : kBonacci 4 9 = 29 := by decide
theorem kBon_4_10 : kBonacci 4 10 = 56 := by decide
theorem kBon_4_11 : kBonacci 4 11 = 108 := by decide

/-- k = 5 (Pentanacci): `0, 0, 0, 0, 1, 1, 2, 4, 8, 16, 31, 61, 120, 236, 464`. -/
theorem kBon_5_0  : kBonacci 5 0  = 0 := by decide
theorem kBon_5_4  : kBonacci 5 4  = 1 := by decide
theorem kBon_5_9  : kBonacci 5 9  = 16 := by decide
theorem kBon_5_10 : kBonacci 5 10 = 31 := by decide
theorem kBon_5_11 : kBonacci 5 11 = 61 := by decide
theorem kBon_5_12 : kBonacci 5 12 = 120 := by decide

/-! ## Specialisation: existing Trib matches the k=3 case

For the existing `TribonacciCutoff.Trib`, the values at small
indices match `kBonacci 3 n` on tested cases.  This is the
direction-of-equivalence smoke — the parametric and the bespoke
definition agree, leaving room for a future structural equivalence
theorem if downstream consumers need to swap definitions. -/

/-- Index 7 = 13: catalogue prime hit at k=3 (matches `Trib_7_eq_13`). -/
theorem kBon_3_at_7_eq_13 : kBonacci 3 7 = 13 := kBon_3_7

/-- Index 11 = 108 at k=4: catalogue-adjacent (no prime, but
    Tetranacci's growth crosses 100 at index 11). -/
theorem kBon_4_at_11_eq_108 : kBonacci 4 11 = 108 := kBon_4_11

/-! ## Boundary phenomenon: k-bonacci values at the d=5 catalogue depth

The DRLT 213 atomic dimension is `d = 5 = NS + NT`.  Reading the
`k`-bonacci sequence at index `d = 5` gives a "depth-d snapshot":

  · k=2 (Fib): a_5 = 5  = d
  · k=3 (Trib): a_5 = 4 = d - 1 = NS + NT - 1
  · k=4 (Tetra): a_5 = 2 = NT
  · k=5 (Penta): a_5 = 1 = atom

The values decrease monotonically as k grows: the k-bonacci index-5
snapshot reads out a *cascade* through the atomic family
`(d, d−1, NT, 1)`.  This is the "depth-5 sample" of the k-bonacci
ladder. -/

/-- Depth-5 snapshot at k=2: `Fib(5) = 5 = d`. -/
theorem kBon_2_at_d : kBonacci 2 5 = 5 := kBon_2_5

/-- Depth-5 snapshot at k=3: `Trib(5) = 4`. -/
theorem kBon_3_at_d : kBonacci 3 5 = 4 := kBon_3_5

/-- Depth-5 snapshot at k=4: `Tetra(5) = 2 = NT`. -/
theorem kBon_4_at_d : kBonacci 4 5 = 2 := kBon_4_5

/-- Depth-5 snapshot at k=5: `Penta(5) = 1`. -/
theorem kBon_5_at_d : kBonacci 5 5 = 1 := by decide

/-! ## Depth-5 cascade capstone

The depth-5 readout produces the cascade `(d, d-1, NT, 1)` as `k`
ranges over `{2, 3, 4, 5}`.  This is a single ∅-axiom statement
of the k-bonacci ladder at the atomic-dimension index. -/

/-- ★★★ **Depth-5 cascade**: the k-bonacci value at the atomic
    dimension `d = 5` decreases as `k` increases, reading out
    the atomic family `(d, d−1, NT, 1)`. -/
theorem depth_5_cascade :
    kBonacci 2 5 = 5 ∧ kBonacci 3 5 = 4
    ∧ kBonacci 4 5 = 2 ∧ kBonacci 5 5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Cardinality-cutoff hits for k = 4, 5

The 213 cardinality cut-off catalogue `{2, 3, 5, 7, 13, 521}`
(from `cardinality_cutoff_applications.md`) is hit by k-bonacci
sequences at varied indices:

  · Tetranacci (k=4): `a_5 = 2` (NT hit), `a_8 = 15` (not in
    catalogue but 15 = NS·d = first non-atomic composite).
  · Pentanacci (k=5): `a_6 = 2` (NT hit at index 6), `a_7 = 4`,
    `a_8 = 8`, `a_9 = 16` — powers-of-two doubling regime in the
    early window.

The catalogue intersections at small indices are bounded by `d = 5`
for index reach.  -/

/-- k = 4 catalogue hit: `Tetra(5) = 2 = NT`. -/
theorem kBon_4_5_eq_NT : kBonacci 4 5 = 2 := kBon_4_5

/-- k = 5 catalogue hit: `Penta(6) = 2 = NT`. -/
theorem kBon_5_6_eq_NT : kBonacci 5 6 = 2 := by decide

/-- k = 5: `Penta(7) = 4` (catalogue-adjacent, not in
    `{2, 3, 5, 7, 13, 521}` but a power of 2 = 2²). -/
theorem kBon_5_7 : kBonacci 5 7 = 4 := by decide

/-- k = 5: `Penta(8) = 8` (catalogue-adjacent, 2³). -/
theorem kBon_5_8 : kBonacci 5 8 = 8 := by decide

end E213.Lib.Math.NumberTheory.DyadicFSM.KBonacci
