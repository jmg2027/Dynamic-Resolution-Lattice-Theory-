import E213.Lib.Math.Combinatorics.PowerSums
import E213.Meta.Nat.PolyNatMTactic

/-!
# Pentagonal figurate numbers and their cross-relations (∅-axiom)

The figurate **pentagonal** number `Pent n = n(3n−1)/2` (1, 5, 12, 22, 35, …,
OEIS A000326) is genuinely absent from the corpus: every existing `pentagonal`
hit is either Euler's *partition* pentagonal-number theorem
(`Combinatorics/PartitionNumbers.lean`) or the Möbius mod-5 rotation closure
(`Geometry/Rotation.lean`, `Foundations/C2DoublingDerivation.lean`) — different
objects.  The elementary figurate identities `8T+1=□`, `T n + T(n+1)=□`,
`Hex = T`, `Σ T = tetrahedral` already live in
`Combinatorics/TriangularNumbers.lean`; this file adds the missing
*pentagonal* layer.

All in division-free, subtraction-free (`+1`-shifted) form, closed by `ring_nat`.

  * `pent2`/`tri2`/`tri2'`/`gen2` : `2·Pent(n+1)`, `2·T(n+1)`, `2·T(n)`, `2·g(n)`.
  * ★ `pent2_eq_tri`  : `Pent2 n = tri2 n + 2·tri2'(n)` — pentagonal = triangular
                        plus twice the previous triangular.
  * ★ `pent2_succ`    : gnomon recurrence `Pent2 (n+1) = Pent2 n + (6n+8)`.
  * ★ `pent2_eq_3tri` : `Pent2 n = 3·tri2' n + 2(n+1)` — `Pent(n+1) = 3·T n + (n+1)`.
  * ★ `pent2_square`  : `12·Pent2 n + 1 = (6n+5)²` — the pentagonal companion of `8T+1=□`.
  * ★ `pent2_add_tri_eq_hex` : `Pent(n+1) + T n = Hex(n+1)`.
  * ★ `gen2_succ_eq_pent2`   : generalized-pentagonal `±`-branch step.
  * ★ `sum_pent2`     : `Σ_{k≤n} Pent2(k) = (n+1)²(n+2)` (sum of pentagonals).

∅-axiom (no `omega`, no Mathlib, `ring_nat` + structural induction).
-/

namespace E213.Lib.Math.Combinatorics.PentagonalNumbers

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)

/-- `2·Pent(n+1)` in subtraction-free shifted form: `Pent2 n = (n+1)(3n+2) = 3n²+5n+2`.
    (`Pent(n+1) = (n+1)(3(n+1)−1)/2`; doubling and shifting clears both div and sub.) -/
def pent2 (n : Nat) : Nat := (n + 1) * (3 * n + 2)

/-- `2·triangular(n+1) = (n+1)(n+2)`. -/
def tri2 (n : Nat) : Nat := (n + 1) * (n + 2)

/-- `2·triangular(n) = n(n+1)` (the "previous" triangular for the pentagonal split). -/
def tri2' (n : Nat) : Nat := n * (n + 1)

/-- ★ **Pentagonal = triangular + twice previous triangular**:
    `Pent2 n = tri2 n + 2·tri2'(n)` i.e. `2·Pent(n+1) = 2·T(n+1) + 2·(2·T n)`. -/
theorem pent2_eq_tri (n : Nat) : pent2 n = tri2 n + 2 * tri2' n := by
  show (n + 1) * (3 * n + 2) = (n + 1) * (n + 2) + 2 * (n * (n + 1))
  ring_nat

/-- ★ **Pentagonal gnomon recurrence**: `Pent2 (n+1) = Pent2 n + (6n+8)`.
    (`Pent(n+2) − Pent(n+1) = 3n+4`, doubled `6n+8`; the figurate gnomon.) -/
theorem pent2_succ (n : Nat) : pent2 (n + 1) = pent2 n + (6 * n + 8) := by
  show (n + 1 + 1) * (3 * (n + 1) + 2) = (n + 1) * (3 * n + 2) + (6 * n + 8)
  ring_nat

/-- ★ **Pentagonal = `3·triangular + (n+1)`** (subtraction-free):
    `Pent2 n = 3·tri2' n + 2(n+1)`, i.e. `Pent(n+1) = 3·T n + (n+1)` —
    three triangles plus the apex row. -/
theorem pent2_eq_3tri (n : Nat) : pent2 n = 3 * tri2' n + 2 * (n + 1) := by
  show (n + 1) * (3 * n + 2) = 3 * (n * (n + 1)) + 2 * (n + 1)
  ring_nat

/-- **Generalized pentagonal** `g(n) = n(3n+1)/2` (the "+" branch), doubled:
    `Gen2 n = n(3n+1)`.  Together with `pent2` these are the generalized pentagonal
    numbers `0,1,2,5,7,12,15,…` of Euler's theorem — here as the *figurate* pair. -/
def gen2 (n : Nat) : Nat := n * (3 * n + 1)

/-- ★ **Generalized-pentagonal split**: `Gen2 n = pent2' n` where the "+"-branch
    equals the "−"-branch at the next index minus a linear gnomon:
    `Gen2 (n+1) = pent2 n + (2n+2)` (the consecutive generalized-pentagonal step). -/
theorem gen2_succ_eq_pent2 (n : Nat) : gen2 (n + 1) = pent2 n + (2 * n + 2) := by
  show (n + 1) * (3 * (n + 1) + 1) = (n + 1) * (3 * n + 2) + (2 * n + 2)
  ring_nat

/-- ★ **Square-pentagonal `8·T+1` analogue**: `12·Pent2 n + 1 = (6n+5)²`.
    Classically `24·Pent(m) + 1 = (6m−1)²`; with `pent2 n = 2·Pent(n+1)` this is
    `12·pent2 n + 1 = (6(n+1)−1)² = (6n+5)²` — the pentagonal companion of `8T+1=□`. -/
theorem pent2_square (n : Nat) :
    12 * pent2 n + 1 = (6 * n + 5) * (6 * n + 5) := by
  show 12 * ((n + 1) * (3 * n + 2)) + 1 = (6 * n + 5) * (6 * n + 5)
  ring_nat

/-- ★ **Pentagonal + previous triangular = hexagonal**:
    `Pent2 n + tri2' n = 2·hex(n+1)` where `hex(m) = m(2m−1)`, i.e.
    `Pent(n+1) + T n = Hex(n+1) = (n+1)(2n+1)`.  (Both sides doubled:
    `(n+1)(3n+2) + n(n+1) = 2·(n+1)(2n+1)`.) -/
theorem pent2_add_tri_eq_hex (n : Nat) :
    pent2 n + tri2' n = 2 * ((n + 1) * (2 * n + 1)) := by
  show (n + 1) * (3 * n + 2) + n * (n + 1) = 2 * ((n + 1) * (2 * n + 1))
  ring_nat

/-- ★ **Sum of pentagonal numbers** (figurate, division-free): since `pent2 = 2·Pent`,
    this is `2·Σ_{k=1}^{n+1} Pent(k) = (n+1)²(n+2)`, i.e. `Σ Pent = (n+1)²(n+2)/2`.
    Induction on the `sumTo` recurrence, gnomon closed by `ring_nat`. -/
theorem sum_pent2 (n : Nat) :
    sumTo (n + 1) (fun k => pent2 k) = (n + 1) * (n + 1) * (n + 2) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumTo_succ, ih]
    show (k + 1) * (k + 1) * (k + 2) + pent2 (k + 1)
        = (k + 1 + 1) * (k + 1 + 1) * (k + 1 + 2)
    show (k + 1) * (k + 1) * (k + 2) + (k + 1 + 1) * (3 * (k + 1) + 2)
        = (k + 1 + 1) * (k + 1 + 1) * (k + 1 + 2)
    ring_nat

/-! ## Smoke tables (closed numerals, `decide`, axiom-clean) -/

/-- `Pent(1..5) = 1,5,12,22,35` via `pent2 = 2·Pent`: `pent2 0..4 = 2,10,24,44,70`. -/
theorem pent_smoke :
    pent2 0 = 2 ∧ pent2 1 = 10 ∧ pent2 2 = 24 ∧ pent2 3 = 44 ∧ pent2 4 = 70 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- `12·pent2 2 + 1 = 12·24 + 1 = 289 = 17² = (6·2+5)²`. -/
theorem pent2_square_smoke : 12 * pent2 2 + 1 = (6 * 2 + 5) * (6 * 2 + 5) := by decide

/-- `Σ_{k≤3} pent2 k = 2+10+24+44 = 80 = 4²·5 = (3+1)²(3+2)`. -/
theorem sum_pent_smoke : sumTo 4 (fun k => pent2 k) = 80 := by decide

end E213.Lib.Math.Combinatorics.PentagonalNumbers
