import E213.Meta.Nat.PureNat
import E213.Meta.Tactic.List213

/-!
# Convolution213 — split-then-reglue: an operation off the `+×^` diagonal

`CoAppend213` gave the **co-operation** dual of gluing: `splits` (cut one
into two).  **Convolution** is the composite *split-then-reglue*: to
combine two **sequences** `f, g : ℕ → ℕ`, split the index `n` every way
(`natSplits n` = all `(i, j)` with `i + j = n`), multiply the pieces
`f i · g j`, and reglue by summing:

  `conv f g n = Σ_{i + j = n} f i · g j`.

This is the **Cauchy / generating-function product** — polynomial
multiplication.  It is genuinely **off the `+×^` diagonal**: the
hyperoperation tower combines two *numbers*; `conv` combines two
*sequences*, via the comultiplication, and lands a new sequence.  The
concrete witness `(1 + x)² = 1 + 2x + x²` is `conv` of the coefficient
sequence `[1,1]` with itself, read off as `[1, 2, 1, 0, …]`
(`conv_sq_0 … conv_sq_3`) — split-then-reglue computing a polynomial
product, no `^` rung involved.

`natSplits` is the ℕ shadow of `CoAppend213.splits` (cuts of `fromNat n`,
read through `count`): `natSplits_sound` — every split sums to `n` (the
`+`-witness, the inverse question); `length_natSplits` — `n + 1` cuts.

Open continuation (the operation's laws): `conv` is **commutative** —
because `natSplits n` is symmetric under reversing a cut `(i,j) ↦ (j,i)`
(the same "commutativity from a swap symmetry" as `+`/append and `×`/grid,
one level up on sequences) — and **associative** (triple splits); both
need sum-permutation-invariance (a heavier list-sum lemma), recorded on the
frontier.

All ∅-axiom; bare recursion / `List.Mem` with PURE `List213` helpers, and
`rfl` computation on the concrete witnesses.
-/

namespace E213.Meta.Nat.Convolution213

open E213.Tactic.List213 (length_map exists_of_mem_map)

/-- The ℕ comultiplication: every cut `(i, j)` of `n`, i.e. `i + j = n`.
    The count shadow of `CoAppend213.splits`. -/
def natSplits : Nat → List (Nat × Nat)
  | 0     => [(0, 0)]
  | n + 1 => (0, n + 1) :: (natSplits n).map (fun p => (p.1 + 1, p.2))

/-- ★ Every split sums to `n` — a cut IS a `+`-witness `i + j = n` (the
    inverse question), the `natSplits` shadow of `CoAppend213.mem_splits_iff`. -/
theorem natSplits_sound :
    ∀ (n : Nat) (p : Nat × Nat), p ∈ natSplits n → p.1 + p.2 = n
  | 0,     _, h => by
      cases h with
      | head      => rfl
      | tail _ h' => nomatch h'
  | n + 1, _, h => by
      cases h with
      | head => exact Nat.zero_add _
      | tail _ h' =>
          obtain ⟨q, hq, hqe⟩ := exists_of_mem_map h'
          subst hqe
          show (q.1 + 1) + q.2 = n + 1
          rw [Nat.add_right_comm, natSplits_sound n q hq]

/-- ★ The co-operation's size: `n + 1` cuts (dual to the single-number
    `count`). -/
theorem length_natSplits : ∀ n : Nat, (natSplits n).length = n + 1
  | 0     => rfl
  | n + 1 => by
      show ((natSplits n).map (fun p => (p.1 + 1, p.2))).length + 1 = (n + 1) + 1
      rw [length_map, length_natSplits n]

/-- Sum a function over a list of cuts (the reglue). -/
def sumMap (h : Nat × Nat → Nat) : List (Nat × Nat) → Nat
  | []     => 0
  | p :: l => h p + sumMap h l

/-- ★★ **Convolution = split-then-reglue.**  `conv f g n = Σ_{i+j=n} f i·g j`
    — split the index every way (`natSplits`), multiply the pieces, reglue
    (`sumMap`).  The Cauchy / generating-function product; a new operation
    combining two *sequences*, off the `+×^` (number) diagonal. -/
def conv (f g : Nat → Nat) (n : Nat) : Nat :=
  sumMap (fun p => f p.1 * g p.2) (natSplits n)

/-- The base coefficient: `conv f g 0 = f 0 · g 0` (the only cut of `0` is
    `(0,0)`). -/
theorem conv_zero (f g : Nat → Nat) : conv f g 0 = f 0 * g 0 := rfl

/-- Coefficient lookup: the `i`-th entry of a finite coefficient list, `0`
    past the end (a polynomial as a sequence). -/
def nth : List Nat → Nat → Nat
  | [],      _     => 0
  | a :: _,  0     => a
  | _ :: l,  i + 1 => nth l i

/-- The polynomial `1 + x` as a coefficient sequence `[1, 1, 0, 0, …]`. -/
def onePlusX : Nat → Nat := nth [1, 1]

/-- ★ `(1+x)² = 1 + 2x + x²` by convolution — coefficient `[0]`. -/
theorem conv_sq_0 : conv onePlusX onePlusX 0 = 1 := rfl
/-- coefficient `[1]` = `2` (the cross terms `f0·g1 + f1·g0`). -/
theorem conv_sq_1 : conv onePlusX onePlusX 1 = 2 := rfl
/-- coefficient `[2]` = `1` (`f1·g1`). -/
theorem conv_sq_2 : conv onePlusX onePlusX 2 = 1 := rfl
/-- coefficient `[3]` = `0` (past the polynomial's degree). -/
theorem conv_sq_3 : conv onePlusX onePlusX 3 = 0 := rfl

end E213.Meta.Nat.Convolution213
