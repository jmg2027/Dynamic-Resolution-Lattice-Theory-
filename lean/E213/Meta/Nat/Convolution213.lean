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

`conv` is **commutative** (`conv_comm`) — because the cut `(0, n)` of one
order is the cut `(n, 0)` of the other (the reverse-a-cut symmetry of
`natSplits`): peel the *left* end of `conv f g` and the *right* end of
`conv g f` and the recursion folds the rest, no full sum-permutation lemma
needed.  This is the same "commutativity from a swap symmetry" as `+`
(append) and `×` (grid transpose), one rung up on **sequences**.
Associativity (`conv_assoc`, the triple split) descends from the **coassociativity**
of the same cut comultiplication `natSplits` — `+`/`×`/`conv` are the three rungs of
"comm/assoc are shadows of a comultiplication swap symmetry".

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

/-! ## Commutativity — from the swap symmetry of the cuts (peel both ends) -/

/-- Shift a sequence left: `shiftL f i = f (i+1)` (drop the constant term). -/
def shiftL (f : Nat → Nat) : Nat → Nat := fun i => f (i + 1)

/-- Sum over a mapped list: `sumMap h (l.map k) = sumMap (h ∘ k) l`. -/
theorem sumMap_map (h : Nat × Nat → Nat) (k : Nat × Nat → Nat × Nat) :
    ∀ l : List (Nat × Nat), sumMap h (l.map k) = sumMap (fun p => h (k p)) l
  | []     => rfl
  | p :: l => by
      show h (k p) + sumMap h (l.map k) = h (k p) + sumMap (fun q => h (k q)) l
      rw [sumMap_map h k l]

/-- ★ **Left peel** — split off the `i = 0` cut.  `conv f g (n+1) =
    f 0 · g(n+1) + conv (shiftL f) g n`; matches `natSplits`' left-build. -/
theorem conv_peelL (f g : Nat → Nat) (n : Nat) :
    conv f g (n + 1) = f 0 * g (n + 1) + conv (shiftL f) g n := by
  show f 0 * g (n + 1)
       + sumMap (fun p => f p.1 * g p.2) ((natSplits n).map (fun p => (p.1 + 1, p.2)))
     = f 0 * g (n + 1) + conv (shiftL f) g n
  rw [sumMap_map]
  rfl

/-- ★ **Right peel** — split off the `j = 0` cut.  `conv f g (n+1) =
    f(n+1) · g 0 + conv f (shiftL g) n`; the other end, by induction on `n`
    from the left peel. -/
theorem conv_peelR (f g : Nat → Nat) :
    ∀ n : Nat, conv f g (n + 1) = f (n + 1) * g 0 + conv f (shiftL g) n
  | 0     => by
      show f 0 * g 1 + (f 1 * g 0 + 0) = f 1 * g 0 + (f 0 * g 1 + 0)
      rw [Nat.add_zero, Nat.add_zero, Nat.add_comm (f 0 * g 1) (f 1 * g 0)]
  | n + 1 => by
      rw [conv_peelL f g (n + 1), conv_peelR (shiftL f) g n,
          conv_peelL f (shiftL g) n]
      exact Nat.add_left_comm _ _ _

/-- ★★ **Convolution commutes** — `conv f g n = conv g f n`.  Peel the
    *left* end of `conv f g` and the *right* end of `conv g f`: the cut
    `(0, n)` of one is the cut `(n, 0)` of the other (the reverse-a-cut
    symmetry of `natSplits`), the recursion folds the inner blocks, and
    `f 0 · g n = g n · f 0` closes the heads.  This is "commutativity from a
    swap symmetry" — append (`+`), grid transpose (`×`) — one rung up, on
    sequences. -/
theorem conv_comm : ∀ (f g : Nat → Nat) (n : Nat), conv f g n = conv g f n
  | f, g, 0     => by
      show f 0 * g 0 = g 0 * f 0
      exact Nat.mul_comm _ _
  | f, g, n + 1 => by
      rw [conv_peelL f g n, conv_peelR g f n, conv_comm (shiftL f) g n,
          Nat.mul_comm (f 0) (g (n + 1))]

/-! ## Bilinearity, and a concrete associativity witness `(1+x)³` -/

/-- Pointwise sum of sequences (the additive structure conv is bilinear over). -/
def addSeq (f g : Nat → Nat) : Nat → Nat := fun i => f i + g i

private theorem add4comm (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc, Nat.add_left_comm b c d, ← Nat.add_assoc]

/-- A summand `(u + v)·w` splits over the sum (`add_mul` under the reglue). -/
theorem sumMap_add_mul (u v w : Nat × Nat → Nat) :
    ∀ l : List (Nat × Nat),
      sumMap (fun p => (u p + v p) * w p) l
        = sumMap (fun p => u p * w p) l + sumMap (fun p => v p * w p) l
  | []     => rfl
  | p :: l => by
      show (u p + v p) * w p + sumMap (fun q => (u q + v q) * w q) l
         = (u p * w p + sumMap (fun q => u q * w q) l)
         + (v p * w p + sumMap (fun q => v q * w q) l)
      rw [E213.Meta.Nat.PureNat.add_mul, sumMap_add_mul u v w l, add4comm]

/-- ★ **Convolution is left-additive** (bilinearity, one side):
    `conv (f1 + f2) g = conv f1 g + conv f2 g` — the distributive law of the
    sequence ring, the comultiplication respecting the pointwise sum. -/
theorem conv_add_left (f1 f2 g : Nat → Nat) (n : Nat) :
    conv (addSeq f1 f2) g n = conv f1 g n + conv f2 g n :=
  sumMap_add_mul (fun p => f1 p.1) (fun p => f2 p.1) (fun p => g p.2) (natSplits n)

/-- ★ **`(1+x)³ = 1 + 3x + 3x² + x³` by repeated convolution.**  The
    left-nested triple convolution `conv (conv (1+x) (1+x)) (1+x)` reads off
    `[1, 3, 3, 1]` (`rfl`) — split-then-reglue computing a cube, no `^`. -/
theorem conv_cube_0 : conv (conv onePlusX onePlusX) onePlusX 0 = 1 := rfl
theorem conv_cube_1 : conv (conv onePlusX onePlusX) onePlusX 1 = 3 := rfl
theorem conv_cube_2 : conv (conv onePlusX onePlusX) onePlusX 2 = 3 := rfl
theorem conv_cube_3 : conv (conv onePlusX onePlusX) onePlusX 3 = 1 := rfl

/-- ★ **Associativity holds concretely**: the left- and right-nested triple
    convolutions of `(1+x)` agree coefficient-by-coefficient — both compute
    the `(1+x)³` coefficients `[1,3,3,1]` (`rfl`).  The general law is `conv_assoc`
    (the triple-split reindex); these are its concrete witnesses. -/
theorem conv_assoc_0 :
    conv (conv onePlusX onePlusX) onePlusX 0 = conv onePlusX (conv onePlusX onePlusX) 0 := rfl
theorem conv_assoc_1 :
    conv (conv onePlusX onePlusX) onePlusX 1 = conv onePlusX (conv onePlusX onePlusX) 1 := rfl
theorem conv_assoc_2 :
    conv (conv onePlusX onePlusX) onePlusX 2 = conv onePlusX (conv onePlusX onePlusX) 2 := rfl
theorem conv_assoc_3 :
    conv (conv onePlusX onePlusX) onePlusX 3 = conv onePlusX (conv onePlusX onePlusX) 3 := rfl

/-! ## Associativity — the triple split, from coassociativity of the cut comultiplication

`conv_comm` came from the cut-reversal swap symmetry; associativity comes from the
**coassociativity** of `natSplits` — cutting `n` into three pieces two ways enumerates the
same `{(i,j,k) : i+j+k = n}`.  Proven in the same end-peel style (no full sum-permutation
lemma), via a scalar pull-out and a pointwise congruence under the reglue. -/

/-- `sumMap` respects pointwise equality (no `funext`). -/
theorem sumMap_congr {h1 h2 : Nat × Nat → Nat} (he : ∀ p, h1 p = h2 p) :
    ∀ l : List (Nat × Nat), sumMap h1 l = sumMap h2 l
  | []     => rfl
  | p :: l => by
      show h1 p + sumMap h1 l = h2 p + sumMap h2 l
      rw [he p, sumMap_congr he l]

/-- Scalar pulls out of the reglue: `Σ c·h = c·Σ h`. -/
theorem sumMap_smul (c : Nat) (h : Nat × Nat → Nat) :
    ∀ l : List (Nat × Nat), sumMap (fun p => c * h p) l = c * sumMap h l
  | []     => by show (0 : Nat) = c * 0; rw [Nat.mul_zero]
  | p :: l => by
      show c * h p + sumMap (fun q => c * h q) l = c * (h p + sumMap h l)
      rw [sumMap_smul c h l, Nat.mul_add]

/-- ★ **Scalar linearity** of `conv` in the first argument:
    `conv (c·f) g = c · conv f g`. -/
theorem conv_smul_left (c : Nat) (f g : Nat → Nat) (n : Nat) :
    conv (fun i => c * f i) g n = c * conv f g n := by
  show sumMap (fun p => (c * f p.1) * g p.2) (natSplits n)
      = c * sumMap (fun p => f p.1 * g p.2) (natSplits n)
  rw [← sumMap_smul c (fun p => f p.1 * g p.2) (natSplits n)]
  exact sumMap_congr (fun p => E213.Meta.Nat.PureNat.mul_assoc c (f p.1) (g p.2)) (natSplits n)

/-- `conv` respects pointwise equality in the first argument (no `funext`). -/
theorem conv_congr_left {f1 f2 g : Nat → Nat} (he : ∀ i, f1 i = f2 i) (n : Nat) :
    conv f1 g n = conv f2 g n :=
  sumMap_congr (fun p => by rw [he p.1]) (natSplits n)

/-- ★★★ **Convolution associates** — `conv (conv f g) h n = conv f (conv g h) n`.  The triple
    split reindexes: peel the outer-left cut on both sides; the left nest's shifted head
    `shiftL (conv f g) = f0·(shiftL g) + conv (shiftL f) g` splits by bilinearity
    (`conv_add_left`) and scalar linearity (`conv_smul_left`), the inner block folds by
    induction, and the heads agree by `mul_assoc`.  This is the **coassociativity** of the cut
    comultiplication `natSplits` — the sequence-scale rung of "comm/assoc are shadows of a
    comultiplication swap symmetry", alongside `+` (`UnitList.append_comm`) and `×`
    (`UnitGrid.mul_comm_from_grid`). -/
theorem conv_assoc : ∀ (f g h : Nat → Nat) (n : Nat),
    conv (conv f g) h n = conv f (conv g h) n
  | f, g, h, 0     => by
      show conv f g 0 * h 0 = f 0 * conv g h 0
      rw [conv_zero, conv_zero]
      exact E213.Meta.Nat.PureNat.mul_assoc (f 0) (g 0) (h 0)
  | f, g, h, n + 1 => by
      rw [conv_peelL (conv f g) h n,
          conv_congr_left (f1 := shiftL (conv f g))
            (f2 := addSeq (fun i => f 0 * shiftL g i) (conv (shiftL f) g))
            (g := h) (fun i => conv_peelL f g i) n,
          conv_add_left, conv_smul_left, conv_assoc (shiftL f) g h, conv_zero,
          conv_peelL f (conv g h) n, conv_peelL g h n, Nat.mul_add,
          E213.Meta.Nat.PureNat.mul_assoc (f 0) (g 0) (h (n + 1))]
      exact (Nat.add_assoc _ _ _).symm

/-! ## The generating-function semiring — unit `δ` and right-bilinearity -/

/-- `sumMap` of the zero function is `0`. -/
theorem sumMap_zero : ∀ l : List (Nat × Nat), sumMap (fun _ => 0) l = 0
  | []     => rfl
  | _ :: l => by show 0 + sumMap (fun _ => 0) l = 0; rw [Nat.zero_add, sumMap_zero l]

/-- The unit sequence `δ = [1, 0, 0, …]` (the constant-`1` generating function). -/
def delta : Nat → Nat := nth [1]

/-- ★★ **`δ` is a left unit for `conv`**: `conv δ f = f`.  Only the cut `(0, n)` survives
    (`δ 0 = 1`); every cut with first part `≥ 1` is killed by `δ (i+1) = 0`. -/
theorem conv_delta_left (f : Nat → Nat) : ∀ n, conv delta f n = f n
  | 0     => by
      show delta 0 * f 0 = f 0
      rw [show delta 0 = 1 from rfl, Nat.one_mul]
  | n + 1 => by
      show delta 0 * f (n + 1)
          + sumMap (fun p => delta p.1 * f p.2) ((natSplits n).map (fun p => (p.1 + 1, p.2)))
        = f (n + 1)
      rw [sumMap_map,
          sumMap_congr (h2 := fun _ => 0)
            (fun p => by
              show delta (p.1 + 1) * f p.2 = 0
              rw [show delta (p.1 + 1) = 0 from rfl, Nat.zero_mul]) (natSplits n),
          sumMap_zero, show delta 0 = 1 from rfl, Nat.one_mul, Nat.add_zero]

/-- ★ **`δ` is a right unit**: `conv f δ = f` (by commutativity). -/
theorem conv_delta_right (f : Nat → Nat) (n : Nat) : conv f delta n = f n := by
  rw [conv_comm f delta, conv_delta_left]

/-- ★ **Right-additivity** (the other half of bilinearity), via commutativity. -/
theorem conv_add_right (f g1 g2 : Nat → Nat) (n : Nat) :
    conv f (addSeq g1 g2) n = conv f g1 n + conv f g2 n := by
  rw [conv_comm f (addSeq g1 g2), conv_add_left, conv_comm g1 f, conv_comm g2 f]

/-- ★★★ **`conv` is a commutative-monoid product with unit `δ`, bilinear over `addSeq`.**
    Together with `conv_assoc`/`conv_comm`/`conv_add_left`/`conv_add_right` and the unit laws,
    `(Nat → Nat, addSeq, conv, δ)` is the **generating-function commutative semiring** — the
    split-then-reglue product completed to its algebraic structure, ∅-axiom. -/
theorem conv_unit_comm_assoc (f : Nat → Nat) (n : Nat) :
    conv delta f n = f n ∧ conv f delta n = f n
    ∧ (∀ g, conv f g n = conv g f n) :=
  ⟨conv_delta_left f n, conv_delta_right f n, fun g => conv_comm f g n⟩

end E213.Meta.Nat.Convolution213
