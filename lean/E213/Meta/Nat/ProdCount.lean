import E213.Meta.Nat.UnitBox

/-!
# ProdCount — the multiplicative count-Lens, dual to the additive count

The additive generation built `+` as the count-shadow of `append` on `List Unit`:
`count : List Unit → Nat`, `count (l ++ m) = count l + count m`, and on
*indistinguishable* units `append_comm` is free, so the whole list collapses to a
single number — the count.

This file builds the **multiplicative dual**. The readout is
`prodL : List Nat → Nat` (the product of a list), the multiplicative count over a
list of *distinguishable* atoms. It is a homomorphism `append ↦ ·`
(`prodL_append`) — the exact dual of `count_append : append ↦ +` — and, because the
`×` it uses is *commutative* (the **generated** `UnitGrid.mul_comm_from_grid`), it is
invariant under reordering (`prodL_swap`): `prodL` factors through the **multiset**,
not the list.

The duality, made precise:
- additive units are **indistinguishable** → the list collapses to *one* number
  (`count`); there is one additive atom;
- multiplicative atoms (primes) are **distinguishable** → the list collapses only to
  its *multiset* — the count of *each* distinct atom, i.e. the exponent vector
  (`prodL (replicate k p) = p^k` reads one prime's exponent; a mixed list keeps one
  exponent per prime). That the multiset is the invariant is exactly **unique
  factorization** (`Lib/Math/NumberTheory/FTAUniqueness.factorization_unique`).

Built on the *generated* semiring laws (`mul_assoc`/`mul_comm`), so this stays inside
the generation program. ∅-axiom.
-/

namespace E213.Meta.Nat.ProdCount

open E213.Meta.Nat.UnitGrid (replicate mul_comm_from_grid)
open E213.Meta.Nat.UnitBox (mul_assoc_from_box)

/-- The multiplicative count: product of a `Nat` list (`prodL [] = 1`,
    `prodL (p :: l) = p · prodL l`). The `×`-dual of `UnitList.count`. -/
def prodL : List Nat → Nat
  | []     => 1
  | p :: l => p * prodL l

/-- ★★★★ **The multiplicative count homomorphism**: `prodL (l ++ m) =
    prodL l · prodL m` — the exact dual of `count_append : append ↦ +`. Built on
    the *generated* `mul_assoc` (`UnitBox.mul_assoc_from_box`), not `Nat.mul_assoc`. -/
theorem prodL_append : ∀ (l m : List Nat), prodL (l ++ m) = prodL l * prodL m
  | [],     m => (Nat.one_mul (prodL m)).symm
  | p :: l, m => by
      show p * prodL (l ++ m) = (p * prodL l) * prodL m
      rw [prodL_append l m, mul_assoc_from_box]

/-- ★★★★ **`prodL` is reorder-invariant** at the head (the multiset, not the list
    order, is what `prodL` sees): `prodL (a :: b :: l) = prodL (b :: a :: l)`. The
    multiplicative dual of `append_comm`; it is generated from the *generated*
    `×`-commutativity + `×`-associativity, not `Nat.mul_*`. -/
theorem prodL_swap (a b : Nat) (l : List Nat) :
    prodL (a :: b :: l) = prodL (b :: a :: l) := by
  show a * (b * prodL l) = b * (a * prodL l)
  rw [← mul_assoc_from_box, ← mul_assoc_from_box, mul_comm_from_grid a b]

/-- ★★★ **One distinguishable prime reads its exponent**: `prodL (replicate k p) =
    p ^ k`. The indistinguishable-*within-one-prime* case — `k` copies of the single
    atom `p` collapse to the single exponent `k`. (A *mixed* list keeps one exponent
    per distinct prime — the exponent vector — which is where `×` outgrows `+`.) -/
theorem prodL_replicate (p : Nat) : ∀ (k : Nat), prodL (replicate k p) = p ^ k
  | 0     => rfl
  | k + 1 => by
      show p * prodL (replicate k p) = p ^ (k + 1)
      rw [prodL_replicate p k]
      show p * p ^ k = p ^ k * p
      exact mul_comm_from_grid p (p ^ k)

/-! ## The duality: distinguishability is the *only* difference

Two blocks, one construction (`replicate j _ ++ replicate k _`), read two ways. The
additive count *merges* them into one number; the multiplicative count keeps them
*separate as an exponent vector* — **iff the two atoms are distinguishable**. Make the
atoms indistinguishable (`p = q`) and the multiplicative count merges too, recovering
the additive behaviour exactly. Distinguishability of the atoms is the sole source of
`×`'s extra structure over `+`. -/

/-- **Distinguishable atoms keep their exponent vector**: a `j`-block of `p` and a
    `k`-block of `q` multiply to `p^j · q^k` — the pair `(j, k)` survives (recoverable
    when `p ≠ q`). The multiplicative dual of `count (fromNat j ++ fromNat k) = j + k`,
    where the additive blocks *merge* into the single number `j + k` because the
    units are indistinguishable. -/
theorem prodL_two_atoms (j k p q : Nat) :
    prodL (replicate j p ++ replicate k q) = p ^ j * q ^ k := by
  rw [prodL_append, prodL_replicate, prodL_replicate]

/-- `p^(m+n) = p^m · p^n`, hand-rolled ∅-axiom on the *generated* `mul_assoc`
    (core `Nat.pow_add` leaks `propext`). -/
theorem pow_add (p : Nat) : ∀ (m n : Nat), p ^ (m + n) = p ^ m * p ^ n
  | m, 0     => by show p ^ m = 0 + p ^ m; rw [Nat.zero_add]
  | m, n + 1 => by
      show p ^ (m + n) * p = p ^ m * (p ^ n * p)
      rw [pow_add p m n, mul_assoc_from_box]

/-- **Indistinguishable atoms merge** (the duality's punchline): set `q = p` and the
    multiplicative count collapses to a *single* exponent `p^(j+k)` — exactly the
    additive `j + k` behaviour, one fold up. So `×` is `+` whenever its atoms are made
    indistinguishable; the entire excess of `×` over `+` (the exponent *vector*, hence
    unique factorization) is the *distinguishability* of primes. -/
theorem prodL_one_atom_merges (j k p : Nat) :
    prodL (replicate j p ++ replicate k p) = p ^ (j + k) := by
  rw [prodL_two_atoms, ← pow_add]

end E213.Meta.Nat.ProdCount
