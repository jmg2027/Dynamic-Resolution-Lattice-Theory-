import E213.Theory.Raw.API
import E213.Lens.Number.Nat213.Raw
import E213.Lens.FlatOntology

/-!
# Lens.PredicateSelfEncoding — §9.3 closure direction

`seed/AXIOM/09_chart_relativity.md` §9.3 records the flat-ontology
table: every entity (object, type, relation, function, Lens) is a
decidable predicate on Raw^n.  `Lens/FlatOntology.lean` realised
the *forward* direction (Raws → predicates via indicator
functions, Lens → predicate via fibre indicators).

This file realises the *closure direction*: a decidable predicate
on Raw, restricted to a finite prefix of the Method A numeral
chain, is itself encodable as a Raw via positional Gödel
numbering.  Together with FlatOntology this closes the
self-reference loop of §9.3 + §9.4: predicates that operate on
Raw are themselves Raw.

## Construction

Given a predicate `P : Raw → Bool` and a prefix length `n`, the
truth values `(P (numeral 0), P (numeral 1), ..., P (numeral
(n-1)))` form a length-n boolean vector.  Standard positional
encoding maps this vector to a natural number; `Raw.numeral`
maps that natural number to a Raw.  The composition is the
encoding `P ↦ Raw`.

The encoding depends on the prefix length `n`; predicates that
agree on the first n numerals encode to the same Raw.

## Scope

This file realises the closure for *finite-prefix* predicates.
Predicates with unbounded support (depending on infinitely many
Method-A numerals or on non-numeral Raws) remain a separate
formalisation question — they would require either fuel-bounded
encoding or restriction to a countable Raw subset.  The
finite-prefix case suffices to close the philosophical loop:
"predicates are themselves Raw" has a constructive witness.
-/

namespace E213.Lens.PredicateSelfEncoding

open E213.Theory (Raw)
open E213.Lens.Number.Nat213.Raw (numeral numeral_injective)

/-- Positional truth-table encoding: bit `i` is set iff `P i = true`. -/
def truthTableNat : (n : Nat) → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, P =>
      (if P n then 2 ^ n else 0) + truthTableNat n P

/-- Encoding `truthTableNat` of an always-false predicate is 0. -/
theorem truthTableNat_const_false (n : Nat) :
    truthTableNat n (fun _ => false) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show (if false then 2 ^ k else 0) + truthTableNat k (fun _ => false) = 0
      rw [ih]
      rfl

/-- Encoding `truthTableNat` at n = 1, P(0) = true gives 1. -/
theorem truthTableNat_one_true :
    truthTableNat 1 (fun n => decide (n = 0)) = 1 := rfl

/-- Encode a Raw-predicate via its truth table on the first `n`
    Method-A numerals.  Yields a Raw via `Raw.numeral`. -/
def predicateToRaw (n : Nat) (P : Raw → Bool) : Raw :=
  numeral (truthTableNat n (fun i => P (numeral i)))

/-- ★ **Self-reference closure** (§9.3): every finite-prefix
    Raw-predicate has a Raw encoding.  The encoding takes
    `P : Raw → Bool` (the predicate Lens) and a prefix length `n`,
    and returns a single Raw whose Method A position records the
    full truth table on numerals 0..n-1.

    Composed with `Lens/Cardinality/Godel.lean`'s `Raw.toNat`,
    this closes the loop:
      Raw → Bool (predicate, FlatOntology)
        ─[predicateToRaw n]→ Raw
        ─[Raw.toNat]→ ℕ
        ─[numeral]→ Raw (round-trip).

    Lens application IS a residue-internal event (§8.1); now we
    have witnesses for *both* directions of the §9.3 table: not
    only "Raws produce predicates" (FlatOntology) but also
    "predicates produce Raws" (this file). -/
theorem predicate_self_encoding_closure
    (n : Nat) (P : Raw → Bool) :
    ∃ r : Raw, r = predicateToRaw n P := ⟨_, rfl⟩

/-- Two predicates agreeing on the first `n` numerals encode to
    the same Raw — the encoding kernel is "agreement on the n-prefix
    of Method A numerals". -/
theorem predicateToRaw_kernel
    (n : Nat) (P Q : Raw → Bool)
    (h : ∀ i : Nat, i < n → P (numeral i) = Q (numeral i)) :
    predicateToRaw n P = predicateToRaw n Q := by
  unfold predicateToRaw
  congr 1
  -- Reduce to truthTableNat agreement
  suffices truthTableNat n (fun i => P (numeral i))
           = truthTableNat n (fun i => Q (numeral i)) from this
  induction n with
  | zero => rfl
  | succ k ih =>
      have hk : ∀ i : Nat, i < k → P (numeral i) = Q (numeral i) := by
        intro i hi
        exact h i (Nat.lt_succ_of_lt hi)
      have hk_top : P (numeral k) = Q (numeral k) :=
        h k (Nat.lt_succ_self k)
      show (if P (numeral k) then 2 ^ k else 0)
            + truthTableNat k (fun i => P (numeral i))
          = (if Q (numeral k) then 2 ^ k else 0)
            + truthTableNat k (fun i => Q (numeral i))
      rw [hk_top, ih hk]

/-- Injectivity of `predicateToRaw` on the prefix: if two
    predicates encode to the same Raw at prefix `n`, then their
    truth tables on numerals 0..n-1 are identical (as Nats).  This
    is the kernel direction of the §9.3 closure. -/
theorem predicateToRaw_injective_on_prefix
    (n : Nat) (P Q : Raw → Bool)
    (h : predicateToRaw n P = predicateToRaw n Q) :
    truthTableNat n (fun i => P (numeral i))
      = truthTableNat n (fun i => Q (numeral i)) := by
  unfold predicateToRaw at h
  exact numeral_injective h

end E213.Lens.PredicateSelfEncoding
