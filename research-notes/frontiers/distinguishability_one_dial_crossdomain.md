# Distinguishability is the one dial — cross-domain insights

Cross-domain insights connecting this session's new work (the generation program,
the completion-engine criterion, the +/× duality) to the pre-existing corpus. Recorded
per the marathon's cross-domain step; the strongest seeds the `/essay`.

## ★ The single dial: distinguishability governs arity, commutativity, AND the +/× gap

Three phenomena across three "domains" turn out to be **one parameter** — whether the
atoms being related are *distinguishable*:

1. **Arity-2 forcing** (`Theory/Atomicity/ArityForcingComplete.arity_two_forced`, new):
   the relation arity is forced to 2 because the step relates *distinct* positions
   (the clause-4 distinctness gate `i ≠ j → f i ≠ f j`). Below arity 2 there are no two
   distinct positions — the relation distinguishes nothing.
2. **Commutativity** (`UnitList.append_comm` vs `append_not_comm_general`, corpus +
   extended this session): on *indistinguishable* units append commutes (arrangement is
   no information); on *distinguishable* elements it does not (`[a]++[b] ≠ [b]++[a]`).
3. **The +/× gap** (`Meta/Nat/ProdCount.prodL_one_atom_merges`, new): `×` *is* `+`
   when its atoms are made indistinguishable (`p^(j+k)` = the additive `j+k`); the
   entire excess of `×` (the exponent vector, hence FTA) is exactly the
   *distinguishability* of primes.

So **one dial — atom distinguishability — runs the whole show**: turn it off and
everything collapses to counting (commutative `+`, no arity structure beyond 2,
factorization merges to a single exponent); turn it on and structure appears (genuine
relations, non-commutativity, the exponent vector, unique factorization). This unifies
the failure-mode catalog's "Count-Lens import as Raw" (indistinguishable → `2` is a
count), the `where_commutativity_is_born` essay (commutativity dies where the object
stops being symmetric), and the new generation boundary (FTA needs distinguishable
×-atoms) as **one principle at three resolutions**. (Essay target.)

## The completion-engine criterion gives the descent leg a mechanical referent

The corpus's `the_descent_leg.md` calls itself "the true spine — generation not
re-derivation," but its diagnosis ("96% of `Lib/Math` imports neither Raw nor Lens")
was a *count*, not a *criterion*. This session's **completion-engine criterion** (does
a proof cone's recursion complete through the distinguishing's own structural descent,
or the borrowed `Nat.strongRecOn`?) gives it a sharp, falsifiable form — and the
finding that `Nat213 := {n : Nat // 1 ≤ n}` is a `Nat` *subtype* (so it inherits `Nat`'s
well-foundedness) shows even the flagship FTA-over-`Nat213` does **not** pass the strict
test. The descent-leg's honest "recognition not genesis" wall is now mechanical.

## The +/× duality is the carrier-level home of the count-Lens essays

The corpus's `multiplicativity_is_the_x_count_lens` and
`addition_and_multiplication_are_two_faces_of_one_count` state that `+` and `×` are two
faces of one count-Lens (`vp`: `vp_mul` adds, `vp_add_eq_min` minimizes). This session's
`ProdCount` gives the **object-level** realization: `+` = `count` on `List Unit`
(indistinguishable), `×` = `prodL` on lists of distinguishable atoms, both `append`-
homomorphisms (`count_append : append↦+`, `prodL_append : append↦×`), the difference
being exactly which atoms. The function-level essays are the shadow of this
carrier-level duality.

## §5.2 Bool-vs-Nat self-reference, operationalized

Seed `05_no_exterior.md` §5.2 distinguishes Bool-style (oscillation, no fixed point) vs
Nat-style (Lambek, completes) self-reference as the *form* of completion. The
completion-engine criterion is its operational use: "generation" = the cone completes
Nat-style on the distinguishing's *own* descent (`MuNuMirror.isPart_wf`), not Bool-style
and not on a borrowed engine. The abstract taxonomy becomes a decidable test.

## Cross-refs

- `research-notes/frontiers/the_genesis_seam.md` — the program these connect to
- `theory/math/numbersystems/arithmetic_generation.md` — the promoted chapter
- `research-notes/frontiers/the_descent_leg.md` — the spine the criterion sharpens
