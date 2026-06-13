# 3 · The witness layer — every property forgotten

The pair construction of chapter 2 used `+`.  Nothing about it was
special to `+`.  This chapter rebuilds the pair layer for an
**arbitrary** operation `f : ℕ → ℕ → ℕ` — tetration included — and,
crucially, *forgets every algebraic property while doing so*.  What
forces what?  Where exactly does each familiar property earn its
keep?  (`Meta/Nat/PairOp.lean` throughout.)

## Step zero: the question bifurcates

With no commutativity, `f a x = b` and `f x a = b` are **different
questions** — there are two pair kinds from the start.
Commutativity's first job, before any relation or lift exists, is
fusing them (`question_fuse`).  For exponentiation the two kinds
never fuse: they are the root and the logarithm.  The famous
root/log split is a step-zero phenomenon.

## The witness relation is the original; the cross-equation is a shadow

When do two pairs point at the same thing?  The honest, property-free
answer: when **one witness solves both questions** —

> `sameWitness f (a,b) (c,d)  :=  ∃x, f a x = b ∧ f c x = d`.

This costs nothing to state, is symmetric for free, and is reflexive
exactly where a witness exists (`sameWitness_symm`,
`sameWitness_refl`) — that "exactly where" is itself information: the
witnessed pairs are the old layer sitting inside the new one.

The cross-equation `f a d = f c b` — the thing every chapter so far
used — turns out to be this relation's **shadow**, and the shadow is
cast by a precise light: **action-commutation**,
`f a (f c x) = f c (f a x)` (`crossEq_of_sameWitness`).  Strictly
weaker than commutativity-plus-associativity; those two merely
*supply* it (`action_comm_of_comm_assoc`).  With cancellation added,
the shadow is faithful — the cross-equation detects the shared
witness wherever one exists (`sameWitness_of_crossEq`).

## The true jobs

| property | its actual job |
|---|---|
| commutativity | fuse the two questions (step zero) |
| cancellation | **witness uniqueness** — transitivity of the witness relation *is* uniqueness of the middle witness (`sameWitness_trans`), nothing more and nothing less |
| medial law `f(f a b)(f c d) = f(f a c)(f b d)` | make the slotwise lift mean something: **the witness of the product is the product of the witnesses** (`pairLift_witness`) — commutativity and associativity are not directly needed |
| comm + assoc + cancellation together | upgrade the cross-relation to an equality-like relation with a compatible lift (`pairEq_trans`, `pairLift_congr_left/right`) |

Instantiation recovers chapter 2 exactly: at `+` the cross-equation
is the difference-pair relation (`pairEq_add_iff`); at `×` it is the
ratio relation, definitionally (`pairEq_mul_iff`).

## The list pays, for operations that respect it

These prices are abstract; on the sorted list they localize.  An
operation that "only moves backward along the list, without merging"
— strictly monotone in the unknown slot — gets cancellation **free
from the list structure** (`cancel_of_strictMono`).  That is why
`+`, `×` (on the positives), `^` feel basic: they are the operations
the list itself underwrites.

A **wrapping** operation — `mod`, whose results can land forward —
keeps every free step and even the medial lift (`modAdd_medial`),
but loses pointwise cancellation (`modAdd_cancel_fails`: mod-2
addition merges the witnesses 0 and 2).  The loss is informative,
not fatal: the witness sets become arithmetic progressions — each
itself a unit-`n` sorted list — so **wrapping pairs mint periodic
classes instead of points**.  And the wrap was never a primitive to
begin with: it is the fiber-position readout of a progressive
question (the ÷-sandwich's remainder).  Progressive operations are
primary; wrapping operations are how their fibers are read.
