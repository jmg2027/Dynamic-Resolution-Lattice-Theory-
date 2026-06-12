# What is `^`?

`^` is the first rung where the iterated action's increment is an
*operation* (`×a`), not a length — so the base and the exponent become
different types, and both commutativity and associativity die at once.
It is the boundary of the "nice" tower: `+`/`×` were one object under
coarser forgetting; `^` is where the atom-distinguishability handle turns
once more, on the operation level.

## 213-native answer

`^` is `×` iterated: `a ^ b = iter (· * a) b 1` (`Iterate213.pow_eq_iter`)
— `b` copies of `a`, multiplied.  But where `×` iterated `+a` (an
increment that is a *length*, the same type as the counter), `^` iterates
`×a` (an increment that is an *operation*).  The base `a` is a length; the
exponent `b` is the **dimension / iteration count** — a different type.
That type-split is the whole story.

## Derivation

Both floor gifts die at this rung (`Meta/Nat/HyperAssoc`).  `^` is
**non-commutative** — `2^3 = 8 ≠ 9 = 3^2` (`pow_not_comm`): the value-object
is a tree (depth-`b` `a`-ary), which has no transpose, where `×`'s grid
did.  And `^` is **non-associative** — `(2^2)^3 = 64 ≠ 256 = 2^(2^3)`
(`pow_not_assoc`): the bracketing the `append` floor discarded
(`BinTree213.flatten_assoc_collapse`) returns as genuine information.  So
**`×` is the last assoc+comm rung**; `^` loses both simultaneously, both
being the one event — the exponent promoted from another length to the
dimension.

The surviving ghost is `(a^b)^c = a^(b·c)` (`HyperAssoc.pow_surviving`),
which is `iter_mul` read one rung up (`Iterate213.iter_mul` /
`pow_pow_eq_pow_mul`): the only associativity-shaped law `^` keeps drops
it to `×` on the exponent, never `^` to `^` — which is why the tower folds
one rung down.

`^` has **two** inverse questions, not one.  `+` and `×` commute, so
`f a x = b` and `f x a = b` fuse; `^` does not (`question_fuse` fails at
step zero), splitting into the *root* (`xⁿ = b`, algebraic) and the *log*
(`aˣ = b`).  The root branch folds to finite tuples — radicals like
`√2 = ((2,1),(2,1))`.  The log branch is the wall: `aˣ = b` folds to a
finite tuple **iff** `exp(a) ∥ exp(b)` — the prime-exponent vectors
collinear (`vp_pow`; `theory/.../numbersystem_square.md`, the fold-back
criterion).  `2ˣ = 3` fails because `exp 2 ∦ exp 3`
(`TwoThreeUnique.two_three_unique`); the answer is reached by no finite
slot, only a `Real213` cut.  The wall is the distinguishability of
`×`-atoms (the primes independent), one resolution above the wall that
`×` did not have.

## Dual function

Classical "exponentiation = repeated multiplication" *is* `pow_eq_iter`;
213 sharpens that `^` is where the iterate-climb's increment first becomes
an *operation* rather than a length, so the base/exponent type-split
forces non-commutativity *and* non-associativity as **one** structural
event (the dimension promotion) — two classical "just facts" unified — and
the wall (the transcendence of `log₂3`) is the ℕ-internal independence of
prime exponents (`two_three_unique`), not an analytic accident.

## Cross-frame connections

Five readings, one rung: iterate `×` (`pow_eq_iter`), the assoc+comm
double-death (`pow_not_assoc`/`pow_not_comm`), the two-inverse split
(root/log, `question_fuse` failing), the `exp`-collinearity fold criterion
(`vp_pow` + `two_three_unique`), and the tree value-object (no transpose).
They converge — the exponent becoming the dimension *is* the loss of
transpose *is* the double-death *is* the inverse-doubling *is* the off-axis
exponent vector.

## Open frontier

Only the **linear** floor of the wall is closed: `two_three_unique` (and
its engine `vp_mul`) proves finitely many prime logs are independent, so
the simplest fold-backs fail.  The **nonlinear** floor — that *no*
algebraic relation among logs/exponentials exists — is Schanuel-conjecture
territory, classically open, and must carry that tag.  And the exponent
lattice `exp` rests on `vp_separation` (UFD), itself open.  So `^`'s wall
is real and ℕ-native at the linear rung; its full transcendence is the
honest open ceiling.
