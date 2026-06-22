# Decomposition: prime factorization (the multiplicative structure of ℕ)

*213-decomposition of "prime factorization", per `../README.md`.*

## The decomposition

- **Construction `C`** — `ℕ_{>0}` under the **×-construction**: numbers built by multiplying,
  iterated. The distinguishing-history here is *which atoms were used, with multiplicity* — and the
  ×-atoms (primes) are **distinguishable from each other** (unlike the +-atom, the unit, which is not:
  `Meta/Nat/UnitList.lean:append_comm`).
- **Reading `L_vp`** — the **prime-valuation reading** `n ↦ (v₂(n), v₃(n), v₅(n), …)`: project a number
  to its vector of prime exponents. A choice to keep *how many of each ×-atom* and forget the order they
  were assembled in.
- **Residue** — for this reading, **none**: the vector is *faithful* — distinct numbers have distinct
  vectors (`vp_separation` / `eq_of_vp_eq`). The reading that *usually* leaves a residue (count mod n,
  ratio, …) here leaves nothing un-pointed on `ℕ_{>0}`. That zero-residue *is itself the content*: it is
  unique factorization.

## Re-seeing the theorems

"Unique factorization" is stated as if it were a fact about *numbers having a canonical form*. It is not.
It is the single fact that `L_vp` is **injective**, and that it is a **homomorphism turning `×` into `+`
componentwise**: the reading respects the way the construction was built — and the operation it respects
is `×`, but the operation it *reads off* is `+`. Written in the calculus:

```
   prime factorization  =  ⟨ ℕ_{>0} (×-construction) | L_vp = (n ↦ (vₚ(n))ₚ) ⟩
   "FTA / unique factorization" =  L_vp injective                 (eq_of_vp_eq / vp_separation)
   "factor the product, add the exponents" =  L_vp(a·b) = L_vp(a) + L_vp(b)   (vp_mul, componentwise)
```

## Revelation (collapse + forcing)

**Collapse — "multiplicative vs additive" is one distinguishing, two readings.** `×` on `ℕ` and `+` on
the exponent-vector are not two structures to be related by a theorem; they are the *same* construction
read at two resolutions. `vp_mul` is verbatim `L_vp(a·b) = L_vp(a) + L_vp(b)`
(`Lib/Math/NumberTheory/PrimeValuation.lean:vp_mul`), and on powers it iterates to
`L_vp(aᵏ) = k·L_vp(a)` (`Meta/Nat/VpMul.lean:vp_pow`) — multiplication *is* vector addition of
valuations. The "multiplicative number theory vs additive number theory" division is the
parity-decomposition's collapse one level up: not "two operations," but **one ×-construction read
through `L_vp`**, where `+` is what the multiplicative distinguishing *looks like* once you have chosen
the prime-axis coordinates.

**Forcing — the exp/log "wall" is forced, and it is the dual of `append_comm`.** Why is there an
`aˣ = b` "wall" (no clean inverse to `×`)? Because the readout vector has *many independent axes*, and
the axes are independent **exactly because the ×-atoms are distinguishable**. `2^a = 3^b` forces
`a = b = 0` (`Meta/Nat/FoldCriterion.lean:two_three_unique`): the 2-axis and the 3-axis never trade.
That non-trade is the *positive form* of the failure-mode row "`^`-wall / `exp` diagnosed via imported
objects" — the log is an exterior ruler; internally the wall is just **×-atom distinguishability**. And
it is the exact **dual** of the +-construction's collapse: the +-atom (unit) is *indistinguishable*, so
its list-readout commutes to a single scalar (`append_comm` → `count`), one axis, no wall; the ×-atoms
are *distinguishable*, so their readout is a vector with one axis per prime, and the wall is mandatory.
**Faithfulness (`vp_separation`) and the wall are the same fact** seen as gift and as cost: distinguishable
atoms buy you an injective coordinate system, and the price is that you cannot collapse the axes back into
one — so `×` has no scalar inverse the way `+`'s unit-count does. Lean certifies all three legs
(homomorphism `vp_mul`, faithfulness `eq_of_vp_eq`/`vp_separation`, axis-independence `two_three_unique`),
so the collapse is proven, not asserted.

## Note for the technique

This decomposition **confirms and sharpens parity.md's "character" generalization**. Parity asked: is "a
construction-preserving *finite* reading" a named pattern? — yes. Prime factorization is the same shape
with the *finite cyclic* readout replaced by a **free `ℕ`-module (vector) readout**: a
**construction-preserving reading into a coordinate space**, where the construction's operation `×` is
*linearized* into the readout's `+`. Candidate name: a **logarithmic reading** (general form of
"character") — a construction-preserving reading whose readout group *changes the operation* (× ↦ +).
Two things this forces about the calculus's shape:

1. **Residue stratifies (README open-question, answered).** Here the *per-reading* residue is **zero**
   (the coordinate is faithful) even though the global non-surjection of any single self-view is not —
   evidence the README's "Residue: one slot or stratified?" should resolve to *stratified*: faithfulness
   is a property of a chosen reading, not of the construction.
2. **Atom (in)distinguishability is a first-class axis of `C`.** Whether the generating atoms are
   distinguishable is *the* parameter deciding scalar-vs-vector readout and wall-vs-no-wall. The README's
   "order/direction of distinguishing" question generalizes: not only order but **atom-identity** belongs
   explicitly in `C`. The +-construction (one indistinguishable atom → scalar, `append_comm`) and the
   ×-construction (many distinguishable atoms → vector, `two_three_unique`) are the two poles of this one
   axis.
