# Logic 213 — Module Index

Blueprint: `blueprints/math/14_logic_213.md` (retired).

## Modules

| File | Topic | Theorems | Status |
|---|---|---|---|
| `Predicate.lean` | Cut as predicate calculus, De Morgan, commutativity, identities | 15 | 15/15 ∅-axiom |
| `Intuitionistic.lean` | Bool LEM atomic, predicate-LEM, witness extraction (no Classical) | 6 | 6/6 ∅-axiom |
| `Proof.lean` | Trajectory = proof, composition, finite-length, normalize skeleton | 11 | 11/11 ∅-axiom |
| `Capstone.lean` | 3 cluster witnesses + `total_witness` | 4 | ∅-axiom |
| `Logic.lean` | umbrella | — | — |

**Total**: 36 atomic facts, all ∅-axiom.

## Key insights

  * **Cut = predicate**: `Cut := Nat → Nat → Bool` IS predicate
    calculus.  De Morgan, double-negation, commutativity all
    reduce to atomic Bool truth tables — no propext needed
    (`Bool.not_not`, `Bool.and_comm`, etc. are `decide`-stable).

  * **Bool LEM is atomic, not classical**: `b = true ∨ b = false`
    is `decide`-decidable for any concrete Bool — no
    `Classical.em` needed.  Off-substrate Prop-LEM is *not*
    asserted (and not needed).

  * **Proof = trajectory**: a `List Bool` of decisions.  Proof
    length = decision count (= bit count).  Composition is
    concatenation, additive in length.  Cut elimination skeleton
    via `normalize` (cancel adjacent inverse pairs).

  * **Constructive only as feature**: every existential carries
    its witness explicitly (`Sigma'` over decidable Bool).  No
    Choice axiom needed because the substrate is decidable.

## Connections to other tracks

  * Information 213: `proofLength` = bit count = entropy of
    proof-path.  `K(213) = 4` clauses (Logic-meta meets info-meta).
  * Probability 213: predicates as event indicators; `Bool` as
    σ-algebra-free atomic event space.

## Out of scope (separate continuation)

  * Gödel incompleteness via diophantine encoding (would use
    Number Theory 213's Pisano machinery).
  * HoTT / Univalence axiom relationship.
  * Reverse mathematics 213 (which theorem needs which axiom).
