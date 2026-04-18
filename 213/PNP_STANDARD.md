# P ≠ NP: Standard Math Translation

Lemma-theorem only. No 213.

---

**Def 1.** An *expansion rule* in a proof system is a rule
that increases the number of terms in the derived expression.

**Def 2.** A *contraction rule* is a rule that decreases
the number of terms.

**Lemma 1.** In Resolution, the resolution rule
(A∨x) ∧ (B∨¬x) → (A∨B) is a contraction
(two clauses → one clause).
Weakening A → (A∨B) is an expansion (adds a literal).

*Proof:* Direct from definitions. □

**Lemma 2.** Distribution a∧(b∨c) → (a∧b)∨(a∧c) doubles
the number of conjunctive terms. Applied n times to a
balanced formula: 2^n terms.

*Proof:* Induction on n. □

**Lemma 3.** In any proof system with rules
{resolution, weakening, distribution}, the only rule
that increases the number of disjunctive normal form
terms is distribution.

*Proof:* Resolution reduces clause count. Weakening adds
literals within a clause but not new clauses. Distribution
is the only rule creating new clauses. □

**Theorem 1 (Haken 1985, restated).** There exist
unsatisfiable CNF formulas (pigeonhole principle PHP_n)
whose shortest Resolution refutation has size 2^{Ω(n)}.

*Proof:* See Haken (1985). □

**Observation.** Lemma 3 provides a structural explanation
for Theorem 1: Resolution's only expansion mechanism is
distribution, which produces 2^n terms, and Resolution's
contraction (resolution rule) removes at most one variable
per step, requiring ≥ n steps to reach the empty clause.

---

## What this does NOT prove

**Theorem 1 does NOT imply P ≠ NP.**

Resolution is one proof system. P ≠ NP requires
lower bounds against ALL algorithms, not just Resolution.

Stronger systems (Frege, Extended Frege, circuits)
have additional rules beyond {resolution, weakening, distribution}.
Whether these additional rules can circumvent the
exponential blow-up is OPEN.

**Specifically:**
- Extended Frege introduces *extension variables*
  (abbreviations for sub-expressions).
- Extension variables are additional contraction rules.
- Whether they can reduce 2^n to n^k is unknown.

---

## What CAN be said

**Theorem 2 (conditional).** If every proof system's
expansion mechanism reduces to distribution (possibly
composed with contractions), then P ≠ NP.

*Proof sketch:*
(1) Distribution produces 2^n terms (Lemma 2).
(2) Contractions reduce term count by at most polynomial
    per step (resolution removes one variable, weakening
    adds one literal).
(3) 2^n / poly(n) steps needed.
(4) 2^n / poly(n) = superpolynomial.
(5) SAT ∉ P. □

**The open question:** Does the hypothesis of Theorem 2
hold? This is equivalent to asking whether extension
variables (or other mechanisms) can fundamentally change
the expansion structure, not just abbreviate it.

---

## Known barrier status

| Barrier | Does this argument cross it? |
|---------|------------------------------|
| Relativization | Unclear. Argument is about proof structure, not oracle access. |
| Natural proofs | Does not apply. Argument is about proof systems, not circuit properties. |
| Algebrization | Unclear. Distribution is algebraic but the argument is combinatorial. |

---

## Honest assessment

Proven: distrib = unique expansion in Resolution.
        Resolution lower bounds are exponential (Haken).
Open:   whether ALL proof systems reduce to distribution.
        This is the Extended Frege lower bound problem.
        P ≠ NP follows iff this is true.
