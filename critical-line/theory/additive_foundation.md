# Additive Foundation: Cycle Counts Without Circular Reference

**Mingu Jeong and Claude (Anthropic)**
**2026-04-15**

---

## 0. The Circularity Concern

We claimed:
1. Graph primitive cycle count pi(n) satisfies PNT
2. The Mobius function mu(n) appears in extracting pi(n) from W(n)
3. Therefore mu(n) is "explained" by the Gram graph

Apparent circularity: we USE mu to DERIVE pi, then claim pi
EXPLAINS mu. This section resolves the circularity.

---

## 1. What Is Directly Computable (No mu Required)

**Definition.** For a graph G with non-backtracking edge
adjacency matrix A (unweighted, {0,1} entries):

  W(n) := Tr(A^n) = number of closed NB walks of length n

**This is a pure integer, computed by matrix multiplication.**
No mu, no analytic continuation, no complex analysis.
Just counting.

**Fact (verified RH_034).** For the complete graph K_N:

  W(n) = N(N-1)(N-2)^{n-1} - correction terms

This is an exact combinatorial formula.

---

## 2. The Mobius Inversion Is a THEOREM, Not an Assumption

**Theorem (Standard, not ours).** For ANY sequence W(n)
of closed walk counts on a finite graph:

  W(n) = sum_{d | n} d * pi(d)

where pi(d) = number of primitive cycles of length d.

This is a DEFINITION of pi(d) via the identity:

  pi(n) = (1/n) sum_{d | n} mu(n/d) * W(d)

**The mu here is the NUMBER-THEORETIC Mobius function,
defined independently:**
  mu(1) = 1
  mu(n) = (-1)^k if n = p1*p2*...*pk (distinct primes)
  mu(n) = 0 if n has a squared prime factor

**Key point:** mu is NOT derived from the graph.
It is a number-theoretic object defined by prime factorization.
The graph provides W(n). The Mobius inversion is a theorem
of elementary number theory that converts W(n) to pi(n).

---

## 3. What the Graph Actually Determines

The graph determines W(n) for all n. From W(n), two things follow:

### 3a. PNT (Graph Version)

**Theorem (RH_034, verified to 10^{-4}).**
For K_N with NB adjacency:

  pi(n) = (N-2)^n / n + O((N-2)^{n/2})

This is the graph-PNT. The FORM of this result
(main term + square root error) is identical to the
classical PNT:

  pi_classical(x) = x / log(x) + O(x^{1/2+epsilon})

### 3b. Divisibility Structure

**Observation (RH_034, verified for K_8, K_10, K_12).**

  n = k * gcd(a,b)  implies  pi(gcd(a,b)) | pi(n)

This divisibility holds as an INTEGER relation.

---

## 4. Where mu Actually Enters (Not Circular)

The logical chain:

```
Step 1: DRLT axiom
  "Things exist with pairwise relations"
  → Gram matrix G = Psi * Psi^dagger
  → Complete graph K_N with N vertices

Step 2: COUNTING (pure combinatorics)
  NB walks on K_N → W(n) = Tr(A^n)
  W(n) is an integer. No choices, no parameters.

Step 3: NUMBER THEORY (independent of graph)
  Mobius inversion: pi(n) = (1/n) sum mu(n/d) W(d)
  This uses mu as a TOOL from number theory.
  mu is defined by primes. Primes exist independently.

Step 4: RESULT (the non-trivial content)
  pi(n) = q^n / n + O(q^{n/2})
  where q = N-2.

  THIS IS THE GRAPH-PNT.
  The fact that it holds is NOT guaranteed by Steps 1-3.
  It is a THEOREM about the structure of K_N.

Step 5: INTERPRETATION
  The error term O(q^{n/2}) corresponds to
  the Riemann Hypothesis for the Ihara zeta of K_N.
  For finite N, this is PROVABLY TRUE (Ramanujan bound).
```

**The non-circular content is in Step 4.**
Steps 1-3 set up the problem. Step 4 is the theorem.
mu is used in Step 3 as a tool, not derived in Step 4.

---

## 5. What IS New (The DRLT Contribution)

The graph-PNT for K_N is known (it follows from the
Ihara zeta function of complete graphs). What DRLT adds:

### 5a. WHY K_N

The complete graph is not a choice — it is FORCED by the
DRLT axiom. N things with pairwise relations = K_N.
The Gram matrix G_{ij} = <psi_i|psi_j> provides weights
for every pair. There is no thresholding or sparsification.

### 5b. WHY the Error Term is q^{n/2}

The Ramanujan bound for K_N gives:
  |lambda_2| <= 2*sqrt(q)  where q = N-2

This is equivalent to: all Ihara zeros on |u| = 1/sqrt(q).
For the WEIGHTED Gram graph (using |G_{ij}|^2):
  Ramanujan holds for d >= 4 and N <= N_c(d)
  (Proven in RH_006-007)

### 5c. WHY q = N-2

In K_N, each vertex has degree N-1.
NB walks subtract 1 (can't go back), giving base N-2.
In DRLT terms: q = N - dim(trivial representation) - 1.

### 5d. The Additive Structure

The DRLT axiom is ADDITIVE:
  - Add a point → new relations (G grows by 1 row/column)
  - Chiral decomposition: 5 = 2 + 3 (sum of atoms)
  - Propagator: sum over channels

The MULTIPLICATIVE structure (Euler product, primes)
EMERGES from the additive structure via:
  W(n) = sum d*pi(d)  [additive identity]
  ζ_G(u) = prod (1-u^|c|)^{-1}  [multiplicative encoding]

These are the SAME information in two forms.
The additive form (W(n)) is primary.
The multiplicative form (zeta, Euler product) is derived.

---

## 6. Formal Statement (No Circularity)

**Theorem (Additive Foundation).**
Let G_N be the Gram matrix of N generic unit vectors in C^d.
Let A_N be the non-backtracking edge adjacency of K_N.
Define W(n) = Tr(A_N^n). Then:

(i) W(n) is a positive integer for all n >= 1.

(ii) The primitive cycle count pi(n), defined by Mobius
    inversion of W, satisfies:
      pi(n) = (N-2)^n / n + O((N-2)^{n/2})

(iii) The error term O((N-2)^{n/2}) is equivalent to
     the Ramanujan bound for K_N, which holds for all
     finite N (proven by Ihara theory).

(iv) Statements (i)-(iii) use only:
     - Matrix multiplication (Step 2)
     - Mobius inversion (Step 3, standard number theory)
     - Ihara theory for finite graphs (Step 4, known)

     No complex analysis of zeta(s) is used.
     No assumption about RH is made.
     The Mobius function mu(n) enters as a TOOL, not a conclusion.

**Corollary.** The DRLT Gram graph REPRODUCES the Prime
Number Theorem structure WITHOUT invoking the Riemann zeta
function. The zeta function, if constructed from this graph,
would inherit the PNT as a consequence of the graph structure
rather than the other way around.

---

## 7. The Deeper Question (Open)

If the Gram graph's cycle structure reproduces PNT,
and if the Gram graph is DETERMINED by the DRLT axiom,
then:

  PNT is a consequence of "things exist with pairwise relations."

The Riemann Hypothesis would then be:

  "The error term in the graph-PNT is optimal"
  = "The Ramanujan bound is tight"
  = "delta(N) > 0 for all finite N" (self-contradiction boundary)

This chain contains no circular reference.
Each step is independently verifiable.
The open question is whether the finite-N graph-PNT
implies anything about the classical (N → infinity) PNT.

---

## 8. Status

| Statement | Evidence | Circular? |
|-----------|----------|-----------|
| W(n) is computable | Matrix mult | No |
| pi(n) via Mobius inversion | Standard NT | No (mu is input) |
| pi(n) ~ q^n/n | RH_034, 10^{-4} | No |
| Error = O(q^{n/2}) | Ihara + Ramanujan | No |
| Gram graph is K_N | DRLT axiom | No |
| PNT from axiom | Steps 1-4 | **No** |
| Classical RH from graph RH | Self-contradiction | **Open** |
