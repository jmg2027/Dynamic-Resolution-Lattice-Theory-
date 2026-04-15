# Chicken McNugget Universality

**Mingu Jeong and Claude (Anthropic)**
**2026-04-15**

---

## Statement

**Theorem (Chiral Universality).**
For any dimension d >= 5, the chiral decomposition C^d reduces
to copies of C^2 and C^3:

  C^d = (C^2)^a + (C^3)^b,  where d = 2a + 3b

Moreover, every d >= 2 admits such a decomposition.

*Proof.*
gcd(2, 3) = 1, so by the Chicken McNugget theorem
(Sylvester-Frobenius), the largest integer NOT representable
as 2a + 3b (with a,b >= 0) is 2*3 - 2 - 3 = 1.
Hence every n >= 2 is representable.  QED.

---

## Explicit Decompositions

| d | 2a + 3b | Chiral content | Physics |
|---|---------|---------------|---------|
| 2 | 2(1)+3(0) | C^2 | Temporal only |
| 3 | 2(0)+3(1) | C^3 | Spatial only |
| 4 | 2(2)+3(0) | C^2+C^2 | Double temporal, no chirality |
| **5** | **2(1)+3(1)** | **C^2+C^3** | **Minimal chiral (our universe)** |
| 6 | 2(3)+3(0) or 2(0)+3(2) | Multiple | Non-minimal |
| 7 | 2(2)+3(1) | C^2+C^2+C^3 | Redundant temporal |
| 8 | 2(1)+3(2) | C^2+C^3+C^3 | Redundant spatial |

---

## Why d = 5 Is Special

d = 5 is NOT the only possible dimension. It is the **smallest
non-trivial chiral** dimension:

1. d < 5: either pure temporal (d=2,4) or pure spatial (d=3),
   or d=1 (trivial). No chiral decomposition.
2. d = 5: **minimal** — exactly one C^2 and one C^3.
   Unique chiral decomposition (Paper 1, Theorem 4.1).
3. d > 5: decomposition exists but is **non-unique**
   (e.g., d=8 has two representations).

**Corollary (Anti-Anthropic).**
d = 5 is not selected by fine-tuning or observer bias.
It is the smallest dimension where chirality (C^2 + C^3)
is possible. Any universe with chiral physics has d >= 5,
and d = 5 is the minimal choice.

---

## Connection to Additive Atoms

The universality theorem is a direct consequence of the
additive atom structure:

- Additive atoms = {2, 3} (Lemma 1 of Doubly Irreducible)
- These are the "generators" of all dimensions >= 2
- The Frobenius number F(2,3) = 1, so there is no gap

This means: **the physics of any dimension reduces to the
physics of C^2 (temporal) and C^3 (spatial).** The only
free parameter is how many copies of each.

---

## Relation to Paper 1

Paper 1, Corollary 5.2 already states this result.
This document adds:
1. The explicit connection to the Chicken McNugget theorem
2. The anti-anthropic interpretation
3. The table of decompositions for small d

**Status:** Remark-level result. Can be added to Paper 1 revision.
