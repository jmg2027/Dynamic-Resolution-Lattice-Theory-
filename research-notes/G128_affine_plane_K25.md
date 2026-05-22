# G128 — Finite-field affine plane reading of K_25

*(Follow-up to G124 §2.3 / §6.2 "Finite-field affine-plane
reading of K_{25}".  Algebraic-geometric structural reading of
the N_U slice at `(d, n) = (5, 2)`.)*

## §0 The identity

For `d = q` prime power, the polynomial function ring
`F_q[x_1, …, x_n] / (x_i^q − x_i)` has cardinality `q^(q^n)`.
Identifying `[5]` with `F_5`:

```
F(5, 2) = 5^25 = configCount 2 = N_U
        = |F_5[x, y] / (x^5 − x, y^5 − y)|
        = |F_5^(F_5²)|                            (function space)
        = dim_{F_5} F_5[x, y] / (x^5 − x, y^5 − y) × 5  (function ring)
        = function ring of the affine plane A²_{F_5}
```

This is one of the **seven independent readings** of `5^25`
catalogued in G124 §5: the **algebraic-geometric reading** of
the count-Lens output at the physics slice.

## §1 Structural question

The DRLT count-Lens at `K_{3,2}^{(c=2)} → K_{25}` reads out
`5^25 = N_U`.  In the algebraic-geometric frame, `5^25` is the
cardinality of the **full function ring** on `A²_{F_5}`.

**Q (G124 §6.2)**: Does the bipartite `K_{3,2}^{(c=2)}` substrate
correspond to a specific **sub-ideal** of
`F_5[x, y] / (x^5 − x, y^5 − y)`?

Candidates:
  · **Degree-bounded polynomials**: polynomials of total degree
    `≤ k` form a sub-`F_5`-module.  Cardinalities:
    ```
    deg ≤ 1: 3 monomials  (1, x, y)              → 5^3  = 125
    deg ≤ 2: 6 monomials  (+ x², xy, y²)         → 5^6  = 15 625
    deg ≤ 3: 10 monomials (+ x³, x²y, xy², y³)   → 5^10 = 9 765 625
    deg ≤ 4: 15 monomials (+ x⁴, x³y, x²y², xy³, y⁴) → 5^15 = 30 517 578 125
    deg ≤ 5: 19 monomials                        → 5^19
    deg ≤ 6: 22 monomials                        → 5^22
    deg ≤ 7: 24 monomials                        → 5^24
    deg ≤ 8: 25 monomials (= full quotient)      → 5^25
    ```

  · **Vanishing-set ideals**: for a variety `V ⊆ A²_{F_5}`, the
    ideal `I(V) = {f : f|_V = 0}` is a sub-`F_5`-module.

  · **Symmetric polynomials**: `f(x, y) = f(y, x)` cuts dimension
    roughly in half.

  · **Bipartite-supported polynomials**: respecting a bipartition
    of `F_5 = A ⊔ B` with `|A| = 3, |B| = 2`.

## §2 The `K_{3,2}^{(c=2)}` ↔ bipartition

The bipartite graph `K_{3,2}` has:
  · `3` vertices in part `A`, `2` in part `B`
  · All `3 × 2 = 6` edges between parts

Identifying `A ⊔ B = F_5` with `|A| = 3, |B| = 2`:

```
A = {0, 1, 2}    (3 elements, "NS-side")
B = {3, 4}       (2 elements, "NT-side")
```

(Or any other partition of `F_5` into `3 + 2`.)

The bipartite cohomology functor reads out functions
`A → B → F_5` (or `A × B → F_5` after currying).  Counting:
`|F_5^(A × B)| = 5^6 = 15 625`.

But that doesn't match `5^25`.  Apparently the
`K_{3,2}^{(c=2)} → K_{25}` lift involves the `c = 2` parameter
in a non-trivial way that promotes `5^6` to `5^25`.

## §3 What `c = 2` does

Per `rust-engine/docs/closure-algorithm.md`:
  · `{NS, NT, d, c} = {3, 2, 5, 2}` generates the atomic
    integer catalogue.
  · `c = 2` is "cup-product depth" / "rank-2 structure".

Heuristic: rank-2 cup product takes `Hom(A × B, F_5)` (= `F_5^6`)
to `Hom(A × B, F_5)^c = (F_5^6)^c = F_5^(6c)`.  With `c = 2`:
`F_5^12`.  Still not `5^25`.

Or: the full square `F_5^(F_5²) = F_5^25` is the *target* of the
fractal closure, and `K_{3,2}^{(c=2)}` is the *generating
configuration* — different objects.

**Open**: the precise functor `K_{3,2}^{(c=2)} → K_{25}` and its
algebraic-geometric reading require new infrastructure.  The
G124 §6.2 catalogue entry remains open at the structural-bridge
level.

## §4 Concrete sub-spaces of `F_5[x, y] / (x^5 − x, y^5 − y)`

For future Lean formalisation (when finite-field infrastructure
exists in `lean/E213/`), the relevant sub-spaces include:

| Sub-space | Description | dim_{F_5} | Cardinality |
|---|---|---|---|
| `R_{≤k}` | Polynomials of total degree ≤ k | varies | `5^{...}` |
| `I(V)` | Ideal vanishing on variety `V` | varies | varies |
| `R^{sym}` | Symmetric polynomials | 15 | `5^15` |
| `R^{alt}` | Alternating polynomials | 10 | `5^10` |
| `R^{lin}` | Multilinear (degree ≤ 1 in each var) | 4 | `5^4 = 625` |
| Full | `F_5[x,y]/(x^5−x, y^5−y)` | 25 | `5^25 = N_U` |

`5^25 = N_U` sits at the top of this filtration as the **full
function ring**.  Smaller cardinalities correspond to natural
algebraic-geometric sub-objects, each potentially DRLT-relevant.

## §5 Numerical observations

  · `5^25 / 5^15 = 5^10 = 9 765 625` (≈ 10⁷) — the "anti-symmetric"
    quotient if `R^{sym}` is the right sub-space.
  · `5^25 / 5^10 = 5^15` — ratio at the alternating quotient.
  · `5^25 / 5^4 = 5^21` — ratio at the multilinear sub-ring.

None of these ratios maps directly to a Hunter-catalogue
atomic integer.

## §6 Cross-field convergences (from G124 §5)

`5^25` admits **seven** independent readings.  G128 records the
algebraic-geometric one explicitly:

| Frame | Reading at `5^25` |
|---|---|
| Combinatorial | `\|F_5^{F_5²}\|` (n=2-variable F_5-valued functions) |
| Cohomological | `5`-colouring count of `K_{25}` |
| Cartesian-closed | `\|Hom_Set([5]², [5])\|` |
| Type-theoretic | STLC `Fin 5 → Fin 5 → Fin 5` inhabitant count |
| Cellular-automata | 2-input 5-state CA rule space |
| **Algebraic-geometric** | `\|F_5[x,y] / (x^5−x, y^5−y)\|` — **G128 focus** |
| DRLT-internal | Count-Lens output at `K_{3,2}^{(c=2)} → K_{25}` |

All seven agree on the integer `5^25`.  The G128 question is
whether the **sub-structures** of the algebraic-geometric frame
(sub-ideals, varieties) map cleanly to **sub-structures** of
the DRLT-internal frame (bipartite generators, cup-product depths).

## §7 Lean status

`F_5` (the field with 5 elements) is not currently formalised
in `lean/E213/`.  The codebase has:
  · `Lib/Math/ModArith/` — modular arithmetic (Bezout, FLT,
    `F_{p²}` machinery via FP2Sqrt5)
  · `Lib/Math/Cohomology/Fractal/` — `configCountD` family and
    bridges to physics

What's missing for a G128 Lean closure:
  · Definition of `F_q` as a Lean type (via `Fin q` with field
    operations)
  · Definition of polynomial ring `F_q[x_1, …, x_n]` and the
    quotient by `x_i^q − x_i`
  · Cardinality theorem `|F_q[x_1, …, x_n] / (x_i^q − x_i)|
    = q^(q^n)`

This is a substantial new infrastructure addition, on the order
of the G122 Real213-p-adic campaign.  Deferred to a future
session.

## §8 Open frontier

The G128 question — sub-ideal correspondence with
`K_{3,2}^{(c=2)}` substrate — is genuinely open and requires:
  1. Formal definition of the `K_{3,2}^{(c=2)} → K_{25}` lifting
     functor (currently informal in DRLT)
  2. Identification of the image as a specific sub-`F_5`-module
     of `F_5[x, y] / (x^5 − x, y^5 − y)`
  3. Verification that the sub-module cardinality matches the
     bipartite cup-product readout

This is a deep algebraic-geometric programme.  G128 records the
groundwork and the seven-reading context; the closure is
multi-session.

## §9 Cross-references

  · `research-notes/G124_n_u_family_cross_field_connections.md`
    §2.3 (finite-field reading), §6.2 (catalogue entry).
  · `theory/math/cohomology/fractal.md` — N_U family chapter.
  · `rust-engine/docs/closure-algorithm.md` — `{NS, NT, d, c}`
    generators.
  · `catalogs/atomic-integers.md` — atomic catalogue.

## §10 Self-check

  · No false dichotomy: algebraic-geometric reading is one of
    seven valid Lens readings of the same integer, not "the
    correct" one.
  · No fake completeness: §7 explicitly states the Lean
    infrastructure gap; §8 lists the multi-session work
    required for full closure.
  · No stereotype matching: identifications with `F_5[x,y]`
    are recorded with the structural question open, not
    asserted by analogy.
