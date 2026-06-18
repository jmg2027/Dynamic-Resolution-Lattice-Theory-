# The finite-signature program — what the no-exterior axiom inspires

**The generative move.**  `seed/AXIOM/05` + `the_form_of_the_residue.md` ("infinity is
the residue's shape, not a god above it"): there is no exterior, and every classical object
defined "via a limit / completion / infinity" is **reached by no pointing**.  What is
computable — what 213 calculates with — is the *finite generator* of the never-closing
process, never the limit.  Turned from a guard into a program:

> For every classical object `X` defined as a `lim`/completion of a constructive process
> `P`, replace "the value `X`" with a **finite signature** `σ(P)` — a number (or finite
> tuple) read off *how the process is constituted*, not what it points at.  Then the
> mathematics is (i) **computing** `σ` for named processes and (ii) studying the **algebra of
> the signatures** and their **pairwise (in)dependence**.  The limit is never an operand;
> `σ` is.  "Sharpening the bracket IS the mathematics."

## The signatures the corpus already carries

| signature `σ` | of which "limit/∞" | anchor |
|---|---|---|
| forward-difference depth `polyDepth d` | is the convergent-difference stream a discrete polynomial | `Cauchy/DepthPRecursive`, `DivergenceLadder.reachesFloor` |
| C-finite order / Casoratian rank | order of the constant-coefficient recurrence the orbit closes into | `Cauchy/FoldSignatureSeparation.LinRec1`, `CasoratianRank` |
| P-recursive (holonomic) order | the polynomial-coefficient recurrence order; CF-holonomicity tier | `Cauchy/HolonomicInterleave`, `cf_holonomicity_hierarchy` |
| cross-determinant degree `W` vs `Δd` | the *rate* of a real's pointing (μ = its limsup) | `Real213/Modulus/{RateProduct,RateAffine,RateArithmetic}`; `degree_calculus.md` |
| p-adic valuation vector | the `×`-cone coordinate; "the shape of `×`" | `Meta/Nat/Valuation`, `Padic/` |
| pole-order / Chebyshev band width | the prime-counting / horizon-constant defect | `ChebyshevLower`, `simplicial_operation_tower.md` |

## Honest overlaps (the individual signatures are all classical)

Conceded as re-skins: **holonomic / D-finite theory** (polynomial ⊊ C-finite ⊊ P-recursive
ladder — Stanley, Kauers–Zeilberger); **proof mining moduli** (Kohlenbach — "the modulus is
the operand, not the limit" is its central move); **valuation/Ostrowski**; **computable-
analysis rate hierarchies** (Zheng–Rettinger divergence-bounded reals = the graded-modulus
ladder, already conceded in `degree_calculus.md`); **heights/regulators** (Weil, Northcott).
213 adds *no new individual signature*.

## What survives the audit (the genuine residue)

1. **The signature is provably a property of the *pointing*, not the object.**  No-exterior
   makes "depth/rate/holonomicity is presentation-relative" a *theorem schema*, not a caveat
   (`PresentationDependence`, `rcut_rescale`; the degree calculus's headline that `e+e` via
   `(i!)²` is rate-free though `2e` is degree 1).  Classical theory states each invariant of
   *a* presentation; 213 proves the *divergence between presentations* is the content.
2. **The ∅-axiom ban removes the cardinality shortcut, forcing the cross-relations open.**
   Classically one Cantor/cardinality argument settles every "reached by no finite stage"
   ceiling at once; the ∅-axiom discipline forbids it, so each ceiling needs a *named
   constructive witness with a domain-specific escape proof* (`CeilingSchema`).  This is *why*
   the cross-relations are individually provable theorems, not corollaries of one soft move.
3. **The algebra OF the signatures and their pairwise (in)dependence is the live edge** —
   under-written classically (which proves only field-closure of the *classes*).  The corpus's
   genuinely-new bricks all live here:
   - the **degree calculus** (`degree_calculus.md`): additive under matched sum, loses a
     degree under product, Möbius-invariant under affine/reciprocal — a per-pointing
     cross-determinant calculus μ cannot express.
   - the **fold-signature independence** (`FoldSignatureSeparation.order_does_not_bound_depth`):
     the additive-fold depth and the multiplicative-fold order are independent — `1` (depth 0,
     order 1) and `2ⁿ` (depth ∞, order 1) are both order-1 C-finite, so order does not bound
     depth.  The founding `G188` invert-twin (`invert(+)` depth vs `invert(×)` order) read at
     the sequence scale.

> One-line frame: *the slogan is "the limit is reached by none"; the program is "then the
> only mathematics left is the algebra of the finite signatures of the pointings — compute
> them, and find which pairs are independent."*

## Next frontier starting points

- **depth × order full strict containment** `finiteDepth ⊊ {C-finite}`: package the
  containment direction (`polyDepth_diff_recurrence`: `Δ^{d+1}` is constant-coefficient) with
  the `2ⁿ` properness witness into one `⊊` theorem.
- **valuation (×-signature) vs Δ-depth (+-signature)** as the §6.7 readout twin
  (`multiplicative_carry_residue.md` item 4, still soft-open in Lean) — the `^`-wall as
  ×-atom distinguishability.
- **the discriminant `tr²−4det` as the order-2 coupling of the two folds** (`G188`) — a
  ∅-axiom statement tying depth and order at order 2 via the shared unit `1 = NS−NT = det P`.
- (genuinely hard, NOT now) a *named transcendental* with low cross-det rate-degree but high
  partial-quotient Δ-depth — needs the open π non-holonomicity (`G170`); do not attempt.
