# The number-system square: two Lenses, two orders, one ℚ

## The square

```
        difference pair (+-question)
   ℕ ────────────────────────────▶ ℤ
   │                               │
   │ ratio pair                    │ ratio pair
   │ (×-question)                  │ (positive denominator)
   ▼                               ▼
   ℚ₊ ───────────────────────────▶ ℚ
        difference pair of ℚ₊
```

Four paths, two composite routes (ℕ→ℤ→ℚ and ℕ→ℚ₊→ℚ); a rational is a
nested ℕ-pair in two bracketings.  The ℕ→ℤ→ℚ route is closed
(`Rat213`: Int numerator × positive Nat denominator, normal form
exact).  The ℕ→ℚ₊ leg is `RatioLensFounding.ratioEquiv`; the ℚ₊→ℚ leg
(difference pairs of positive ratios) is **not yet built**.

## Why the routes converge (the principle, to be made a theorem)

**Distributivity is the commutation law of the two Lenses.**  The
difference fiber is a +-action `(a,b) ~ (a+c, b+c)`; the ratio fiber
is a ×-action `(a,b) ~ (ka, kb)`; `k(a+c) = ka + kc` says the
×-transport maps +-fibers to +-fibers, so quotienting in either order
lands in the same place.  Repo pins: the mixed keystone
`Int213.subNatNat_mul_ofNat` (difference pair × scalar), the ∣-side
`Gcd213.gcd213_mul_left`, and the canonical target
`Rat213.lowest_exists`/`lowest_unique` (any presentation normal-forms
to sign × coprime pair).  Contrast: where commutation *fails* —
order × sign, `OrderMul.mul_le_mul_right_nonpos` — the square does
not close and the positive cone must be carved out first.  Same
phenomenon, positive and negative instances.

## The detectors (judgment formulas across levels)

Each rung's judgment formula becomes, one level up, the membership
detector of the old system and the normal-form selector of the new:

| formula | in ℕ | in ℤ / ℚ₊ | in ℚ |
|---|---|---|---|
| sandwich (order) | witness dichotomy (`witness_total`/`not_both`) | sign readout (`subNatNat_eq_ofNat_iff`/`negSucc_iff`) | floor / integer part (`div_sandwich` lifted); ℤ-membership = denominator 1 |
| coprimality (∣) | a relation between two naturals | lowest-terms selector (`gcd_strip_coprime` + `coprime_repr_unique`) | canonical representative (`IsLowest`); ℕ/ℤ-membership = `b ∣ a`; Farey `det P = 1` |

In ℚ the two detectors are exactly the two normal-form projections:
order frame → sign + integer part; ∣ frame → coprime magnitude pair.

## Open bricks

1. The ℚ₊→ℚ leg: difference pairs over positive ratio pairs, with its
   own sandwich (cross-subtraction) — all over ℕ⁴.
2. **Square-commutes theorem** (PURE): the ℕ→ℚ₊→ℚ composite and the
   ℕ→ℤ→ℚ composite normal-form to the same `Rat213` representative;
   the proof content should be exactly distributivity.
3. The Lens-frame reading (one fact, several frames — morphism / added
   axis / boundary): essay after the Lean closes, not before.

## The equation ladder (extension of the square)

Each system is the totality domain of an equation class with ℕ
coefficients and **one unknown**:

| class | completion |
|---|---|
| `x + b = c` (monic, +) | ℤ |
| `a·x = b` (×) | ℚ₊ |
| `a·x + b = c` (general degree 1) | ℚ |
| monic polynomial | algebraic integers |
| general polynomial | algebraic numbers |

Two rules to pin: (i) class = one reversed arrow + closure under the
available folds; degree = ×-question iterated on the unknown;
(ii) **monic ↔ ring-like, general leading coefficient ↔ field-like**,
persisting up the ladder.  Boundary: non-polynomial questions
(`a^x = b`) leave equation-completion for sandwich-family completion
(ℝ order-frame, ℚ_p ∣-frame).

## Collapse vs rigid axis (the doubling dichotomy)

A pair-Lens either *collapses* (quotient by the operation's action —
ℕ→ℤ→ℚ, dimension stays 1) or stays a *rigid axis* (ℚ(√2) over ℚ;
ℝ→ℂ→ℍ→𝕆 Cayley–Dickson, dimension 1→2→4→8).  Criterion: **per-frame
visibility of the obstruction readout** — sign (2-valued) and
remainder (`a`-valued) are old-data-visible → collapse; `x² = 2` is
order-visible (sandwich locates it → absorbed by ℝ) but
algebra-invisible (rigid 2-dim over ℚ); `x² = −1` is invisible in
every frame (`Int213.int_sq_nonneg` is the positivity certificate)
→ a genuinely new axis in all frames.  The CD conjugation
`(a,b)* = (a*, −b)` is the iterated sign-swap (`neg_subNatNat`); the
per-doubling law-loss ladder (order → commutativity → associativity →
norm composition) is combinatorially derivable from the doubling
formula and is partially PURE in `Lib/Math/Algebra/CayleyDickson/`
(`CDDoubleMoufang`, `CDDoubleAlternative`, sedenion failure of
`TraceNormed213` lift).

**First concrete witness — ★ CLOSED**
(`Lib/Math/NumberSystems/CompletionDichotomy.lean`, 3 PURE / 0 DIRTY):
`int_sumSq_eq_zero` (two integer squares sum to zero only at the
origin — the `a²+b²` ℤ[i]/ℂ-norm anisotropy), `sq_eq_neg_sq_imp`
(`a*a = −(b*b) → a = b = 0`), `no_rat_sqrt_neg_one` (no rational
squares to −1, phrased via `Rat213.ratioEqZ`).  The ℝ→ℂ doubling
cannot collapse: its obstruction `x²+1` reads out positive in the
order frame for every input — invisible in sign, remainder, *and*
order frames, unlike the collapsing extensions whose obstruction
readouts (sign 2-valued, remainder `a`-valued) live in the old data.
Contrast `x²=2`: order-visible (`Irrational/Sqrt2Cut`, absorbed by
ℝ) but algebra-rigid over ℚ.

Open brick 4 (remaining): the general collapse-vs-rigid criterion as
a theorem *schema* (obstruction readout valued in old data ⟺ the pair
quotient is total) connecting the completion square to the CD tower —
`int_sumSq_eq_zero` is the base case (rank-1 doubling anisotropy).

## The hyperoperation refinement (^ splits along the normal form)

`^` is non-commutative, so it has **two** reverse questions: root
(`xⁿ = b`, algebraic) and log (`aˣ = b`, outside the polynomial class
— sandwich-family completion only).  The root-completion acts on the
sign × magnitude normal form **factorwise**:

| operation | exponent-lattice event | completion |
|---|---|---|
| + | ℕ → ℤ | ℤ |
| × | per-prime exponents ℕ^ω → ℤ^ω | ℚ₊ (= the +-completion re-run inside the exponent lattice) |
| ^ root | magnitude exponents ℤ^ω → ℚ^ω **and** sign ℤ/2 → ℚ/ℤ | radicals (order-visible, absorbed by ℝ) + roots of unity (torsion → **rigid**, first rung `i`) |
| ^ log | leaves the lattice | sandwich-family only (the ℝ boundary) |

Rule: each hyperoperation's root-completion = the previous completion
re-applied inside the exponent lattice; **free parts collapse (or are
absorbed by the order completion), torsion parts are rigid** — the
collapse-vs-rigid criterion concretized as free-vs-torsion.  ℤ[i] is
the monic/integer form of the sign-axis rung at depth 2
(`int_sumSq_eq_zero` its rigidity certificate; `ZIUnits`:
`ℤ[i]^× = {±1, ±i} ≅ ℤ/4` — "positive Gaussian integer" = the
associate-class normal form, sign (2-valued) grown into phase
(4-valued); `ImaginaryQuadraticUnitTrichotomy` 2/4/6 bounds the
circle-torsion an integer form can hold).  Polar form `r·e^{iθ}` =
the sign × magnitude normal form lifted through the ^-completion.

Open brick 5: the magnitude side as a theorem — the ℚ₊ exponent
lattice (`vp` valuation vectors) and its divisible hull as the
root-completion, connecting `Valuation.le_vp_iff` to the radical
tower.

## Question tuple vs answer axes (the fold-back rule)

**The representation principle.**  In a pinning question `f(x) = b`,
the number of ℕ-slots (coefficient *or* exponent — any position a
natural fills) **equals** the number of naturals needed to represent
the possibly-non-natural solution: the new number *is* the question's
parameter tuple, and the number system is the tuple space modulo the
same-solution equivalence.  Verified across the session:
`a+x=b` (2 → ℤ, fiber `subNatNat_add_add`), `a·x=b` (2 → ℚ₊,
`ratioEquiv`), `x^a=b` (2 → radicals, exponent-scaling
`(a,b)~(ka,bᵏ)`), `a·x+b=c·x+d` (4 → ℚ, `ratioEqZ`/`Rat213`),
general irreducible degree n (coefficient slots → algebraic numbers).
Two refinements: tuples over-name (the same-solution equivalence is
mandatory; lowest-terms = minimal representative), and unknown
occurrence ≥ 2 adds a finite root selector (discrete, does not change
the freedom count).  Reversed, it stratifies numbers: **a number's
representation cost = the ℕ-freedom of its minimal pinning question**
(2: ℤ/ℚ₊/radicals; 4: ℚ; k: algebraic, minimal polynomial = the
lowest-terms form of the minimal-freedom question; divergent:
transcendental — no finite question pins it, sandwich-family only).
The classical *height* of an algebraic number is this principle's
shadow.

Two different tuple counts, separated: the **question tuple** (the
equation's data) and the **answer-system axes** (the dimension of the
+,×-closure over ℚ).  The question-tuple count is governed by the
**occurrence count of the unknown in the fold**: constants fold away
(`x + a₁ + a₂ + ⋯ = b₁ + ⋯` compresses to `x + a = b`, two slots),
but occurrences of the unknown do not — `a·xⁿ = b` keeps `n` as
irreducible data, `((a, b), n)`.  Three grades:

1. unknown occurs **once** — constants compress, 2 slots, pair
   completion, **collapse** (ℤ, ℚ₊, ℚ);
2. unknown occurs **n times (known n)** — `n` survives as data,
   the answer system grows n axes, **rigid** (algebraic);
3. **the occurrence count itself is the unknown** (`aˣ = b`) — no
   fold-back, **transcendental** (sandwich-family only).

**The mixed form, derived from the sandwich (the crossing rule).**
The earlier "give each side one ×-slot and one +-slot" was a
postulate; the sandwich derivation replaces it.  **Slot attachment
rule**: a slot may be attached wherever it preserves monotonicity of
the fold in the unknown (+-slots, positive ×-slots, exponent slots
all do; a subtraction slot would break it — which is why that data
lives elsewhere, see below).  **Generalization rule**: the general
question is not "fold = constant" but "*where do two monotone folds
cross*"; the constant is the degenerate crossing partner.  The
sandwich generalizes to the crossing sandwich

```
        F(x) ≤ G(x)  ∧  G(x+1) < F(x+1)
```

and for affine folds this **reduces exactly to the ÷-sandwich of the
slot differences** — closed PURE
(`NatDiv213.affine_cross_iff_div_sandwich`,
`affine_cross_eq_div`: in witness form `a = c + e`, `d = b + f`, the
crossing sandwich of `a·x + b` vs `c·x + d` is `e·x ≤ f < e·(x+1)`,
location `f / e`).  So the 4-slot form is forced: a crossing needs
two folds, each with one ×-slot and one +-slot; the **sign data is
the crossing orientation** (which fold is steeper, which starts
higher — two swap bits multiplying to the rational's sign), which is
where the monotonicity-breaking "subtraction slot" actually lives.
Degree-n crossings (two polynomial folds) locate real algebraic
numbers; refining the crossing through rational grids (clearing
denominators returns ℕ-fold comparisons) is the `Real213` cut — a
crossing that never lands on a lattice point at any resolution is the
equation/sandwich boundary again.

**Witness-form discipline (house rule, stated).**  Constructions are
phrased over ℕ-pairs only: extension systems are *targets being
described*, never *tools used in the description* — no inverse
operations or imported systems in hypotheses.  Every closed theorem
of this arc already obeys it (`gcd_strip_coprime`'s `a = g·a₁`, not
`a/g`; `subNatNat_eq_negSucc_iff`'s `b + (y+1) = a`, not `a − b`;
`affine_cross`'s `a = c + e`, `d = b + f`).

**The degree-n mix, same rule**: the crossing of `a·xⁿ + b` and
`c·xⁿ + d` in witness form (`a = c + e`, head start on either side) —
data `((c, e, b, f), n)`.  The orientation dichotomy (which fold is
steeper / which starts higher) is total for `n = 1`: a mismatched
orientation moves its witness to the slot-swapped question (the
x-reflection).  **Even folds are reflection-symmetric, so a
mismatched orientation cannot be moved** — that is the
`CompletionDichotomy` rigidity (`int_sumSq_eq_zero`, the
cleared-denominator form at `n = 2`).  Fully general:
`Σ aᵢ x^{eᵢ} = Σ bⱼ x^{fⱼ}` — the equation data is itself a **pair
of ℕ-polynomial folds**: the pair structure recurs one level up
(numbers = pairs of unit-folds; algebraic numbers = pairs of
monomial-folds), whose lowest-terms normal form is the minimal
polynomial (open brick 6).
Adjoining α a priori creates infinitely many axes α, α², …; the
equation `a·αⁿ = (lower terms)` is a **fold-back rule** sending the
n-th power into the span of the first n, so the axes stop at n:

| equation | operand slots + counter slots | answer axes |
|---|---|---|
| `a+x=b`, `a·x=b` | 2 + 0 | 1 (collapse — degree 1 folds α itself into the base) |
| `a·xⁿ=b` | 2 + 1 | n |
| general degree n (irreducible) | (n+1) + 1 | n |
| k independent square roots | 2 each | 2^k (compositum doubling — the commutative twin of the CD tower; `ZSqrt*`/`ZOmega`/`ZI` the 2-axis PURE instances, `HurwitzTower` the 4-axis) |
| no equation (transcendental) | ∞ | ∞ (sandwich-family only) |

So **algebraic vs transcendental = finite fold-back vs infinite
axes = equation-completable vs sandwich-family-only** — the
equation/sandwich split of the witness characterization, promoted to
the classification of numbers.  Collapse-vs-rigid concretizes once
more as degree-1 vs degree-≥2, and *irreducibility* is the
lowest-terms criterion one rung up: a factorable equation is the
polynomial world's gcd-strip.

Open brick 6: **the minimal polynomial as the next rung's
lowest-terms normal form** — existence (every algebraic number has a
monic minimal polynomial) + uniqueness, mirroring
`gcd_strip_coprime` + `coprime_repr_unique` one level up; candidate
ground: the existing `PolyRoot/` (FactorTheorem, IntEuclid) +
`ZSqrt*` instances.
