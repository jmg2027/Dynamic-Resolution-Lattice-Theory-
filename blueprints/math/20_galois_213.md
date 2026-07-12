# Galois Theory 213 — Blueprint (finite seed)

**Priority**: ★★★ (verified structural absence; the corpus's own objects demand it)

Implements topic **D7** of `research-notes/frontiers/research_program_year_horizon.md`:
the second verified absence — the corpus has order-theoretic Galois connections
(`lean/E213/Lib/Math/Order/GaloisConnection.lean`) but **zero field-extension
Galois theory**, while already living inside ℚ(√5), ℚ(i), ℚ(ζ₅), 𝔽_{p²}
(Frobenius is formalized).  Conceptual decomposition already written:
`research-notes/decomposition/practice/galois.md` (Fix ⊣ Inv as an adjoint pair
of readings; correspondence = closure collapses to id).  This blueprint turns
that decomposition into Lean, on **fixed small cases only**.

---

## 1. Why This Field

Classically: field extensions, splitting fields, Gal(L/K), the fundamental
theorem, solvability.  The classical route needs splitting-field *existence*
(quotients of polynomial rings, maximal ideals — choice-adjacent) and a
general theory of bases.  213 does not take that route (see §6 walls).

What the corpus has **already proven**, without ever saying "Galois":

- `fp2Frob` (`Lib/Math/NumberTheory/ModArith/FP2Sqrt5.lean`, generalized in
  `FP2SqrtD.lean`): the 𝔽_{p²} Frobenius as a map on pair-carriers, with
  involution (`fp2Frob_involution`), ring-hom (`fp2Frob_add`, `fp2Frob_mul`),
  and `x · σ(x) = (Norm(x), 0)` (`fp2Mul_self_frob`) — all universal in `p`, PURE.
- `theory/essays/synthesis/conjugation_flips_the_modulus.md`: conjugation in
  ℤ[ω] carries `mod π` to `mod π̄` (`EisensteinConjModEq.conj_modEq`), descends
  to the quotient **iff** the modulus is conj-stable, and in the inert case
  *is* the q-power Frobenius (`EisensteinFrobeniusConj`).  A Galois-action
  fact, proven ∅-axiom, waiting to be named.
- `GoldenFieldBridge.lean`: the `x ↦ −x` morphism `bPoly(−x) = gPoly(x)`
  identifying the two generators of one field ℚ(√5) — Galois-theoretic
  change-of-generator bookkeeping already in the repo.
- `Icosahedral/CyclotomicFive.lean`: the tower ℚ ⊂ ℚ(√5) = ℚ(ζ₅)⁺ ⊂ ℚ(ζ₅),
  Gal ≅ C₄, σ: ζ↦ζ², ⟨σ²⟩ = conjugation; Gauss periods proven
  (`golden_real_subfield`).
- Both reciprocity laws closed: quadratic via Zolotarev
  (`ModArith/Zolotarev*.lean`), cubic in both cases
  (`theory/math/numbertheory/cubic_reciprocity.md`,
  `CayleyDickson/Integer/EisensteinCubicReciprocity*.lean`).

The seed's job is not to import field theory; it is to **name the structure
these proofs already share** and close the small correspondence theorems that
tie them into one picture.

## 2. 213-native Emergence

### 2.1 A field extension is a Lens refinement

The base reading cannot separate the two roots of `x² − 5`: from ℚ's
distinguishing, `√5` and `−√5` are one undifferentiated thing (the polynomial
is the finest base-expressible pointing at them).  Adjoining `√5` is a **finer
distinguishing of roots** — a Lens refinement (`Lens.refines`: kernel
containment), not a new ontological layer.  Per the slot-arithmetic ontology
(`theory/math/numbersystems/slot_arithmetic.md` §1: **the tuple is the
number**), the extension carrier is literally a tuple: `a + b√5` **is** the
pair `(a, b)`, with hand-written multiplication.  `FP2 := Nat × Nat` in
`FP2Sqrt5.lean` already does exactly this mod p.

### 2.2 The Galois group is the group of readings preserving the base

An automorphism is a **self-reading of the extension carrier that preserves
the operations and fixes the base slot** — a reading, not a mysterious
symmetry.  The group exists *because* the base cannot separate the root-pair:
the swap `(a, b) ↦ (a, −b)` is invisible to every base-expressible relation.
Conjugation = the **swap-Lens** on the root-pair.  The fixed field = what all
readings agree on = the base distinguishing recovered.  This is the
`⟨C|L⟩ ⊕ Residue` shape: the root-pair indistinguishability is the *residue of
the base reading*, and the Galois group is that residue made into a group of
readings (cf. `decomposition/practice/galois.md`: Fix/Inv as two
order-reversing family-readings).

### 2.3 Conjugation-flips-the-modulus is already the Galois action

The corpus's own theorem: conjugation does **not** act inside a split residue
field (`ℤ[ω]/(π)` ≅ 𝔽_p is prime, automorphism-free); it maps *between* the
conjugate readouts, and descends exactly when the modulus is conj-stable — the
inert case, where it equals Frobenius.  "Which element of the Galois group is
Frobenius at p" is therefore a question the repo has already answered twice
(k = 2: `FP2SqrtD` docstring Lens `(√D)^p ≡ (D/p)·√D`; k = 3:
`EisensteinFrobeniusConj`).  Phase GE only restates it.

### 2.4 The correspondence is the namesake, finally at home

`Order/GaloisConnection.lean` has the full adjunction engine (unit, counit,
triangle identities, closure `g∘f` extensive/monotone/idempotent) —
relation-parametric, no typeclasses, PURE.  Its namesake instance — subgroup
lattice ↔ subfield lattice — was never built.  For a fixed biquadratic case
both lattices are **5-element finite posets**: the fundamental theorem becomes
a finite lattice-isomorphism, `decide`-friendly.  The correspondence =
*closure collapses to id on the closed elements* — the residue vanishes there.

### 2.5 No basis-independence needed

Classically Gal(L/K) needs `[L:K]` and linear independence.  The tuple
ontology sidesteps this: the carrier **is** the tuple type, automorphisms are
defined on tuples, and cross-relations (e.g. `(0,1)·(0,1) = (5,0)`) are
theorems about the carrier.  Irrationality (`Sqrt5IrrationalPure`) exists
where the classical reading wants it, but nothing here depends on a basis
theorem.

## 3. Building Blocks

| Tool | Use |
|---|---|
| `ModArith/FP2Sqrt5.lean`, `FP2SqrtD.lean` | 𝔽_{p²} pair-carrier, `fp2Frob`, norm, ring laws — Phase GC is half-done |
| `Order/GaloisConnection.lean` (+ `Composition`) | the adjunction engine for Phase GB |
| `CayleyDickson/Integer/` ℤ[i], ℤ[ω] arc | conj as ring involution, split/inert primes, cubic character + reciprocity |
| `EisensteinConjModEq`, `EisensteinFrobeniusConj` | conjugation-flips-the-modulus; conj = Frobenius (inert) |
| `GoldenFieldBridge.lean` | `bPoly(−x) = gPoly(x)`, shared disc 5, ramification at 5 |
| `Norm5.lean`, `GoldenNormBridge.lean`, `PellNorm.lean` | the norm `a² − 5b²`; Cassini as norm value (`lucas_fib_isNorm5neg`), the corpus's det = ±1 object |
| `Icosahedral/CyclotomicFive.lean` | ℚ(ζ₅) tower, Gauss periods, `golden_real_subfield` |
| `ModArith/Zolotarev*.lean`, `QRNegOne`, `SumTwoSquares*` | quadratic reciprocity corpus for Phase GE |
| `Padic/TeichmullerUnit.lean` | μ_{p−1} ⊂ ℤ_p^× — the p-adic face of the cyclotomic phase (GD cross-link) |
| `PolyRoot/FactorTheorem.lean`, `UnitsOfZn`, `MultiplicativeOrder` | root counting; order of 2 mod 5 = 4 (GD) |
| `Group/` (ℤ/nℤ, Sₙ, actions) | C₂, C₂×C₂, C₄ as concrete groups |

## 4. Phase Plan

### Phase GA — the quadratic case: ℚ(√5) and ℚ(i) as pair-carriers

1. `ZSqrt5 := Int × Int` (slot form of `a + b√5`; Int213 witness-style), with
   add/mul/conj; likewise reuse the Cayley–Dickson level-1 pair for ℤ[i].
2. **Conjugation is the swap-Lens**: `conj (a, b) = (a, −b)`; involution +
   ring-hom (the `fp2Frob_add`/`fp2Frob_mul` pattern, now over Int with
   `ring_intZ` — no mod-p bookkeeping, easier).
3. **The norm is the de-signed square**: `N(a,b) = a² − 5b² = x · conj x`;
   multiplicativity (Brahmagupta, cf. `PellNorm`); tie to the corpus's
   det = ±1 object: `lucas_fib_isNorm5neg` says `(L_m, F_m)` realizes
   `N = 4(−1)^m` — Cassini **is** a Galois-norm evaluation.
4. **Gal = C₂**: any operation-preserving self-reading fixing the scalar slot
   sends `(0,1)` to a square root of `(5,0)`, and `(a,b)² = (5,0)` forces
   `(a,b) = (0, ±1)` (witness-form Diophantine: `ab = 0`, `a² + 5b² = 5`) —
   exactly {id, conj}.
5. **Fixed-field theorem**: `conj x = x ↔ x.2 = 0` — one line, but it is *the*
   statement "the base = what all readings agree on".

Success: Gal(ℚ(√5)/ℚ) ≅ C₂ and Gal(ℚ(i)/ℚ) ≅ C₂ as classification
theorems on the carriers, no basis lemma anywhere, all PURE.

### Phase GB — the correspondence for ℚ(i, √5): C₂×C₂ ↔ subfield lattice

1. Carrier: 4-tuples `(a, b, c, d)` = `a + bi + c√5 + di√5`, explicit
   multiplication table.
2. Three involutions: σ (`i ↦ −i`), τ (`√5 ↦ −√5`), στ; group table = C₂×C₂
   (`decide` on the 4-element group).
3. Fixed sets by vanishing slots: Fix(σ) = `{(a,0,c,0)}` = ℚ(√5),
   Fix(τ) = ℚ(i), Fix(στ) = `{(a,0,0,d)}` = ℚ(√−5) (the disc −20 slot),
   Fix(1) = all, Fix(G) = scalars.
4. **The finite Galois correspondence**: subgroup poset (5 elements) ↔
   subfield poset (5 elements), `Fix` and `Inv` mutually inverse,
   order-reversing — a finite lattice isomorphism, closed by `decide` +
   instantiation of `Order/GaloisConnection` (`gc_unit`, `gc_counit`,
   closure = id since every subgroup is closed here).  The machinery meets
   its namesake.
5. Degree bookkeeping as counting: |subgroup| · |index| = 4 read as slot
   dimensions — the tuple arity is the degree, no `[L:K]` theory.

Success: one capstone `galois_correspondence_biquadratic` bundling the
bijection + order reversal + fixed-field computations, PURE.

### Phase GC — 𝔽_p: Frobenius as the generator

1. **Frobenius = p-th power**: `fp2Pow p x p = fp2Frob p x` for canonical
   `x`, `p` odd prime with 5 NQR.  Per-prime `decide` smoke (p = 3, 7, 13, 17)
   first; universal via Euler's criterion `(√5)^p = 5^((p−1)/2)·√5 ≡ −√5`
   (freshman-dream + `BinomPrime` machinery; the `FP2SqrtD` docstring already
   states the Lens).
2. **Gal(𝔽_{p²}/𝔽_p) = ⟨Frob⟩ ≅ C₂**: a ring self-reading fixing the scalar
   slot sends `(0,1)` to a root of `x² = D`; a quadratic has ≤ 2 roots
   (`PolyRoot/FactorTheorem` + mod-p inverses from `ModBezoutInvariant`),
   giving exactly {id, fp2Frob}.
3. **Fixed-field theorem**: `fp2Frob p x = x ↔ x.2 ≡ 0 (mod p)` for odd p
   (from `2b ≡ 0 → b ≡ 0`) — the fixed field of Frobenius is 𝔽_p.  Universal
   in p, PURE.
4. Weld: `EisensteinFrobeniusConj` (conj = q-Frobenius on ℤ[ω]/(q) ≅ 𝔽_{q²})
   re-cited as the same theorem in a second carrier.

Success: `fp2Frob` becomes *the* generator, fixed-field theorem universal
in p.

### Phase GD — the cyclotomic case ℚ(ζ₅): Gal ≅ (ℤ/5)^× ≅ C₄

1. Carrier: 4-tuples on the basis `ζ, ζ², ζ³, ζ⁴` (relation
   `1 + ζ + ζ² + ζ³ + ζ⁴ = 0` baked into the multiplication table — explicit
   polynomial `x⁴+x³+x²+x+1`, no quotient construction).
2. σ: `ζ ↦ ζ²` = the basis permutation by mult-by-2 on exponents; **order 4**
   because 2 is a primitive root mod 5 (`MultiplicativeOrder`/`UnitsOfZn`;
   `decide` on the permutation).  Gal ≅ (ℤ/5)^× ≅ C₄.
3. **Gauss periods**: η₀ = ζ+ζ⁴, η₁ = ζ²+ζ³ are the ⟨σ²⟩-orbit sums; fixed
   field of ⟨σ²⟩ (= conjugation) is ℚ(√5), the periods the roots of
   `x²+x−1` — already proven as `golden_real_subfield`
   (`CyclotomicFive`) and bridged by `GoldenFieldBridge.bPoly_neg_eq_gPoly`.
4. **A cyclic correspondence instance**: chain 1 ⊂ ⟨σ²⟩ ⊂ C₄ ↔
   ℚ(ζ₅) ⊃ ℚ(√5) ⊃ ℚ — a second, cyclic, finite lattice-isomorphism
   (3-element chains), same `GaloisConnection` instantiation as GB.
5. Cross-domain payoff (cite `research-notes/frontiers/cp_crossdomain_insights.md`
   Insight/bridge 3): the CP-phase **C₄** and the **golden modulus** 1/φ² are
   this Galois group and this fixed field; the p-adic face is the Teichmüller
   decomposition μ₄ × μ_{(p−1)/4} (`Padic/TeichmullerUnit`).  The physics
   deployment's apex objects get their Galois names.

Success: `gal_cyclotomic_five ≅ C₄` + the chain correspondence + the
period-fixed-field theorem re-welded, PURE.

### Phase GE — payoff: reciprocity as Frobenius-splitting

1. **Quadratic**: restate the Legendre symbol as *the Frobenius element*:
   `(D/p) = +1 ⟺ Frob_p acts trivially on the root-pair of x² − D` — i.e. the
   `FP2SqrtD` split/inert fork **is** "which element of Gal(ℚ(√D)/ℚ) is
   Frob_p".  Weld to the Zolotarev corpus (`ZolotarevMuBridge`, `psign_mulPerm_qr`):
   quadratic reciprocity = a symmetry of Frobenius assignments, the modern
   reading, at fixed D ∈ {−1, ±2, 5} where the corpus already computes.
2. **Cubic**: the residue symbol `(·/π)₃` = the value of Frobenius on cube
   roots (`EisensteinCubicCharFp` arc); the inert case's engine — conj **is**
   the q-Frobenius — is `conjugation_flips_the_modulus` verbatim.  Restate
   `EisensteinCubicReciprocity` (+ `Split`) as: *the Frobenius elements
   attached to the two primes agree* — one Frobenius picture over both the
   μ₂ (Zolotarev sign) and μ₃ (Eisenstein) readouts.
3. **The 5-selection as Frobenius**: `CyclotomicFive`'s "5 splits in ℤ[i],
   inert in ℤ[ω]" (C₄ over C₆ selection) restated as Frob₅ trivial in
   Gal(ℚ(i)/ℚ), nontrivial in Gal(ℚ(ω)/ℚ).
4. Capstone: `reciprocity_is_frobenius_splitting` — a bundled statement tying
   the quadratic and cubic corpora into the single reading "a reciprocity law
   is a constraint on the Frobenius-assignment map", every citation PURE.

Success: no new arithmetic — GE is pure re-reading; its value is that the
reciprocity corpus, `fp2Frob`, and the Galois seed become **one** object.

## 5. Connections to Other Tracks

**Reciprocity corpus** (GE = its modern restatement, D7's stated cross-payoff);
**Cayley–Dickson** ℤ[i]/ℤ[ω] (the conjugation involutions were the Galois
actions all along); **CP-phase physics** (GD names the C₄ and 1/φ² objects,
bridge 3); **Order/GaloisConnection** (GB/GD are the namesake instances);
**GRA universality** (`16_gra_universality.md` — the Frobenius picture is the
entry point to any future Langlands-flavored reading).

## 6. Honest walls (scope fence, stated up front)

- **No splitting-field existence in general.**  Constructing a splitting
  field for an arbitrary polynomial needs quotient-ring/maximal-ideal
  machinery (choice-adjacent, axiom-dirty in known routes).  Everything here
  is **explicit-polynomial, fixed-degree**: carriers are tuples with
  hand-written multiplication tables for named polynomials (`x²−5`, `x²+1`,
  `x²−x−1`, `x⁴+x³+x²+x+1`).  Universality is in *parameters* (p, D), never
  in the polynomial.
- **No general fundamental theorem.**  The correspondence is proven per fixed
  case as a finite lattice isomorphism (`decide` + the adjunction engine),
  not for arbitrary finite extensions.
- **Solvability by radicals out of scope** (likewise general Sₙ Galois
  groups, primitive-element, infinite Galois theory) — a future blueprint if
  ever, not scope creep here.

## 7. Key Insights (★)

★ **The Galois group is the residue of the base reading, organized**: the
root-pair the base cannot separate *is* the swap's existence proof.

★ **Conjugation-flips-the-modulus was Galois all along** — the corpus proved
the action (descent iff conj-stable; = Frobenius when inert) before naming it.

★ **The correspondence is finite and decidable** at fixed small cases — the
fundamental theorem as a 5-element lattice iso, the adjunction's closure
collapsing to id.

★ **Reciprocity = Frobenius bookkeeping** — the μ₂ and μ₃ symbol corpora
become one picture.

## 8. First Marathon Command

```
"Start Phase GA.  ZSqrt5 pair-carrier + conj swap-Lens (involution, ring-hom)
 + norm = x·conj x + Gal(ℚ(√5)/ℚ) ≅ C₂ + fixed-field theorem."
```
