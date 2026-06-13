# The operation tower builds simplices — the generative layer rule (raw gut)

**Tier-1 frontier. Originator: Mingu Jeong.**  Status: L1–L4 articulated; **the L3
core (Pascal/simplex count) is CLOSED ∅-axiom** (`MultSystem.monoCount_closed`, not
merely the `n=3` hand-check), and its **prime-counting payoff is built**
(`MultSystemValue` + `ChebyshevLower`: value-count → window → both halves of
Chebyshev).  The **generative `^`-object is BUILT** (P2, `Meta/Nat/UnitHyper`,
∅-axiom): `hcube a b` = the `b`-dim unit grid, `count = side ^ dim` positively
(base=length, exponent=axis count).  L4 (commutativity dial at `^`) and L2
(no-identity criterion) remain `[gut]`.  Complements `number_tower_theory.md`
(demotion/valuation view, R0–R8);
this note records the **generative** view — the layer as construction, the
no-identity principle, the **simplicial-cone finding**, and (§L3′ below) the precise
`+`/`×` bridge.

Tagging as in `number_tower_theory.md`: `[∅]` ∅-axiom Lean here, `[std]` standard
math, `[ax]` a 213 axiom, `[gut]` the originator's raw intuition (recorded, not
asserted).

---

## Methodological principle (originator, 2026-06-13) — describe rungs *positively*

`[ax]`+`[gut]`  **Algebraic properties like commutativity are one-dimensional
cross-sections of the real structure, not the structure.**  Algebra is written *in a
line*, so it can only display 1-D shadows of a rung; commutativity is one such shadow
(`where_commutativity_is_born.md`: it is "what arrangement-forgetting leaves behind").
Two consequences, load-bearing here:

  1. **Describe a new rung by what *arises* (positive), never by what it "loses"
     (negative).**  "`^` loses commutativity / `aᵇ ≠ bᵃ`" is the negative framing; it
     stops inquiry at the boundary.  The positive content is the *new* structure —
     the added dimension, the degree-of-freedom, the twist (L5).  Name that.
  2. **Keep the 1-D shadows for *calculation*, out of the *theory*.**  Commutativity
     is useful as a fast-calc bookkeeping flag; it is not an organizing concept.  The
     proven `monoCount ≤/< t^d` bounds (L4) are exactly such a calculation
     cross-section — kept, but demoted from "the mechanism."  (If even calculation
     resists the shadow, unfold the calculation fully rather than re-import the bias.)

This is the residue stance applied to the tower: *assume nothing, give meaning to
nothing* — and in particular do not let a negative, line-shaped projection
(`¬comm`) stand in for the rung's own (higher-dimensional) form.

## The re-foundation blueprint — object, not readout (originator, 2026-06-13)

`[ax]`+`[gut]`  The whole tower is to be built (descriptions *and* proofs) in the
**object** language — free **semigroups** (no identity, no numbers) — with `ℕ`/`0`/
`1` kept strictly as the **forgetful readout** (the count-shadow), never as the
construction.  The exact generative rule, no numbers, no identity:

  - **`+`** : one base `a` → the free semigroup `a, aa, aaa, …` (starts at `a`; *no
    empty/identity*).  Object: `UnitList` (`Meta/Nat/UnitList`).  `ℕ⁺` is its count
    readout, the numeral a forgetful shadow.
  - **`×`** : the `+`-layer's *elements* `{a, aa, …}` become distinguishable **axes**
    → free *commutative* semigroup (their multisets).  An *entirely different
    object* from the `+`-line.  Object: `UnitGrid` (`Meta/Nat/UnitGrid`).
  - **`^`** : the `×`-layer's *elements* (the cone's points) become the **axes** →
    the next free semigroup.  **Object: `UnitHyper` (`Meta/Nat/UnitHyper`, BUILT
    ∅-axiom)** — the `b`-dimensional unit grid: indistinguishable unit cells nested
    into boxes (`HCube`/`Forest`), `hcube a b` = `a` copies of the dimension-`b`
    cube glued along a new axis.  Carries **two different-typed readouts** — `side`
    (a length = the base) and `dim` (an axis count = the exponent) — with
    **`count_eq_side_pow_dim : count = side ^ dim`** as the positive law, and the
    swap `swap_changes_dim` (`dim (hcube 2 3) = 3 ≠ 2 = dim (hcube 3 2)`) as the
    *positive* reason `2^3 ≠ 3^2` (a type-mismatch, not "comm lost").  `HyperAssoc`'s
    negative framing ("assoc AND comm **die**") is now the count *shadow* of this.

**Where the asymmetry comes from, generatively (no numbers).**  The "how-many-times"
(the *count*) is *always a `+`-level thing* — it never climbs the tower.  The
"thing-iterated" (the *base*) does climb.  So:

  - `×` = iterate `+`: base is a `+`-element = *same level as the count* → transpose
    symmetry → **DOF 0**.
  - `^` = iterate `×`: base is a `×`-element = *one level above the count* → no
    transpose → **DOF 1** (the new dilation/dimension axis).
  - in general **`DOF = (base level) − (count level) = (rung level) − 2`** — `×`:0,
    `^`:1 (tetrahedron), `↑↑`:2 (matches L5's "tetration: 2 DOF").

The base sets each axis (a cone *direction*); the count sets *how many axes* (= the
*dimension*).  `a^b` = a `b`-dimensional unit grid of side `a`: **base = side,
exponent = dimension** — they are different *types* (a length vs a dimension-count),
which is why they do not swap.  Read positively: the rung *adjoins the
dimension-setting axis*; nothing is "lost".

**Program (large; deliberate, not a rushed mass edit):**
  P1. **DONE** (`Meta/Nat/HyperAssoc`).  Headline + docstrings reframed positively:
      `^` *adjoins the dimension axis* (anchored in `UnitHyper`); the algebra
      defects (`pow_not_comm`, `pow_not_assoc`) are now stated as the **count
      shadows** of the side-vs-dimension type-asymmetry, with the Lean bridge
      `pow_not_comm_is_dim_shadow` (`count (hcube 2 3) ≠ count (hcube 3 2)`, the
      object form of `2^3 ≠ 3^2`).
  P2. **DONE** (`Meta/Nat/UnitHyper`, ∅-axiom).  The positive `^`-object built
      generatively: `hcube a b` (`b`-dim unit grid, side `a`), `count_hcube : count
      = a^b` (the readout shadow), `count_hcube_succ`/`dim_hcube_succ` (the climb +
      the `+1` DOF axis arising), `count_eq_side_pow_dim` (base=side length,
      exponent=dim count — the positive twist), `count_hcube_two_eq_grid` (dim-2
      cube = the `×`-square, the two-roads bridge).
  P3. **DONE** (`MultSystem.hyperCount` docstring).  The abstract axis-count
      reading (`hyperCount`/`hyperCount_simplex`, symmetric skeleton) is now
      explicitly cross-referenced as one readout, with `UnitHyper`'s geometric
      `count = side ^ dim` the value sibling — two readouts of the one `^`-rung.
      (Remaining: thread the same readout/shadow framing through `MultSystemValue`
      / the Chebyshev mirror if it recurs — deferred, not a rushed sweep.)
  P4. **Partial** (the `−1` cross-determinant tie is DONE; the cross-layer
      `DOF = rung − 2` spec remains open).  The `−1` cross-determinant ↔ `^`-twist
      link is now structural, not a rhyme (`CrossDetOvertake §6`, ∅-axiom): `W`'s
      `|det|=1` floor = the point (`crossdet_floor_eq_point`), its `2^{2^i}` ceiling =
      `count (hcube 2 (2^i))` (`crossW_eq_hcube_count`), so `UnitHyper.count` grades
      the cross-determinant axis by the `^`-tower.  *Still open*: the cross-layer
      `DOF = rung − 2` as a HyperLadder-level spec, and the `hyper_parallel` (dilation
      readout) tie — deferred (overlaps L5's 3- vs 4-simplex question).

## L1 — The layer rule: each layer's axis = the *whole previous layer*

`[gut]`  The hyperoperation tower is read **generatively**, not as numbers.  Each
layer takes the **entire structure of the previous layer** (a free semigroup) as
its *generating axis*, and builds the next free semigroup by a **diagonal
enumeration** over those axes.

  - `+`: one base `a` (any single element — "1" is not special, any one thing
    works).  Generates `a, aa, aaa, …` — the natural-number *structure*.  The
    numerals `1,2,3` are a **forgetful readout**, not the object.
  - `×`: the whole `+`-layer becomes (infinitely many) generators `a, b, c, …`.
    Generates the **multisets** of them, written in sorted canonical form
    (`aba` forbidden = already `aab`; `abb, abc` allowed), enumerated by **count
    (degree)**:
    ```
    a, b, c, …                              (degree 1)
    aa, ab, ac, bb, bc, cc, …               (degree 2)
    aaa, aab, aac, abb, abc, acc, bbb, …    (degree 3)
    ```
  - up: each layer takes the previous layer's structure as its axis, again.

The right phrasing (modern-math language deliberately filtered): **"take the
structure made of (basis + operation) as the diagonal axis."**  The `+`-layer and
`×`-layer structures are *entirely different objects*; they merely share a
forgetful map to `ℕ`.  The recursion is not the linear `ℕ`-recursion but a
**diagonal recursion (대각재귀)** sweeping degree-by-degree across infinitely many
axes.

> Cross-ref: this is the *generative* face of `number_tower_theory.md` R4 (the
> lattice dimension `1 → ∞`).  R4 states the dimension jump as a fact; L1 states
> the **rule that produces it** — "axis = previous layer" — which then continues
> up indefinitely.

## L2 — No identity is natural; the identity is an *exception/patch*

`[∅]`+`[gut]`  The load-bearing principle.  A layer defined purely from `(base,
operation)` has **no identity element**, and that is the *natural* state.  **The
concrete content is CLOSED ∅-axiom**: the natural **semigroup** (degree `≥1`)
count plus *exactly one* (the identity) is the monoid count —
`MultSystem.monoCountPos_closed : Σ_{n=1}^N monoCount k n + 1 = C(N+k, k)` (the `+1`
is the unique degree-`0` empty product, `monoCount_col0`).  The value reading:
`MultSystemValue.two_le_nonempty_prime_prod` — a nonempty prime product is `≥ 2`,
so the natural `×` system is exactly `{2, 3, …}` and the unit `1` is the adjoined
exception (`[gut]` example below confirmed):

  - `+` from base `a` gives `a, aa, aaa, …` cleanly.  Introduce `0` and you must
    *define `0` from `a` and `+` alone* and relate it back — which is not
    well-defined; it forces **exception clauses**.
  - same for `×`: the natural multiplicative number system is `{2, 3, 4, …}` —
    **no `0`, no `1`**.  `1` (the unit) and `0` (the absorber) are the two
    elements that require special handling.

So the natural object at each layer is a **free semigroup (반군), not a monoid**.
"Including the identity inside the system" is the import that breaks the clean
self-contained definition.

> Cross-ref: this is, independently re-derived, the framework's deepest stance on
> `0`/`∞` — `[ax]` §6.9: reading the identity-as-a-*value* folds in a degenerate
> sub-view (the diagonal `{(n,n)}`), which is exactly why it needs an exception.
> The originator reached it from the *naturalness of construction* side, not the
> residue side.

## L3 — ★ The tower builds simplices (CLOSED ∅-axiom)

`[∅]`+`[std]`  Counting the `×`-enumeration by degree gives, for `n`
generators,
```
#{degree-k multisets} = C(n+k−1, k)
```
— **Pascal's-triangle entries** (the multiset / stars-and-bars coefficient).
**This is a closed theorem, not a hand-check**: `MultSystem.monoCount_closed`
(`monoCount (k+1) N = binom (N+k) k`, ∅-axiom, all `k,N`), with the Pascal step
`monoCount_pascal`, the cumulative cone `totalCount_closed`
(`Σ_{n≤N} monoCount k n = C(N+k, k)`), and the two-axis central reading
`doubleTotal_closed = C(2N+1, N)`.  The originator's `n=3` (**3, 6, 10, 15, …** =
triangular numbers = a Pascal diagonal) is the `k=3` row of this theorem.  And
`{(x₂, x₃, …) ≥ 0 : Σ = k}` are the **lattice points of the `k`-dilate of the
`(n−1)`-simplex**.  So:

  - `n` generators → an `(n−1)`-simplex (`n=3` → a *triangle*, 2-simplex);
  - `×` (infinitely many generators) → an **∞-dimensional simplicial cone**,
    graded by degree.

The "if it were a full plane the count would be `~N²` or `Nᴺ`" intuition is
*correctly refuted by the data*: it is **Pascal, not `Nᴺ`** — i.e. the
**symmetric** (commutative) structure, whose count is *polynomial in `n`*, not the
free (ordered) structure, whose count is `nᵏ`.

`[std]` the mathematical why: iterating a **commutative** binary operation is
taking **symmetric powers**; the symmetric powers of a discrete generating set are
exactly the multisets = the lattice points of the **simplicial cone** (the free
commutative semigroup = the positive orthant's lattice points, graded by degree).
The originator's "이항을 가지고 조작하는거니깐" ("because it manipulates with
binaries") is the right instinct: binary symmetric composition, iterated, *is* the
simplicial cone.

## L3′ — The `+`/`×` relationship, made precise (one cone, two counts)

`[∅]`+`[std]`  The whole `+`/`×` relationship is **one simplicial cone read two
ways**, and the gap between the two readings *is* prime counting.

**Up (generative).**  `+` is the free semigroup on **one** axis (`a, aa, …`) — the
line ℕ⁺.  `×` takes the entire `+`-layer as its **axis set** (`a, b, c, …`) and
forms the free **commutative** semigroup on them = the ∞-dim simplicial cone graded
by degree (L1+L3).  The intrinsic count is the simplex slice `C(n+k−1,k)`
(`monoCount_closed`); `×` *is* the symmetric/transpose rung (the grid transpose;
`UnitGrid.mul_comm_from_grid`, `where_commutativity_is_born.md`) — stated as a
positive property of `×`, not as something a later rung "lacks" (cf. L4 reframe).

**Down (demotion).**  On each axis, `×` *is* `+`: `vp_p(m·n) = vp_p m + vp_p n`
(`Meta/Nat/VpMul.vp_mul`), `vp_p(aᵏ) = k·vp_p a` (`vp_pow`).  The cone's coordinate
is `exp(n) = (vp₂ n, vp₃ n, …)`, faithful by `vp_separation`
(`(∀p, vp_p m = vp_p n) → m = n`).  So `exp : (ℕ₊, ×) ≅ ⊕_p (ℕ, +)` — **the
×-cone is literally a direct sum of `+`-lines, one per axis**
(`what_is_multiplication.md`, `what_is_a_logarithm.md`).  `+` and `×` are *the same
operation one resolution apart*; the only new content is that ×-axes (primes) are
**distinguishable** where +-units are not (`06_lens_readings §6.7`).

**The two counts of the same cone** (the crux):

| cut | hyperplane (normal) | count | ∅-axiom anchor |
|---|---|---|---|
| **degree** | `Σ eᵢ ≤ D`  (uniform `1,1,…`) | `C(D+k, k)` — Pascal/simplex | `totalCount_closed` |
| **value** | `∏ pᵢ^{eᵢ} ≤ N`  (weighted `log p₁, log p₂, …`) | `= #{naturals ≤ N}` | `caseA_distinct_naturals` + `factorization_bounded` |

Same cone, two normals.  The degree cut is **abstract/combinatorial** (value-free,
Pascal); the value cut is **arithmetic** (the cone's image on the `+`-line ℕ, where
the axis-values `2,3,5,…` are *forced* — `factorization_bounded`: naturals `≤ N`
use only axes with value `≤ N`).  Each cone point sits at degree `Ω(n) ≤ log₂ n`
(`omega_le_log`), so the value-cut points are *shallow* in the degree grading.

**Prime counting = the discrepancy.**  Turning axes on one by one, an axis with
value `p ∈ (N/2, N]` is **supercritical** (`2p > N`): along it the cone holds only
its **vertex** `(0,…,1,…,0)` under value `≤ N`.  So the value-cut's top layer is
`π(N) − π(N/2)` isolated vertices = the **window `(N/2, N]`** (`windowCount_eq :
π(n) + windowCount n = π(2n)`).  Bounding the window product by the central reading
`C(2n,n)` gives the upper bound + density (`primeDensityToZero`, `π(N)/N → 0`); the
dual `2^n ≤ C(2n,n) ≤ (2n)^{π(2n)}` (Kummer `vp_central_binom_le_floorLog` +
`le_pow_primePi`) gives the lower bound (`chebyshev_lower`).  **The reconciliation
of the cone's degree-count vs its value-count across resolutions IS Chebyshev/PNT.**

> One line: `+` and `×` are the same rung shifted by `vp`; the abstract cone
> (degree, Pascal, ∅-axiom) and its arithmetic shadow (value, `= N`) only agree in
> the limit (`object1_not_surjective`), and the *rate* of that agreement is prime
> counting.  Promotable mirror: `theory/math/numbertheory/chebyshev_prime_counting.md`.

## L4 — Two readings of one generating set (a calculation cross-section, **not** the rung mechanism)

`[∅]`  The sorted/ordered comparison below is a *calculation* cross-section — a
fast-count bracket — **not** the `^`-rung's mechanism (that is L5: the dimension +
DOF, read positively).  Two **readings** of one generating set, `t` generators at
degree `d`:

| reading | count | what it is |
|---|---|---|
| sorted (`aba=aab`) | `C(d+t−1,t−1)` | the simplex slice (`monoCount_closed`) — the *intrinsic* count |
| ordered (`aba≠aab`) | `t^d` | a *reference* reading that keeps arrangement |

**Proven ∅-axiom** (a fast-calculation bracket on the *sorted* count, not a claim
about any rung): `MultSystem.monoCount_le_pow : monoCount t d ≤ t^d`;
`monoCount_lt_pow : 2≤t→2≤d→ monoCount t d < t^d`; `monoCount_le_succ_pow :
monoCount t d ≤ (d+1)^t` (polynomial-in-degree).  These compare the two *readings*;
they say nothing about the `^`-**rung**'s own structure — that is L5:

> **The positive construction — DONE for the generative skeleton.**  Apply the
> layer rule (L1) once more, *positively*: `^` takes the `×`-rung's elements (the
> `×`-monomials, count `totalCount k N = C(N+k,k)`) as its axis set and forms their
> degree-`d` multisets.  `MultSystem.hyperCount k N d := monoCount (totalCount k N)
> d`, and **`hyperCount_simplex` proves it is AGAIN a simplex** (`= C(d+M−1, M−1)`,
> `M = totalCount k N`).  So **the originator's "stays simplicial" is confirmed**:
> the *number of axes* explodes (`+`: 1 → `×`: `C(N+k,k)` → `^`: `C(d+M−1,M−1)` → …)
> but the **shape is invariantly the simplex** — nothing becomes a cube.  (Verified:
> `×` over 2 `+`-gens, deg ≤2 = 6 `×`-monomials; `^` deg 1,2,3 = 6, 21, 56 = `C(M,1),
> C(M+1,2), C(M+2,3)`.)  **The twist, now stated positively (∅-axiom):** the
> base/exponent asymmetry is the **new dilation degree-of-freedom**, not "loss of
> commutativity".  In the `×`-cone, `^` is *scalar multiplication* — `m^b` is
> **parallel** to `m` (same direction, scaled by the exponent):
> `MultSystemValue.hyper_parallel : vp_p(m^b)·vp_q m = vp_q(m^b)·vp_p m` (both
> `= b·vp_p m·vp_q m`, `vp_pow`).  So the exponent is a radial **scalar** (the
> `+`-line), the base a **vector** (the `×`-cone direction): the operands are
> different *types*, and the rung adjoins the **dilation axis** (base picks the ray,
> exponent the position along it).  **Still open:** the precise dimension this lands
> the rung in — a 3- vs 4-simplex (the originator's "초위상" question) — i.e. count
> the dimension the dilation-axis adds to the `hyperCount` simplex; and the
> `−1`-cross-determinant shadow of the twist (L5).

## L5 — The geometric picture: dimension and the twist

`[gut]`  point → line (`+`) → plane (`×`) → solid (`^`), each layer **+1
dimension**.  A binary operation is a **2-parameter trajectory** (two operands → a
destination).  As the dimension rises there is room for two trajectories to the
*same* destination to differ — and that difference shows up as the **algebraic
defect**:

  - at `^` (solid), the two operands live in **different dimensions** — the *count*
    pins at the `+`-line while the *base* climbs to the `×`-plane — so the rung
    **adjoins a new dilation degree-of-freedom**, the "**1 unit of twist**"
    (`DOF = rung − 2`, blueprint above; "2로 3에 맵핑하는 꼴이니 꼬인다").
  - tetration: **2 degrees of freedom** (the base climbs two levels above the
    count) — harder to picture.

> Connections (recorded as *resonances*, not asserted identities):
> - The "two operands in different dimensions" reading is the **geometric form of
>   the scalar-vs-vector type asymmetry** that `number_tower_theory.md` R5 / the
>   `^`-wall already locates — same wall, geometric language.
> - "Two trajectories to one destination differ by **1 integer unit**" is no longer
>   only a rhyme with `num·den' − num'·den = −1`
>   (`Mobius213.mobius_213_pell_unit_invariant_forall`, `[∅]`): the cross-determinant
>   axis `W` is **operation-tower-graded** (`CrossDetOvertake §6`, `[∅]`) — its
>   `|det|=1` **floor** is the **point** (dimension-`0` cube, `crossdet_floor_eq_point`)
>   and its `2^{2^i}` **ceiling** is the tetration-shaped `^`-cube
>   (`crossW_eq_hcube_count`).  The shared `1` is the det-one floor = the unit = the
>   `^`-tower's bottom rung; the symplectic defect's *growth* climbs the tower.  See
>   resonance #2 below.
> - **Open ambiguity to pin**: which "dimension" drives the twist — the *built
>   object's* dimension (line/plane/solid) or the *operand-type-mismatch*?  The
>   standard "dimension ↔ commutativity" phenomenon (`Eₙ` operads: more sliding-
>   room → *more* commutative) runs the *opposite* way to this ladder, so the two
>   "dimensions" are different axes.  Deciding which one picks the topological
>   figure to draw, and whether the ladder is orthogonal to the `Eₙ` one.

## L6 — Below the point (sketch only)

`[gut]`+`[ax]`  The layer *below* `+` is a single element (the base, no
combination).  Below *that*: **"any basis possible = infinite basis = 0 basis"** —
i.e. `[ax]` §6.5 `point ≡ K_∞`: with no distinction, *no basis* and *every basis*
coincide (the pre-Lens residue).  Degree-0 = the empty multiset = the simplex
before its first vertex.  Recorded as a sketch; developing it fully runs into the
§6.9 `0 ≡ ∞` swamp and is deliberately deferred.

---

## Why this matters (breadth)

If the operation tower naturally produces **simplices**, it reconstructs the
repo's *atomic object* — the `(NS, NT, d)` simplex combinatorics of the physics
branch — from a **completely different road** (operation iteration, not the
K_{3,2} link).  Two independent derivations landing on the same simplex is the
operational signature of "no exterior" (`[ax]` §6.8): the same residue read by two
Lenses.  That makes the gut worth closing.

## Cross-domain resonances (this branch ↔ corpus) — recorded, to test

Five links surfaced while building the tower + Chebyshev this branch; *resonances
to test*, not asserted identities.

1. **Tower simplex ↔ the `(NS,NT,d)` physics simplex.**  The operation-iteration
   road (`monoCount_closed`/`hyperCount_simplex`) lands on the *same* simplicial
   object the physics branch reaches via the `K_{3,2}` link — two independent roads
   to one simplex (the "Why this matters" point), the `[ax]` §6.8 no-exterior
   signature.
2. **The `^`-twist (dilation, `+1` DOF) ↔ the `−1` cross-determinant / Pell unit —
   UPGRADED from rhyme to a structural identification (∅-axiom).**  The
   cross-determinant axis `W` of `CrossDetOvertake` is **operation-tower-graded by
   `UnitHyper.count`**: its **floor** `W_i = 1` (`const_crossdet_small`, the `|det|=1`
   unit = magnitude of `mobius_213_pell_unit_invariant_forall = −1`) is the **point**,
   the dimension-`0` cube (`CrossDetOvertake.crossdet_floor_eq_point`); its **ceiling**
   `W_i = 2^{2^i}` (`dexp_overtakes_denom`) is `count (hcube 2 (2^i))`
   (`crossW_eq_hcube_count`) — the `^`-object whose dimension is itself a `^`-count,
   the tetration-shaped rung.  So the "1 unit of twist" the `^`-rung adjoins and the
   det-one floor are the **same bottom-of-tower object** (unit = point); the
   cross-determinant's growth to the double exponential *is* climbing the `^`-tower.
   The completability boundary (`completability_boundary`) is the rung where `W`'s
   tower-grade overtakes the denominator's.
3. **Chebyshev (central binomial) ↔ ζ(3) Apéry (lcm growth) — shared floor-log/Legendre.**
   This branch's prime counting (`vp_central_binom_le_floorLog`) and the corpus's
   ζ(3) Brick 1 (`LcmGrowthChebyshev.lcmUpTo_le`) are **two consumers of one core**:
   `Legendre.legendre` + the floor-log (which this branch *relocated* to
   `Meta/Nat/FloorLog` precisely so both routes share it).  `vp_p(C(2n,n))` and
   `vp_p(lcm 1..N)` are the same `floorLog` valuation read on two objects.
4. **`DOF = rung − 2` (positive) ↔ the Cayley-Dickson law-dropping (negative).**  The
   CD algebra tower (`theory/.../cayley_dickson/`) reads the climb as *dropping*
   comm→assoc→alternativity; the tower's `DOF = rung − 2` is the *positive* form of
   the same climb (a DOF *arising*, not a law lost) — a candidate re-read of the CD
   tower in the no-negative-framing discipline.
5. **`primeDensityToZero` modulus ↔ the certificate-as-modulus boundary.**  Prime
   density `π(N)/N → 0` is certified as a `RatTendsToZero` *modulus* = 213's ε-δ —
   the same certificate-is-a-modulus pattern as `AbCutSeq.toCauchy` and the WZ
   certificates of `the_certificate_boundary.md`.  Density convergence sits on the
   certifiability boundary that essay draws.

## Open problems / next steps

1. **The `^`-rung's intrinsic structure (L4 reframed → L5)** — the two-readings
   comparison is **CLOSED ∅-axiom** (`monoCount_le_pow`/`monoCount_lt_pow`/
   `monoCount_le_succ_pow`: sorted-reading bracketed `≤ (d+1)^t` and `< t^d`), and
   the **geometric `^`-object is now built** (P2 / `Meta/Nat/UnitHyper`, ∅-axiom):
   `hcube a b` = the `b`-dim unit grid, with `count = side ^ dim`
   (`count_eq_side_pow_dim`), the per-rung `+1` dimension axis (`dim_hcube_succ`),
   and the climb `count (hcube a (b+1)) = a · count (hcube a b)` (`^` *as*
   `×`-iteration).  The base/exponent asymmetry is captured *positively* as a
   length-vs-dimension type-mismatch (`swap_changes_dim`).  *Still open*: the
   precise topological figure for one `^` step — a **3- vs 4-simplex** (the
   originator's "초위상" question) — i.e. the dimension the dilation axis adds to the
   `hyperCount` simplex; and the `−1` cross-determinant shadow of the twist (L5).
   Anchors: `Mobius213.mobius_213_pell_unit_invariant_forall` (`[∅]`),
   `PairOp.pow_lift_impossible`.
2. **Simplex theorem (L3)** — count half **CLOSED** (`MultSystem.monoCount_closed`,
   `C(n+k−1,k)` = degree-`k` multiset count, ∅-axiom).  The `+`/`×` bridge and its
   prime-counting payoff (L3′) are **built** (`MultSystemValue` + `ChebyshevLower`;
   mirror `theory/math/numbertheory/chebyshev_prime_counting.md`).  *Remaining*: tie
   the abstract cone to the `(NS,NT,d)` simplex objects (the physics-branch
   combinatorics) — the "two independent roads to one simplex" of §"Why this matters".
3. **The twist dimension (L5)** — pin which dimension drives the non-commutativity
   (built-object vs operand-mismatch); decide the topological figure for one `^`
   step, then picture the `↑↑` two-DOF case.
4. **No-identity formalization (L2)** — concrete content **CLOSED ∅-axiom**
   (`MultSystem.monoCountPos_closed` = semigroup count `+ 1` = monoid count, the
   `+1` = the identity; `MultSystemValue.two_le_nonempty_prime_prod` = the natural
   `×` system is `{2,3,…}`).  *Remaining* `[gut]`: the **meta-criterion** itself —
   "a construction is natural iff its identity need not be a special case" — as a
   precise (cross-layer) statement, not just the per-layer decomposition.

## Anchors

`number_tower_theory.md` (the demotion/valuation view, R0–R8) ·
`seed/AXIOM/06_lens_readings.md` §6.5 (`point ≡ K_∞`), §6.8 (atomic cofactors),
§6.9 (`0 ≡ ∞`) · `Mobius213.mobius_213_pell_unit_invariant_forall` (the `−1`
cross-determinant) · the `(NS,NT,d)` simplex combinatorics (physics branch).
