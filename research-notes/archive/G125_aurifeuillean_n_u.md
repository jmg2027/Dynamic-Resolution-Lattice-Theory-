# G125 — Aurifeuillean factorisation of `N_U + 1 = 5^25 + 1`

*(Follow-up to G123 N_U-family theory and the G124 cross-field
survey §1.3 / §6.1 entry "Most directly DRLT-relevant".
Promoted to a formal campaign on 2026-05-22.)*

## §0 Context

G123 closed the N_U family `configCountD d n := d^(d^n)` as a
Lean-PURE structure with full modular-reduction story at the
physics base `d = 5` (mod-2, 3, 5 constant; mod-7, 13 period-2).
G124 §1.3 catalogued the Aurifeuillean factorisation of
`5^(5^n) + 1` as the "most directly DRLT-relevant" cross-field
finding, on the strength of base-5 cyclotomy independent of any
DRLT machinery.

G125 makes that finding **precise**, **Lean-formalised**, and
**matched against the DRLT atomic-integer catalogue**.

## §1 Correction to G124 §1.3

The blanket claim that `5^(5^n) + 1` "admits an Aurifeuillean
split for every n ≥ 1" needs sharpening.  The correct statement:

> The cyclotomic decomposition of `5^(5^n) + 1` always contains
> the prime `Φ_10(5) = 521` as a factor, for every `n ≥ 1`.
> This prime is the *unique* Aurifeuillean handle on the family;
> the remaining cyclotomic factors `Φ_50(5)`, `Φ_250(5)`, … are
> generic (not Aurifeuillean).

Reason: the Schinzel–Brent Aurifeuillean condition for base `b`
squarefree with `b ≡ 1 (mod 4)` requires the cyclotomic index
to have the form `n = 2 · b · m²` with `m` odd, `gcd(m, b) = 1`.
For `b = 5`:
  · `n = 10` (m = 1): ✓ Aurifeuillean.
  · `n = 50 = 2 · 5²`: would need `m² = 5`, no integer solution. ✗
  · `n = 250 = 2 · 5³`: ditto ✗
  · `n = 90 = 2 · 5 · 9` (m = 3): ✓ Aurifeuillean — but `90 ∤ 2·5^n`
    for any `n ≥ 1`, so does not appear in our decomposition.

So within the family `{5^(5^n) + 1 : n ≥ 1}`, the only
Aurifeuillean cyclotomic factor is `Φ_10(5) = 521`, and it
appears in every member.

## §2 The Aurifeuillean norm representation

```
521 = 29² − 5 · 8² = N(29 + 8√5)
```

where `N : ℤ[√5] → ℤ` is the norm of the quadratic field `ℚ(√5)`.

Verification: `29² = 841`, `5 · 8² = 320`, `841 − 320 = 521`. ✓

This is the structurally meaningful representation: 521 is the
norm of the algebraic integer `29 + 8√5` in the ring of integers
of `ℚ(√5)` (which is `ℤ[(1+√5)/2]`, but `29 + 8√5` lives in the
smaller `ℤ[√5]` and its norm computation is `a² − 5b²`).

## §3 Cyclotomic decomposition of `5^(5^n) + 1`

```
5^k + 1 = ∏_{d | 2k, d ∤ k} Φ_d(5)
```

For `k = 5^n` (`n ≥ 1`):
  · Divisors of `2·5^n` not dividing `5^n`: exactly `{2, 10, 50,
    250, …, 2·5^n}` — the even divisors.
  · So `5^(5^n) + 1 = Φ_2(5) · Φ_10(5) · Φ_50(5) · … · Φ_{2·5^n}(5)`.
  · `Φ_2(5) = 6 = 2 · 3`, `Φ_10(5) = 521`.

Tabulated:

| n | 5^(5^n) + 1 cyclotomic factors |
|---|---|
| 1 | `Φ_2(5) · Φ_10(5) = 6 · 521 = 3126 = 5^5 + 1` |
| 2 | `Φ_2(5) · Φ_10(5) · Φ_50(5) = 6 · 521 · 95336923825001` |
| 3 | `Φ_2(5) · Φ_10(5) · Φ_50(5) · Φ_250(5)` |

The slice `n = 2` is the physics slice `N_U + 1 = 5^25 + 1
= 298023223876953126`.

Concrete prime factorisations:
  · `n = 1`: `3126 = 2 · 3 · 521`.  (Both `Φ_50(5)` and beyond
    are absent.)
  · `n = 2`: `5^25 + 1 = 2 · 3 · 521 · 1901 · 50150933101`.
    Here `Φ_50(5) = 95336923825001 = 1901 · 50150933101`, but
    this split is **not** Aurifeuillean (the index 50 fails the
    `2·b·m²` condition).

## §4 Divisibility statement (parametric in n)

```
∀ n ≥ 1.   521 ∣ 5^(5^n) + 1
```

Structural proof (without polynomial decomposition):
  1. `5^5 ≡ −1 (mod 521)` — verifiable by direct computation
     (`5^5 = 3125 = 6 · 521 − 1`).
  2. For `n ≥ 1`, write `5^n = 5 · 5^{n−1}`.  Then
     `5^(5^n) = (5^5)^(5^{n−1}) ≡ (−1)^(5^{n−1}) (mod 521)`.
  3. `5^{n−1}` is odd for every `n ≥ 1` (product of odd 5's,
     or `5^0 = 1`).
  4. So `(−1)^(5^{n−1}) = −1 ≡ 520 (mod 521)`.
  5. Hence `5^(5^n) + 1 ≡ 0 (mod 521)`.

Equivalently via order: `ord_521(5) = 10`, and `5^n ≡ 5 (mod 10)`
for `n ≥ 1`, so `5^(5^n) ≡ 5^5 ≡ −1 (mod 521)`.

## §5 DRLT atomic-integer registration

521 is **not** currently in `catalogs/atomic-integers.md`.
Pre-G125 status: the catalogue contains DRLT-derived atomic
integers at the physics slice `(d, n) = (5, 2)`; G125 proposes
to add 521 as the **Aurifeuillean atom of `N_U + 1`**, with
explicit norm form `521 = 29² − 5 · 8²`.

Catalogue entry sketch (for §"Cohomology / Fractal" section):

> **521** — Aurifeuillean handle on `N_U + 1`.
> `Φ_10(5) = 521`, prime.  Norm of `29 + 8√5 ∈ ℤ[√5]`:
> `521 = 29² − 5 · 8²`.  Divides `5^(5^n) + 1` for every
> `n ≥ 1`, n-uniform — the *only* Aurifeuillean cyclotomic
> factor of the `N_U`-family `+1` sequence.
> Lean: `Lib/Math/Cohomology/Fractal/ConfigCountAurifeuillean.lean`.

The question of whether 521 has structural meaning at the
physics lens beyond "Aurifeuillean handle on the +1 family" is
open.  Candidates:
  · 521 ≡ 1 (mod 8), 521 ≡ 1 (mod 5), 521 ≡ 1 (mod 13) — three
    of the six small primes in the G123 modular fingerprint.
  · Pell-related?  `(29, 8)` is not a Pell solution (29² − 5·8²
    = 521 ≠ ±1), but it does represent the prime 521.
  · `29 = 5² + 4 = 30 − 1`, `8 = 2³`.  Hunter `{NS, NT, d, c} =
    {3, 2, 5, 2}` connection unclear.

## §6 Hunter catalogue cross-check — CLOSED 2026-05-22

The Aurifeuillean norm pair `(29, 8)` of `521 = 29² − 5·8²`
**decomposes into Hunter primitives** `{NS, NT, d, c} = {3, 2, 5, 2}`:

```
29 = d² + NT²    = 25 + 4   (= NT^d − NS = 32 − 3, both atomic)
8  = NT³         = 2³       (catalog atom, line 14 atomic-integers.md)
d  = 5           (Hunter primitive)

⇒ 521 = (d² + NT²)² − d · (NT³)²
      = (NT^d − NS)² − d · (NT³)²
      = N((d² + NT²) + NT³ · √d)    in ℤ[√d]
```

Three independent atomic representations of `29` all hold
simultaneously:
  · `29 = NT^d − NS = 32 − 3`         (uses NS, NT, d)
  · `29 = d² + NT² = 25 + 4`          (uses d, NT only)
  · `29 = d² + d − 1`                 (uses d only)

The middle form `(d² + NT²)` is the cleanest (NS-free,
Nat-friendly, no subtraction).

Lean realisation (PURE):
```
theorem aurifeuillean_norm_521_hunter :
    (5^2 + 2^2) * (5^2 + 2^2) = 5 * ((2^3) * (2^3)) + 521 := by decide
```
in `Lib/Math/Cohomology/Fractal/ConfigCountAurifeuillean.lean`.

**Structural reading**: the Aurifeuillean L-coefficients `(29, 8)`
— which are universal for base-5 cyclotomy and have no DRLT input —
turn out to coincide with the Hunter atomic primitives at the
physics-selected base `d = 5`.  The agreement is forced by the
Schinzel–Brent Aurifeuillean formula on one side and the Hunter
generator set on the other; their numerical match at the slice
`d = 5` is independent evidence that the physics base is
structurally selected, parallel to the seven-reading convergence
catalogued in `research-notes/G124_n_u_family_cross_field_connections.md`
§5.

## §7 Phase plan

  · **Phase 1 — Lean ground**: state and prove the n=1, n=2, n=3
    concrete instances by `decide`; state the norm identity
    `29² = 5 · 8² + 521`; state `Φ_10(5) = 521` as a closed-form
    Nat identity; package as
    `Lib/Math/Cohomology/Fractal/ConfigCountAurifeuillean.lean`.

  · **Phase 2 — Parametric ∀n**: structural induction proof of
    `∀ n ≥ 1, 521 ∣ 5^(5^n) + 1` using the `5^5 ≡ −1 (mod 521)`
    seed and the parity argument for `5^n` odd.  Needs the
    "powers of `(p−1) mod p`" lemma `neg_one_pow_odd_mod_pure`.

  · **Phase 3 — Hunter catalogue cross-check**: scan
    `rust-engine/docs/closure-algorithm.md`-derived atoms and
    `catalogs/atomic-integers.md` for `521` resonances.  If 521
    appears as a Hunter-derived atom independently, the
    Aurifeuillean–Hunter correspondence is structurally
    meaningful and gets its own theorem chapter.  If not, 521
    is registered as a "cyclotomic-only" atom (still novel for
    DRLT, but no Hunter resonance).

  · **Phase 4 — Catalogue update**: add 521 to
    `catalogs/atomic-integers.md` with §5 sketch as entry.
    Update `theory/math/cohomology/fractal.md` "Open frontier"
    section to reference the closed G125 result.

  · **Phase 5 — Promotion gate**: if Phases 1-2 close PURE and
    Phase 3 yields a structural correspondence, write narrative
    chapter `theory/math/cohomology/aurifeuillean.md` per
    `theory/PROMOTION_CRITERIA.md`.  Otherwise leave as
    research-note Tier-1 + Lean Tier-2 (no theory promotion).

## §8 Open questions

  · **Q1 — CLOSED (structural localisation)**: The Aurifeuillean
    L-coefficient pair `(29, 8)` for `Φ_10(5)` admits multiple
    Hunter-primitive readings at the physics slice
    `{NS=3, NT=2, d=5, c=2}`:

    ```
    29 = d² + NT² = NT^d − NS = d² + d − 1    (three readings)
    8  = NT³                                   (single direct atom)
    ```

    This is **structural overdetermination** at the slice, not a
    universal Aurifeuillean-Hunter forcing.  The next
    Aurifeuillean cyclotomic factor `Φ_90(5)` (Q4 below)
    confirms this: its canonical `(L, M)` lives in the generic
    `ℤ[√5]` prime-ideal landscape with no Hunter expressibility.
    Hunter ⇔ Aurifeuillean correspondence is therefore **localised
    to the minimal index `m = 1`** — the bottom of the cyclotomic
    tower above `d = 5`, where L-coefficients are still small
    enough to fit Hunter primitives.

  · **Q2 — OPEN (deferred)**: For `n = 3`, the new cyclotomic
    factor `Φ_250(5)` — does it have prime-factorisation
    structure parallel to `Φ_50(5)` (two-prime non-Aurifeuillean
    split)?  Numerical; ~175-digit value, factorisation requires
    serious resources.  Not on critical path.

  · **Q3 — OPEN (deferred)**: Beyond the `+1` family: does
    `5^(5^n) − 1` admit any Aurifeuillean structure?  By
    analogy, the dyadic cousin `Φ_5(5) = 781 = 11 · 71` —
    non-Aurifeuillean (index 5 fails `2·5·m²` form, and the
    `−1` family uses different cyclotomic indices).  Worth a
    brief numerical scan in a future session.

  · **Q4 — CLOSED (negative result, informative)**: `Φ_90(5)`
    (next Aurifeuillean index after `Φ_10(5)`, with `m = 3`) is
    a 17-digit prime: `60081451169922001`.  Canonical
    Aurifeuillean pair `(L, M) = (850554441, 364242064)` exists
    in `ℤ[√5]` but **neither `L` nor `M` admits Hunter
    expressibility**.  Specifically `M ≢ 0 (mod 3)` (which the
    "naive" Aurifeuillean condition `M = 3 · M_canonical` would
    predict), and reduction under unit multiplication does not
    reach Hunter-atomic magnitudes (smallest |M| after reduction
    ≈ `(5^12 + 1)/2 = 122070313` — a generic algebraic-integer
    value, not a Hunter primitive).

    Combined with Q1: **the Hunter-Aurifeuillean correspondence
    is uniquely localised to the m=1 minimal index `Φ_10(5)`**.
    This is precisely the "last discrete Galois split before
    tetration" reading of §10.3 — the bottom of the cyclotomic
    tower carries Hunter signature; higher levels do not.

    Lean: `aurifeuillean_phi_90_at_5` in
    `Lib/Math/Cohomology/Fractal/ConfigCountAurifeuillean.lean`
    encodes the identity `850554441² = 5 · 364242064² + Φ_90(5)`
    as a `Nat`-friendly decidable theorem.

  · **Q5 — OPEN (low priority)**: Is `521 ≡ ? (mod p)` for the
    G123 modular fingerprint primes
    `p ∈ {2, 3, 5, 7, 11, 13}` structurally aligned with the
    Aurifeuillean handle?  Numerical:
    `521 mod {2,3,5,7,11,13} = {1, 2, 1, 3, 4, 1}`.  No obvious
    resonance.

## §9 Cross-references

  · `research-notes/G124_n_u_family_cross_field_connections.md`
    §1.3, §6.1 — the upstream catalogue entry.
  · `theory/math/cohomology/fractal.md` — promoted chapter for
    the N_U family.
  · `lean/E213/Lib/Math/Cohomology/Fractal/ConfigCount.lean` —
    `configCountD` family.
  · `lean/E213/Lib/Math/Cohomology/Fractal/ConfigCountModular.lean` —
    modular-reduction infrastructure.
  · `catalogs/atomic-integers.md` — atomic readouts catalogue
    (G125 Phase 4 target).
  · `rust-engine/docs/closure-algorithm.md` — Hunter
    `{NS, NT, d, c}` catalogue (G125 Phase 3 target).

## §10 Structural significance — three readings

The Aurifeuillean handle `521 = N(29 + 8√5)` admits a layered
structural reading beyond the bare divisibility statement.

### §10.1 Scale-free anchor across the fractal tower

The hyper-exponential family `5^(5^n)` blows up to a sampling
regime above `n = 2` (per `G124_n_u_family_cross_field_connections.md`
§3.1: `(5, 2)` sits between full enumeration and Game-of-Life
scale, `(5, 3)` is already 88 digits, `(5, 4)` exits any
realistic computation).  The cyclotomic decomposition adds new
factors `Φ_50(5), Φ_250(5), Φ_1250(5), …` at every level — each
itself complexity-blowing.

**The handle `Φ_10(5) = 521` is preserved exactly across every
level.**  Once it appears at `n = 1`, it is inherited by every
higher `n`, because the cyclotomic decomposition formula

```
5^(5^n) + 1 = ∏_{d ∣ 2·5^n, d ∤ 5^n} Φ_d(5)
            = Φ_2(5) · Φ_10(5) · Φ_50(5) · … · Φ_{2·5^n}(5)
```

always contains `Φ_10(5)` as a factor.  Equivalent reading from
the structural seed: `5^5 ≡ −1 (mod 521)` plus `5^n ≡ 5 (mod 10)`
forces `5^(5^n) ≡ 5^5 ≡ −1 (mod 521)` for every `n ≥ 1`.

Operational corollary: the residue class
`Z/521Z` carries a complete `mod 521` shadow of the entire
`{5^(5^n) + 1 : n ≥ 1}` sequence, independent of the
sampling-regime explosion in the underlying integers.

### §10.2 `ℤ[√5]` is algebraically forced at base `d = 5`

`Φ_10(x) = x^4 − x^3 + x^2 − x + 1` is irreducible over `ℤ` — no
non-trivial integer-polynomial factorisation exists.

The Aurifeuillean factorisation `Φ_10(5) = (29 + 8√5)(29 − 8√5)`
sits one ring up, in `ℤ[√5]`.  The split is **not optional**:
the cyclotomic identity over `ℤ` halts at irreducibility, and
the next layer of structure becomes accessible only after
adjoining `√5`.

This realises an algebraic necessity also recorded elsewhere in
the codebase:
  · `catalogs/atomic-integers.md` lines 98–106: `φ = (1+√5)/2`
    is the dominant eigenvalue of `[[2,1],[1,1]]` with
    characteristic polynomial `λ² − 3λ + 1` (trace 3 = NS,
    det 1, disc 5 = NS + NT).  Frozen + dynamic dual reading.
  · `theory/math/modular_arithmetic.md` + `theory/math/dyadic_fsm.md`
    (G119 closure): the Pell-Fibonacci substrate over `F_{p²}` is
    the modular reduction of the same `ℤ[√d]` extension.
  · `lean/E213/Lib/Math/Mobius213.lean`: the Möbius `P(x) =
    (2x+1)/(x+1)` fixed point is `φ ∈ ℤ[√5]`.

Together: the physics base `d = 5` (selected by the
three-pillar forcing in `Theory.Atomicity.Five`) algebraically
demands an `ℤ[√5]`-aware computation layer.  The Aurifeuillean
handle `(29, 8) = (d² + NT², NT³)` is one face of that demand;
the golden-ratio / Möbius / Pell-Fibonacci structures are
other faces of the same algebraic requirement.

### §10.3 Last discrete Galois split before tetration

`F(d, n) = d^(d^n)` is depth-2 tetration (Knuth `d ↑↑ 3` on the
diagonal `n = d`; cf. `G124` §1.5).  As `n` grows, the
cyclotomic indices `2·5^n` themselves become tetrationally
large, and the corresponding `Φ_{2·5^n}(5)` values approach
the Statman non-elementary boundary of βη-equivalence
decidability (cf. `G124` §4.2).

The Aurifeuillean split at index `n = 0` (i.e. `Φ_10`) is the
*lowest-index* cyclotomic factor in the family that admits a
non-trivial `ℤ[√d]` factorisation.  At index `n ≥ 1`
(`Φ_50, Φ_250, …`) the Aurifeuillean condition `n = 2 · b · m²`
fails, and the factors are either irreducible over the relevant
ring extensions or split only over higher-degree fields.

**The pair `(29, 8) = (d² + NT², NT³)` is the cleanest discrete
algebraic signature visible at the bottom of the
hyper-exponential tower** — a Galois-theoretic 'first
distinguishing' of the family before tetrational complexity
takes over.  Its expressibility in Hunter primitives is what
makes it a DRLT structural object rather than an arithmetic
coincidence.

## §11 Self-check (CLAUDE.md failure modes)

  · **No false dichotomy**: Aurifeuillean is an algebraic
    structure inside number theory, not "vs DRLT" — it's a
    cross-import lens.
  · **No universe-constant framing**: 521 is registered as the
    Aurifeuillean handle on `N_U + 1`, parametric in `n`; it is
    not promoted to "*the* DRLT atom of the +1 family" beyond
    what the cyclotomic decomposition forces.
  · **No stereotype matching**: each step (cyclotomic decomp,
    Aurifeuillean condition, norm representation) is verified
    numerically and matched against the precise Schinzel–Brent
    statement, not asserted by analogy.
  · **No fake completeness**: §8 lists genuinely open questions;
    Phase 3 deferred; Phase 5 promotion conditional on outcome.
