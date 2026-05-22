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

## §6 Hunter catalogue cross-check (open)

`rust-engine/docs/closure-algorithm.md` lists the
`{NS, NT, d, c} = {3, 2, 5, 2}` 30-integer atomic catalogue.
The question for G125 §6: does 521 appear as an atom in any
derived catalogue (e.g., as a divisor of a closure-derived
integer, or as a residue of `R(NS, NT, d, c) · Π(1 + κ_i · α_i^{n_i})`
at some atomic configuration)?

This is a Hunter-side audit, deferred to G125 Phase 3.

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

  · **Q1**: Is the norm pair `(29, 8)` itself derivable from the
    Hunter `{NS, NT, d, c} = {3, 2, 5, 2}` parameters?
    `29 = 4 · NS² + 5 = 4 · 9 + 5 − 12 = ...` — no obvious match
    yet.  Numerical search required.
  · **Q2**: For `n = 3`, the new cyclotomic factor `Φ_250(5)` —
    does it have prime-factorisation structure parallel to
    `Φ_50(5)` (two-prime non-Aurifeuillean split)?  Numerical.
  · **Q3**: Beyond the `+1` family: does `5^(5^n) − 1` admit any
    Aurifeuillean structure?  By analogy, the dyadic cousin
    `Φ_5(5) = 781 = 11 · 71` — non-Aurifeuillean (index 5 fails
    `2·5·m²` form, and the `−1` family uses different cyclotomic
    indices).  Worth a brief numerical scan.
  · **Q4**: Is `521 = N(29 + 8√5)` related to any of the small
    primes in the G123 modular fingerprint via
    `521 ≡ ? (mod p)` for `p ∈ {2, 3, 5, 7, 11, 13}`?
    Numerical: `521 mod {2,3,5,7,11,13} = {1, 2, 1, 3, 4, 1}`.
    No obvious resonance at small primes.

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

## §10 Self-check (CLAUDE.md failure modes)

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
