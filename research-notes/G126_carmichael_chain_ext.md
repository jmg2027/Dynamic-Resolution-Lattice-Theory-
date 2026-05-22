# G126 — Carmichael chain extension at base 5

*(Follow-up to G123 ConfigCountModular and G124 §6.4 "Iterated
Carmichael chain beyond `{2, 3, 5, 7, 11, 13}`".  Cheap Lean
addition per G124 §6 catalogue.)*

## §0 Question

G123 closed the modular fingerprint of `configCountD 5 n` for
primes `p ∈ {2, 3, 5, 7, 11, 13}`, with the pattern:
  · `p ∈ {2, 3, 5}`: constant
  · `p ∈ {7, 11, 13}`: period 2 from `n = 1`

G124 §6.4 asked: does **period-2 dominate** at higher primes, or
do new patterns emerge?

## §1 Numerical findings (primes 17–47)

```
p   | ord_p(5) | K = ord_p(5) | ord_K(5) | period of n ↦ 5^(5^n) % p
----|----------|--------------|----------|----------
17  |    16    |     16       |    4     |  4
19  |     9    |      9       |    6     |  6
23  |    22    |     22       |    5     |  5
29  |    14    |     14       |    6     |  6
31  |     3    |      3       |    2     |  ★ 2 (mod-7 family)
37  |    36    |     36       |    6     |  6
41  |    20    |     20       |  (1)     |  ★★ CONSTANT (= 9)
43  |    42    |     42       |    6     |  6
47  |    46    |     46       |   22     |  22
```

**Verdict**: period-2 dominance **does NOT** extend universally
beyond `{7, 11, 13}`.  New patterns:
  · `p = 41` produces a **constant** readout `9` from `n ≥ 1`
  · `p = 17, 23` produce periods `4, 5`
  · `p = 19, 29, 37, 43` cluster at period `6`
  · `p = 47` produces period `22` (longest in the range)

## §2 The `p = 41` constant — structurally distinguished

`41 = α_GUT integer` per `catalogs/atomic-integers.md`.  The
modular fingerprint at `α_GUT` is **invariant under fractal level
iteration**: for every `n ≥ 1`,

```
configCountD 5 n ≡ 9 (mod 41).
```

Mechanism (parallel to the G125 Aurifeuillean `5^(5^n) ≡ −1 (mod 521)`
proof): `ord_41(5) = 20`, and `5^n mod 20 = 5` for every `n ≥ 1`
(since `5 · 5 = 25 ≡ 5 (mod 20)`).  Hence
`5^(5^n) ≡ 5^5 ≡ 9 (mod 41)`.

The constant `9 = NS²` is itself a count-Lens 2-power (DRLT atomic
integer at the small slice).  The pair `(α_GUT, NS²) = (41, 9)`
forms a clean modular fingerprint identity at the physics base.

Lean: `configCountD_5_succ_mod_41` in
`Lib/Math/Cohomology/Fractal/ConfigCountModular.lean` §H.1 —
proves the parametric `∀ m, 5^(5^(m+1)) % 41 = 9` by induction
via two decidable seeds (`5^5 % 41 = 9` and `9^5 % 41 = 9`, the
latter expressing that `9` is a `5`-power fixed point modulo `41`)
combined with `pow_mul_pure` + auxiliary `pow_mod_base`.

## §3 The `p = 31` period-2 — extending the mod-7 family

`ord_31(5) = 3`, and `5^n mod 3 = 2^n mod 3` alternates `{2, 1}`
with period 2.  Hence `5^(5^n) mod 31` alternates `{25, 5}` from
`n = 1`.  Same structure as the G123 mod-7 / mod-13 cases.

Lean: `configCountD_5_mod_31_table` (decide-checked for `n ∈
{0, 1, 2, 3}`, full period visible).

## §4 Longer periods — `p ∈ {17, 19, 23, 29, 37, 43, 47}`

For these primes, the period of `5^(5^n) % p` is governed by
`ord_K(5)` where `K = ord_p(5)`.  Parametric ∀ n proofs would
follow the same inductive template as `configCountD_5_succ_mod_41`
but with longer-period self-stabilising seeds (instead of
`9^5 ≡ 9 mod 41`, one needs a fixed-point identity matching the
period).  Recorded as decidable instances:

  · `configCountD_5_mod_17_table` (period 4; partial cycle in `n ≤ 3`)
  · `configCountD_5_mod_23_table` (period 5; partial cycle in `n ≤ 3`)

Tractable parametric proofs deferred; the table form already
serves the n=2 physics-slice need.

## §5 Capstone table extension

`configCountD_5_2_mod_table_extended` bundles:

```
configCountD 5 2 % 17 = 12
configCountD 5 2 % 23 = 10
configCountD 5 2 % 31 = 5
configCountD 5 2 % 41 = 9     ★ α_GUT residue
```

Together with the G123 `configCountD_5_2_mod_table` for primes
`{2, 3, 5, 7, 11, 13}`, the modular fingerprint of `N_U`
(= `configCount 2 = 5^25`) at small primes is fully catalogued.

## §6 Closure status + open

  · ★ G126.1 (`p = 41` constant) — closed in Lean, parametric.
  · G126.2 (`p = 31` period-2) — closed as table; parametric proof
    follows mod-7 template.
  · G126.3 (longer periods at 17, 23, 19, 29, 37, 43, 47) —
    closed as concrete tables; parametric ∀ n proofs deferred.

Open: structural reading of the `(p = 41, value = 9) = (α_GUT, NS²)`
pair.  Is it forced by the same physics-base selection that gives
`d = 5`, or coincidental?

## §7 Cross-references

  · `lean/E213/Lib/Math/Cohomology/Fractal/ConfigCountModular.lean` §H
    — Lean realisation (8 new PURE theorems)
  · `catalogs/atomic-integers.md` — `41 = α_GUT`, `9 = NS²`
  · `research-notes/G124_n_u_family_cross_field_connections.md` §6.4
    — original catalogue entry (now closed)
  · `theory/math/cohomology/aurifeuillean.md` — G125 sibling
    campaign (parametric induction template)

## §8 Self-check

  · No universe-constant framing: `41` is one of the small primes
    in the modular fingerprint cascade; the constant `9` is a
    Lens output at the specific slice `(p, n) = (41, n ≥ 1)`,
    parametric in `n`.
  · No false dichotomy: period-2 vs constant vs longer-period
    are all valid Lens readouts of the same family at different
    primes; no "true vs false" framing.
  · No stereotype matching: the `(α_GUT, NS²) = (41, 9)`
    coincidence is recorded as observation, structural reading
    explicitly open.
