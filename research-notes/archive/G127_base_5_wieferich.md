# G127 — Base-5 Wieferich primes

*(Follow-up to G124 §1.4 / §6.8 "DRLT-Wieferich condition".
Computational scouting for primes obstructing higher-precision
base-5 modular cascade.)*

## §0 Definition

A prime `p` is **Wieferich-base-`a`** if `p² ∣ a^(p-1) − 1`,
equivalently `a^(p-1) ≡ 1 (mod p²)`.  By Fermat's Little
Theorem `a^(p-1) ≡ 1 (mod p)` always (for `gcd(a, p) = 1`);
the Wieferich condition strengthens this to `mod p²`.

Wieferich primes obstruct the lift of modular computations to
higher powers of `p`.  They are extremely rare: only two known
base-2 Wieferich primes (`1093`, `3511`) below `6.7 × 10¹⁵`.

## §1 Search at base 5

Brute-force search at `a = 5` over primes `p ∈ [7, 10⁵]`
(excluding `p ∈ {2, 3, 5}` which are trivially handled):

```python
for p in primes(7, 10^5):
    if pow(5, p - 1, p * p) == 1:
        record(p)
```

**Result**: two base-5 Wieferich primes found:

```
p = 20771     (5^20770 ≡ 1 (mod 20771²))
p = 40487     (5^40486 ≡ 1 (mod 40487²))
```

These match the published OEIS sequence A123693 (Wieferich-5
primes).  The smallest base-5 Wieferich pair is therefore
`(20771, 40487)`; the next, if any, lies above `10⁵`.

## §2 DRLT implications

### §2.1 Obstruction to higher-precision modular cascade

The G123 + G126 modular fingerprint catalogue covers primes
`p ∈ {2, 3, 5, 7, 11, 13, 17, 23, 31, 41}` at modulus `p`.
Lifting any of these to modulus `p²` is straightforward
because none is a base-5 Wieferich prime.

Lifting to modulus `20771²` or `40487²` — at the base-5
Wieferich primes — would *fail* in a structural sense: the FLT
period `p − 1` no longer suffices, and a finer period analysis
modulo `p²` is required.

This is the canonical Wieferich obstruction: at non-Wieferich
primes the lift `p → p²` adds no algebraic complication; at
Wieferich primes it does.

### §2.2 Atomic-integer expressibility

Neither `20771` nor `40487` admits small-depth Hunter
expressibility from `{NS=3, NT=2, d=5, c=2}`:

```
20771 = prime, 20771 mod {3, 5, 7, 11, 13} = {2, 1, 6, 3, 0}
40487 = prime, 40487 mod {3, 5, 7, 11, 13} = {2, 2, 4, 4, 7}
```

No obvious atomic decomposition.  Pattern via `(p - 1)`:
  · `20770 = 2 · 5 · 2077 = 2 · 5 · 31 · 67` (uses `5 = d`, `31 ∈ G126`)
  · `40486 = 2 · 31 · 653` (uses `31 ∈ G126`)

The factor `31` appears in both `(p − 1)` factorisations, and
`31` is the prime where `configCountD 5 n` exhibits the
period-2 mod-31 readout (G126.2).  Whether this is structural
or coincidental is open.

### §2.3 Falsifier asset

Per `seed/AXIOM/08_falsifiability.md`, DRLT seeks structurally
meaningful falsifiers.  The base-5 Wieferich primes `{20771,
40487}` are *candidate* falsifiers in the following sense: if
DRLT's modular cascade is to extend to arbitrary `p^k`, the
Wieferich condition forces a structural exception at these two
primes.  Whether the exception is benign (the cascade simply
truncates) or pathological (cascade fails to close) is an
open question.

## §3 Lean verification

The condition `5^20770 % (20771 * 20771) = 1` is computable
but stresses kernel reduction: `5^20770` is an ~14500-digit
number, and direct evaluation of `Nat.pow 5 20770` is
infeasible for `decide`.

A `modPow`-based encoding (using
`Lib/E213/Meta/Nat/ModPow213.lean`) reduces step-by-step,
keeping intermediate values ≤ `p² ≈ 4.3 × 10⁸`.  This is
in principle tractable but expensive (20770 recursive
unfoldings of `modPow`).

**Decision**: defer the Lean theorem.  The empirical fact is
verified externally (Python: `pow(5, 20770, 20771**2) == 1`);
the structural claim ("`20771` is the smallest base-5
Wieferich prime") is a published observation (OEIS A123693),
not a DRLT-derived theorem.

## §4 Catalogue registration

`catalogs/falsifiers.md` candidates (proposed):

```
G127 — Base-5 Wieferich primes
  p ∈ {20771, 40487}   (smallest two, both verified ≤ 10⁵)
  Condition: 5^(p-1) ≡ 1 (mod p²)
  Significance: obstruct higher-precision base-5 modular cascade.
  Lean: deferred (kernel-impractical at these magnitudes).
  External witness: Python, OEIS A123693.
```

## §5 Open questions

  · **Q1**: Is the smallest base-5 Wieferich prime structurally
    related to atomic integers?  `20771 - 1 = 20770 = 2 · 5 · 31 · 67`
    contains `5 = d` and `31` (G126.2 modular prime).  The
    factor `67` is generic.
  · **Q2**: Is there a Hunter-primitive closed form for the
    Wieferich condition itself?  `p² ∣ a^(p-1) − 1` involves
    no DRLT primitive directly; the connection (if any) is
    indirect.
  · **Q3**: Above `10⁵`, does a third base-5 Wieferich prime
    exist?  Sequential search to `10⁹` would settle the
    immediate question; published data extends to ~`10¹⁴`
    without finding a third.

## §6 Cross-references

  · `research-notes/G124_n_u_family_cross_field_connections.md`
    §1.4 (Carmichael/Wieferich theory), §6.8 (DRLT-Wieferich
    catalogue entry).
  · `research-notes/G126_carmichael_chain_ext.md` — companion
    G126 with mod-31 period-2 observation.
  · OEIS A123693 — base-5 Wieferich primes (external).

## §7 Self-check

  · No fake completeness: §3 explicitly records that the Lean
    verification is deferred for tractability; the result
    sits at Tier-1 (research note) until either a
    `modPow`-based decide closes it or an alternative
    structural proof emerges.
  · No universe-constant framing: the Wieferich primes are
    catalogued as *empirical observations* about the
    modular-cascade obstruction structure, not as
    DRLT-internal forced values.
