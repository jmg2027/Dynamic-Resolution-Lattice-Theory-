# Signed rationals: normal form = sign × coprime pair (open: Euclid lemma)

## Goal

A fully ∅-axiom presentation of **all of ℚ** (signed rationals) as the
composite of the two independent obstruction readouts established on
this branch:

```
  nonzero q  ↦  ( sign : Bool ,  (p, q) : Nat × Nat  coprime, q ≥ 1 )
```

- **sign** = the difference-Lens swap readout
  (`Int213.neg_subNatNat`; witness side per
  `Int213.witness_total`/`witness_not_both`).
- **coprime pair** = the ∣-order normal form
  (`Gcd213.gcd_strip_coprime`: stripping the gcd leaves a coprime
  pair; lowest terms = `det P = 1` per
  `RatioLensFounding.convergent_lowest_terms_is_det`).

## Why the two readouts must be mixed this way (closed)

An order-presented (cross-`≤`) ratio reading does **not** descend
through the sign quotient: a nonpositive factor reverses `≤` —
`OrderMul.mul_le_mul_right_nonpos` (PURE) is the torsion witness.  So
"both presented as inequalities" cannot be combined directly: the sign
must be read off *first* (Bool axis), after which cross-`≤`
(`RatioLensFounding.ratioEquiv`, trans at positive resolution
`ratioEquiv_trans`) runs on magnitudes.  The ∣-order data (gcd,
valuation `Valuation.le_vp_iff`) is orientation-blind and composes
freely with the sign axis.

## Missing bricks (open)

1. **Euclid lemma** (PURE): `gcd213 a b = 1 → a ∣ b * c → a ∣ c`.
   Needs the Bezout chain — flagged "future work" at
   `Lens/Instances/Leaves/ModNat.lean` ("Requires Bezout chain").
   Candidate route: `gcd213` distributivity `gcd213 (k*a) (k*b) =
   k * gcd213 a b` by `gcdFuel` induction (avoids signed Bezout
   coefficients entirely).
2. **Uniqueness of the coprime representation** (PURE): from
   `p₁ * q₂ = p₂ * q₁`, `gcd213 p₁ q₁ = 1`, `gcd213 p₂ q₂ = 1`,
   `0 < q₁`, `0 < q₂` conclude `p₁ = p₂ ∧ q₁ = q₂`.
   Direct from brick 1 + `Gcd213.dvd_antisymm_213`.
3. **Signed composite** (PURE): the full normal form above, with the
   derived order (sign-major, cross-`≤` on magnitudes within the
   positive sign) and its compatibility with `ratioEquiv`.

## Where it feeds

Closes the ladder sign (2-valued) → remainder (`a`-valued, +-shadow)
→ coprime/valuation (∣-native) at the ℚ level; the two completions
of the same ×-question (+-order reading → `Real213`, ∣-order reading
→ `Padic/`) then sit over a single ∅-axiom ℚ.
