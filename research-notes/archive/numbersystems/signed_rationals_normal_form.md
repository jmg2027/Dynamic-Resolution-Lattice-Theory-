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

## Bricks

1. **Euclid lemma** — ★ CLOSED (`Gcd213.coprime_dvd_of_dvd_mul`, PURE).
   Bezout-free as planned: `gcd213_mul_left` distributivity by
   Euclidean descent (`gcd213_rec` + the new `mul_mod_mul_left_pure`,
   replacing propext-dirty `Nat.mul_mod_mul_left`), then
   `a ∣ gcd213 (c·a) (c·b) = c · gcd213 a b = c`.
2. **Uniqueness of the coprime representation** — ★ CLOSED
   (`Gcd213.coprime_repr_unique`, PURE): `p₁·q₂ = p₂·q₁` + both pairs
   coprime + `0 < q₁` force componentwise equality.  With
   `gcd_strip_coprime` (existence), the ∣-order normal form of a
   ratio pair is now exact.
3. **Signed composite** — ★ CLOSED for the normal form
   (`Lib/Math/NumberSystems/Rat213.lean`, PURE): numerator `Int`
   (sign carried by the constructor = the swap readout) × positive
   `Nat` denominator; `ratioEqZ` the signed cross-equation,
   `IsLowest` the lowest-terms condition; `lowest_exists`
   (normalization via `gcd_strip_coprime`) + `lowest_unique`
   (mixed signs die by constructor clash; same signs reduce to
   `coprime_repr_unique`).
4. **Derived order** — ★ CLOSED (`Rat213.ratioLeZ_descends` /
   `ratioLeZ_iff`, PURE): the cross-order `ratioLeZ` (positive `Nat`
   denominators — the positive cone, sign already in the numerator)
   descends through `ratioEqZ`: multiply into the join frame `B·D`,
   transport along the cross-equations (`Int213.mul_mul_mul_comm`),
   cancel the positive frame (`le_of_mul_le_mul_right_pos`).

**All bricks closed** — candidate for promotion
(`theory/PROMOTION_CRITERIA.md`) next session: the signed ℚ normal
form (existence, uniqueness, well-defined order) is ∅-axiom end to
end.

## Where it feeds

Closes the ladder sign (2-valued) → remainder (`a`-valued, +-shadow)
→ coprime/valuation (∣-native) at the ℚ level; the two completions
of the same ×-question (+-order reading → `Real213`, ∣-order reading
→ `Padic/`) then sit over a single ∅-axiom ℚ.
