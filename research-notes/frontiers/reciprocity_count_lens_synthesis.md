# Synthesis — reciprocity as a count-Lens reading

**Anchor.**  Quadratic reciprocity closed strict ∅-axiom entirely by counting (the Eisenstein
lattice double-count), landing alongside the COUNT proof-ISA series (Sperner, Ramsey) and the
`counting_as_cardinality` essay.  Read laterally, these make a few structures concrete.

## Patterns

- **A classical sign is the parity bit of an explicit finite count.**  `quadratic_reciprocity`'s
  `(−1)^{mn}` is literally `(m·n) % 2`, the parity of the cardinality of the lattice box
  `[1,m]×[1,n]` (`floor_sum_rectangle`).  This is the same move the second supplement makes
  (`(−1)^{cnt2}`) and that the `counting_as_cardinality` essay names: the residue read by
  cardinality, here read one bit further by `mod 2`.  Template: *a ±1 invariant ⟺ parity of a
  named count*.
- **Finite Fubini appears twice, unrecognised as one.**  `Linalg213/SumLinear.sumZ_swap`
  (Int double-sum swap, built for the QR cross term) is the same incidence-matrix-read-two-ways as
  the COUNT series' union-bound/double-count duality (the `sumOver_swap` used for Sperner/Ramsey).
  One is over `sumZ : List Int → Int`, the other over a Nat list sum — candidate for a single
  generic finite-double-sum-swap in `Meta/`.
- **"No point on the boundary" = `object1_not_surjective`.**  The clean two-way partition in the
  rectangle count rests on `p ∤ q·x` — the exact diagonal `q·x = p·y` is reached by no integer
  point (`elem_tri`).  This is the reached-by-none shape (`seed/AXIOM/05_no_exterior.md` §8.1) the
  counting essay ties to the Cantor diagonal: the boundary value is a Lens-artifact, never an
  inhabited residue, so the count splits exhaustively with no remainder.

## New questions

- **Cubic / biquadratic reciprocity over `ℤ[ω]` / `ℤ[i]`** — the same count-Lens question in the
  Eisenstein / Gaussian residue rings (`theory/math/numbertheory/eisenstein_period_arithmetic.md`).
  Is there a lattice-count proof reusing `floor_sum_rectangle`'s shape over a 2-D residue lattice?
- **Zolotarev's lemma** — `(a/p) = sign(mul-by-a permutation)`.  The `psign` machinery
  (`Algebra/Linalg213/Permutation.lean`, `psign_swap_prefix`) is the sign side; `gauss_qr` is the
  count side.  Does the count-Lens reading unify the sign-product `∏ sgFn` with `psign` (one Raw
  permutation, two readouts)?
- **Unify the two Fubini swaps** — fold `sumZ_swap` (Int) and the COUNT series' Nat double-sum swap
  into one `Meta` finite-Fubini over an arbitrary commutative-monoid list sum.
- **A shared Int-parity home** — `int_even_or_odd` / `two_mul_ne_one` are cloned in
  `QuadraticReciprocity` and `FourSquare`; both depend only on `CenteredDivision.centered_div_int`.
  Their canonical home is `CenteredDivision` (dedup gate).

## Cross-references
`theory/math/numbertheory/quadratic_reciprocity.md`; `theory/essays/proof_isa/counting_as_cardinality.md`;
`lean/E213/Lib/Math/NumberTheory/ModArith/{QuadraticReciprocity,GaussLemma,SecondSupplement}.lean`;
`lean/E213/Lib/Math/Algebra/Linalg213/{SumLinear,Permutation}.lean`.
