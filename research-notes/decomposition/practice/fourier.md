# Decomposition: Fourier / character duality

*213-decomposition of "the Fourier transform / character duality", per `../README.md`. LEVERAGE
attempt: does the calculus PREDICT spectral decomposition + orthogonality from the character/Aut
structure, or only re-describe Fourier?*

The hypothesis under test: **a function on a construction = its spectrum over the construction's
CHARACTERS** — the family of construction-preserving readings into a cyclic readout (roots of unity).
"Read through ALL characters" is the Fourier transform; orthogonality is forced by the Aut/character
structure. L₂ (parity/Legendre) is the simplest character; Gauss sums / quadratic reciprocity the
depth-2 case.

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a cyclic construction `⟨g⟩`: the **orbit of a primitive root**. For a prime
  `p`, the units `(ℤ/p)ˣ` are *exactly* `{g^0, g^1, …, g^{p−2}}` — one generator, iterated. This is the
  `groups.md` `Aut`-family in its simplest non-trivial form: a **cyclic** group, `C = ℕ-count read mod
  (p−1)` carried on the multiplicative orbit. Lean certifies the cyclic structure is real, not posited:
  every unit *is* a power of `g` (`dlog_exists`), and a primitive root *exists*
  (`exists_primitive_root`). So `C` here is literally `parity.md`'s `ℕ`-count, wrapped into a circle of
  circumference `p−1`.

- **Reading — the character family (the DUAL).** A **character** of `⟨g⟩` is a
  construction-preserving reading `χ : ⟨g⟩ → (cyclic readout)` — `χ(ab) = χ(a)·χ(b)`. Fixing the
  discrete log `a = g^k` (the isomorphism `(ℤ/p)ˣ ≅ ℤ/(p−1)`, `dlog_exists`), a character is fully
  determined by where it sends `g`: `χ_j(g^k) = ζ^{jk}` for a `(p−1)`-th root of unity `ζ`. The
  characters are themselves **indexed by `ℤ/(p−1)`** — the dual is *another copy of the same cyclic
  construction*. The **quadratic character** `L₂ = χ_{(p−1)/2}` is the order-2 character: it sends `g^k`
  to `(−1)^k`, i.e. it is **`parity.md`'s L₂ composed with the discrete log** —
  `qr_pow_iff_even_exp`: `g^k` is a QR ⟺ `2 ∣ k`. The full duality claim: **the dual of `C` = the
  family of all its characters = `Hom(⟨g⟩, roots of unity)`**, itself a cyclic construction.

- **Residue** — for the *character family as a whole*, none on a single cyclic group: the characters
  **separate points** (a non-identity element has a character not sending it to 1 — the dual is
  faithful), exactly as `prime_factorization.md`'s `vp` coordinate is faithful (`vp_separation`). The
  residue surfaces one level up, at the **additive** characters / the **transform kernel** `ζ^x`: the
  root of unity `ζ` is a `Real213`/`Complex` **cut** (a pointing, never a finite token), so the
  *analytic* Fourier kernel sits in the residue (the transcendental-as-residue row), while the
  *combinatorial* character `χ : ⟨g⟩ → ℤ/(p−1) ↦ {±1, ζ^k}` is residue-free.

## Re-seeing

```
   a character        =  ⟨ ⟨g⟩ (cyclic C) | χ : g^k ↦ ζ^{jk} ⟩       (groups.md's "readout OF the family")
   the DUAL Ĉ         =  the family {χ_j}_{j∈ℤ/(p−1)} of all such characters   (≅ C, a 2nd cyclic copy)
   Fourier transform  =  "read a function f on C through every χ_j"   f̂(j) = Σ_k f(g^k) χ_j(g^k)
   L₂ / Legendre      =  the order-2 character  χ_{(p−1)/2}           (qr_pow_iff_even_exp; psign_mulPerm_qr)
   "χ is multiplicative" =  legendre_mul / psign_mulPerm_hom          (the character homomorphism, = vp_mul)
```

So the Legendre symbol, the permutation sign, the parity bit, and `det = ±1` (`parity.md`'s collapse)
are **the order-2 slot of the character group** — the unique non-trivial character of a cyclic group of
even order. Fourier "reads through all characters"; parity reads through *one* of them. This is the
`groups.md` stacking made explicit: **`C` = the cyclic group, `Ĉ` = the character family = a reading OF
that group, and the two are isomorphic** — Pontryagin self-duality of a finite cyclic group, seen as
"the Aut-family of `groups.md` has a dual Aut-family of the same shape."

## LEVERAGE — does the calculus PREDICT orthogonality / spectral decomposition?

**Honest verdict: PARTIAL leverage — one genuine prediction, the deepest leg (analytic orthogonality
`Σ_x χ(x) = 0`, the DFT inversion) is conceptual-only / THIN in Lean.**

What the calculus genuinely **predicts** (forcing, not re-description), all Lean-grounded:

1. **The character group is forced to be ≅ `C` (self-duality), and the order-2 character is forced to
   exist iff `|C|` is even.** From `dlog_exists` + `exists_primitive_root`, a character is determined by
   `χ(g)`, and `χ(g)` must be a `|C|`-th root of unity — so `Ĉ ≅ ℤ/(p−1)`. The quadratic character
   exists **because** `p−1` is even, and is `L₂ ∘ dlog` — `qr_pow_iff_even_exp` *derives* it, it is not
   posited. This is real prediction: the calculus says "the dual is the same cyclic shape, and a
   `d`-order character exists ⟺ `d ∣ |C|`," and Lean confirms the `d=2` instance.

2. **The character is a homomorphism `×↦·` — the SAME arrow as `vp_mul`/`det2_mul`/independence.**
   `legendre_mul` (Legendre symbol multiplicative) and `psign_mulPerm_hom` (sign character a `{±1}`
   homomorphism) are *forced* by "construction-preserving reading," exactly as `parity.md` predicted.
   So multiplicativity of characters is derived from the character definition, not assumed.

What the calculus **predicts but Lean does NOT yet certify** (the honest gap):

3. **Orthogonality `Σ_{x} χ(x) = 0` for non-trivial χ** — the load-bearing Fourier fact — has a clean
   *prediction* from the structure: `Σ_k ζ^{jk}` over a full orbit is a **geometric sum over a complete
   set of roots of unity = 0** (the geometric series telescopes because `ζ^j ≠ 1`). This is *exactly*
   `derivative.md`/telescoping `× resolution` machinery the repo has (`QuintupleTelescope`,
   `TelescopingConservation`) applied to the root-of-unity orbit. **But I found no Lean theorem
   `Σ_{x∈⟨g⟩} χ(x) = 0`** (grep for `orthogonal`/`charSum`/root-of-unity-sum-to-zero in
   `NumberTheory/` returns nothing). So the prediction is *available* but **un-cashed** — this is the
   one place the calculus would earn full leverage and the Lean is missing.

4. **DFT inversion / Plancherel** — entirely conceptual; no `f = Σ_j f̂(j) χ_j` anywhere. THIN.

**Net:** the calculus does more than collapse — it *predicts* the self-dual cyclic character group and
the existence/form of the order-`d` character from `|C|`, both Lean-confirmed at `d=2`
(`qr_pow_iff_even_exp`). It also *predicts* orthogonality as a root-of-unity telescoping sum — a sharp,
testable Lean target — but does **not** yet certify it; Fourier-proper (orthogonality sum, inversion,
Plancherel) is thin/conceptual. So: **prediction on the duality + character-existence legs;
collapse-plus-open-target on orthogonality; miss on inversion.** Honest, not full leverage.

## Note for the technique — is "the dual = the family of all characters" a new construct?

**It EXTENDS `groups.md`'s `Aut`-family with one promotion: the reading slot gains a DUAL.**

`groups.md` established `C` can be a *composition-closed family of self-readings* (`Aut C`), and a
character is a *reading OF that family*. Fourier forces the next move: **the set of ALL characters of
`C` is itself a construction `Ĉ` of the same kind** (here, `Aut`-of-a-cyclic = cyclic ⟹ `Ĉ ≅ C`). So
the calculus's normal form should carry, alongside `Aut(C)` (the symmetries), a **dual `Ĉ = Hom(C,
roots of unity)` (the spectrum-indices)**:

> **Add `Ĉ = the character family of `C`` as a derived construction.** For a cyclic `C` it is *forced*
> to be `≅ C` (self-dual, `dlog_exists` + root-of-unity codomain). A **function on `C`** and **its
> spectrum on `Ĉ`** are the two readings of one object (the Fourier pair); the **transform** is the
> resolution-style pairing `⟨f, χ⟩`. This is the `weight ∘ character` series-composition of
> `entropy.md` run over the *whole* dual at once: entropy reads one character (`−log p`) weighted by
> `p`; Fourier reads *every* character. So Fourier = the **`groups.md` family + `entropy.md` series
> composition, summed over the full dual** — no new primitive, but the explicit promotion "the
> character family is a first-class dual construction."

This generalizes `groups.md`'s Aut-family to a **character-family** in the precise sense: Aut-family =
*self-maps preserving `C`*; character-family = *maps `C → (cyclic readout)` preserving `C`'s operation*
— **the codomain side of the same `LensIso`/homomorphism arrow**, now collected into its own indexed
construction. The order-2 slot of that family is `parity.md`'s L₂; the whole family is the spectrum. The
deepest open Lean target the calculus *predicts*: `Σ_{x∈⟨g⟩} χ_j(x) = 0` for `j ≠ 0` as a
root-of-unity telescoping sum (orthogonality) — closing it would convert this entry's partial leverage
into full prediction.

## Verified Lean anchors (grep-verified to exist; source docstrings declare STRICT ∅-AXIOM — not
independently rebuilt this session, the axiom-scan tool could not write its probe in this sandbox)

- `Lib/Math/NumberTheory/ModArith/DiscreteLogParity.lean`:
  - `qr_pow_iff_even_exp` (★ the quadratic character IS the discrete-log parity: `g^k` QR ⟺ `2∣k` —
    the order-2 character = L₂ ∘ dlog)
  - `dlog_exists` (★ every unit is `g^k` — the cyclic-group iso `(ℤ/p)ˣ ≅ ℤ/(p−1)`, the dual's backbone)
  - `qr_iff_even_dlog`, `qr_iff_even_dlog_exists` (fully-internal per-unit form), `psign_iff_even_dlog_exists`
- `Lib/Math/NumberTheory/ModArith/PrimitiveRoot.lean`:
  - `exists_primitive_root` (★ a generator exists — the cyclic construction is inhabited)
  - `maxOrd_eq_pred`, `segInt_roots` (the orbit hits all `p−1` residues)
- `Lib/Math/NumberTheory/ModArith/LegendreMultiplicative.lean`:
  - `legendre_mul` (★ the Legendre character is multiplicative — the character homomorphism `×↦·`)
  - `qr_iff_pow_one` (Euler criterion: QR ⟺ `a^m ≡ 1`)
- `Lib/Math/NumberTheory/ModArith/Zolotarev.lean`:
  - `psign_mulPerm_hom` (★ the sign character is a `{±1}` homomorphism), `psign_mulPerm_qr`
    (Zolotarev: sign = Legendre = the order-2 character), `mulPerm_comp` (Cayley: × ↦ ∘)
- `Lib/Math/NumberTheory/MultiplicativeOrder.lean`:
  - `ord`, `ord_dvd_totient`, `pow_ord_eq_one` (the orbit length divides `|C|` — character-order
    structure)
- `Lib/Math/Algebra/Icosahedral/CyclotomicFive.lean`:
  - `galois_group_is_C4` (`Gal(ℚ(ζ₅)/ℚ) ≅ (ℤ/5)ˣ ≅ C₄` — the dual/character group as a cyclic
    construction, structural/decidable; the field statements are catalog-frame)

## Conceptual-only legs (honest — Fourier proper is THIN)

- **Orthogonality `Σ_{x∈⟨g⟩} χ(x) = 0`** — NO Lean theorem found (grep: no `orthogonal`/`charSum`/
  root-of-unity-sum-to-zero in `NumberTheory/`). Predicted as a geometric/telescoping sum over roots of
  unity but un-cashed. **The one sharp open target.**
- **DFT / Fourier inversion `f = Σ_j f̂(j) χ_j`, Plancherel** — entirely conceptual; absent.
- **Additive characters `x ↦ ζ^x` and Gauss sums `Σ χ(x)ζ^x`** — the repo's `gauss_mu`
  (`SecondSupplement`, used by `QuadraticReciprocity`) is **Gauss's LEMMA** (sign-flip count / Eisenstein
  floor-sum route to QR), *not* the Gauss *sum*; the analytic root-of-unity kernel `ζ` lives in the
  `Real213`/`Complex` cut residue, not as a finite combinatorial object. So "Gauss sums = depth-2
  character" is conceptual here, grounded only via the multiplicative-character + QR machinery, not an
  actual `Σχ(x)ζ^x` theorem.
- **`MultParityOrthogonal.mult_parity_orthogonal_to_cup_orientation`** exists and is PURE but is
  *linear-independence* "orthogonal" (two ℤ/2's on disjoint data), NOT character-orthogonality — NOT
  cited as a Fourier anchor (would be overclaiming).

## ★ Update — orthogonality prediction CLOSED in ∅-axiom Lean (Legendre level)

The predicted character-orthogonality `Σ_x χ(x)=0` is now a machine-checked theorem at the order-2
(Legendre) character: `ModArith/CharacterOrthogonality.quadratic_orthogonality` (20 PURE) — for a
primitive root `g` mod `p`, the order-2 character sums to zero over the orbit `{g^0,…,g^{p−2}}` AND
each summand is the Legendre symbol (`altSign k = 1 ⟺ g^k` is a QR), via `altSign_eq_one_iff_even` ∘
`qr_pow_iff_even_exp`. Count form `qr_count_eq_nonqr_count` (#QR = #nonQR = (p−1)/2). Propext-avoidance:
Bool `n%2==0` parity instead of `Decidable (2∣n)`. This turns this entry's prediction into a verified
derivation. Open: general order-`>2` χ needs a `Real213` cyclotomic root-of-unity `ζ` (the
transcendental-cut residue this note already located).

## ★ Update 2 — order-`>2` orthogonality CLOSED at the cyclotomic orders realised in `ℤ[ω]`

The "general order-`>2` χ needs a `Real213` cyclotomic `ζ`" boundary is **partially relocated**,
not absolute. The Eisenstein integers `ℤ[ω]` (`CayleyDickson/Integer/ZOmega`, a concrete,
decidable, ∅-axiom `CommRing213`) already **contain** roots of unity of orders 3 and 6 — so for
those `n` the additive-character orthogonality `Σ_{k=0}^{n−1} ζᵏ = 0` is a finite integer identity,
no transcendental cut. New module `CayleyDickson/Integer/RootOfUnityOrthogonality.lean` (23 PURE,
`#print axioms` clean):

- ★★★ `geomSum_telescope` — `(ζ−1)·Σ_{k<n} ζᵏ = ζⁿ − 1`, **generic over the ring**, by induction.
  This is the single algebraic engine the note predicted — the order-`d` generalisation of the
  order-2 `+1,−1` pair-cancellation, now a real symbolic telescope (`ZOmega` `add_mul`/`mul_add`/
  `mul_assoc`), not a per-order trick.
- ★★★ `omega_orthogonality` — `1 + ω + ω² = 0` (order-3 character sum, `ω = ⟨0,1⟩` primitive cube root).
- ★★★ `zeta6_orthogonality` — `Σ_{k=0}^{5} ζ₆ᵏ = 0` (order-6, `ζ₆ = 1+ω = ⟨1,1⟩` primitive 6th root).
- ★★★★ `root_orthogonality` — for *any* `ζ : ZOmega` with `ζⁿ = 1`, `(ζ−1)·Σ_{k<n} ζᵏ = 0`: the
  whole orthogonality defect is carried by the factor `ζ − 1`; a primitive root (`ζ ≠ 1`) in the
  integral domain `ℤ[ω]` forces `Σ = 0`.

**Verdict refinement: PARTIAL → fuller partial.** The character-orthogonality leg now holds at
orders `2` (Legendre, `quadratic_orthogonality`) AND `3, 6` (cyclotomic, `ℤ[ω]`) — three concrete
orders via two rings, with the geometric telescope as the common forced mechanism. It does **NOT**
close the *arbitrary*-`n` case: a primitive `n`-th root for `n ∉ {1,2,3,4,6}` (e.g. `n = 5, 7`) is
not an Eisenstein/Gaussian integer (`ℤ[ω]^×` has only orders `1,2,3,6`; `ℤ[i]^×` adds `4`), so those
`ζ` genuinely remain `Real213` cuts — the honest residue boundary this note located still holds for
non-quadratic-cyclotomic orders. Inversion / Plancherel remain THIN.
