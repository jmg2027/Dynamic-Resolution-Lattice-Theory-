# Decomposition: modular arithmetic (the residue Lens — 213's count-Lens, named)

*213-decomposition of "modular arithmetic / congruences", per `../README.md`.*

This is the calculus's **self-portrait at the number level**: the operation classical mathematics calls
"reduction mod `m`" *is* 213's count-Lens (`seed/AXIOM/06_lens_readings.md`).  So modular arithmetic is
not one field among the 136 — it is the place where the normal form `⟨C|L⟩ ⊕ Residue` is most literally a
theorem of arithmetic.  It also fixes a name collision the corpus has carried implicitly: classical
**"residue" (the remainder) is the Lens *image*** — what is *kept* — while the **213 Residue is the
quotient** — what the Lens *drops*.  They are the two halves of one division.

## The decomposition

- **Construction `C`** — `ℕ` under the **count** (`+1` iterated): a number is *how many times you
  stepped*.
- **Reading `L_m`** — the **residue Lens** `n ↦ n % m`: keep the count *modulo* `m`, forget how many full
  `m`-cycles were completed.  This is the prototype count-Lens — a `Fin m`-valued readout that flattens
  the `+1`-construction onto a cycle.
- **Residue `⊕`** — the **quotient `⌊n/m⌋`**: exactly what `L_m` forgets.  The reconstruction is a single
  ∅-axiom identity,
  ```
     n  =  m · (n / m)  +  (n % m)
        =  [ 213-Residue: the dropped quotient ]  ⊕  [ L_m image: the classical "residue" ]
  ```
  `Meta/Nat/NatDiv213.lean:126 div_add_mod_pure` (`a·(b/a) + b%a = b`).  Reading off the image is
  classical "taking the residue"; reading off the dropped part is the 213 Residue.  **The two senses of
  "residue" are opposite halves of `div_add_mod`** — the cleanest possible disambiguation, and a theorem.

## Re-seeing the theorems

- **CRT = the residue Lens is a *jointly faithful* family at coprime moduli.**  A single `L_m` is
  lossy (residue = the quotient), but the *family* `(L_m, L_n)` at `gcd(m,n)=1` reconstructs `n` uniquely
  on `[0, m·n)`: `ModArith/CRTReconstruction.lean:79 crt_solve_residues` (every residue-pair is hit) +
  `:115 crt_unique` (the reconstruction is unique).  This is the count-Lens analogue of `vp_separation`
  (`prime_factorization.md`): no single resolution is faithful, but the right *family* is.
- **`(ℤ/p)*` theorems = the multiplicative structure of the Lens image.**  Wilson
  (`ModArith/WilsonTheorem.lean:731 wilson`: `(p−1)! ≡ p−1 ≡ −1`), Euler's criterion, Fermat — all live
  on the image `Fin p` read multiplicatively, never on the dropped quotient.

## Revelation (collapse + forcing)

**Collapse — "the residue" and "the Residue" are one division, two halves.**  Classical residue
(remainder, kept) and 213 Residue (quotient, dropped) are not two notions: they are `L_m`'s image and its
complement in `div_add_mod`.  One distinguishing (`÷m`), read forward (remainder) or backward (quotient).

**Forcing — the `q=±1` tag's name *is* the quadratic residue.**  The Legendre symbol `(a/p) ∈ {+1,−1}`
is the standing `q=±1` residue tag realized on `(ℤ/p)*`: `a` is a quadratic **residue** (`q=+1`, a square)
or a non-residue (`q=−1`).  The tag is not named after quadratic residues by analogy — it *is* one:
- `ModArith/EulerCriterion.lean:57 euler_dichotomy` — the two-valued split (square vs the `q=−1` pole),
  Euler's criterion `a^{(p−1)/2} ≡ ±1`;
- `ModArith/LegendreMultiplicative.lean:77 legendre_mul` — the tag is **multiplicative** (a homomorphism
  `(ℤ/p)* → {±1}`: `(ab/p) ↔ (a/p)·(b/p)`), verbatim the character arrow `×↦·` landing in `{±1}`;
- `Lib/Math/Foundations/ResidueTag.lean:86 multiplier_unimodular` (`q² = 1`) + `:228 residue_tag_two_poles`
  — the abstract tag `multiplier : → Int`, `q² = 1`, two poles.  The Legendre symbol is its `(ℤ/p)*`
  instance: `(a/p)² = 1`, two poles `±1`.

So the residue tag the whole corpus runs on (`golden_is_converge` / `escape_residue_outside`, the
`q=±1` spine) has its **name and its first instance** here — quadratic residues are where "residue + a
unimodular ±1 sign" was first read.

## Verified Lean anchors (file:line:theorem — grep-confirmed, scans from repo root this session)

- `Meta/Nat/NatDiv213.lean:126 div_add_mod_pure` (`a·(b/a)+b%a = b`, the reconstruction = 213-Residue ⊕
  Lens-image); `:107 zero_mod_pure`, `:113 mul_mod_self_pure` (`a·x % a = 0`, the Lens kills full cycles).
- `Lib/Math/NumberTheory/ModArith/CRTReconstruction.lean:79 crt_solve_residues`, `:115 crt_unique` —
  joint faithfulness of the coprime residue-Lens family. **PURE (12/0).**
- `…/ModArith/EulerCriterion.lean:57 euler_dichotomy`, `:90 euler_qr_pow_one` — the `q=±1` dichotomy.
  **PURE (2/0).**
- `…/ModArith/LegendreMultiplicative.lean:77 legendre_mul` — the tag is multiplicative (`×↦·` into
  `{±1}`). **PURE (5/0).**
- `…/ModArith/WilsonTheorem.lean:731 wilson` — `(p−1)! ≡ −1`, the image's multiplicative structure.
  **PURE (50/0).**
- `Lib/Math/Foundations/ResidueTag.lean:86 multiplier_unimodular`, `:228 residue_tag_two_poles`,
  `:180 golden_is_converge` — the abstract `q=±1` tag the Legendre symbol instantiates. **PURE (55/0).**
- Spec: `seed/AXIOM/06_lens_readings.md` — the count-Lens, of which `L_m` is the prototype.

## BUILT vs ABSENT

- **BUILT (∅-axiom):** the reconstruction `div_add_mod`, the CRT joint faithfulness, the multiplicative
  image (Wilson/Euler/Legendre), the `q=±1` tag and its multiplicativity.
- **ABSENT (predicted-not-built):** Dirichlet's theorem (primes in residue classes — the *distribution*
  residue of `L_m`, the sibling of `prime_distribution.md`); `(ℤ/m)*` cyclicity for general `m` (the
  full primitive-root classification — `PrimitiveRoot.lean` has the prime case); higher-power residue
  symbols (the `q^k=1` generalization of the `±1` tag, cube/quartic — `EisensteinCubeRoot` has fragments).

## Touches the model?

**No new primitive — this is the model looking at itself.**  `L_m` is the count-Lens (`§6`), and
`div_add_mod` is `⟨C|L⟩ ⊕ Residue` as an arithmetic identity.  The new datum is twofold and structural:
(i) the **name disambiguation** — classical "residue" = Lens image, 213 Residue = dropped quotient, the
two halves of one division; (ii) the `q=±1` tag's **origin** — the Legendre symbol on `(ℤ/p)*` is the
tag's first instance, whence the word "residue." Both invariants (character arrow `legendre_mul`; `q=±1`
tag `euler_dichotomy`) hold verbatim, here at their source.
