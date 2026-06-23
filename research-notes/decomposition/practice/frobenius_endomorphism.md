# Decomposition: the Frobenius endomorphism `x ↦ xᵖ` (where the character arrow collapses)

*213-decomposition of "Frobenius / the p-power map in characteristic p", per `../README.md`. The **collapse
point of Invariant A**: in char `p` the `p`-power map respects **both** operations at once — it is the unique
place `×↦·` and `+↦+` are the *same self-map*. Its fixed set is Fermat's little theorem.*

> **False-friend flag.** `Lib/Math/NumberTheory/ModArith/Frobenius.lean` is the **Frobenius *number***
> (the Chicken-McNugget / coin problem — largest non-representable `ax+by`), **not** this endomorphism
> (CLAUDE.md "arithmetic Frobenius" false-friend row).  The arithmetic Frobenius is grounded in
> `freshman_binom` + `fermat` below, not in that file.

## The decomposition

- **Construction `C`** — the **`p`-th power** `x ↦ xᵖ` (the ×-construction iterated `p` times), over a
  reduction-mod-`p` carrier (`modular_arithmetic.md`'s Lens supplies the characteristic).
- **Reading `L`** — reduction **mod `p`** (the residue Lens): Frobenius lives on `𝔽_p`-algebras.
- **Residue `⊕`** — the part Frobenius **moves**: `xᵖ ≠ x` off the prime field.  Its **fixed set** is
  `𝔽_p` (Fermat: `aᵖ ≡ a`), the `q=+1` invariant core; the residue is the proper extension
  `𝔽_{pⁿ} ∖ 𝔽_p` where Frobenius acts nontrivially (`q=−1`), generating `Gal(𝔽_{pⁿ}/𝔽_p)` (cyclic of
  order `n`).

## Re-seeing the theorems

**The content is the collapse: in char `p`, `x ↦ xᵖ` is a ring endomorphism — it respects `×` *and* `+`.**
- *Multiplicative* always: `(xy)ᵖ = xᵖ yᵖ` (the `×↦·` character, trivially).
- *Additive* **in char `p`**: `(x+y)ᵖ ≡ xᵖ + yᵖ`, the **freshman's dream**, because every middle binomial
  coefficient vanishes mod `p`: `Lib/Math/NumberTheory/ModArith/LucasTheorem.lean:50 freshman_binom`
  (`choose p i % p = 0` for `0 < i < p`). **PURE (18/0).**

So Frobenius is the **unique coincidence of Invariant A's two arrows**: `×↦·` and `+↦+` are *one and the
same map* `(·)ᵖ`.  Everywhere else the character arrow turns one operation into the *other* (`vp`:
`×↦+`); here, at characteristic `p`, it turns each operation into *itself* — the arrow folds to an
endomorphism.  The freshman's dream is exactly that fold (`freshman_binom` = "the additive defect of `(·)ᵖ`
is `0` mod `p`").

**Fermat's little theorem = the fixed-point set.**  `Lib/Math/NumberTheory/ModArith/MulOrder.lean:51
fermat` (`a^(p−1) % p = 1` for a unit `a`) is the unit-group form; equivalently `aᵖ ≡ a` — Frobenius fixes
exactly `𝔽_p`.  The multiplicative order divides `p−1` (`:181 ord_dvd_p_sub_one`: `ordModP a p ∣ p−1`) — the
unit group `(𝔽_p)*` is the cyclic `q=±1`-graded carrier Frobenius acts on trivially. **PURE (13/0).**

## Revelation (collapse + forcing)

**Collapse — "additive number theory" and "multiplicative number theory" *literally become one map* at
char `p`.**  `prime_factorization.md` collapsed `×` and `+` into one *construction read at two resolutions*
(`vp_mul`: `×↦+`); Frobenius is the sharper collapse — at characteristic `p` the resolution that separates
them **vanishes**, and the single self-map `(·)ᵖ` *is* both the multiplicative and the additive structure.
The freshman's dream is not a curiosity; it is the character arrow's fixed point as an *operation*.

**Forcing — Frobenius is `A` at maximal strength, and its `q=+1` residue is Fermat.**  Per `SYNTHESIS.md`
§2 (iv) (`B` = `A`'s unimodular shadow / fixed part), Frobenius is the case where `A` (the character) is a
full ring endomorphism, and `B`'s `q=+1` (fixed/converge) pole is its **fixed field** `𝔽_p` (Fermat
`aᵖ≡a`), the `q=−1` (moved/escape) pole the proper extension.  The Galois group `Gal(𝔽_{pⁿ}/𝔽_p) = ⟨Frob⟩`
(cyclic order `n`) is the residue's orbit — Frobenius *is* the generator whose fixed points peel off `𝔽_p`.

## Verified Lean anchors (file:line:theorem — grep-confirmed, scans this session)

- `Lib/Math/NumberTheory/ModArith/LucasTheorem.lean:50 freshman_binom` (`choose p i % p = 0`, `0<i<p`) —
  the additivity of Frobenius `(x+y)ᵖ ≡ xᵖ+yᵖ`. **PURE (18/0).**
- `Lib/Math/NumberTheory/ModArith/MulOrder.lean:51 fermat` (`a^(p−1) % p = 1`) — Frobenius' fixed set
  `𝔽_p` (Fermat's little, the `q=+1` core); `:181 ord_dvd_p_sub_one` (`ordModP a p ∣ p−1`, the unit-group
  order). **PURE (13/0).**
- Cross-frame: `modular_arithmetic.md` (the mod-`p` residue Lens supplying the characteristic),
  `prime_factorization.md` (the `×↦+` character this collapses), `SYNTHESIS.md` §2 (iv) (`B` = `A`'s fixed
  part — here `𝔽_p`).

## BUILT vs ABSENT

- **BUILT (∅-axiom):** the additivity of Frobenius (`freshman_binom`), Fermat's little theorem
  (`fermat`), the unit-order divisibility (`ord_dvd_p_sub_one`), and now the **fixed-point form
  `aᵖ ≡ a (mod p)`** for *all* `a` — `Lib/Math/NumberTheory/ModArith/FermatFixedPoint.lean`
  `fermat_fixed_point` (`a^p % p = a % p`) + `fermat_fixed_unit` (`0<a<p ⟹ a^p%p=a`), **PURE (2/0)**, the
  explicit statement that Frobenius fixes the prime field.  The collapse and its `q=+1` fixed core.
- **ABSENT (predicted-not-built):** the **named ring endomorphism** `frobenius : 𝔽_p-alg → 𝔽_p-alg` as a
  packaged additive-and-multiplicative map (only its two halves `freshman_binom` + `(xy)ᵖ=xᵖyᵖ` are built);
  the **Galois generation** `Gal(𝔽_{pⁿ}/𝔽_p)=⟨Frob⟩` (the residue's cyclic orbit, `galois.md`'s finite-field
  case).

## Touches the model?

**No new primitive — Invariant A's collapse point.**  The new datum: Frobenius is the **sharpest** form of
the character-arrow collapse — not "`×` read as `+`" (two resolutions of one construction, `prime_factorization`)
but "`×` and `+` are the *same self-map* `(·)ᵖ`" (one operation, char `p`), with the freshman's dream
(`freshman_binom`) as that identification and Fermat (`fermat`) as its `q=+1` fixed residue.  Sharpens
`SYNTHESIS.md` §2 (iv): where `A` is a full endomorphism, `B`'s fixed pole is the fixed field.
