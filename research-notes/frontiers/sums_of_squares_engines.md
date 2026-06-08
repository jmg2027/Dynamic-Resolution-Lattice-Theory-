# Frontier — sums-of-squares representation engines (post four-square)

**Status**: synthesis seed.  **Tier**: 1.  Anchor: the closure of Lagrange's four-square
theorem (`FourSquare.nat_isSum4`, ∅-axiom) leaves the representation corpus with **two distinct
engines**, and that split makes several next questions crisp.

## Patterns (each visible across ≥2 closed chapters)

- **Two counting engines, not one.**  The disc-`−3`/`−4`/`−D` theorems
  (`theory/essays/synthesis/representation_theorems_one_counting_bound.md`) run on a
  *multiplicative* root-bound seed (`PolyRoot.RootBound.eval_zero`) + a *commutative*
  norm-Euclidean descent (`zomega_div_step`, `zi_div_step`, `zsqrt_div_step`), gated by a
  congruence.  Four-square (`theory/essays/synthesis/four_square_additive_pigeonhole.md`) runs on
  an *additive* pigeonhole seed (`Pigeonhole.no_inj_lt` on a sum-collision) + an over-`ℤ` parity
  descent, ungated and ranging over all `n`.  The repo now has both a degree-bound and a
  box-counting collision as seed-producers.

- **The "hard case" is a mis-split, recurringly.**  Four-square's classical `r = m` mod-8 crux
  dissolves once the recursion is cut by the parity of `m` (odd → strict by even-`≤`-odd; even →
  halving, not descent).  This echoes the disc-`−D` sharpness result
  (`ZSqrtNegSharp.descent_false_at_three`): the obstruction was never the arithmetic, it was the
  lattice being asked to do something (`D=3` integral closure) it does not do — look at the
  structural parameter (parity / covering radius) first.

## New questions (structural shape now clear)

- **Disc-`−8` congruence iff — CLOSED** (`ZSqrtNegTwoSquare.disc_neg_eight_iff`, 11 PURE):
  `p = a²+2b² ⟺ p ≡ 1,3 (mod 8)` for an odd prime.  The missing forward half (*which* primes have
  `−2` a QR) is supplied by the **Legendre homomorphism**, not a non-residue search:
  `(−2/p) = (−1/p)·(2/p)` (`legendre_mul` at `a = p−1`, `b = 2`, using `((p−1)·2) % p = p − 2`),
  the two factors being the closed first/second supplements (`neg_one_qr_iff`, `second_supplement`);
  the characters agree exactly on `p ≡ 1,3 mod 8` ⟹ `p ∣ z²+2` ⟹ `split_form_two`.  Necessity is a
  square / `2·square`-mod-8 enumeration (`form8_residue`).  Narrative folded into
  `theory/essays/synthesis/representation_theorems_one_counting_bound.md` (open-frontier paragraph).

- **Three-square theorem (`n = a²+b²+c²` iff `n ≠ 4ᵏ(8m+7)`).**  Genuinely outside *both* engines
  as stated: three squares is **not** multiplicative (no `isSum3_mul`), so the prime reduction
  that powers four-square and the disc-`−D` family does not apply.  The honest question is whether
  any ∅-axiom route exists at all (the classical proof uses Dirichlet primes-in-AP +
  ternary-form genus theory) — record as a hard, possibly-out-of-reach frontier, not a near seed.

- **`isSum4` as a closed predicate — what else is multiplicative-and-pigeonhole-seeded?**  The
  four-square shape (multiplicative closure via a norm identity + an additive seed) is a template;
  the open question is whether sums of `k` squares / Waring-type counts for small exponents admit
  the same two-part `ring_intZ`-identity + pigeonhole decomposition.

## Cross-references

- `theory/essays/synthesis/four_square_additive_pigeonhole.md` — the additive engine.
- `theory/essays/synthesis/representation_theorems_one_counting_bound.md` — the multiplicative engine.
- `theory/math/numbertheory/eisenstein_period_arithmetic.md` — the disc-`−3` arithmetic.
- `lean/E213/Lib/Math/Algebra/CayleyDickson/Integer/ZSqrtNeg{Split,Sharp}.lean` — the `−D` family + the `D=3` sharpness boundary.
