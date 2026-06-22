# Decomposition: the exponential `exp` / `a^x` (and the constant `e`)

*213-decomposition of `exp` and `a^x`, per `../README.md`.*
*Cross-links `practice/prime_factorization.md` — `exp` is the INVERSE reading of
the prime-valuation/character reading `L_vp` (× ↦ +); and `practice/derivative.md`
— `e` is a residue computed via a finite generator, never a held object.*

## The decomposition

- **Construction `C`** — the same `ℕ_{>0}` **×-construction** of
  `prime_factorization.md`: numbers built by multiplying distinguishable ×-atoms
  (primes), with multiplicity. Nothing new is constructed for `exp`; it reads the
  *same* distinguishing-history the other way round.
- **Reading `L_exp`** — the **+ ↦ × direction of the character reading**. Where
  `L_vp = (n ↦ (vₚ(n))ₚ)` reads a ×-construction **off** into a +-vector of exponents
  (`vp_mul : vp p (m·n) = vp p m + vp p n`, `Meta/Nat/VpMul.lean:vp_mul`), `L_exp`
  is the reading that takes an exponent **into** the ×-construction:
  `exp_p : k ↦ pᵏ`, with `vp p (pᵏ) = k` (`Meta/Nat/VpMul.lean:vp_self_pow`) and
  `vp p (aᵏ) = k · vp p a` (`Meta/Nat/VpMul.lean:vp_pow`). So `a^x` is **scalar
  multiplication on the exponent axis** read back through the ×-construction:
  `a^(r·q) = (a^r)^q` is `L_exp` of `r·q = q·r`, i.e. `vp_pow` iterated. `^` is the
  per-axis `×`-readout of `+`-on-exponents.
- **Residue** — for the *fold question* `a^x = b` ("does this `+`-on-exponents land
  back in the ×-construction?"), the residue is the **`^`-wall**: `a^x = b` folds in
  ℕ exactly when the exponent-vectors are parallel, and **distinct ×-atoms never
  trade** — `2^a = 3^b ⟹ a = 0 ∧ b = 0` (`Meta/Nat/FoldCriterion.lean:two_three_unique`),
  the criterion being `a^r = b^q ↔ ∀ prime p, r·vp p a = q·vp p b`
  (`Meta/Nat/FoldCriterion.lean:pow_eq_pow_iff_vp`). For the *value question* "what is
  `a^x` at non-integer `x`, what is `e`", the residue is the real itself: `e` is the
  residue of the partial-sum reading `Σ_{j≤n} 1/j!`, reached by no finite `n`
  (`ExpLog/EulerCut.lean:eulerCut`), only bracketed — `e ∈ (8/3, 3)`
  (`ExpLog/EulerCut.lean:eulerCut_in_8_3_to_3`).

## Re-seeing

```
   L_vp   (prime factorization)  =  ⟨ ℕ_{>0} (×) | n ↦ (vₚ n)ₚ ⟩      × ↦ +   (vp_mul)
   L_exp  (exponential)          =  ⟨ ℕ_{>0} (×) | k ↦ pᵏ        ⟩      + ↦ ×   (vp_self_pow, vp_pow)
   "aˣ = scalar·exponent"        =  vp p (aᵏ) = k · vp p a               (vp_pow)
   "the ^-wall"                  =  a^r = b^q ↔ ∀p, r·vp p a = q·vp p b  (pow_eq_pow_iff_vp)
                                    distinct atoms never parallel        (two_three_unique)
   e = ⟨ Σ_{j≤n} 1/j! | partial-sum reading ⟩ ⊕ Residue,  Residue ∈ (8/3, 3)  (eulerCut_*)
```

`exp` and `log` are **one character reading, the two directions of one arrow**:
`L_vp` linearizes the ×-construction into the +-readout (the "logarithmic mode" of
`prime_factorization.md`'s note), `L_exp` de-linearizes the +-readout back into the
×-construction. They compose to the identity *because they are the same arrow read
forward and backward* — the only verified leg in `Real213` is the depth-0 baseline
(`ExpLog/CutLogExpInverse.lean:exp_log_zero_baseline`, `:inverse_baseline_at_zero`),
which fixes the basepoint; the full series inverse `cutExp ∘ cutLog = id` at depth N
is **declared open in-file**, not proved (honest: see grounding).

## Revelation (collapse: exp/log = one character reading in two directions; e = residue, not object)

**Collapse.** `exp`/`a^x` is not a new operation built on top of `×`; it is the
**inverse reading-direction of the prime-valuation character `L_vp`**. `L_vp` reads
the ×-construction off as a +-vector (`vp_mul`, the × ↦ + homomorphism); `L_exp`
reads a +-exponent back into the ×-construction (`vp_self_pow : vp p (pᵏ) = k`,
`vp_pow : vp p (aᵏ) = k·vp p a`). The classical pair "exponential vs logarithm" is
therefore **one `(C, L)` traversed both ways**, not two functions an identity relates
— exactly the `prime_factorization.md` collapse ("× and + are one construction at two
readings") seen as a *direction toggle on one character arrow*. The `^`-wall (no clean
ℕ-inverse to `×` the way the unit-count inverts `+`) is the **forced** companion: the
+ ↦ × direction folds back into ℕ only when exponent-vectors are parallel
(`pow_eq_pow_iff_vp`), and distinguishable ×-atoms are never parallel
(`two_three_unique`) — so the "logarithm" of a non-power is **not in the ×-construction
at all; it is the residue**, the same surplus the partial-sum reading leaves.

**e = residue, not object.** `e` is never an entity `exp` evaluates at `1`; it is the
**residue of the partial-sum reading** `Σ_{j≤n} 1/j!`, reached by no finite `n`, only
bracketed `(8/3, 3)` (`eulerCut_in_8_3_to_3`) and narrowed by a supplied modulus
(`eulerLimit_in_8_3_to_3`) — "the limit is never the operand" of `derivative.md`,
verbatim. And `e` is **computed from the discrete prime-power skeleton, not approached
as a target**: its two homes — the factorial `Σ1/k!` and the lcm `lcm(1..N) ~ eᴺ`
(PNT's `ψ`-form) — are *one* structure read two ways,
`vₚ(N!) = Σ_{i=1}^N vₚ(lcm(1..⌊N/i⌋))`
(`NumberTheory/FactorialLcmIdentity.lean:vp_factorial_eq_sum_vp_lcm`, Legendre as a
Fubini count over `{(i,e) : (i+1)·p^{e+1} ≤ N}`). The two homes are **two `L_vp`
readouts of the same ×-construction** — so `e`, the constant that looks irreducibly
analytic, is the residue of a reading whose *finite generator is a prime-valuation
count*. The same shape governs the PNT-direction constant `log₂ e`, which is not a
held value but a **computable narrowing interval** `∈ [(m+1)/(2(m+2)), 6]`
(`Lens/Number/Nat213/ChebyshevLower.lean:chebyshev_constant_interval`), sharpening as
`m` grows.

Lean certifies the load-bearing legs: the character homomorphism and its inverse
direction (`vp_mul`, `vp_pow`, `vp_self_pow`), the fold criterion / wall
(`pow_eq_pow_iff_vp`, `two_three_unique`), `e` as a bracketed residue cut
(`eulerCut_in_8_3_to_3`, `eulerLimit_in_8_3_to_3`), and the two-homes identity
(`vp_factorial_eq_sum_vp_lcm`). The full continuous `exp ∘ log = id` is **not** yet a
theorem — only the depth-0 basepoint is (`exp_log_zero_baseline`); stated honestly, the
collapse is certified on the **discrete/character side and conceptual on the analytic
inverse**.

## Note for the technique

**Yes — `exp` confirms the character-mode is INVERTIBLE: it is a reading and its
inverse-reading, one arrow with a direction toggle.** `prime_factorization.md`
introduced the "logarithmic / character mode" as a reading whose readout *changes the
operation* (× ↦ +). `exp` supplies the missing half: the **+ ↦ × direction of the same
mode**. This sharpens README's "`L` carries a character mode" entry — the character
mode is not a one-way projection but a **direction parameter** on one arrow
(`vp_mul` / `vp_self_pow` are the two senses), with the residue (the `^`-wall, the
non-power's "log") sitting *between the directions*, exactly where `prime_factorization.md`'s
faithfulness (`vp_separation`) and the wall (`two_three_unique`) meet. The "logarithmic
mode" should be recorded in README as **bidirectional**: a character reading and its
inverse-reading are one `(C, L)`, the toggle being which operation is the operand and
which the readout.

**Yes — `e as residue` generalizes `φ as residue` and instances the residue-as-
computable-generator rule.** `φ` is the residue of the golden continued-fraction /
`AbCutSeq` reading (algebraic, total modulus); `e` is the residue of the partial-sum /
lcm reading (transcendental, modulus-as-hypothesis). Same shape: **a real is the
residue of a reading, the operand is the reading's finite generator** — for `e`, the
generator is literally a **prime-valuation count** (`vp_factorial_eq_sum_vp_lcm`),
tying the residue-as-generator rule back to the *very character reading `exp` inverts*.
So the calculus's "residue computed via a finite generator, never approached" rule
(`derivative.md`, `the_form_of_the_residue.md`) is not special to limits of difference
quotients: it is the **general status of every transcendental real**, and the generator
is, for `e`, the count-readout `L_vp` of the ×-construction. The deepest collapse here
sits where three meet: `L_vp` (character, `prime_factorization.md`) supplies both the
inverse direction `exp` *and* the finite generator for the residue `e` whose status is
fixed by the resolution parameter (`derivative.md`) — three practice files, one arrow.
