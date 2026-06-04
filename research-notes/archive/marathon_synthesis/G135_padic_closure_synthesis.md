# G135 — Cross-corpus synthesis from G122 Real213-p-adic closure

**Status**: Synthesis note (Phase 7.6 of `ready-to-merge` skill).
Written after the G122 Padic library merged into `main`
(308 PURE / 0 DIRTY / 8 modules; `theory/math/padic_real213.md`).

## Anchor

G122 closed the 213-native, ∅-axiom construction of `ℤ_p` and `ℚ_p`,
together with full Hensel lift (existence + uniqueness) for both
inverse and square root, the strong ultrametric on the p-adic
norm, and Frobenius-lift + Teichmüller iteration Cauchy convergence
that holds for any `p ≥ 1` (i.e. no primality required for the lift
itself, only for Fermat at the base case).

## Patterns

### Pattern A — Modulus-witness over Skolem-existential

Recurrent theme: 213's existential structures carry an explicit
modulus / level / digit-position parameter as part of the witness,
not hidden behind `∃`.  Examples:

- `theory/math/cauchy.md`: Cauchy sequence is `{ f : ℕ → ℕ // ∀ N k l,
  k ≥ f N → l ≥ f N → |s_k − s_l| < 1/2^N }`.  The convergence
  modulus `f` is *part of the witness* — no Skolemization, no
  hidden choice.
- `theory/math/padic_real213.md`: every "x is the inverse of y"-style
  statement is parameterised by trunc level `n`.  We never prove
  "`y ≡ x⁻¹` as `ZpSeq`s"; we prove `∀ n, (x · y).trunc (n+1) = 1`.
  The level `n` IS the modulus, made explicit at every site.

Equivalent reformulations in classical analysis would Skolemize:
"there exists an inverse" / "the sequence is Cauchy".  213 forces
the modulus into the type so propext / Quot.sound / Classical.choice
never have to be invoked.

This is not just hygiene — it's the **operational form of the
finite-resolution discipline** (per `seed/RESOLUTION_LIMIT_SPEC.md`):
every theorem stated as a family parameterised by resolution depth
rather than as an existential about an infinite object.

### Pattern B — Diagonal extraction for limit objects

Three constructions in `Padic/Hensel.lean` follow the identical
template:

  - `invFull.digits k := (invSeq k).digits k`
  - `sqrtFull.digits k := (sqrtSeq k).digits k`
  - (hypothetical) `teichmullerFull.digits k := (teichmuller_iter k).digits k`

The pattern: each `approxSeq n` is correct at level `n+1` (its
trunc-`(n+1)` matches the target's trunc-`(n+1)`); higher digits
are 0 / undetermined.  The diagonal `digits k := approxSeq k .digits k`
extracts the "settled" digit at each position.  Stability lemma
(`invSeq_digit_stable` / `sqrtSeq_digit_stable`) verifies that
extending the level beyond `k` doesn't disturb digit `k`.

In classical Lean / Mathlib this would be an inverse limit /
projective limit construction with `propext` + `Classical.choice`
for representative selection.  213's diagonal extraction is the
∅-axiom replacement: instead of "pick a representative of the
equivalence class", say "evaluate the n-th approximation at
position n".

**Possible export to other domains**:
- `theory/math/cauchy.md` sequence families already carry explicit
  moduli — would the same diagonal-extraction trick provide a
  ∅-axiom completion to ℝ-style limits?  The Euler / Wallis / Pell
  families would be the obvious test cases.
- `theory/math/dyadic_fsm.md` FSM signatures are sequence-level
  objects with explicit-level reads — is there a "diagonal FSM" /
  "stable bit at depth n" extraction analogous to `invFull`?

### Pattern C — Cancellation by inverse as a one-liner methodology

Hensel inverse uniqueness, Hensel sqrt uniqueness, the trio of
cancellation laws (`mul_left_cancel_trunc`, `mul_right_cancel_trunc`,
`mul_eq_zero_of_unit_left`), and the `(y+z)(y−z) ≡ 0 → y ≡ z`
reasoning in `sqr_unique_trunc` all flow from one observation:

  *Left-multiplication by `invFull x` is a bijection at trunc level
  whenever `x` is a unit.*

The full proof structure for any "uniqueness via cancellation"
question becomes:
  1. Apply `invFull x` on the left.
  2. Use `mul_trunc_assoc` to regroup.
  3. Use `mul_invFull_correct` to collapse `inv · x ≡ 1`.
  4. Use `mul_one_left_trunc` to finish.

This is a 5-line lemma chain that closes a whole class of
problems.  In `modular_arithmetic.md` the same cancellation pattern
appears for `ModInverseFromBezout` — explicit Bezout witness gives
`a · a⁻¹ ≡ 1 (mod p)`, then any cancellation question reduces to
"multiply both sides by the explicit inverse".

**Generalisation conjecture**: in any ∅-axiom ring-with-explicit-unit
context (currently `ℤ/p` via Bezout, `ZpSeq p` via `invFull`,
`QpSeq p` via `QpSeq.inv`, hypothetically Witt vectors or Cohen
rings), cancellation laws should be provable by this same 5-line
template.  If they're not, the underlying "ring with explicit unit"
abstraction is missing something.

### Pattern D — Binomial-free proofs via "p equal terms sum to 0 mod p"

The G122 Frobenius lift's most distinctive feature: it does NOT use
the classical fact `p ∣ C(p, k)` for `0 < k < p` (with p prime).
Instead it uses the elementary identity

  `∑ᵢ₌₀ᵖ⁻¹ (same value) = p · (same value) ≡ 0 (mod p)`.

Applied to the geometric sum `S = ∑ᵢ (a+b)ⁱ · aᵖ⁻¹⁻ⁱ` when
`b ≡ 0 (mod p)`, each term reduces to `aᵖ⁻¹ mod p`, total ≡ 0.
The "p equal things summed" trick is the binomial-coefficient-free
substitute.

**Where this might recur**:

- Wilson's theorem `(p−1)! ≡ −1 (mod p)`: classical proof uses
  pairing `k · k⁻¹ ≡ 1`.  213's `modInverseFromBezout` (in
  `modular_arithmetic.md`) already gives explicit inverses without
  binomial coefficients — Wilson should be expressible directly.
- Lucas's theorem (binomial mod p): explicit binomial coefficients
  needed here, but maybe the 213 version only needs a digit-wise
  recursion (since `C(n, k) mod p` is well-known to depend on the
  base-p digits of n and k).
- Euler's totient `φ(p^k) = p^k − p^(k−1)`: counting argument, no
  binomial needed — should be trivially 213-native.

**Methodological lesson**: when the classical proof uses binomial
coefficients, look first for a sum-of-equal-things rewrite.  213's
strict-∅-axiom discipline often unearths a more elementary identity.

## New questions

### Question α — ω(x) as explicit ZpSeq (not just Cauchy)

We proved Teichmüller iteration is Cauchy.  The natural limit
object `ω(x)` — the unique fixed point of `y ↦ yᵖ` with `ω(x) ≡ x
(mod p)` — is **not** yet constructed as a ZpSeq.

Diagonal extraction (Pattern B) is the obvious next step:

  `Zp.teichmuller (x : ZpSeq p) (sb : ...) : ZpSeq p
   where digits k := (teichmuller_iter x k).digits k`

Need: stability lemma analogous to `sqrtSeq_digit_stable`,
correctness `(teichmuller x)^p ≡ teichmuller x (mod p^(n+1))` at all
n, and the identifying property `teichmuller x ≡ x (mod p)`.

Estimated effort: ~150 lines.  All infrastructure exists.

### Question β — `ℤ_p^× ≃ μ_{p−1} × (1 + p·ℤ_p)`

Once ω(x) is built, the decomposition `x = ω(x) · u` (where u ≡ 1
mod p) is a one-line corollary using existing inv/mul machinery.

This gives Padic the standard "Witt-style" multiplicative structure.
Combined with `theory/math/modular_arithmetic.md`'s F_{p²} content,
the framework has the building blocks for quadratic / cyclotomic
extensions of ℤ_p — a real frontier toward Galois representations.

### Question γ — Diagonal extraction in Cauchy / DyadicFSM?

Pattern B (diagonal extraction) was 213's substitute for "take the
inverse limit".  Does the same trick apply to:

- `Cauchy.Euler`, `.Wallis`, `.Pell`: the sequences have explicit
  ε-moduli; can the diagonal `seq_n.value_at_n` give a 213-native
  "value at the modulus" that behaves like a limit?
- `DyadicFSM` signatures: each signature reads finitely many bits.
  Is there a "stable-bit-at-depth-n" diagonal that captures
  asymptotic FSM behaviour without invoking limit objects?

If Pattern B exports cleanly, we have a **general 213-native
completion** that could replace propext-quotient constructions
across the corpus.

### Question δ — Sequence-level ring laws: imported residue or real gap?

We deferred sequence-level ring axioms in Padic (e.g. `Zp.add x y =
Zp.add y x` as ZpSeq).  The trunc-level versions are closed.

The deferral was annotated as "not obviously the right 213-native
question" — perhaps trunc-level equivalence (at every n)
*is* the appropriate 213 notion, and sequence-level equality is an
imported classical residue that should not be chased.

Is there a chapter in `theory/` that has formalised this dichotomy?
(Search candidates: `seed/AXIOM/05_no_exterior.md`,
`seed/RESOLUTION_LIMIT_SPEC.md`, `theory/meta/raw_derivation_levels.md`.)
If not, this might warrant a `theory/meta/` chapter on **trunc-level
vs sequence-level identity** as a 213 stance.

## Cross-references

- `theory/math/padic_real213.md` — the anchor closure (G122).
- `theory/math/modular_arithmetic.md` — supplies Bezout +
  Frobenius-on-F_{p²} that Padic builds on (G119 marathon).
- `theory/math/dyadic_fsm.md` — sister sequence-machinery chapter,
  candidate for Pattern B export.
- `theory/math/cauchy.md` — explicit-modulus Cauchy framework;
  Pattern A neighbour, Pattern B candidate.
- `seed/RESOLUTION_LIMIT_SPEC.md` — formal home of the
  finite-resolution discipline that Pattern A operationalises.
- `theory/meta/raw_derivation_levels.md` — meta-architecture for
  multi-level reasoning; potential home for Question δ.

## How to use this note

Pick one of α / β / γ / δ for a follow-up campaign.  α and β are
direct extensions of G122 (small effort, immediate payoff).  γ is a
cross-chapter generalisation campaign (medium effort, potentially
high payoff if Pattern B exports).  δ is meta-architectural (a
research note → seed proposal, not Lean code in the first instance).
