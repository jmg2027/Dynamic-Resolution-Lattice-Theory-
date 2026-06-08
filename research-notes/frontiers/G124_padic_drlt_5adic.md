# G124 — H: DRLT-specific 5-adic content (terrain map)

Live open direction carried from `G123_padic_next_directions.md` §H, the
last of the post-closure p-adic directions.  This note is the honest
terrain map produced by *genuinely looking* (per `seed/AXIOM/05_no_exterior.md`
§5.4 guard), not a closure.  Approached carefully: H touches DRLT
physics, where the two standing failure modes are *forcible map onto
existing physics* (CLAUDE.md operating principles) and *universe-constant
framing* / *DRLT-validation-as-the-goal* (CLAUDE.md failure catalog).

## The three sub-questions, read against the actual repo

### H1 — "Is there a 5-adic obstruction to a DRLT precision result?"
**Settled — as removed, not deferred.**  The chain that would have
carried this — `5²⁵ = N_U = d^(d²) = configCount 2` as "the resolution
index at which 1/α_em is evaluated" — is **deleted and unrecoverable**
(`RERESEARCH_n_u_removal.md`: identifying a configuration COUNT with a
spectral-sum TRUNCATION index is a category error; the fractal-level
axis has no privileged level; the tower has no top).  What survives is
bare arithmetic: `configCount 2 = 5^25` and the level-25 truncation
bound `(x : ZpSeq 5).trunc 25 < 5^25`
(`Padic/DRLTIntegration.padic_DRLT_alignment`) — true, parametric, and
carrying *no* resolution meaning.  The 0.2 ppb 1/α_em precision chain
rests on `π²` as a literal analytic input, never on `5²⁵`
(`AlphaEM/GramStructural*`).  So there is no 5-adic obstruction to find:
the place one would have lived was excised on purpose.

### H2 — "Does i₅ = √(−1) ∈ ℤ_5 carry physics meaning (spinors, CP)?"
**No internal handle found.**  Searched: no edge from `i_5` / `i₅` to
anything under `lean/E213/Lib/Physics/` or `theory/physics/`;
`catalogs/physics-constants.md` has no 5-adic, imaginary-unit, CP, or
L-value entry.  A "5-adic spinor" or "5-adic CP phase" would have to be
*constructed to match* a physics target — exactly the forcible map the
operating principles forbid.  Stated plainly (§5.4): after looking, the
internal handle is not there.  This is the falsifier doing its work, not
a deferral — the residue earns 5-adic physics reach by *finding* an
internal bridge while testable, and none is present.

### H3 — "Are there 5-adic L-values relevant to α_em, m_μ/m_e?"
**No internal handle found.**  The DRLT constants are built from
π-literal analytic inputs (ζ(2)/π⁵ factors in the graded 1/α_em
formula; the mass ratios from simplex/golden combinatorics), not from
p-adic L-functions.  No `L`-value object exists in the corpus to bridge
*from*.  Same verdict as H2: constructing one would be fudge (no exterior
dialer to source it — `seed/AXIOM/07_primacy.md` §7.2).

## What H *did* unlock — a pure-arithmetic internal handle (CLOSED)

Looking for an internal handle turned one up, but in **math, not
physics**: the concrete 5-adic imaginary unit is a root of unity.

`i₅`'s digit 0 is `2`, a *primitive* root mod 5 (`2,4,3,1` — order
4 = p−1).  So `i₅` is a primitive 4-th root of unity:
- `i₅² ≡ −1` (`Padic/Hensel.i_5_sq_trunc_two`),
- `i₅⁴ ≡ 1` at every level (`Padic/TeichmullerUnit.i_5_pow_four_trunc`,
  via the general `Arith.neg_one_sq_trunc`, `(−1)²≡1`),

pinning its order at exactly `4 = p − 1`, i.e. `i₅ ∈ μ₄ ⊂ ℤ_5^×`.  This
is the `p = 5` instance of `teichmuller_pow_pred_trunc` (the A/B work) made
explicit: the "imaginary unit" of `ℤ_5` IS a Teichmüller representative,
not an extra structure adjoined to it.  Essay:
`theory/essays/algebra/teichmuller_as_forced_fixed_point.md`.

## The only 213-native form a future H can take

Any further H must avoid the deleted category error (count ≠ truncation
index) and the forcible-map trap.  The admissible shape is
**arithmetic-first**: ask whether a 5-adic *arithmetic* invariant of an
object the corpus *already builds* (a graded-formula coefficient, a
simplex count, a Cassini/continuant value) is non-trivial — and only
*then*, if a bridge appears unforced, read it toward an observable.

## A second arithmetic-first handle exhibited (CLOSED)

Looking again in the admissible shape turned up a second unforced
handle, on the Cassini/continuant object the corpus already builds (the
golden recurrence behind `R_u = 1/φ²`, the CKM CP modulus): the
**Fibonacci rank of apparition at the ramified prime 5**.

`5` is the discriminant of `x² − x − 1`, the *unique ramified* prime of
the golden modulus `ℚ(√5)` (`x² − x − 1 ≡ (x − 3)² mod 5`).  At the
double root the two Binet branches split in status, and the corpus's two
mod-5 FSMs read the split exactly:

- **Fibonacci** (singular branch, `F_n ≡ n·3ⁿ⁻¹`):
  `FibApparitionMod5.five_dvd_fib_iff` — `5 ∣ F_n ⟺ 5 ∣ n`.  The rank of
  apparition is `α(5) = 5 = p` itself (`rank_apparition_five`), the
  **ramified-prime signature** (generic primes have `α(p) ∣ p ± 1`; only
  the ramified prime has `α(p) = p`, and `F_5 = 5 = p`).
- **Lucas** (regular branch, `L_n ≡ 2·3ⁿ`):
  `FibApparitionMod5.lucasMod5_never_zero` — `5 ∤ L_n` for every `n`, no
  rank of apparition.

Packaged: `fib_lucas_apparition_divergence` (13 PURE, ∅-axiom,
`lean/E213/Lib/Math/NumberTheory/DyadicFSM/FibApparitionMod5.lean`).
This is the FSM-level proof of the divergence the `LucasFSMmod5`
docstring had stated only verbally.  It ties the resolution prime `5`
(`configCount 2 = 5²⁵`) to the *ramified* prime of the DRLT golden
modulus through one structural fact — the singular/regular split of the
Binet branches at the double root — without any forcible map onto an
observable (the handle is pure 5-adic arithmetic of an already-built
object; no physics target is constructed-to-match).

Remaining rung (open, not closable ∅-axiom by FSM alone): the full
valuation lift `ν₅(F_n) = ν₅(n)` (lifting-the-exponent), of which this
closes the `n = 1` (zero-set / rank) rung.

## Status
- H1: settled (removed).  H2, H3: no internal handle — recorded plainly.
- Pure-math spinoff `i₅ ∈ μ₄`: CLOSED (∅-axiom), folded into the
  Teichmüller chapter + essay.
- Pure-math spinoff Fibonacci rank of apparition `α(5) = 5` +
  Lucas-never-zero: CLOSED (∅-axiom, `FibApparitionMod5`).  Open rung:
  `ν₅(F_n) = ν₅(n)` (LTE).
