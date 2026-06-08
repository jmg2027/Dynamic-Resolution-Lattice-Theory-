# The CKM apex modulus is the residue's self-reference contraction

The Wolfenstein apex modulus `R_u = √(ρ̄²+η̄²)` is the contracting eigenvalue `(NS−√d)/2` of the
matrix that encodes the 213 axiom — the same matrix whose attracting fixed point is the golden
residue `φ`. Its value `1/φ²` is read off a characteristic polynomial built from atomic counts, not
fitted.

## 213-native answer

The axiom's four clauses, written algebraically, are the Möbius matrix `M = [[2,1],[1,1]]`
(`seed/AXIOM/03_form.md` §3.5; the encoding is the ∅-axiom bridge `Lib/Math/Algebra/Mobius213`).
Its characteristic data is fully atomic: `trace = NS = 3`, `det = 1`,
`disc = NS²−4 = 5 = NS+NT = d`, so its eigenvalues are `(NS ± √d)/2 = φ², 1/φ²`
(`Mobius213.{mobius_213_trace, mobius_213_discriminant}`). The apex modulus is the **contracting**
one, `R_u = (NS−√d)/2 = 1/φ²` — the eigenvalue `< 1`, selected from the reciprocal pair `λ₊λ₋ = det
= 1` by `R_u < 1` (`JarlskogApex.apex_modulus_is_selfref_contracting_eigenvalue`,
`apex_modulus_subunit_forced`). The primitive statement is `(NS−√d)/2`; "1/φ²" is its golden
reading.

## Derivation

Two further facts pin the form. First, **why a square** — why `1/φ²` (two Fibonacci steps) and not
`1/φ` (one). `M = Q²` with `Q = [[1,1],[1,0]]` the Fibonacci matrix
(`FibonacciAtomicLock.P_eq_Q_squared`). One step `Q` has `det Q = −1`: its contracting eigenvalue
`−1/φ` is **negative**, so it cannot be a modulus. Squaring de-signs it — `det Q² = (det Q)² = +1`,
eigenvalues `φ², 1/φ²` both positive — so the contracting eigenvalue is its own modulus only at the
`Q²` level (`FibonacciAtomicLock.apex_modulus_is_designed_square`). A modulus is sign-free; the
square is the operation that removes the sign.

Second, the `√d = √5` is not incidental. The discriminant `disc = NS²−4` equals the atomic sum
`d = NS+NT` only at the forced shape `(NS,NT) = (3,2)`: under `NT ≥ 1` (a time axis) and `NT < NS`
(fewer time than space axes), the equation `ns²−4 = ns+nt` has the unique solution `(3,2)`
(`FibonacciAtomicLock.disc_eq_atomic_sum_selects_shape`). So `disc = d` is a selection, not an
accident — a second route to the atomic shape independent of `Theory/Atomicity/PairForcing`, and the
`√5` inside `R_u` is the same `d = 5` carried by the rest of the framework.

## Dual function

Read classically, `√(ρ̄²+η̄²)` is a free Standard-Model fit parameter and `1/φ²` a numerical
coincidence to two decimals. Strip the packaging and the modulus is the contraction rate of the one
self-map the axiom already commits to: the residue points at itself, `P(x) = (2x+1)/(x+1)` ascends
to `φ` (`seed/AXIOM/05_no_exterior.md` §5.6), and `1/φ²` is the eigenvalue governing that ascent.
213's reading is sharper in locating the golden structure precisely: it is in the **radius** (a
length, `(NS−√d)/2`), not the angle. The apex angle `γ = arccos(1/φ²) ≈ 67.5°` is not a
golden-triangle angle (`cos 36° = φ/2`, `cos 72° = 1/2φ`; `arccos(1/φ²)` is neither), so the
golden-ness does not propagate to the CP phase — the phase is the separate Gaussian object `i`
(disc `−4`, `90°`; `theory/physics/cp_phase.md`).

## Cross-frame connections

The same `M` is four objects at once: the algebraic form of the axiom (§3.5), the self-reference
iterator with fixed point `φ` (§5.6), the companion matrix of `x²−3x+1` (so the apex reciprocal pair
is read by the same `companion_det`/`psign` lens as the Casoratian depth ladder), and — via `M = Q²`
— the Fibonacci/Cassini engine whose `det = ±1` is the difference-Lens sign that recurs as the
Cassini `W = ±1`, the Casoratian multiplier `altSign(k−1) = psign(shift)`, and the Legendre symbol.
One `2×2`, `det = 1` matrix carries the residue's self-reference, the CP apex modulus, and the
sign-readout shared with number theory.

## Open frontier

The value `(NS−√d)/2` is forced; the standing premise is the **identification** — why the physical
apex modulus `|V_ud V_ub|/|V_cd V_cb|` *is* this eigenvalue. The candidate arrow is `det = 1`:
the reciprocal pair `λ₊λ₋ = 1` is the unitarity-triangle base-normalization (one leg ≡ 1 carries
`λ₊`, forcing the apex onto `λ₋`), to be built by expressing the CKM matrix in `M`'s eigenbasis and
showing the 1–3 sector inherits `λ₋`. Separately, the companion `α = 90°` (right unitarity triangle,
from the proven Hodge `C₄`) is a distinct hypothesis whose sharp prediction `ρ̄ = R_u² = 1/φ⁴ ≈
0.146` is the falsifier to watch — it should be tested apart from the radius claim, not bundled with
it.
