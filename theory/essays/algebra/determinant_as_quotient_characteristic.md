# The determinant as the Lens-quotient characteristic

A determinant is the **characteristic value of the quotient a Lens takes** — the
distinguishing-volume of the row-pointings, read as one number. For an integer matrix it is
not a metaphor but a count: `|det M| = |ℤⁿ / M·ℤⁿ|`, the order of the cokernel — how much
of the lattice the rows fail to reach.

## 213-native answer

A matrix is a bundle of row-pointings `M i : Nat → Int`. `det` reads the **distinguishing
among them** into a single integer (`lean/E213/Lib/Math/Algebra/Linalg213/DetN.lean`: the first-row
cofactor expansion `det (n+1) M = Σⱼ (−1)ʲ · M 0 j · det n (minor M j)`, base `det 0 _ = 1`).
The value answers one question: *do these pointings span their own dimension, and if so with
what quotient-size?* The reading has named ends.

- **`det = ±1` — the unit end.** The rows are a lattice isomorphism: the quotient is trivial,
  the map "divides evenly" over `ℤ`. This is *monic* — the leading coefficient is a unit, so
  `ℤ`-division closes. We already hold this end concretely: the Fibonacci Casoratian
  `[[fibₙ, fibₙ₊₁], [fibₙ₊₁, fibₙ₊₂]]` has `det 2 (fibCas n) = (−1)ⁿ⁺¹`
  (`Linalg213/FibCassiniDet.fibCas_det_eq_unit`, with `cassini_fibZ_eq_altSign` pinning the
  closed form, and `Cauchy/OrbitDimension.cassini_fibZ_step` the period-2 oscillation).

- **`det = 0` — the collapse end.** A direction maps to nothing (kernel ≠ 0); the rows are
  *degenerate*. Two coincident row-pointings make no distinguishing-volume, so the reading is
  `0`. This is the alternating property: *equal rows ⟹ `det = 0`*.

## Derivation

The two ends are the same object — `det` as quotient-characteristic — read at opposite
extremes, and the **sharpening matters**: "divides evenly" names the
`det = ±1` *unit* end, **not** `det = 0`. Clean division is the quotient *closing* with a unit;
`det = 0` is the quotient *failing to close* (a free direction survives, the cokernel is
infinite). They are not the same intuition — they are the poles of one.

That the unit end is a *single value across the number-axis readings* is the number-tower
founding's result: `Lens/Number/SharedUnitAcrossReadings.the_unit_is_one_across_readings`
collects the count-difference glue `NS − NT = 1` (`Mobius213OneAsGlue.ns_minus_nt_is_one`),
the Möbius/ratio determinant `det P = NS − NT` and `det P = 1`
(`mobius_det_eq_ns_minus_nt`, `mobius_det_is_unit`), and the Cassini toggle `det = 1`
(`CassiniUnimodular.toggle_det_unit`) into **one value `1`**. The Fibonacci witness closes the
loop: `Mobius213/Px/PnFibonacciUniversal.det_pn_universal` (`det Pⁿ = 1`) is the same
unimodular datum as `fibCas_det_eq_unit`'s `(−1)ⁿ⁺¹`, read on the difference axis where the
sign-flip is the count-Lens negation = `PairCompletion`'s swap.

So the **monic obstruction** for the C-finite Hadamard product
(`theory/math/analysis/cfinite_orbit_dimension.md`, "Open frontier") is not a separate
difficulty bolted onto the determinant program. A monic `ℤ`-annihilator is exactly "leading
coefficient is a unit" = the `det = ±1` end; reaching it for the general product needs the
characteristic polynomial `det(zI − M)`, whose *that-it-is-monic* is free (the diagonal `zᴺ`)
and whose *Cayley–Hamilton* (the work) is governed by the `det = 0` end. **One object, both
ends.**

## Dual function

This is the classical determinant with its packaging stripped: "oriented volume" is the
analyst's coordinate-laden name for "the count of the quotient / the distinguishing among the
pointings," and the volume's sign is the count-Lens binary axis (`altSign`,
`cassini_fibZ_step`'s period-2 flip), not an orientation imported from a metric. The 213
reading is sharper precisely here — it does not hand you a number and ask what it *measures*;
it names the spectrum `{0 : collapse, ±1 : unit-iso, other : proper quotient}` and identifies
`±1` with monic-ness, the shared unit, and clean `ℤ`-division as **one** thing
(`the_unit_is_one_across_readings`).

## Cross-frame connection

The alternating property's natural home is **antisymmetrization**, not cofactor cancellation.
In the Leibniz reading `det M = Σ_σ sign(σ) · Πᵢ M[i, σ(i)]`, a row swap is `σ ↦ σ∘τ` and
`sign(σ∘τ) = −sign(σ)`, so coincident pointings cancel *structurally* — "overlapping pointings
make no distinction" is the syntax, not a lemma. The cofactor route reaches the same `0` by a column-skip
involution: `Linalg213/DetN.colShift_comm` (deleting two columns in either order is the same)
pairs the terms `(j=a, k=b−1)` and `(j=b, k=a)` with opposite `altSign` and equal double-minor
(`detMinorMinor_comm`). The pairing-cancellation **is** `sign(σ∘τ) = −sign(σ)` read through a
fixed expansion order — same fact, two resolutions. Degeneracy as collapse-of-distinguishing,
antisymmetry of the wedge, and the count-Lens sign on the quotient are one structural event.

## Open frontier

The unit end is built (`fibCas_det_eq_unit`); the collapse end's clean construction is now
settled through the Leibniz antisymmetrization. The sign homomorphism
`psign(σ∘τ) = psign σ·psign τ` (`Linalg213/PermSign.psign_mul`, the bubble-sort build) makes
the alternating property structural — equal rows ⟹ `det = 0` is `psign_mul` read at the
row-swap fixed point — and from it both `det Mᵀ = det M` (`DetTranspose.det_transpose`) and
`det(A·B) = det A·det B` (`DetMul.det_matMul`) descend ∅-axiom (see
`permutation_sign_as_homomorphism.md`). The remaining open work is downstream: the general
both-non-split Hadamard product (`fib·fib`, irrational spectra) still needs the monic resultant
`= det(zI − M)`, but its expansion-time antisymmetry is now a corollary of the sign theory
rather than a missing lemma. The intuition fixes *what* `det = 0` is — the collapse pole of the
quotient-characteristic, the same object as the monic unit at the other pole — and
antisymmetrization, not forced cancellation, is its home.

## Self-check note

The draft risked a substrate reading — "`det` measures a volume the rows live in," as if the
volume pre-existed the pointing. Retreated in place: there is no volume prior to the
row-pointings; `det` *is* the distinguishing those pointings constitute, read as a count. The
quotient is not a space `det` reports on from outside — `|ℤⁿ / M·ℤⁿ|` is the pointing's own
cokernel, and `det = 0` is that self-reading collapsing, not an external verdict of
degeneracy.
