# The Legendre symbol is the sign of a pointing

The Legendre symbol `(a/p)` is not a primitive.  It is the **parity bit of the
multiply‑by‑`a` permutation** — the finite‑state readout the unit pointing
carries, equal at once to a count's parity, a determinant, and an inversion sign.

## 213-native answer

Multiplication by a unit `a` permutes the residues `{0,…,p−1}`: `σ_a : x ↦ a·x
mod p`, carried as the value‑list `mulPermMod a p = (iota p).map (·*a % p)`
(`theory/math/numbertheory/zolotarev.md`).  A permutation's sign is the
count‑Lens parity of its inversion count, `psign σ := altSign (inversions σ)`
(`seed/AXIOM/06_lens_readings.md` §6.7; `Linalg213.Permutation`).  **`(a/p)` is
`psign σ_a`** — `+1` iff that permutation is even
(`ModArith/ZolotarevMuBridge.zolotarev_mu`).  No symbol is assumed; the bit is
read off a pointing.

## Derivation

That `psign σ_a` deserves to be *called* `(a/p)` is Zolotarev's lemma, a theorem
for every odd prime.  The residue side is structural: `a ≡ z²` gives
`σ_a = σ_z ∘ σ_z`, a square, so its sign is `1` (`psign_mulPermMod_qr`).  The
converse — non‑residue ⟹ odd — turns on `σ_a` commuting with negation,
`σ_a(p−x) = p − σ_a(x)`, which forces `σ_a` into block form
`0 :: (fh ++ (revL fh).map(p−·))` (`mulPermMod_block`).  The block sign collapses
to a single symmetric cross‑count whose off‑diagonal pairs cancel mod 2; the
surviving diagonal `#{x∈[1,m] : σ_a(x) > m}` is exactly Gauss's `μ`
(`altSign_crossInv_map_psub`, `altSign_diag_eq_prodSgn`).  Composed with Gauss's
lemma `∏ sgFn = 1 ⟺ QR` (`theory/math/numbertheory/legendre_symbol.md`), this is
`psign σ_a = (a/p)`.

So `(a/p)` reads three ways on one pointing: the inversion sign `psign σ_a`, the
determinant `det(permMatrix σ_a)` (`det_permMatrix_mulPermMod`, via `det = psign`),
and the half‑system sign‑product `∏ sgFn` (Gauss).  Three readouts, one
residue‑internal permutation.

## Dual function

This is the classical Legendre symbol with its packaging stripped: the textbook
`(a/p)` is a *function defined to be* `±1` by cases on quadratic residuacity,
then *proven* (Zolotarev) to equal a permutation sign.  The definitional detour
is redundant — there is only the pointing and its parity, and
"residue/non‑residue" is the count‑Lens read one bit further by `mod 2`.  The
refinement is that the equality of the three readouts is not a coincidence to be
discovered but the *same count* viewed through inversions, determinant
antisymmetry, and the half‑system fold.

## Cross-frame connections

The sharper convergence is with the **finite‑state** frame.  The synthesis
`theory/essays/synthesis/finite_state_is_of_the_pointing.md` holds that
finite‑state‑ness is a property of the *pointing*, not the value.  Multiplication
on the one carrier splits exactly here: `× a` (unit) is a **finite** permutation
`σ_a` — a finite‑state pointing — while `× p` **escapes** finite state
(`mulCarry_unbounded` / `carry_is_nu_escape`).  `(a/p)` is precisely the Z/2
invariant the finite pointing *carries* and the escape *lacks*: the Legendre
symbol is the finite‑state readout of the multiply‑by‑`a` pointing.  The negation
case ties to the spiral axis: `psign σ_{−1} = (−1/p) = +1 ⟺ p ≡ 1 (mod 4) ⟺
i ∈ ℤ/p` — the sign of the order‑2 negation permutation is the obstruction to the
order‑4 axis point `ℤ[i]^× = C₄` (`the_i_point_of_the_spiral_axis.md`) existing
mod `p`.  The §6.7 count‑Lens reading, the `det = psign` permutation‑sign engine,
and the finite‑state‑of‑the‑pointing thesis are one fact at three resolutions.

## Open frontier

Zolotarev itself is closed (all odd primes).  The neighbouring faces — the
Legendre symbol as the 2‑torsion projection of the Teichmüller `ω`, and the
Hensel/`diagLimit` square‑root face — remain open (tracked in
`research-notes/frontiers/`, the "permutation's three readouts" board).
