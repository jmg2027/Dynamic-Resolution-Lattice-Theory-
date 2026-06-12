# Cross-domain: Zolotarev / permutation-sign branch ↔ merged main

Scratch synthesis after merging `origin/main` (the one-carrier / p-adic νF arc,
the Casoratian / spiral-axis arc, the CKM CP-phase arc, the "finite-state-is-of-
the-pointing" essay) into the **Zolotarev converse** branch (`zolotarev_mu`:
`psign σ_a = (a/p)` for every odd prime, plus the reusable `InversionsAppend`
permutation-sign combinatorics).  Insights as they come to mind — proven cores
cited inline; the bridges are the open work.

## 1. ★ `σ_a` is the *finite-state* side of main's finite-state / escape split

main's `one_carrier_crossdomain` note already flagged: multiplication's unit /
non-unit split IS the finite-state / escape split — `× unit` = a finite
permutation with a sign (Zolotarev `mulPermMod`) vs `× p` = the valuation escape
(`mulBase_eq_mul_pElem`, the νF carry that is *not* finite-state).  With Zolotarev
now **closed** (`zolotarev_mu`: the sign IS the Legendre symbol `(a/p)`), the split
sharpens to a statement about *invariants*:

- `× a` (unit): `σ_a` is a **finite** permutation of `ℤ/p`; its single Z/2 invariant
  is `(a/p) = psign σ_a` — a clean parity readout the finite-state pointing carries.
- `× p`: the pointing **escapes** finite state (`mulCarry_unbounded`/
  `carry_is_nu_escape`); there is no analogous finite sign — the escape is exactly
  the absence of such an invariant.

So the Legendre symbol is the **finite-state readout of the multiply-by-`a`
pointing** — directly instancing main's "finite-state-ness is a property of the
pointing, not the value" essay (`finite_state_is_of_the_pointing.md`): the unit
`a` is pointed at finite-state-ly (a permutation), so it *has* a sign; `p` is not.
Buildable: state `(a/p)` as "the Z/2 obstruction the `×a` pointing carries and the
`×p` escape lacks" on one carrier.

## 2. ★ Zolotarev `psign σ_a` and main's companion-determinant sign are one schema

main's `casoratian_axis_cp_crossdomain` note: the companion-determinant sign
`altSign(k−1)` is the `psign` of the shift cycle — "a fourth instance of the
permutation-under-three-readouts schema."  My branch **closes** the number-theory
instance: `psign σ_a = det(permMatrix σ_a) = (a/p)` (`zolotarev_mu` +
`det_permMatrix_mulPermMod`).  So the schema "one permutation, three readouts
(inversions = determinant = a domain invariant)" now has **two closed instances**:

| instance | permutation | three readouts |
|---|---|---|
| Zolotarev (this branch) | `σ_a = ×a mod p` | `psign` = `det(permMatrix)` = `(a/p)` Legendre |
| Casoratian (main) | the shift cycle of a `k`-recurrence | `psign` = `det(companion)` = `altSign(k−1)` |

Both rest on the *same* engine `PermMatrixDet.det_permMatrix` (`det = psign`).
**CLOSED** (`Cauchy.CasoratianPermSign`, ∅-axiom): `det_permMatrix_cycShift :
det(permMatrix (cycShift m)) = altSign m` routes the cyclic shift through
`det_permMatrix` (just like `psign(mulPermMod a p) = (a/p)`), and
`companion_det_eq_permMatrix_det : det(companion a (m+1)) = det(permMatrix
(cycShift m))·a 0` makes the Casoratian depth multiplier *literally* a
permutation-matrix determinant.  "Permutation under three readouts" is now a
**shared theorem family** across number theory and the determinantal recurrence
ladder, both on the one `det_permMatrix` engine — not two pictures.

## 3. `crossInv` (inversions cross-term) ↔ the determinant's multilinear cross-terms

`InversionsAppend.inversions_append` factors the inversion count of `L ++ M`
through the cross-term `crossInv L M = Σ_{x∈L} ltCount x M`, and the Zolotarev
converse turns on a **symmetric cross-count** whose off-diagonal pairs cancel mod 2
(`altSign_crossInv_map_psub`).  This is the permutation-level shadow of the
determinant antisymmetry main uses in `det_matMul` / the Casoratian expansion: a
determinant with a repeated row vanishes for the *same* reason the symmetric
cross-count is even — paired off-diagonal contributions cancel.  Speculative bridge:
present `altSign_crossInv_map_psub` and "repeated-row ⟹ `det = 0`" as one
antisymmetry lemma read at the count level vs the alternating-form level.

## 4. ★ `psign σ_{-1} = (−1/p)` ↔ main's spiral-axis order-4 point / `ℤ[i]^× = C₄`

The negation permutation `σ_{-1} : x ↦ p − x` is the order-2 element of
`(ℤ/p)^×`; this branch computes `psign σ_{-1} = (−1)^m = (−1/p)`
(`ZolotarevConverse.psign_mulPermMod_negone_qr`).  main's spiral-axis arc places
the **order-4** point at `ℤ[i]^× = C₄` (the CP phase's `C₄`, `the_i_point_of_the
_spiral_axis.md`), where `i` is the order-4 floor rotation `μ = −i`.  The two meet
at `−1`'s square root: `psign σ_{-1} = (−1/p) = +1 ⟺ −1 is a QR ⟺ p ≡ 1 (mod 4)
⟺ i ∈ ℤ/p ⟺ the order-4 axis point exists mod p`.  So the **sign of the negation
permutation** (this branch, order-2) is exactly the **obstruction to the order-4
axis point** (main): the Legendre supplement `(−1/p)` is the mod-`p` shadow of
"does the disc-`−4` rung (`ℤ[i]`) split here."  Buildable: a synthesis note tying
`psign σ_{-1}` (negation = order-2 floor rotation `μ=−1`) to main's order-4 floor
rotation `μ=−i`, both as `ℤ[i]^×`-rotations of the residue circle, with `(−1/p)`
the parity that decides whether the order-4 lift exists.

## Status

Edge **(2) is CLOSED** (`Cauchy.CasoratianPermSign`, 4 PURE — `det_permMatrix_cycShift`,
`companion_det_eq_permMatrix_det`); (1), (3), (4) remain open synthesis directions
(the proven cores on each side are closed; the bridging edges are not).  Closed
cores: this branch — `ModArith/ZolotarevMuBridge.zolotarev_mu`,
`Linalg213/InversionsAppend` (28 PURE), `theory/math/numbertheory/zolotarev.md`;
main — `one_carrier`, `casoratian`/`spiral_coordinate_classification`,
`cp_phase`/`the_i_point...`, `finite_state_is_of_the_pointing`.  Insight 1 is now
the ripest open edge (the `×a`/`×p` invariant-vs-escape statement on one carrier).

---

# Addendum — the primitive-root route ↔ merged main (second merge)

A second branch (`p-adic-reciprocity-topics`) closes Zolotarev the **classical**
way: `(ℤ/p)*` is cyclic (`PrimitiveRoot.exists_primitive_root`), a primitive root
is a `(p−1)`-cycle of sign `−1` (`ZolotarevCycle.zolotarev_full`), and that single
odd witness drives the character.  This brings the **multiplicative-order**
infrastructure (`ordModP`, `ord_dvd`, `ord_mul_coprime`, `every_ord_dvd_maxOrd`)
that the μ-route never builds — and that infrastructure is what bridges to main's
golden-field / rank-of-apparition arc.

## 5. ★ The rank of apparition `α(p)` is a multiplicative order — `ordModP` is its rational shadow

main's rank law `α(p) ∣ p − (5/p)` (`RankApparition`) is, structurally, the
**order of the golden ratio `φ`** in `𝔽_p[√5]`: `α(p) = ord(φ)` in the field where
`φ` lives — `𝔽_p` when `5` splits (`(5/p)=+1`, `α(p) ∣ p−1`), `𝔽_{p²}` when `5` is
inert (`α(p) ∣ p+1`).  This branch's `ordModP a p` with `ord_dvd_p_sub_one`
(`ord ∣ p−1`) is **exactly the split-case shadow**: the rational-prime
multiplicative order, of which `α(p)` is the quadratic-extension lift.  Buildable
bridge: state `α(p)` as `ordModP`-in-`𝔽_{p²}` (the same `ord_dvd` Euclidean-split
argument, run in `FP2SqrtD` rather than `ℤ/p`), unifying `ord_dvd_p_sub_one`
(this branch) and `rank_law_dispatch` (main) as one "order divides the group order"
fact across the two fields.

## 6. ★ `(5/p)` is the parity of the discrete log of `5` — main's `psign σ_5` and this branch's cyclic structure are one Z/2 bit

main reads `(5/p) = psign σ_5` (`zolotarev_mu`) — a permutation parity — and uses
it as the Fibonacci rank offset (`the_fibonacci_rank_is_a_permutation_sign`).  This
branch's `exists_primitive_root` gives the **structural** reading: with a generator
`g`, `(5/p) = +1 ⟺ 5 ∈ ⟨g²⟩ ⟺ dlog_g(5)` is **even**.  So the rank offset
`p − (5/p)` is the **parity of the discrete log of `5`** in the cyclic group
`(ℤ/p)*` — the same Z/2 invariant main reads as a permutation sign, here read as
"even/odd power of the generator."  The squares being an index-2 subgroup
(`⟨g²⟩`, this branch, `primitive_not_qr`: the generator is a non-residue) is the
*structural why* behind the μ-route's parity: the quadratic character is the unique
`(ℤ/p)* ↠ {±1}`, which exists **because** the group is cyclic of even order
`p−1 = 2m`.  Buildable: `(a/p) = (−1)^{dlog_g(a)}` as a Lean theorem, identifying
this branch's cyclic/discrete-log reading with main's `psign σ_a` and with Euler's
`a^m`, a fourth co-equal readout of the one quadratic character.

## Status (addendum)

Both 5–6 are **open synthesis directions**; the proven cores are closed on each
side — this branch: `ModArith/{PrimitiveRoot,ZolotarevCycle,MulOrder}`
(`theory/math/numbertheory/primitive_roots.md`); main: `RankApparition`,
`ZolotarevMuBridge`, `the_fibonacci_rank_is_a_permutation_sign`.  Insight 6 is the
ripest single edge: `(a/p) = (−1)^{dlog_g(a)}` ties the cyclic structure, the
permutation sign, and Euler's power into one Z/2 readout.
