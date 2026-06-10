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
Buildable bridge: `psign (cyclicShift n) = altSign (n−1)` as a Lean theorem
mirroring `psign (mulPermMod a p) = (a/p)` — the cyclic-shift companion sign read
through the same `det_permMatrix`, making "permutation under three readouts" a
*shared theorem family* across number theory and the determinantal recurrence
ladder, not two pictures.

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

All four are **open synthesis directions** (the proven cores on each side are
closed; the bridging edges are not).  Closed cores: this branch —
`ModArith/ZolotarevMuBridge.zolotarev_mu`, `Linalg213/InversionsAppend` (28 PURE),
`theory/math/numbertheory/zolotarev.md`; main — `one_carrier`,
`casoratian`/`spiral_coordinate_classification`, `cp_phase`/`the_i_point...`,
`finite_state_is_of_the_pointing`.  Insights 1–2 are the ripest (each a single
∅-axiom Lean edge: the `×a`/`×p` invariant-vs-escape statement, and
`psign(cyclicShift) = altSign(n−1)` through `det_permMatrix`).
