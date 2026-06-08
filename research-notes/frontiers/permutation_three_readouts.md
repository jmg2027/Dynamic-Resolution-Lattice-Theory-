# Cross-domain: one permutation, three readouts (branch ↔ main synthesis)

Scratch synthesis after merging `origin/main` (the Legendre-symbol /
quadratic-residue package) into the determinant + p-adic branch
(`det(permMatrix σ) = psign σ`, the `ZpSeq` commutative-ring Setoid, the shared
`diagLimit`).  Insights "as they come to mind" — the open directions where the two
campaigns touch.  Proven cores cited inline; the bridges are the open work.

## 1. ★ The permutation's THREE readouts (Zolotarev is the missing edge)

A permutation `σ` of a finite set has, in this repo, two proven numerical
readouts that **agree**:

- the **inversion sign** `psign σ = (−1)^(inversions σ)`
  (`Permutation.psign`);
- the **determinant of its permutation matrix** `det (permMatrix σ)`
  (this branch, `PermMatrixDet.det_permMatrix : det (permMatrix σ) = psign σ`).

main brought the **third** readout into the repo without yet wiring it to the
first two: for `σ_a = (×a mod p)`, the multiply-by-`a` permutation of `ℤ/p`,
**Zolotarev's lemma** says `psign σ_a = (a/p)` (the Legendre symbol).  main's QR
package proves the count-side `(a/p)` via Gauss's lemma (`ModArith.gauss_qr` /
`gauss_mu`) and Euler's criterion (`euler_criterion`, `qr_iff_pow_one`).

So the open synthesis is **one permutation, three readouts**:

```
   inversions (psign)  ──[PermMatrixDet, proven]──  det(permMatrix)
            │                                              │
            └──────── Zolotarev (OPEN edge) ───────────────┘
                              │
                    Legendre (a/p)  ──[main: gauss_qr / euler_criterion, proven]
```

The frontier note `reciprocity_as_count_lens` already flagged "Zolotarev
unification (`psign` sign side ↔ `gauss_qr` count side, one permutation two
readouts)".  `det_permMatrix` makes the **sign side concrete as a determinant** —
the Legendre symbol is literally `det` of the permutation matrix of `×a mod p`.

**Closed ∅-axiom (`ModArith/ZolotarevSign.lean`, 7 PURE):** the structural backbone.
`mulPermMod a p = (iota p).map (·*a %p)` is the value-list of `σ_a : x ↦ a·x mod p`;
`mulPermMod_mem_perms` (it is a permutation for units), `mulPermMod_comp`
(`σ_a ∘ σ_b = σ_{ab}`), and `psign_mulPermMod` (`psign σ_{ab} = psign σ_a · psign σ_b`
— the sign **character homomorphism**).  One direction of Zolotarev is closed:
`psign_mulPermMod_qr` — **quadratic residues map to even permutations**
(`QR(a) ⟹ psign σ_a = 1`, since `σ_a = σ_z ∘ σ_z`).  Via `gauss_qr`
(`QR(a) ⟺ ∏ sgFn = 1 = (a/p)`) this is the residue side: the sign character agrees
with the Legendre symbol on the quadratic-residue subgroup.

**Converse — closed on the `−1` axis + for `p ≡ 3 (mod 4)`**
(`ModArith/ZolotarevConverse.lean`, 22 PURE): `σ_{-1}` is the reversal `[0, p−1, …, 1]`,
whose inversion count `tri₂(p−1)` has parity `m`, so `psign σ_{-1} = (−1)^m`
(`psign_mulPermMod_negone`).  `(−1)^m = 1 ⟺ m` even `⟺ p ≡ 1 mod 4 ⟺ −1` is a QR
(`neg_one_qr_iff`), i.e. `psign σ_{-1}` **matches the Legendre symbol at `−1`**
(`psign_mulPermMod_negone_qr`) — the `(−1/p)` corner of the inversion-sign square.
For `p ≡ 3 (mod 4)`, `−1` is a *non-residue* with `psign σ_{-1} = −1`: the
**nontriviality witness**.  Every non-residue `a` is then `(QR)·(−1)`
(`legendre_mul`), so `psign σ_a = psign σ_{QR} · psign σ_{-1} = 1·(−1) = −1 = (a/p)`
(`zolotarev_pmod4_three`) — the **full identity** for half the primes.

**Residual (the last edge):** the full identity for `p ≡ 1 (mod 4)` (where `−1` is a
*residue*, so the `−1` axis yields no nontriviality witness).  Two routes: (a) a
**primitive root** `g` (then `σ_g` is a single `(p−1)`-cycle of sign `−1`, and the
index-2 kernel argument closes it); (b) the **Gauss-`μ` parity bridge**
`psign σ_a = (−1)^μ` via the `σ_a = (block lift) ∘ (μ within-pair flips)` decomposition
through the half-system `[1,m]` (the `fold`/`sgFn` machinery already in `GaussLemma`).
Closing either gives the triangle `det (permMatrix (mulPermMod a p)) = (a/p)` for all `p`.

## 2. Teichmüller ω ↔ the quadratic character (p-adic lift of Euler's criterion)

main's Euler criterion is `a^((p−1)/2) ≡ (a/p) (mod p)`.  This branch's
neighbours: `ω(x)^(p−1) ≡ 1` (`teichmuller_pow_pred_trunc` — `ω` is a
`(p−1)`-th root of unity), and the unit decomposition `ℤ_p^× ≃ μ_{p−1} ×
(1+pℤ_p)`.  The quadratic character is exactly the order-2 component:
`(a/p) ≡ ω(a)^((p−1)/2)` read in `μ_{p−1}`.  So **Euler's criterion is the
mod-`p` shadow of a statement about the Teichmüller `μ_{p−1}` torus** — the
Legendre symbol is the projection of `ω` to the 2-torsion `{±1} ⊂ μ_{p−1}`.
Open: state `qr_iff_pow_one` as a `μ_{p−1}`-component identity on `ω`, lifting
the QR character p-adically (would tie the `Padic/TeichmullerUnit` split to the
`ModArith/EulerCriterion` package on one carrier).

## 3. Ring-quotient tower: ZpSeq commRing ⊃ (ℤ/p^n) ⊃ (ℤ/p where QR lives)

This branch closed `(ZpSeq p, ZpSeqEquiv)` as a **commutative ring**
(`SetoidMul.zp_setoid_commRing_capstone`), built by descending each operation to
`ℤ/p^n` via the `*_trunc` quotient maps.  main's QR package lives entirely at
`n = 1` (`ℤ/p`).  The truncation tower `ZpSeq ↠ ℤ/p^n ↠ ℤ/p` is one chain of
ring quotients; QR is the quadratic-character layer of its bottom floor, and the
Teichmüller lift (insight 2) is the section back up.  Reading: **the same
ring-quotient machinery (`mul_trunc`/`add_trunc`) that builds the p-adic ring at
all levels specializes at level 1 to the ring where reciprocity is proved** — no
new structure, one tower read at two heights.  (Conceptual; not a theorem target
unless a level-`n` quadratic-character statement is wanted.)

## 4. `diagLimit` ↔ Gauss-sum / Hensel of the QR data (speculative)

`diagLimit` is the repo's one "reach the limit reached by no approximant"
constructor (now shared by `invFull`/`sqrtFull`/`teichmuller`).  The QR package's
square-roots of units (`i_5 = √(−1)`, Hensel `sqrtFull`) ARE `diagLimit`s, and a
quadratic residue mod `p` is exactly a unit whose `sqrtFull` exists in `ℤ_p`
(Hensel lifts the mod-`p` root).  So **"`(a/p) = 1`" ⟺ "`a` has a `diagLimit`
square root in `ℤ_p`"** — the analytic (Hensel/`diagLimit`) face of the
arithmetic (Legendre) predicate.  Open: prove `qr_iff_sqrtBase_exists` — `(a/p)=1
↔ ∃ SqrtBase` for the constant sequence `a` — directly bridging
`ModArith` ↔ `Padic/Hensel` via `diagLimit`.

## Status

All four are **open synthesis directions** (the proven cores on each side are
closed; the bridging edges are not).  Closure records of the two sides:
`theory/math/numbertheory/{legendre_symbol,quadratic_reciprocity}.md` (main) and
`lean/E213/Lib/Math/Algebra/Linalg213/PermMatrixDet.lean` +
`theory/math/numbersystems/padic_real213.md` (branch).  Insight 1 (Zolotarev) is
the ripest — a single ∅-axiom edge that would make "one permutation, three
readouts" a theorem, not a picture.
