# Cross-domain insights — the CP-phase cohomology meets main's sign/number-theory campaigns

**Opened**: 2026-06-08 (merge marathon: `origin/main`'s permutation-sign /
determinant / Legendre-QR / p-adic-cyclotomic campaigns merged into this branch's
CKM-CP-phase-via-cohomology arc).  Recorded directions where the two genuinely
**share one object** — candidate bridging theorems / essays.

## Insight 1 — the inversion sign is ONE object (det · Hodge ⋆ · CP)

- **main**: `det(permMatrix σ) = psign σ = (−1)^{inv(σ)}` (`PermMatrixDet`,
  `PermSign`) — the permutation sign is the parity of an inversion count.
- **this branch**: the signed-`ℤ` cup wedge sign `mergeSign(S,T) = (−1)^{inv(S,T)}`
  (`Cup/SignedCup`), `inv = #{(s,t): s∈S, t∈T, s>t}` — the Hodge-star orientation
  is the **same** inversion parity, and the cup's **antisymmetry**
  `e_i∧e_j = −(e_j∧e_i)` IS the determinant's antisymmetry (Leibniz).
- **Bridge**: the signed Hodge cup IS a determinant — `⟨e_i, ⋆e_j⟩ = δ_{ij}`
  (`hodge_pairing_is_identity`, `det h = 1`) is the `det(permMatrix) = psign`
  story on the Hodge basis.  Candidate theorem: the cohomological CP pairing's
  positivity (`h = I`, `det = 1`) is `det_permMatrix` / `det_mul` at the
  identity.  The "one permutation, three readouts" essay
  (`the_permutation_under_three_readouts`) gains a **fourth** readout: the Hodge
  ⋆ orientation.

## Insight 2 — `ℤ[i]` Gaussian: the CP phase IS main's QR splitting

- **this branch**: the CP phase lives in `ℤ[i]^× = C₄` (`SignedStarC4`,
  `CPPhaseC4Forcing`); `d=5` splits in `ℤ[i]`: `5 = (2+i)(2−i) = 2²+1²`
  (`CyclotomicFive`), opening the `90°` phase.
- **main**: Euler's criterion / Gauss's lemma / the Legendre symbol
  (`ModArith/*`, `legendre_symbol` chapter) — `5` splits in `ℚ(i)` **iff**
  `(−1/5) = +1`, i.e. `5 ≡ 1 (mod 4)` (`neg_one_qr_iff`).
- **Bridge**: the CP-phase `C₄`/`90°` and main's QR are the *same* Gaussian
  fact — `d=5 ≡ 1 mod 4` ⇒ `(−1/5)=+1` ⇒ `5` splits in `ℤ[i]` ⇒ `μ₄=⟨i⟩`/`90°`.
  Candidate theorem: `δ_CP = 90° ⟺ (−1/d) = +1` (the CP phase is the QR class of
  `−1 mod d`).  And **Zolotarev** (`psign(×a mod p) = (a/p)`) ties the permutation
  sign (Insight 1) to the Legendre symbol — so all three are one.  The Zolotarev
  side is **proven**: `psign_mulPermMod_qr` (`ModArith/ZolotarevSign`, PURE) gives
  `psign(σ_a) = +1 ⟺ a` is a QR mod `p`, with `psign_mulPermMod` the
  sign-homomorphism `σ_a ∘ σ_b = σ_{ab}`.  What remains open is the **CP** leg —
  identifying `δ_CP`'s `C₄` class with the `(−1/d)` QR class as a theorem, not the
  permutation↔Legendre identity itself.

## Insight 3 — `ℚ(ζ₅)` cyclotomic: CP modulus+phase ↔ main's Teichmüller/Gauss sums

- **this branch**: `ℚ(ζ₅)` unifies the golden modulus (real subfield `ℚ(√5)`,
  Gauss periods `ζ+ζ⁴=1/φ`, `ζ²+ζ³=−φ`) and the `C₄` phase (Galois group)
  (`CyclotomicFive`, `A5ThreeRepPhase`).
- **main**: the p-adic **Teichmüller** units `μ_{p−1}` and the quadratic
  character as their 2-torsion (the p-adic harvest; `qr_iff_pow_one` as a
  `μ_{p−1}`-component identity, the open p-adic-QR frontier); Gauss sums in
  `gauss_qr`.
- **Bridge**: the CP **Gauss periods** of `ℚ(ζ₅)` and main's **Gauss sums**
  (`gauss_qr`) / **Teichmüller** cyclotomic units are the same cyclotomic
  arithmetic.  Candidate: the golden modulus `1/φ²` (CP) is the real Gauss
  period of `ζ₅`, and the `C₄` phase is its Galois group — both p-adically the
  Teichmüller decomposition `μ₄ × μ_{(p−1)/4}` at the relevant prime.

## Insight 4 — the polarization positivity is a determinant (Hodge ↔ det_mul)

- **this branch**: `HodgeRiemann`'s positivity `h = Q·J = I ≻ 0`
  (`hodge_riemann_positivity_signed`), `det h = 1`.
- **main**: `DetMul.det_matMul` (`det(A·B) = det A · det B`), `det_transpose`.
- **Bridge**: the Hodge–Riemann Hermitian form's positive-definiteness is a
  `det`/signature statement; `det(Q·J) = det Q · det J = 1` (main's `det_mul`)
  gives the polarization's unit determinant.  The "positive definite" is the
  `det > 0` of main's determinant campaign on the Weil-operator pair.

## Status

All four are **candidate bridges** tying main's sign/QR/cyclotomic campaigns to
the CP-phase cohomology.  The richest: Insight 1+2 together — *the permutation
sign, the Hodge-⋆ orientation, the Legendre symbol, and the CP phase are one
inversion/Gaussian object*.  Three corners of that square are now theorems: the
permutation sign = the determinant (`PermSign`/`PermMatrixDet`), and the
permutation sign = the Legendre symbol (`ModArith/ZolotarevSign.psign_mulPermMod_qr`,
PURE).  The remaining corner — the **CP** phase's `C₄` class = the `(−1/d)` QR
class — is the open leg.  Closure record (the proven 213 sides): `Cup/SignedCup`,
`Hodge/*`, `Mixing/CP*`, `Icosahedral/CyclotomicFive`; `PermSign`/`PermMatrixDet`,
`ModArith/*` incl. `ZolotarevSign`, the p-adic harvest.
