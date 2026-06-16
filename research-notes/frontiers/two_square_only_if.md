# Frontier: sum-of-two-squares "only if" (inert-prime obstruction)

`NumberTheory/SumTwoSquaresCharacterization` (18 PURE) closed the **"if"**
direction (every n whose ≡3-mod-4 primes appear to even powers is a sum of two
squares, via the Brahmagupta product folded over the prime-power list) + the
elementary mod-4 "only if" fragment (`not_isSumTwoSq_three/_seven`).

**CLOSED (core):** `NumberTheory/InertPrimeThreeMod4` (7 PURE) —
`inert_three_mod4` (q≡3mod4 ∣ a²+b² ⟹ q∣a ∧ q∣b), `neg_one_nonresidue_three_mod4`
(−1 a non-residue mod q≡3mod4, via the contrapositive of `sq_plus_one_dvd_iff`),
and the descent step `qsq_dvd_of_dvd_three_mod4` (q∣a²+b² ⟹ q²∣a²+b²).

**Remaining (the full odd-power statement):** the inert-prime obstruction (NOW PROVEN)
`q ≡ 3 (mod 4) ∧ q ∣ a² + b² ⟹ q ∣ a ∧ q ∣ b`.
Classically: `−1` is a quadratic *non-residue* mod `q ≡ 3 mod 4`, so `a² ≡ −b²`
with `q ∤ b` would make `−1` a residue — contradiction. The corpus has
`QRNegOne.qr_neg_one` (the residue direction, for p≡1 mod4) and
`EulerCriterion`, but **not** the non-residue direction packaged for q≡3 mod4.

**Remaining work:** thread `EulerCriterion` to get "`−1` is a non-residue mod
q≡3 mod4" (`(−1)^((q−1)/2) = −1` since `(q−1)/2` is odd), then the inert-prime
lemma, then the full characterization `isSumTwoSq n ⟺ ∀ q≡3mod4 prime, vq(n) even`.
This is QR-machinery-heavy; do interactively with `EulerCriterion`/`GaussLemma`.
