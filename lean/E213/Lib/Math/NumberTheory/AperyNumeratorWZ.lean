import E213.Lib.Math.NumberTheory.AperyCollapsing

/-!
# AperyNumeratorWZ — the reduced polynomial core of the NUMERATOR certificate

The ζ(3) numerator Apéry recurrence has an explicit certificate in the extended
`(b, √b, c)` language (found + verified exact:
`research-notes/frontiers/zeta3_wz/derive_numerator_certificate.py`): with
`φ(j,k) = −k(2j+3)P₄(j,k)/((j+1)(j+2)²(j−k+1)(j+k+1)(j+k+2))` and the half-weight
ratio `ρ = (j−k)(j+k+1)/(k+1)²` (`AperyCollapsing.sqw_shift_k`), the residual
`U = (−1)^k √b·u` telescopes: `U(j,k) = ψ(j,k+1) − ψ(j,k)` for `k < j`, with a
3-term boundary at `k = j` and `U(j,j+2) ≡ 0`.

This file deposits the **polynomial cores** — the numerator analogues of
`AperyRecurrence.reduced_wz_identity` — as ∅-axiom theorems: `rnum_reduced`
(R-NUM, the cleared per-`k` telescoping identity, additive `j = k+d` form,
common denominator `(j+1)(j+2)²(k+1)(j−k+1)(j+k+1)(j+k+2)(j+k+3)`) and
`rbnd_reduced` (R-BND, the cleared `k = j` boundary identity).  The identities
were derived and verified symbolically + numerically (exact, all `j < 26`)
before deposit; the Lean kernel re-proves them from scratch here.  R-NUM's
single-`ring_nat` form exceeds the reflective normalizer's budget, so its proof
is split: six machine-generated per-term expansion lemmas + a pairwise
collection chain + the `rw`-composition.

The remaining assembly — binomial `W`-factoring on the `AperyCollapsing`
contiguities, `sumTo` telescoping, the boundary/`R-NIL` cases, and the
`zeta3Num = (n!)³·A` induction — is the recorded mechanical frontier
(`numerator_plan.md` §"THE NUMERATOR CERTIFICATE").

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.AperyNumeratorWZ

/-- `P₄(j,k)` — the quartic of the numerator certificate `ψ` (all coefficients
    positive, so the compositions at `j = k+d` and at `k+1` stay
    subtraction-free). -/
def numP4 (j k : Nat) : Nat :=
  8 * (j * j * j * j) + 24 * (j * j * j) * k + 48 * (j * j * j)
    + 31 * (j * j) * (k * k) + 107 * (j * j) * k + 104 * (j * j)
    + 13 * j * (k * k * k) + 86 * j * (k * k) + 153 * j * k + 96 * j
    + 18 * (k * k * k) + 60 * (k * k) + 70 * k + 32

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
private theorem e1_expand (k d : Nat) :
    (34 * ((k + d) * (k + d) * (k + d)) + 153 * ((k + d) * (k + d)) + 231 * (k + d) + 117) * ((k + d + 1) * (k + 1) * ((2 * k + d + 1) * (2 * k + d + 1)) * (2 * k + d + 3))
    = 272 * k * k * k * k * k * k * k * k + 1496 * k * k * k * k * k * k * k * d + 2448 * k * k * k * k * k * k * k + 3468 * k * k * k * k * k * k * d * d + 11628 * k * k * k * k * k * k * d + 9464 * k * k * k * k * k * k + 4386 * k * k * k * k * k * d * d * d + 22780 * k * k * k * k * k * d * d + 37986 * k * k * k * k * k * d + 20472 * k * k * k * k * k + 3264 * k * k * k * k * d * d * d * d + 23647 * k * k * k * k * d * d * d + 61087 * k * k * k * k * d * d + 67425 * k * k * k * k * d + 27017 * k * k * k * k + 1428 * k * k * k * d * d * d * d * d + 13855 * k * k * k * d * d * d * d + 49958 * k * k * k * d * d * d + 85392 * k * k * k * d * d + 70018 * k * k * k * d + 22197 * k * k * k + 340 * k * k * d * d * d * d * d * d + 4471 * k * k * d * d * d * d * d + 21636 * k * k * d * d * d * d + 51606 * k * k * d * d * d + 65454 * k * k * d * d + 42399 * k * k * d + 11046 * k * k + 34 * k * d * d * d * d * d * d * d + 697 * k * d * d * d * d * d * d + 4600 * k * d * d * d * d * d + 14724 * k * d * d * d * d + 26015 * k * d * d * d + 26010 * k * d * d + 13815 * k * d + 3033 * k + 34 * d * d * d * d * d * d * d + 357 * d * d * d * d * d * d + 1557 * d * d * d * d * d + 3679 * d * d * d * d + 5106 * d * d * d + 4173 * d * d + 1863 * d + 351 := by
  ring_nat

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
private theorem e2_expand (k d : Nat) :
    2 * (2 * k + 2 * d + 3) * (4 * (d * d) + 8 * d * k + 12 * d + 2 * (k * k) + 11 * k + 9) * ((k + d + 1) * ((k + d + 2) * (k + d + 2)) * ((2 * k + d + 1) * (2 * k + d + 1)))
    = 32 * k * k * k * k * k * k * k * k + 288 * k * k * k * k * k * k * k * d + 416 * k * k * k * k * k * k * k + 1032 * k * k * k * k * k * k * d * d + 3008 * k * k * k * k * k * k * d + 2176 * k * k * k * k * k * k + 1984 * k * k * k * k * k * d * d * d + 8704 * k * k * k * k * k * d * d + 12624 * k * k * k * k * k * d + 6056 * k * k * k * k * k + 2272 * k * k * k * k * d * d * d * d + 13292 * k * k * k * k * d * d * d + 28902 * k * k * k * k * d * d + 27688 * k * k * k * k * d + 9862 * k * k * k * k + 1600 * k * k * k * d * d * d * d * d + 11676 * k * k * k * d * d * d * d + 33762 * k * k * k * d * d * d + 48356 * k * k * k * d * d + 34306 * k * k * k * d + 9644 * k * k * k + 680 * k * k * d * d * d * d * d * d + 5932 * k * k * d * d * d * d * d + 21350 * k * k * d * d * d * d + 40578 * k * k * d * d * d + 42952 * k * k * d * d + 24006 * k * k * d + 5534 * k * k + 160 * k * d * d * d * d * d * d * d + 1620 * k * d * d * d * d * d * d + 6958 * k * d * d * d * d * d + 16432 * k * d * d * d * d + 23042 * k * d * d * d + 19184 * k * d * d + 8780 * k * d + 1704 * k + 16 * d * d * d * d * d * d * d * d + 184 * d * d * d * d * d * d * d + 916 * d * d * d * d * d * d + 2578 * d * d * d * d * d + 4486 * d * d * d * d + 4942 * d * d * d + 3366 * d * d + 1296 * d + 216 := by
  ring_nat

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
private theorem e3_expand (k d : Nat) :
    ((k + d + 1) * (k + d + 1)) * ((k + d + 2) * (k + d + 2)) * (k + 1) * (d + 1) * (2 * k + d + 2) * (2 * k + d + 3)
    = 4 * k * k * k * k * k * k * k * d + 4 * k * k * k * k * k * k * k + 20 * k * k * k * k * k * k * d * d + 58 * k * k * k * k * k * k * d + 38 * k * k * k * k * k * k + 41 * k * k * k * k * k * d * d * d + 202 * k * k * k * k * k * d * d + 313 * k * k * k * k * k * d + 152 * k * k * k * k * k + 44 * k * k * k * k * d * d * d * d + 315 * k * k * k * k * d * d * d + 802 * k * k * k * k * d * d + 863 * k * k * k * k * d + 332 * k * k * k * k + 26 * k * k * k * d * d * d * d * d + 254 * k * k * k * d * d * d * d + 933 * k * k * k * d * d * d + 1624 * k * k * k * d * d + 1347 * k * k * k * d + 428 * k * k * k + 8 * k * k * d * d * d * d * d * d + 106 * k * k * d * d * d * d * d + 534 * k * k * d * d * d * d + 1339 * k * k * d * d * d + 1784 * k * k * d * d + 1207 * k * k * d + 326 * k * k + k * d * d * d * d * d * d * d + 20 * k * d * d * d * d * d * d + 140 * k * d * d * d * d * d + 486 * k * d * d * d * d + 935 * k * d * d * d + 1014 * k * d * d + 580 * k * d + 136 * k + d * d * d * d * d * d * d + 12 * d * d * d * d * d * d + 60 * d * d * d * d * d + 162 * d * d * d * d + 255 * d * d * d + 234 * d * d + 116 * d + 24 := by
  ring_nat

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
private theorem e4_expand (k d : Nat) :
    ((k + d + 1) * (k + d + 1) * (k + d + 1) * (k + d + 1)) * (k + 1) * ((d + 1) * (d + 1)) * (2 * k + d + 3)
    = 2 * k * k * k * k * k * k * d * d + 4 * k * k * k * k * k * k * d + 2 * k * k * k * k * k * k + 9 * k * k * k * k * k * d * d * d + 31 * k * k * k * k * k * d * d + 35 * k * k * k * k * k * d + 13 * k * k * k * k * k + 16 * k * k * k * k * d * d * d * d + 81 * k * k * k * k * d * d * d + 149 * k * k * k * k * d * d + 119 * k * k * k * k * d + 35 * k * k * k * k + 14 * k * k * k * d * d * d * d * d + 98 * k * k * k * d * d * d * d + 260 * k * k * k * d * d * d + 332 * k * k * k * d * d + 206 * k * k * k * d + 50 * k * k * k + 6 * k * k * d * d * d * d * d * d + 58 * k * k * d * d * d * d * d + 212 * k * k * d * d * d * d + 388 * k * k * d * d * d + 382 * k * k * d * d + 194 * k * k * d + 40 * k * k + k * d * d * d * d * d * d * d + 15 * k * d * d * d * d * d * d + 77 * k * d * d * d * d * d + 195 * k * d * d * d * d + 275 * k * d * d * d + 221 * k * d * d + 95 * k * d + 17 * k + d * d * d * d * d * d * d + 9 * d * d * d * d * d * d + 33 * d * d * d * d * d + 65 * d * d * d * d + 75 * d * d * d + 51 * d * d + 19 * d + 3 := by
  ring_nat

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
private theorem e5_expand (k d : Nat) :
    k * (2 * k + 2 * d + 3) * numP4 (k + d) k * (k + 1) * (2 * k + d + 3)
    = 304 * k * k * k * k * k * k * k * k + 1172 * k * k * k * k * k * k * k * d + 2252 * k * k * k * k * k * k * k + 1830 * k * k * k * k * k * k * d * d + 7334 * k * k * k * k * k * k * d + 7008 * k * k * k * k * k * k + 1488 * k * k * k * k * k * d * d * d + 9439 * k * k * k * k * k * d * d + 18778 * k * k * k * k * k * d + 11859 * k * k * k * k * k + 670 * k * k * k * k * d * d * d * d + 6105 * k * k * k * k * d * d * d + 19192 * k * k * k * k * d * d + 25177 * k * k * k * k * d + 11772 * k * k * k * k + 160 * k * k * k * d * d * d * d * d + 2060 * k * k * k * d * d * d * d + 9302 * k * k * k * d * d * d + 19247 * k * k * k * d * d + 18648 * k * k * k * d + 6851 * k * k * k + 16 * k * k * d * d * d * d * d * d + 328 * k * k * d * d * d * d * d + 2102 * k * k * d * d * d * d + 6245 * k * k * d * d * d + 9528 * k * k * d * d + 7239 * k * k * d + 2166 * k * k + 16 * k * d * d * d * d * d * d + 168 * k * d * d * d * d * d + 712 * k * d * d * d * d + 1560 * k * d * d * d + 1864 * k * d * d + 1152 * k * d + 288 * k := by
  unfold numP4
  ring_nat

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
private theorem e6_expand (k d : Nat) :
    (2 * k + 2 * d + 3) * numP4 (k + d) (k + 1) * (d + 1) * ((2 * k + d + 1) * (2 * k + d + 1))
    = 608 * k * k * k * k * k * k * k * d + 608 * k * k * k * k * k * k * k + 2648 * k * k * k * k * k * k * d * d + 7240 * k * k * k * k * k * k * d + 4592 * k * k * k * k * k * k + 4832 * k * k * k * k * k * d * d * d + 21812 * k * k * k * k * k * d * d + 31484 * k * k * k * k * k * d + 14504 * k * k * k * k * k + 4806 * k * k * k * k * d * d * d * d + 30438 * k * k * k * k * d * d * d + 69846 * k * k * k * k * d * d + 68954 * k * k * k * k * d + 24740 * k * k * k * k + 2828 * k * k * k * d * d * d * d * d + 23119 * k * k * k * d * d * d * d + 73225 * k * k * k * d * d * d + 112545 * k * k * k * d * d + 84123 * k * k * k * d + 24512 * k * k * k + 990 * k * k * d * d * d * d * d * d + 9911 * k * k * d * d * d * d * d + 40138 * k * k * d * d * d * d + 84212 * k * k * d * d * d + 96712 * k * k * d * d + 57765 * k * k * d + 14048 * k * k + 192 * k * d * d * d * d * d * d * d + 2266 * k * d * d * d * d * d * d + 11173 * k * d * d * d * d * d + 29763 * k * d * d * d * d + 46287 * k * d * d * d + 42095 * k * d * d + 20768 * k * d + 4296 * k + 16 * d * d * d * d * d * d * d * d + 216 * d * d * d * d * d * d * d + 1252 * d * d * d * d * d * d + 4042 * d * d * d * d * d + 7938 * d * d * d * d + 9718 * d * d * d + 7254 * d * d + 3024 * d + 540 := by
  unfold numP4
  ring_nat

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
private theorem sum_left (k d : Nat) :
    (272 * k * k * k * k * k * k * k * k + 1496 * k * k * k * k * k * k * k * d + 2448 * k * k * k * k * k * k * k + 3468 * k * k * k * k * k * k * d * d + 11628 * k * k * k * k * k * k * d + 9464 * k * k * k * k * k * k + 4386 * k * k * k * k * k * d * d * d + 22780 * k * k * k * k * k * d * d + 37986 * k * k * k * k * k * d + 20472 * k * k * k * k * k + 3264 * k * k * k * k * d * d * d * d + 23647 * k * k * k * k * d * d * d + 61087 * k * k * k * k * d * d + 67425 * k * k * k * k * d + 27017 * k * k * k * k + 1428 * k * k * k * d * d * d * d * d + 13855 * k * k * k * d * d * d * d + 49958 * k * k * k * d * d * d + 85392 * k * k * k * d * d + 70018 * k * k * k * d + 22197 * k * k * k + 340 * k * k * d * d * d * d * d * d + 4471 * k * k * d * d * d * d * d + 21636 * k * k * d * d * d * d + 51606 * k * k * d * d * d + 65454 * k * k * d * d + 42399 * k * k * d + 11046 * k * k + 34 * k * d * d * d * d * d * d * d + 697 * k * d * d * d * d * d * d + 4600 * k * d * d * d * d * d + 14724 * k * d * d * d * d + 26015 * k * d * d * d + 26010 * k * d * d + 13815 * k * d + 3033 * k + 34 * d * d * d * d * d * d * d + 357 * d * d * d * d * d * d + 1557 * d * d * d * d * d + 3679 * d * d * d * d + 5106 * d * d * d + 4173 * d * d + 1863 * d + 351)
    + (32 * k * k * k * k * k * k * k * k + 288 * k * k * k * k * k * k * k * d + 416 * k * k * k * k * k * k * k + 1032 * k * k * k * k * k * k * d * d + 3008 * k * k * k * k * k * k * d + 2176 * k * k * k * k * k * k + 1984 * k * k * k * k * k * d * d * d + 8704 * k * k * k * k * k * d * d + 12624 * k * k * k * k * k * d + 6056 * k * k * k * k * k + 2272 * k * k * k * k * d * d * d * d + 13292 * k * k * k * k * d * d * d + 28902 * k * k * k * k * d * d + 27688 * k * k * k * k * d + 9862 * k * k * k * k + 1600 * k * k * k * d * d * d * d * d + 11676 * k * k * k * d * d * d * d + 33762 * k * k * k * d * d * d + 48356 * k * k * k * d * d + 34306 * k * k * k * d + 9644 * k * k * k + 680 * k * k * d * d * d * d * d * d + 5932 * k * k * d * d * d * d * d + 21350 * k * k * d * d * d * d + 40578 * k * k * d * d * d + 42952 * k * k * d * d + 24006 * k * k * d + 5534 * k * k + 160 * k * d * d * d * d * d * d * d + 1620 * k * d * d * d * d * d * d + 6958 * k * d * d * d * d * d + 16432 * k * d * d * d * d + 23042 * k * d * d * d + 19184 * k * d * d + 8780 * k * d + 1704 * k + 16 * d * d * d * d * d * d * d * d + 184 * d * d * d * d * d * d * d + 916 * d * d * d * d * d * d + 2578 * d * d * d * d * d + 4486 * d * d * d * d + 4942 * d * d * d + 3366 * d * d + 1296 * d + 216)
    = 304 * k * k * k * k * k * k * k * k + 1784 * k * k * k * k * k * k * k * d + 2864 * k * k * k * k * k * k * k + 4500 * k * k * k * k * k * k * d * d + 14636 * k * k * k * k * k * k * d + 11640 * k * k * k * k * k * k + 6370 * k * k * k * k * k * d * d * d + 31484 * k * k * k * k * k * d * d + 50610 * k * k * k * k * k * d + 26528 * k * k * k * k * k + 5536 * k * k * k * k * d * d * d * d + 36939 * k * k * k * k * d * d * d + 89989 * k * k * k * k * d * d + 95113 * k * k * k * k * d + 36879 * k * k * k * k + 3028 * k * k * k * d * d * d * d * d + 25531 * k * k * k * d * d * d * d + 83720 * k * k * k * d * d * d + 133748 * k * k * k * d * d + 104324 * k * k * k * d + 31841 * k * k * k + 1020 * k * k * d * d * d * d * d * d + 10403 * k * k * d * d * d * d * d + 42986 * k * k * d * d * d * d + 92184 * k * k * d * d * d + 108406 * k * k * d * d + 66405 * k * k * d + 16580 * k * k + 194 * k * d * d * d * d * d * d * d + 2317 * k * d * d * d * d * d * d + 11558 * k * d * d * d * d * d + 31156 * k * d * d * d * d + 49057 * k * d * d * d + 45194 * k * d * d + 22595 * k * d + 4737 * k + 16 * d * d * d * d * d * d * d * d + 218 * d * d * d * d * d * d * d + 1273 * d * d * d * d * d * d + 4135 * d * d * d * d * d + 8165 * d * d * d * d + 10048 * d * d * d + 7539 * d * d + 3159 * d + 567 := by
  ring_nat

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
private theorem sum_r34 (k d : Nat) :
    (4 * k * k * k * k * k * k * k * d + 4 * k * k * k * k * k * k * k + 20 * k * k * k * k * k * k * d * d + 58 * k * k * k * k * k * k * d + 38 * k * k * k * k * k * k + 41 * k * k * k * k * k * d * d * d + 202 * k * k * k * k * k * d * d + 313 * k * k * k * k * k * d + 152 * k * k * k * k * k + 44 * k * k * k * k * d * d * d * d + 315 * k * k * k * k * d * d * d + 802 * k * k * k * k * d * d + 863 * k * k * k * k * d + 332 * k * k * k * k + 26 * k * k * k * d * d * d * d * d + 254 * k * k * k * d * d * d * d + 933 * k * k * k * d * d * d + 1624 * k * k * k * d * d + 1347 * k * k * k * d + 428 * k * k * k + 8 * k * k * d * d * d * d * d * d + 106 * k * k * d * d * d * d * d + 534 * k * k * d * d * d * d + 1339 * k * k * d * d * d + 1784 * k * k * d * d + 1207 * k * k * d + 326 * k * k + k * d * d * d * d * d * d * d + 20 * k * d * d * d * d * d * d + 140 * k * d * d * d * d * d + 486 * k * d * d * d * d + 935 * k * d * d * d + 1014 * k * d * d + 580 * k * d + 136 * k + d * d * d * d * d * d * d + 12 * d * d * d * d * d * d + 60 * d * d * d * d * d + 162 * d * d * d * d + 255 * d * d * d + 234 * d * d + 116 * d + 24)
    + (2 * k * k * k * k * k * k * d * d + 4 * k * k * k * k * k * k * d + 2 * k * k * k * k * k * k + 9 * k * k * k * k * k * d * d * d + 31 * k * k * k * k * k * d * d + 35 * k * k * k * k * k * d + 13 * k * k * k * k * k + 16 * k * k * k * k * d * d * d * d + 81 * k * k * k * k * d * d * d + 149 * k * k * k * k * d * d + 119 * k * k * k * k * d + 35 * k * k * k * k + 14 * k * k * k * d * d * d * d * d + 98 * k * k * k * d * d * d * d + 260 * k * k * k * d * d * d + 332 * k * k * k * d * d + 206 * k * k * k * d + 50 * k * k * k + 6 * k * k * d * d * d * d * d * d + 58 * k * k * d * d * d * d * d + 212 * k * k * d * d * d * d + 388 * k * k * d * d * d + 382 * k * k * d * d + 194 * k * k * d + 40 * k * k + k * d * d * d * d * d * d * d + 15 * k * d * d * d * d * d * d + 77 * k * d * d * d * d * d + 195 * k * d * d * d * d + 275 * k * d * d * d + 221 * k * d * d + 95 * k * d + 17 * k + d * d * d * d * d * d * d + 9 * d * d * d * d * d * d + 33 * d * d * d * d * d + 65 * d * d * d * d + 75 * d * d * d + 51 * d * d + 19 * d + 3)
    = 4 * k * k * k * k * k * k * k * d + 4 * k * k * k * k * k * k * k + 22 * k * k * k * k * k * k * d * d + 62 * k * k * k * k * k * k * d + 40 * k * k * k * k * k * k + 50 * k * k * k * k * k * d * d * d + 233 * k * k * k * k * k * d * d + 348 * k * k * k * k * k * d + 165 * k * k * k * k * k + 60 * k * k * k * k * d * d * d * d + 396 * k * k * k * k * d * d * d + 951 * k * k * k * k * d * d + 982 * k * k * k * k * d + 367 * k * k * k * k + 40 * k * k * k * d * d * d * d * d + 352 * k * k * k * d * d * d * d + 1193 * k * k * k * d * d * d + 1956 * k * k * k * d * d + 1553 * k * k * k * d + 478 * k * k * k + 14 * k * k * d * d * d * d * d * d + 164 * k * k * d * d * d * d * d + 746 * k * k * d * d * d * d + 1727 * k * k * d * d * d + 2166 * k * k * d * d + 1401 * k * k * d + 366 * k * k + 2 * k * d * d * d * d * d * d * d + 35 * k * d * d * d * d * d * d + 217 * k * d * d * d * d * d + 681 * k * d * d * d * d + 1210 * k * d * d * d + 1235 * k * d * d + 675 * k * d + 153 * k + 2 * d * d * d * d * d * d * d + 21 * d * d * d * d * d * d + 93 * d * d * d * d * d + 227 * d * d * d * d + 330 * d * d * d + 285 * d * d + 135 * d + 27 := by
  ring_nat

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
private theorem sum_r345 (k d : Nat) :
    (4 * k * k * k * k * k * k * k * d + 4 * k * k * k * k * k * k * k + 22 * k * k * k * k * k * k * d * d + 62 * k * k * k * k * k * k * d + 40 * k * k * k * k * k * k + 50 * k * k * k * k * k * d * d * d + 233 * k * k * k * k * k * d * d + 348 * k * k * k * k * k * d + 165 * k * k * k * k * k + 60 * k * k * k * k * d * d * d * d + 396 * k * k * k * k * d * d * d + 951 * k * k * k * k * d * d + 982 * k * k * k * k * d + 367 * k * k * k * k + 40 * k * k * k * d * d * d * d * d + 352 * k * k * k * d * d * d * d + 1193 * k * k * k * d * d * d + 1956 * k * k * k * d * d + 1553 * k * k * k * d + 478 * k * k * k + 14 * k * k * d * d * d * d * d * d + 164 * k * k * d * d * d * d * d + 746 * k * k * d * d * d * d + 1727 * k * k * d * d * d + 2166 * k * k * d * d + 1401 * k * k * d + 366 * k * k + 2 * k * d * d * d * d * d * d * d + 35 * k * d * d * d * d * d * d + 217 * k * d * d * d * d * d + 681 * k * d * d * d * d + 1210 * k * d * d * d + 1235 * k * d * d + 675 * k * d + 153 * k + 2 * d * d * d * d * d * d * d + 21 * d * d * d * d * d * d + 93 * d * d * d * d * d + 227 * d * d * d * d + 330 * d * d * d + 285 * d * d + 135 * d + 27)
    + (304 * k * k * k * k * k * k * k * k + 1172 * k * k * k * k * k * k * k * d + 2252 * k * k * k * k * k * k * k + 1830 * k * k * k * k * k * k * d * d + 7334 * k * k * k * k * k * k * d + 7008 * k * k * k * k * k * k + 1488 * k * k * k * k * k * d * d * d + 9439 * k * k * k * k * k * d * d + 18778 * k * k * k * k * k * d + 11859 * k * k * k * k * k + 670 * k * k * k * k * d * d * d * d + 6105 * k * k * k * k * d * d * d + 19192 * k * k * k * k * d * d + 25177 * k * k * k * k * d + 11772 * k * k * k * k + 160 * k * k * k * d * d * d * d * d + 2060 * k * k * k * d * d * d * d + 9302 * k * k * k * d * d * d + 19247 * k * k * k * d * d + 18648 * k * k * k * d + 6851 * k * k * k + 16 * k * k * d * d * d * d * d * d + 328 * k * k * d * d * d * d * d + 2102 * k * k * d * d * d * d + 6245 * k * k * d * d * d + 9528 * k * k * d * d + 7239 * k * k * d + 2166 * k * k + 16 * k * d * d * d * d * d * d + 168 * k * d * d * d * d * d + 712 * k * d * d * d * d + 1560 * k * d * d * d + 1864 * k * d * d + 1152 * k * d + 288 * k)
    = 304 * k * k * k * k * k * k * k * k + 1176 * k * k * k * k * k * k * k * d + 2256 * k * k * k * k * k * k * k + 1852 * k * k * k * k * k * k * d * d + 7396 * k * k * k * k * k * k * d + 7048 * k * k * k * k * k * k + 1538 * k * k * k * k * k * d * d * d + 9672 * k * k * k * k * k * d * d + 19126 * k * k * k * k * k * d + 12024 * k * k * k * k * k + 730 * k * k * k * k * d * d * d * d + 6501 * k * k * k * k * d * d * d + 20143 * k * k * k * k * d * d + 26159 * k * k * k * k * d + 12139 * k * k * k * k + 200 * k * k * k * d * d * d * d * d + 2412 * k * k * k * d * d * d * d + 10495 * k * k * k * d * d * d + 21203 * k * k * k * d * d + 20201 * k * k * k * d + 7329 * k * k * k + 30 * k * k * d * d * d * d * d * d + 492 * k * k * d * d * d * d * d + 2848 * k * k * d * d * d * d + 7972 * k * k * d * d * d + 11694 * k * k * d * d + 8640 * k * k * d + 2532 * k * k + 2 * k * d * d * d * d * d * d * d + 51 * k * d * d * d * d * d * d + 385 * k * d * d * d * d * d + 1393 * k * d * d * d * d + 2770 * k * d * d * d + 3099 * k * d * d + 1827 * k * d + 441 * k + 2 * d * d * d * d * d * d * d + 21 * d * d * d * d * d * d + 93 * d * d * d * d * d + 227 * d * d * d * d + 330 * d * d * d + 285 * d * d + 135 * d + 27 := by
  ring_nat

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
private theorem sum_right (k d : Nat) :
    (304 * k * k * k * k * k * k * k * k + 1176 * k * k * k * k * k * k * k * d + 2256 * k * k * k * k * k * k * k + 1852 * k * k * k * k * k * k * d * d + 7396 * k * k * k * k * k * k * d + 7048 * k * k * k * k * k * k + 1538 * k * k * k * k * k * d * d * d + 9672 * k * k * k * k * k * d * d + 19126 * k * k * k * k * k * d + 12024 * k * k * k * k * k + 730 * k * k * k * k * d * d * d * d + 6501 * k * k * k * k * d * d * d + 20143 * k * k * k * k * d * d + 26159 * k * k * k * k * d + 12139 * k * k * k * k + 200 * k * k * k * d * d * d * d * d + 2412 * k * k * k * d * d * d * d + 10495 * k * k * k * d * d * d + 21203 * k * k * k * d * d + 20201 * k * k * k * d + 7329 * k * k * k + 30 * k * k * d * d * d * d * d * d + 492 * k * k * d * d * d * d * d + 2848 * k * k * d * d * d * d + 7972 * k * k * d * d * d + 11694 * k * k * d * d + 8640 * k * k * d + 2532 * k * k + 2 * k * d * d * d * d * d * d * d + 51 * k * d * d * d * d * d * d + 385 * k * d * d * d * d * d + 1393 * k * d * d * d * d + 2770 * k * d * d * d + 3099 * k * d * d + 1827 * k * d + 441 * k + 2 * d * d * d * d * d * d * d + 21 * d * d * d * d * d * d + 93 * d * d * d * d * d + 227 * d * d * d * d + 330 * d * d * d + 285 * d * d + 135 * d + 27)
    + (608 * k * k * k * k * k * k * k * d + 608 * k * k * k * k * k * k * k + 2648 * k * k * k * k * k * k * d * d + 7240 * k * k * k * k * k * k * d + 4592 * k * k * k * k * k * k + 4832 * k * k * k * k * k * d * d * d + 21812 * k * k * k * k * k * d * d + 31484 * k * k * k * k * k * d + 14504 * k * k * k * k * k + 4806 * k * k * k * k * d * d * d * d + 30438 * k * k * k * k * d * d * d + 69846 * k * k * k * k * d * d + 68954 * k * k * k * k * d + 24740 * k * k * k * k + 2828 * k * k * k * d * d * d * d * d + 23119 * k * k * k * d * d * d * d + 73225 * k * k * k * d * d * d + 112545 * k * k * k * d * d + 84123 * k * k * k * d + 24512 * k * k * k + 990 * k * k * d * d * d * d * d * d + 9911 * k * k * d * d * d * d * d + 40138 * k * k * d * d * d * d + 84212 * k * k * d * d * d + 96712 * k * k * d * d + 57765 * k * k * d + 14048 * k * k + 192 * k * d * d * d * d * d * d * d + 2266 * k * d * d * d * d * d * d + 11173 * k * d * d * d * d * d + 29763 * k * d * d * d * d + 46287 * k * d * d * d + 42095 * k * d * d + 20768 * k * d + 4296 * k + 16 * d * d * d * d * d * d * d * d + 216 * d * d * d * d * d * d * d + 1252 * d * d * d * d * d * d + 4042 * d * d * d * d * d + 7938 * d * d * d * d + 9718 * d * d * d + 7254 * d * d + 3024 * d + 540)
    = 304 * k * k * k * k * k * k * k * k + 1784 * k * k * k * k * k * k * k * d + 2864 * k * k * k * k * k * k * k + 4500 * k * k * k * k * k * k * d * d + 14636 * k * k * k * k * k * k * d + 11640 * k * k * k * k * k * k + 6370 * k * k * k * k * k * d * d * d + 31484 * k * k * k * k * k * d * d + 50610 * k * k * k * k * k * d + 26528 * k * k * k * k * k + 5536 * k * k * k * k * d * d * d * d + 36939 * k * k * k * k * d * d * d + 89989 * k * k * k * k * d * d + 95113 * k * k * k * k * d + 36879 * k * k * k * k + 3028 * k * k * k * d * d * d * d * d + 25531 * k * k * k * d * d * d * d + 83720 * k * k * k * d * d * d + 133748 * k * k * k * d * d + 104324 * k * k * k * d + 31841 * k * k * k + 1020 * k * k * d * d * d * d * d * d + 10403 * k * k * d * d * d * d * d + 42986 * k * k * d * d * d * d + 92184 * k * k * d * d * d + 108406 * k * k * d * d + 66405 * k * k * d + 16580 * k * k + 194 * k * d * d * d * d * d * d * d + 2317 * k * d * d * d * d * d * d + 11558 * k * d * d * d * d * d + 31156 * k * d * d * d * d + 49057 * k * d * d * d + 45194 * k * d * d + 22595 * k * d + 4737 * k + 16 * d * d * d * d * d * d * d * d + 218 * d * d * d * d * d * d * d + 1273 * d * d * d * d * d * d + 4135 * d * d * d * d * d + 8165 * d * d * d * d + 10048 * d * d * d + 7539 * d * d + 3159 * d + 567 := by
  ring_nat

set_option maxRecDepth 40000 in
/-- ★★★ **R-NUM: the reduced numerator-certificate identity** — the cleared per-`k`
    telescoping core `u + ρ·φ(k+1) + φ = 0` of the ζ(3) numerator certificate, in the
    additive `j = k+d` form.  LHS = the two positive `u`-pieces (the `aperyLead`
    piece and the `Ĝ`-shifted piece, `Q(j,k+1) = 4d²+8dk+12d+2k²+11k+9`); RHS = the
    two negative `u`-pieces plus the two `φ`-terms (`numP4` at `k` and `k+1`).
    Proof: six machine-generated per-term expansions + a pairwise collection chain
    (the single-`ring_nat` form exceeds the reflective normalizer's budget).
    ∅-axiom; the analogue of `AperyRecurrence.reduced_wz_identity` one language up. -/
theorem rnum_reduced (k d : Nat) :
    (34 * ((k + d) * (k + d) * (k + d)) + 153 * ((k + d) * (k + d)) + 231 * (k + d) + 117) * ((k + d + 1) * (k + 1) * ((2 * k + d + 1) * (2 * k + d + 1)) * (2 * k + d + 3))
    + 2 * (2 * k + 2 * d + 3) * (4 * (d * d) + 8 * d * k + 12 * d + 2 * (k * k) + 11 * k + 9) * ((k + d + 1) * ((k + d + 2) * (k + d + 2)) * ((2 * k + d + 1) * (2 * k + d + 1)))
    = ((k + d + 1) * (k + d + 1)) * ((k + d + 2) * (k + d + 2)) * (k + 1) * (d + 1) * (2 * k + d + 2) * (2 * k + d + 3)
    + ((k + d + 1) * (k + d + 1) * (k + d + 1) * (k + d + 1)) * (k + 1) * ((d + 1) * (d + 1)) * (2 * k + d + 3)
    + k * (2 * k + 2 * d + 3) * numP4 (k + d) k * (k + 1) * (2 * k + d + 3)
    + (2 * k + 2 * d + 3) * numP4 (k + d) (k + 1) * (d + 1) * ((2 * k + d + 1) * (2 * k + d + 1)) := by
  rw [e1_expand, e2_expand, e3_expand, e4_expand, e5_expand, e6_expand,
      sum_r34, sum_r345, sum_right]
  exact sum_left k d

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
/-- ★★ **R-BND: the reduced boundary identity** — the `k = j` edge where the
    certificate's `(j−k+1)`-pole meets the vanishing binomial:
    `φ(j,j) + u(j,j) = T1(j)`, `T1 = 2(2j+1)(19j²+58j+45)/((j+1)(j+2)²)` (the closed
    form of `U(j,j+1)·(−1)^{j+1}/√b(j,j)`), cleared over
    `(j+1)(j+2)²(2j+1)(2j+2)(2j+3)`; `Q(j,j+1) = 2j²+11j+9`.  ∅-axiom. -/
theorem rbnd_reduced (j : Nat) :
    (34 * (j * j * j) + 153 * (j * j) + 231 * j + 117) * ((j + 1) * ((2 * j + 1) * (2 * j + 1)) * (2 * j + 3))
    + 2 * (2 * j + 3) * (2 * (j * j) + 11 * j + 9) * ((j + 2) * (j + 2)) * ((2 * j + 1) * (2 * j + 1))
    = ((j + 1) * (j + 1)) * ((j + 2) * (j + 2)) * (2 * j + 2) * (2 * j + 3)
    + ((j + 1) * (j + 1) * (j + 1) * (j + 1)) * (2 * j + 3)
    + j * ((2 * j + 3) * (2 * j + 3)) * numP4 j j
    + 2 * ((2 * j + 1) * (2 * j + 1)) * (19 * (j * j) + 58 * j + 45) * (2 * j + 2) * (2 * j + 3) := by
  unfold numP4
  ring_nat

end E213.Lib.Math.NumberTheory.AperyNumeratorWZ
