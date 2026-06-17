# Frontier: Gauss-Wilson ±1 value classification

`NumberTheory/WilsonGeneralization` (29 PURE) closed the **inverse-pairing core**:
`units_prod_eq_selfinv_prod` (∏ units of ℤ/n = ∏ self-inverse units, via the
involution `u ↦ unitInv n u`), `unitInv_eq_self_iff` (self-inverse ⟺ u²≡1), prime
recovery, and Gauss +1/−1 smokes.

**Open (the value classification):** `∏(units of ℤ/n) ≡ −1 (mod n) ⟺ n ∈
{1,2,4,pᵏ,2pᵏ}` (i.e. ⟺ (ℤ/n)^× is cyclic, with a unique element of order 2).
Remaining work: characterize the self-inverse units (solutions of x²≡1 mod n) by
CRT/the prime-power structure — for n=2pᵏ or pᵏ there are exactly two (1 and −1),
product −1; for n with ≥2 odd prime factors or 8∣n there are ≥4, paired off to
product +1. Reuses `units_prod_eq_selfinv_prod` + a count/structure of √1 mod n.
QR/CRT-structure heavy; do interactively.
