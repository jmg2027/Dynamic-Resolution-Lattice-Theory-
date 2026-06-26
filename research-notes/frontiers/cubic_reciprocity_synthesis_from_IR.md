# The cubic-reciprocity cross-modulus synthesis — extracted proof (Ireland–Rosen ch. 9 / Xu REU 2021)

Source: Nancy Xu, "Reciprocity Laws", UChicago REU 2021 §4 (follows Ireland–Rosen ch. 9).
Found via deep research (no existing proof-assistant formalization of cubic reciprocity exists —
Mathlib has Jacobi/Gauss-sum infrastructure + quadratic reciprocity only).

## Setup
`χ_π = (·/π)₃` cubic residue character mod a complex prime `π` (`Nπ = p ≡ 1 mod 3`), a character on
`𝔽_p ≅ ℤ[ω]/(π)`.  `(α/π)₃ = ζ₃^m` where `α^{(Nπ−1)/3} ≡ ζ₃^m (mod π)`.

## Gauss-sum engine (Props 4.7–4.9)
- `g(χ_π)³ = p·J(χ_π,χ_π)`  (Prop 4.7; uses `χ_π(−1)=1`).
- `J(χ_π,χ_π) = π`  for `π` **primary** (Prop 4.8).
- **`g(χ_π)³ = p·π`**  (Cor 4.9).  [my `gauss_cube` / `jacobi_primary` give this]

## The law (Thm 4.6)
For primary primes `π₁, π₂` with `Nπ₁ ≠ Nπ₂`:  `(π₁/π₂)₃ = (π₂/π₁)₃`.

## Case 3 — BOTH π₁, π₂ complex (split).  THE cross-modulus synthesis.
Preliminary identities (Case 1):
- (1) `conj(χ_π(α)) = χ_π(α)² = χ_π(α²)`.
- (2) `χ_π(ᾱ) = conj(χ_π(α))`  (since `Nπ̄ = Nπ`).
- (3) `χ_p(n) = 1` for a rational integer `n` coprime to a **rational** prime `p`.

**Two symmetric computations** (each = Case-2-style: raise `g(χ_{πᵢ})³ = pᵢπᵢ` to `(p_j−1)/3`, reduce
mod `π_j`):
- mod `π₂`:  **`χ_{π₁}(p₂²) = χ_{π₂}(p₁·π₁)`**     (relation A)
- mod `π₁`:  **`χ_{π₂}(p₁²) = χ_{π₁}(p₂·π₂)`**     (relation B)

**Combination** (using (2): `χ_{π₁}(p₂²) = χ_{π₁}(p̄₂)`-type collapse + multiplicativity):
```
χ_{π₁}(π₂)·χ_{π₂}(p₁π₁) = χ_{π₁}(π₂)·χ_{π₁}(p₂²)    [A]
                        = χ_{π₁}(π₂)·χ_{π₁}(p₂)
                        = χ_{π₁}(π₂·p₂) = χ_{π₁}(p₂·π₂)
                        = χ_{π₂}(p₁²)                [B]
                        = χ_{π₂}(π₁)·χ_{π₂}(p₁π₁)
⟹  χ_{π₁}(π₂) = χ_{π₂}(π₁)    (cancel the unit χ_{π₂}(p₁π₁)).
```
(NB: the PDF OCR lost some conjugate bars; reconcile the exact `χ(p²)↔χ(p̄)` step against a clean
Ireland–Rosen copy before formalizing.)

## What this means for the Lean formalization (the unblock)
My machinery is **generic in `(d, p, m, x)`** (the first prime + its cube root).  So:
- **Relation A** ≈ my `EisensteinSplitResidueSymbol.split_conj_residue_relation`
  (`J̄^{s+1} ≡ χ̄(pr)·J^{s+1} mod π'`, `J = π₁`, `pr = p₂`, `s+1 = (p₂−1)/3`).
- **Relation B** = the SAME theorem **instantiated with the primes swapped**
  (`d := π'`, `p := pr`, second prime `:= d`) — needs the cube root `ω ≡ x' (mod π')` (`hπ'ω`, already a
  hypothesis) and `ω ≡ x (mod d)` (`hω`, the original).  Both hypotheses are symmetric & available.
- **Combination**: a short ℤ[ω] algebra step (multiplicativity `chiOmega_mul` / `char_mul`, the conjugate
  laws Case 1(1)(2), and cancelling the unit `χ_{π₂}(p₁π₁)` — cancellation in the domain `ℤ[ω]/(π')`,
  which I have as `modEq_cancel_right`).

So the synthesis is **bounded additional work**, not a new large theory: build the second character's
Gauss-sum computation by swapped instantiation, then the combination.  Earlier pessimism was wrong —
the block was not knowing relation B is the swapped relation A.

## Caveat (falsifiability)
The exact symbol bookkeeping (which conjugates, which exponents `pᵢ` vs `pᵢ²`) must be pinned against a
clean Ireland–Rosen copy — the REU PDF's lost bars make the literal equations unreliable.  Formalize the
STRUCTURE (two swapped relations + cancel), verifying each congruence in Lean (which forces the bars to be
right).
