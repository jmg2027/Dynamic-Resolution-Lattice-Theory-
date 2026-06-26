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

## STATUS UPDATE (Phase B2h–B2k, this session) — both halves built in μ₃-element form

The relaxation + relation B are **done and PURE**.  In Lean now (`J = π₁` primary, `J₂ = π₂` primary):

| brick | statement | file |
|---|---|---|
| relation A | `(π̄/π')₃ ≡ χ̄_π(pr)·(π/π')₃  (mod π')` | `split_conj_residue_relation` |
| relation B | `(π̄'/π)₃ ≡ χ̄_{π'}(p)·(π'/π)₃  (mod π=d)` | `split_conj_residue_relation_B` |
| (π/π')₃ ∈ μ₃ | `J^{m₂} mod π' ∈ {1,ω,ω²}` | `split_residue_symbol_exists` |
| (π'/π)₃ ∈ μ₃ | `J₂^{m} mod π ∈ {1,ω,ω²}` | `split_residue_symbol_exists_B` |

where `(π/π')₃ := π^{m₂} mod π'` (`m₂=(pr−1)/3`), `(π'/π)₃ := π'^{m} mod π` (`m=(p−1)/3`), and
`χ_π = chiOmega p m x`, `χ_{π'} = chiOmega pr m₂ x₂` are the **rational** (𝔽-field) characters.

### CORRECTION to the source's "conjugate law" (the OCR-garbled identity)

The REU note's Case-1 identity `(2) χ_π(ᾱ) = conj(χ_π(α))` is **wrong as written** (it would force the
rational character of the norm `χ_π(N(π'))` to be `1` always, via multiplicativity — false).  The honest
identity is **`χ_{conj d}(conj α) = conj(χ_d(α))`** (character at the *conjugate modulus*, not conjugate
argument): `conj` is a ℤ[ω] ring hom, so `conj(α^m) = (conj α)^m`, and reducing the congruence `χ_d(α) =
α^m (mod d)` under `conj` gives a congruence **mod `conj d`**.  This is why `conj R` in relation A is
naturally a statement mod `π̄'`, not `π'` — `conj` does **not** descend to an automorphism of
`ℤ[ω]/(π')` (it maps `ℤ[ω]/(π') → ℤ[ω]/(π̄')`; `π̄' ≢ 0 mod π'`).  Note `pow (conj J) (s+1) mod π'` in
relation A is **not** `conj(R)` reduced — it is the *honest* residue symbol `(π̄/π')₃ = (conj π)^{m₂} mod
π'`, a computable μ₃ element.  So relation A reads `(π̄/π')₃ ≡ χ̄_π(pr)·(π/π')₃ (mod π')` with **both**
symbols genuine μ₃ elements mod `π'`.

### The remaining combination — exact bricks (each clean & provable; no source needed)

Let `a := (π/π')₃`, `b := (π̄/π')₃` (both μ₃ mod π'); `S := (π'/π)₃`, `S̄ := (π̄'/π)₃` (both μ₃ mod π).

1. **norm-multiplicativity mod π'** (mirror of `eisChar_norm_split`, but for `χ_{π'}` at the rational
   `p = N(π)`):  `χ_{π'}(p) ≡ a·b  (mod π')`  [`char_mul` + `N(π)=π·π̄` via `mul_conj_self`].  Symmetrically
   `χ_π(pr) ≡ S·S̄  (mod π)`.
2. **rational-character = literal μ₃**:  `χ_{π'}(p)` and `χ_π(pr)` are each `≡` a literal `{1,ω,ω²}`
   (`cubic_char_value` / `chiOmega_unit_value`).
3. **conjugate-modulus bridge** `χ_{conj d}(conj α) = conj(χ_d(α))` (above) — relates `b = (π̄/π')₃` and
   `S̄ = (π̄'/π)₃` to `a`, `S` via `π̄ = conj π`, `π̄' = conj π'`.  *This is the brick the source garbled.*
4. **μ₃-lift across moduli**: a congruence between two literal μ₃ elements mod a prime of norm `> 3` is an
   equality (`mu3_eq_of_modEq` for `ofInt`; needs the **Eisenstein-modulus** analog for `π'`/`π` — distinct
   μ₃ differ by an element of norm `3`, and `pr,p ∤ 3`).
5. **combine + cancel**: substitute (1)+(3) into A and B, pin everything to literals via (2)+(4), and the
   shared rational-character unit cancels (`modEq_cancel_right`), leaving `a = S`, i.e. `(π/π')₃ =
   (π'/π)₃`.

The structural risk (which conjugate, which exponent) is fully controlled by Lean: every congruence above
typechecks only if the bars are right.  Brick 3 (conjugate-modulus bridge) and brick 4 (Eisenstein μ₃-lift)
are the two genuinely-new lemmas; 1, 2, 5 are assembly from existing machinery.
