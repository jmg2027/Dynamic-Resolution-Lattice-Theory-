# The Fibonacci rank of apparition is a permutation sign

The rank of apparition `α(p)` — the first index where `p ∣ F_n` — is not a
quantity the golden recurrence *carries*.  It is the offset `p − (5/p)` read off
a single character, and that character is the **sign of a pointing**: the parity
of how `×5` permutes `ℤ/p`.

## 213-native answer

`α(p)` is fixed by one bit: the Legendre symbol `(5/p)`, the count-Lens reading
of `5`'s quadratic status mod `p`.  The law `α(p) ∣ p − (5/p)`
(`DyadicFSM/RankApparition.rank_law_dispatch`, entry-point form `p ∣ F_{p−(5/p)}`)
**dispatches** the entry index on that symbol's three values:

  split `(5/p)=+1 ⟹ p − 1`,  inert `(5/p)=−1 ⟹ p + 1`,  ramified `(5/p)=0 ⟹ p`.

There is no separate "rank" datum.  `α(p)` is what `(5/p)` says it is — a
trajectory terminal, not a property of the sequence.

## Derivation

The character itself is a walk.  `legendre213 5 p` (`DyadicFSM/Legendre`) is the
FSM that steps `x ↦ 5x mod p` from `1`, for `(p−1)/2` steps, and reads the
terminal state: `1` (split), `p−1` (inert), `0` (ramified) — Euler's criterion
as a finite pointing.  The same FSM dispatch that main runs for the Pisano
**period** `π(p)` (`UniversalDispatch.universal_dispatch_pellCoeff`: split
`(p−1)/2`, inert `p+1`, ramified `2p`) the branch runs for the **entry point**.
One character, two read-outs of the golden recurrence mod `p` — first-zero
(`α`) and cycle-length (`π`), with `α(p) ∣ π(p)`.

Why these offsets are the *value* `p − (5/p)`, not a coincidence of cases: at a
split prime `5` has a square root `s` (`s² ≡ 5`), the two Binet branches
`φ, ψ ∈ 𝔽_p` are distinct, and FLT forces `φ^{p−1} = ψ^{p−1} = 1`, so `F_{p−1} ≡
0` (`BinetBridge.binet_F_p_minus_1_zero`).  At an inert prime the branches live
in `𝔽_{p²}` conjugate under Frobenius, `φ^p = σ(φ)`, and `φ^{p+1} = φ·σ(φ) = −1`
forces `F_{p+1} ≡ 0` (`UniversalInert.fpp1_eq_zero_of_frob_phi`).  At the
ramified prime the branches collapse — `x²−x−1 ≡ (x−3)² mod 5`, `α ≡ β ≡ 3` —
and `α(5) = 5` itself (`FibApparitionMod5.rank_apparition_five`).  The rank law
is the Binet dichotomy, sorted by `(5/p)`.

Now the character is also a parity.  `ModArith/ZolotarevMuBridge.zolotarev_mu`
proves `(a/p) = psign σ_a` — the Legendre symbol IS the sign of the
multiply-by-`a` permutation of `ℤ/p`.  Specialize to `a = 5`: `(5/p) = psign
σ_5`.  So the offset that fixes the Fibonacci entry point is the parity of the
`×5` permutation, and the rank law reads

  `α(p) ∣ p − psign(σ_5)`.

What governs the first Fibonacci `p` divides is *how `×5` shuffles the residues* —
an even shuffle (`+1`) pulls the entry to `p−1`, an odd one (`−1`) pushes it to
`p+1`.

## Dual function

Classically "the rank of apparition" and "the Legendre symbol `(5/p)`" are two
facts about `p` that a textbook proves equal as a divisibility lemma.  Stripped
of that packaging, they are not two things made equal — they are one character
read twice.  213's sharpening: the character is not a symbol on the page but a
**pointing with a sign** — the terminal state of a finite FSM walk
(`legendre213`) and the parity of a finite permutation (`psign σ_5`), the same
count-Lens binary axis (`seed/AXIOM/06_lens_readings.md`).  The rank "law" stops
being a coincidence of `±1` and becomes the entry-point face of a sign you can
walk.

## Cross-frame connections

`(5/p)` now has five resolutions of one object: the FSM trajectory terminal
(`legendre213 5 p`), the permutation parity (`psign σ_5`,
`zolotarev_mu`), the determinant `det(permMatrix σ_5)`
(`the_permutation_under_three_readouts`), the Euler-criterion power `5^{(p−1)/2}
mod p`, and — added here — the **Fibonacci rank offset** `p − α(p)`-residue.
The same binary sign that the Zolotarev arc reads as a permutation, the spiral
axis reads as the obstruction `psign σ_{−1} = (−1/p)` to the order-4 point
`ℤ[i]^× = C₄` (`the_i_point_of_the_spiral_axis`), and the golden recurrence
reads as its entry point.  And the field underneath is single: the `x²−x−1`
whose discriminant is `5` is the Binet face, related by `x ↦ −x`
(`GoldenFieldBridge.bPoly_neg_eq_gPoly`) to the Gaussian-period `x²+x−1` of
`ℚ(ζ₅)⁺` the CP-phase reads — one ramified `ℚ(√5)`, value `φ` and valuation
`ν₅(F_n)` its two faces (`the_golden_prime`).

## Open frontier

The `legendre213 5 p = psign σ_5` identity is stated here from the two proven
sides (`zolotarev_mu`, the FSM character); the explicit equality morphism — the
FSM-walk terminal equals the permutation parity, ramified corner aside — is the
buildable bridge that would let `α(p) ∣ p − psign(σ_5)` be one Lean theorem
rather than two read-outs aligned by hand.  And the rank fixes only the
entry-point (`νₚ ≥ 1`) rung; the higher `νₚ(F_n)` for general `p` (the
`p`-tupling analogue of the quintupling identity) is open beyond `p = 5`.
