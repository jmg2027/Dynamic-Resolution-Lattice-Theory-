# G164 — the HolonomicReal generator's constructive boundary is the algebraic/transcendental line

**Date**: 2026-06-01. **Status**: finding (∅-axiom evidence both sides). Real-number
thread; companion to `Real213/HolonomicReal.lean` + `Real213/ExpLog/EulerCertifiedBracket.lean`.

## The question

`HolonomicReal` carries its convergence modulus as a *constructed field*.  The
autonomous case (φ) closed with a **total** modulus `N(m,k) = 2k`.  Does the general
generator `Holonomic → CertifiedModulus` — derive the modulus from arbitrary
recurrence data — extend to the transcendental rungs (e, coefficient `n+1`; π, deg 4)?

## The finding: it stops exactly at the algebraic/transcendental line

**Algebraic (autonomous, det-1) side — TOTAL modulus, constructive.**
φ's convergent cut equals its closed-form cut past `2k` (`PhiCauchyLimit`,
`cs_eq_phiCut`), so `N(m,k)=2k` is exact and total.  Generally: a det-1 order-2
(Pell) recurrence has a *closed decidable cut* the convergents hit exactly — the
modulus is then a finite, total function.  This is the `depth ≤ 1` floor
(`DepthFloorDetOne`: the depth-0 floor IS the det-1 P-orbit invariant).

**Transcendental side — modulus only on the DECIDED region.**
e has no closed-form decidable cut.  `MonotonicBounded` proves monotone-bounded ⟹
Cauchy *only under LEM*: the total `∀(m,k) ∃N` closure is the case split
"`orderProj m k` true for all layers" vs "false at some layer" — which is exactly
**deciding `e` against `m/k`**.  For transcendental `e` that is a *constructive
irrationality measure* (a computable lower bound on `|e − m/k|`), unavailable ∅-axiom.
So:

  - **No total ∅-axiom modulus for e** (the LEM wall).
  - **But** wherever a strict rational bracket is *proven*, the witness gives the
    modulus constructively (`orderCauchy_from_{true_forever,false_witness}`).
    `EulerCertifiedBracket`: e is certified-Cauchy on `(8/3, 3)` —
    `euler_certified_at_3` (modulus 0, true forever) + `euler_certified_at_8_3`
    (modulus 4, false-witness).  The generator certifies e on every `(m,k)` the
    bounds decide; only the undecided boundary (rationals approaching e) is open.

## Why this is the right reading (not a gap to paper over)

The wall is **structural**, mirroring ZFC's power-set commitment: a *total* cut
modulus for a transcendental smuggles a decision (`e =?= m/k` with an explicit rate)
that the falsifiability contract refuses.  The divide is the same one the depth arc
draws: algebraic = depth 0/1 = det 1 = autonomous (constructive modulus); structured
transcendental = depth ≥ 3 (e 3, π 6) = the holonomic generator's *analytic* core,
gated per-real on an irrationality measure.

## Status of the generator

  - **Autonomous class** (algebraic, det-1): constructive total modulus — DONE
    (φ instance `phiHolonomicReal`; generalises by the closed-cut/Pell-exactness
    pattern).
  - **Transcendental class** (e, π): constructive on the decided region (brackets);
    the **total** modulus needs a per-real constructive irrationality measure — the
    genuine open analytic core, not a packaging gap.

So `Holonomic → CertifiedModulus` is total-constructive **exactly on the autonomous
(algebraic) class**; beyond it, the certificate is partial (decided region) until an
irrationality bound is supplied.  Future real-number target, if pursued: a
constructive irrationality measure for e (lower bound `|e − m/k| > f(k)`) — that, and
only that, lifts e's bracket certificate to a total modulus.
