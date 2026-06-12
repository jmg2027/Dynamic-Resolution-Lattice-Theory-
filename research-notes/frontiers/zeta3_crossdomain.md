# Cross-domain: ζ(3) Apéry arithmetic ↔ main (weld / vp-log / certificate) — 2026-06-12 merge

Surfaced by merging main (weld bilinear Casoratian + Bessel-Lambert, the
`what_is_a_logarithm` = `vp` essay, `equality_is_a_certificate`, the number-tower)
into the ζ(3) branch (Apéry's recurrence CLOSED, denominator bridge, numerator
opened).

## 1. The Apéry Casoratian `6·(m!)⁶` is the "forced by two" alternating form

Main's `the_form_forced_by_two.md` + `weld_bilinear_casoratian`: a **rank-2**
holonomic solution space carries a *unique* alternating form, so every cross-
determinant of two solutions collapses to `det(coeff)·K_J` — the form is forced,
no exterior dialer chooses it (§5.1).  ζ(3) is exactly this on the *arithmetic*
side: the Apéry recurrence is order 2, so its Casoratian is forced — and
`Zeta3Cut.zeta3_cross_det` gives it in **closed form** `zeta3Num(m+1)zeta3Den(m) −
zeta3Num(m)zeta3Den(m+1) = 6·(m!)⁶`.  Same object as the weld's `K_J`
(numerator/denominator pair of one 2-D recurrence), here the *integer* Casoratian
of the two Apéry orbits.  The weld's `K_J` is the Bessel Wronskian; `6(m!)⁶` is its
ζ(3) avatar.  The "forced by two" essay's claim — rank 2 fixes the *shape* but not
the *size* — matches exactly: the shape (one Casoratian) is forced, the size
`6(m!)⁶` is the arithmetic content, just as the weld's det-floor `+1` is separate
from its bilinear shape.

## 2. The lcm race IS a logarithm bound — `vp` is its engine

Main's `what_is_a_logarithm.md`: the 213-native logarithm is **not** an analytic
import but `vp` (the prime-exponent valuation), `vp_mul` (×→+), `vp_pow` (^→·); "the
log" = the family of valuations, the algebraic place plus the archimedean `ln|·|`.
Brick 1's deliverable `lcm(1..n) ≤ √10ⁿ` (`lcmUpTo_le`) is precisely a **logarithm
bound in this sense**: `lcm(1..n)`'s structure is read entirely by `vp` —
`vₚ(lcm 1..N) = #{f≥1 : pᶠ≤N} = floorLog p N` (`vp_lcmUpTo`), the *archimedean* and
the *p-adic* logs meeting (the count `floorLog` is `⌊log_p N⌋`).  The race
`√10ⁿ < 3.236ⁿ` is the statement that `Σ_p floorLog_p(n)·log p ≈ n` (Chebyshev `ψ`),
i.e. the vp-as-log made quantitative.  So main's essay names the object (`vp`=log)
that Brick 1 computes with; the lcm race is the `vp`-log's growth law.  (Main's new
`VpMul`/`VpSeparation` are the same `vp`, now with `vp_pow`/`vp_separation` — a
dedup opportunity with `PrimeValuation.vp_mul` flagged.)

## 3. The certificate dichotomy — harmonic is the boundary of certifiability

Main's `equality_is_a_certificate.md`: an equality is paid for in structure — a
*checkable* certificate (exponent-vector, order-sandwich, CF) whose content is the
number's structure.  ζ(3) sharpens this into a **dichotomy with a named boundary**:
Apéry's recurrence for the *denominator* `B(n)=ΣC(n,k)²C(n+k,k)²` has a **clean WZ
certificate** `Ĝ(j,k)` (a fixed rational, found by interpolation, verified) — a
finite certificate of the recurrence.  The *numerator* (harmonic
`A=H₃·B+K`) satisfies the *same* recurrence but has **no clean certificate**
(`cert_A`, `cert_K`, even `cert_A−cert_B·c` all messy — checked `numcert2.py`).  The
boundary is exactly the harmonic content: a pure hypergeometric (proper)
summand is certifiable; adjoining `H₃(n)=Σ1/j³` (a transcendental valuation, the
*archimedean* log of №2) breaks certifiability — the recurrence still holds but
must be proven by explicit kernel telescoping, not a finite certificate.  This
locates "when is a holonomic recurrence WZ-certifiable" precisely: at the
hypergeometric/harmonic boundary — the same place №2's `vp`-log goes from algebraic
(finite-support, certifiable) to archimedean (`ln`, transcendental).
