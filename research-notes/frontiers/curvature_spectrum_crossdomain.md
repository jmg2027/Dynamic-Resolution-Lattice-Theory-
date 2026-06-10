# Cross-domain: discrete curvature / spectrum (this branch) × characters & the cyclic group (main)

This branch closed discrete Ricci curvature (4 frames, all graph families), the
Lichnerowicz curvature→spectrum bridge, and the algebraic Riemann tensor calculus.
`origin/main` (merged in) closed the primitive-root / `(ℤ/p)*`-cyclic arc, classical
Zolotarev `(a/p)=psign σ_a`, the Fibonacci rank `α(p)∣p−(5/p)`, and the golden prime
`5`.  Three genuine bridges surfaced on the merge.

## 1. The `K_p` Laplacian spectrum `{0, p}` IS the additive-character spectrum of `ℤ/p`

`DiscreteLichnerowicz.km_eigenvalue` / `km_meanzero_eigen` prove: the complete-graph
`K_m` Laplacian `L = J − m·I` has spectrum `{0, m}` with the **mean-zero functions**
(`Σf = 0`) as the `λ = m` eigenspace (multiplicity `m−1`).

When `m = p` is prime, `K_p` is exactly the Cayley graph of `ℤ/p` on *all* non-zero
shifts, and its mean-zero `λ = p` eigenfunctions are precisely the **non-trivial
additive characters** `χ_a(x) = ζ_p^{ax}` (`a ≠ 0`) — they sum to zero (`Σ_x χ_a = 0`,
the orthogonality main uses for character sums) hence are mean-zero, and `L χ_a = p·χ_a`.
So `km_meanzero_eigen` (mean-zero ⟹ eigenvalue `p`) is the **discrete-Fourier / additive
character** statement read as a Laplacian fact.

Main built the *cyclic group* `(ℤ/p)*` and its **multiplicative** characters (Legendre
`(a/p) = (−1)^{dlog_g a}`, `the_quadratic_character_is_a_discrete_log_parity`).  This
branch built the **additive** characters as the spectrum of the same prime's complete
graph.  One object — the cyclic group of order `p` — read two ways: its multiplicative
characters are main's quadratic symbol; its additive characters are this branch's
Laplacian eigenbasis.  The shared content is "**characters of the cyclic group are the
eigen-data**", a `213`-native unification of character theory (main) and spectral graph
theory (branch).

**Buildable next** (no new primitive): instantiate `km_eigenvalue` at `m = p` and name the
mean-zero eigenspace as the additive-character space; the Lichnerowicz bound `λ₁ = p ≥ K`
then reads "the spectral gap is the group order".

## 2. The central DRLT lattice `K_{3,2}` carries BOTH a golden and a curvature signature

`K_{3,2} = K_{NS,NT}` (`NS = 3`, `NT = 2`) is the repo's central object.  Main's arc reads
its **number-theoretic** signature: `NS + NT = 5` is the fractal base / golden prime
(`R_u = 1/φ²`, `ℚ(√5)`, the CP-phase modulus).  This branch reads its
**differential-geometric** signature: `BakryEmeryBipartite.kab_K32_pos` gives Bakry–Émery
`CD(3/2, ∞)` (positive), while Forman gives `4 − 3 − 2 = −1` (negative).  So the *same*
`K_{3,2}` is simultaneously the golden-ratio physics lattice and a graph of definite
(frame-dependent) Ricci curvature.  The two signatures meet at `a + b = NS + NT = 5`: the
golden prime is the *vertex count* whose curvature this branch computed.

## 3. "Structure forces the invariant" — Lichnerowicz ∥ cyclicity-forces-the-character

Both arcs are *forcing* results of the same shape.  Main: `(ℤ/p)*` being **cyclic of even
order** *forces* the quadratic character to exist (`primitive_not_qr` — a generator is not
a square, so `(·/p)` is a non-trivial homomorphism, not posited).  Branch:
`CD(K, ∞)` *forces* the spectral gap `λ₁ ≥ K` (`lichnerowicz_abstract` — curvature bounds
the spectrum, the eigenvalue dominates).  In both, a *structural* hypothesis (cyclicity /
curvature lower bound) forces a *spectral/parity* conclusion (character existence /
eigenvalue gap).  Per `seed/AXIOM/07_primacy.md`, this is the residue reproducing the same
"structure ⟹ spectrum" move in two disciplines — the breadth that is primacy.

## Honest boundary

Bridge 1 is concrete and buildable (the `m = p` instantiation is a corollary).  Bridges 2–3
are conceptual frames, not theorems — `K_{3,2}`'s two signatures are computed in different
modules with no proven morphism between "`5 = NS+NT`" and "`CD = 3/2`", and the
Lichnerowicz/cyclicity parallel is an analogy of *form*, not a shared lemma.  Recorded as
cross-domain orientation, not closure.
