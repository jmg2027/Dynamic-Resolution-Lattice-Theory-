# A character of a finite cyclic group is the group's eigen-data

A character of `ℤ/p` is not a function posited on the group — it is an
**eigen-quantity of the group acting on itself**.  The cyclic group has two
self-actions, and each forces a character as its eigen-data: the
*multiplication* action `×a` forces a sign (the quadratic character), and the
*shift* action forces an eigenbasis (the additive characters).  One group, two
character-faces, both spectral.

## 213-native answer

Read the cyclic group as an operator on functions, and read off its spectrum.

**Multiplicative face — the sign of `×a`.**  The map `σ_a : x ↦ a·x mod p` is a
permutation of the `p−1` units; its permutation **sign** `psign σ_a` is a
`{±1}`-valued homomorphism on `(ℤ/p)*`.  That homomorphism *is* the Legendre
symbol: `(a/p) = psign σ_a` (`theory/math/numbertheory/zolotarev.md`,
`zolotarev_mu`).  Because `(ℤ/p)*` is cyclic of even order `2m`
(`primitive_roots.md`, `exists_primitive_root`), a generator is not a square, so
the sign is non-trivial and *forced*, not chosen: `(a/p) = (−1)^{dlog_g a}`, the
mod-2 readout of `a`'s orbit position
(`theory/essays/synthesis/the_quadratic_character_is_a_discrete_log_parity.md`).
The quadratic character is the order-2 eigen-datum of the multiplication action.

**Additive face — the eigenbasis of the shift.**  Take the same prime's
complete graph `K_p` — the Cayley graph of `ℤ/p` on *all* non-zero shifts.  Its
Laplacian `L = J − p·I` has spectrum `{0, p}`, and the **mean-zero functions**
(`Σ f = 0`) are exactly the `λ = p` eigenspace, multiplicity `p−1`
(`lean/E213/Lib/Math/Geometry/GeometrizationConjecture/DiscreteLichnerowicz.lean`,
`km_eigenvalue` + `km_meanzero_eigen`: `Σf = 0 ⟹ Lf = −p·f`).  That eigenspace
is spanned by the non-trivial **additive characters** `χ_a(x) = ζ_p^{ax}`
(`a ≠ 0`): they sum to zero — the orthogonality `Σ_x χ_a = 0` — hence are
mean-zero, hence are the shift-Laplacian's eigenfunctions.  The additive
characters are the eigenbasis of the shift action.

## Derivation

The two faces are the same move at different group-actions.  A character is
defined by what the group's action does to it: `χ` is a character iff the action
sends `χ` to a scalar multiple of `χ` — an eigenfunction.  For the *shift*
action this is literal (`Lf = λf`), and the scalars-and-eigenvectors are the
additive characters; for the *multiplication* action the relevant invariant is
the action's effect on orientation, i.e. its **sign**, and the order-2
eigen-datum is the quadratic character.  Both are forced by the group being
cyclic: cyclicity of `(ℤ/p)*` forces the non-trivial sign
(`primitive_not_qr`), and the single-orbit (`p−1`)-cycle structure of `σ_a`
forces the spectrum.  Neither character is an external choice; each is what the
self-pointing of the group returns when counted
(`seed/AXIOM/01_residue.md`: the readout is the count a view returns, not a
substance the group has).

## Dual function

Classically these are two theories — multiplicative characters (Dirichlet,
Legendre, Gauss sums) and the discrete Fourier basis (additive characters,
graph spectra) — taught in different courses.  The 213 reading strips the
separation: both are *eigen-data of the cyclic group acting on itself*, and the
"two theories" are the multiplication action versus the shift action of one
object.  The reading is sharper than "a character is a homomorphism to roots of
unity," because it says *why* the character exists and is unique: it is the
eigenbasis (additive) or the sign (multiplicative) the group's own action
**forces** — a thing you can point at (`psign σ_a` ∈ `{±1}`; the mean-zero
eigenspace `ker(Σ)`), not a structure imposed from outside.

## Cross-frame connections

The same "structure ⟹ spectrum" fact appears in both frames and in a third,
geometric one.  Cyclicity forces the quadratic character
(`the_quadratic_character_is_a_discrete_log_parity`); the complete-graph
structure forces the Laplacian spectrum `{0,p}` (`km_eigenvalue`); and a
curvature lower bound forces a spectral gap (`lichnerowicz_abstract`:
`CD(K,∞) ⟹ λ₁ ≥ K`).  Sign-of-a-permutation, eigenbasis-of-a-graph, and
gap-from-curvature are three resolutions of one residue move — a structural
hypothesis returning a spectral/parity invariant — which is the breadth that
counts as primacy (`seed/AXIOM/07_primacy.md`).

## Open frontier

The two faces are computed in different modules with no proven bridge between
them.  Concretely buildable (a corollary, no new primitive): instantiate
`km_eigenvalue` at `m = p` and name the mean-zero eigenspace the
additive-character space, so "the `K_p` spectral gap is the group order `p`"
becomes a theorem.  Genuinely open: a proven morphism identifying the
multiplicative sign `psign σ_a` with an additive-character functional (a
Gauss-sum-style identity tying the two faces of the one cyclic group), which
would close the bridge rather than state it from two sides.
