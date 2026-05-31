# Is a real number graspable without completeness?

Triggering question: *실수란 무엇인가 — 완비성 없이 실수가 손에 잡히는가?*

A real `x` is a decision procedure `c : ℕ → ℕ → Bool`, `c m k = ⟦x ≤ m/k⟧`.
The procedure *is* the real. The limit is the cut the procedure already
computes, not an axiom laid on top. This essay walks the full arc — cut →
probe-twist conic → divergence depth → ordinal axes → ceiling-reference =
residue — as one trajectory, marking **(L)** zero-axiom Lean theorem,
**(C)** classical fact, **(✗)** out of scope.

## 213-native answer

To *use* a real is never to hold its completed decimal; it is to answer
comparisons — "given `m/k`, is `x ≤ m/k`?" — at every precision. Take that
as the definition: `Real213` cut + `ValidCut` (`theory/math/real213.md`).
No completion step, no equivalence-class quotient is *needed* for the object
to exist. The cut is the real; two cuts denote the same real when each
refines the other, and "refine" is one Lens-arrow `Lens.refines`, not four
parallel equivalences (`theory/lens/unified_equivalence.md`).

## Derivation

The classical move — "a real *is* an equivalence class of Cauchy sequences"
— is recovered, not assumed. A monotone bounded ab-sequence yields a cut
(`AbCutSeq`, `IsAbMonotonic`), and the statement usually called *Cauchy
completeness* becomes a **constructed theorem** about cuts — `MonotonicBounded`
→ `Math.Analysis.CauchyComplete` — not an axiom about a quotient. The limit is
not posited; it is the cut the procedure already computes. That is the first
sense of "completeness without completeness" (`theory/math/completeness_relocated.md`).

Graspable, then — in what sense? 213 calls *reaching a pointable syntactic
object* graspability (constructive accessibility). The identity of a real is
pointed at not as a position on a line (which a completeness axiom would pin)
but as the *curve its finite convergents inhabit*. Twist convergents by the
hyperbolic `P=[[2,1],[1,1]] ∈ SL₂(ℤ)`: the φ-norm `Q(m,k)=m²−mk−k²` is
preserved (`ProbeTwistConic.Q_preserved`), so each real wobbles on its own
hyperbola `Q=N`. Algebraic = stays on **one** conic (φ is twist-fixed
`PhiProbeFixed`; √2 keeps Pell `pell_invariant`); transcendental = **escapes
every** conic (e is not fixed, `ProbeTwistFixedPoint`). The identity is the
conic, not a coordinate (`theory/math/probe_twist_conic.md`).

Even the *manner* of escape is finitely grasped. The cross-determinant
(discrete Wronskian) `Wₙ`: φ gives `±1` (Cassini), e gives `−n!`, π gives
Wallis (`EulerDivergenceForm`). The number of finite differences needed to
floor that divergent sequence is the **divergence depth** — φ 1, e 3, π 6,
Liouville ∞ (`DivergenceLadder`, `DivergenceDepth.depth_three`). An infinite
object (a divergent determinant sequence) reduced to a finite reference (its
depth). That is the second sense of graspability.

## Dual function

This answer is the classical concept with redundant packaging stripped, *and*
a sharpening, in one move. **Interpretation**: the ε-δ existential of "the
limit exists" is replaced by the cut the procedure emits at each precision —
nothing is lost. **Refinement**: where the classical irrationality measure
`μ` *collapses* algebraic irrationals, e, and π all to `μ=2`, divergence depth
*separates* them 1·3·6·∞. Depth is **orthogonal** to `μ`, and it equals the
P-recursive (holonomic) rank (`DepthPRecursive`). The same algebraic/
transcendental split — closed-form modulus, single conic, finite depth — is
drawn three independent times.

## Cross-frame connection

That line is drawn once more, then folds onto itself. Resolving depth needs a
tower of axes: difference, ratio-lift (= difference on the exponent,
`ratio_is_diff_on_exponent`), recursion into the exponent
(`value_floors_iff_exponent_floors`). The coordinate `(h,d)` is an ordinal
below `ω²` (`DepthOrdinal.lex_wf`); above it `ω^ω`, `ε₀` — but no top
(`DepthDoubleExp.dexp_not_const`). And *naming the ceiling-raising* — pointing
at all the levels as one object — is a diagonalisation `diag f n = f n n + 1`
whose object lies outside the sequence it summarises
(`DepthCeilingResidue.diag_not_in_seq`). This is `cantor_general`: the *same*
non-surjectivity by which `Object1 : Raw → (Raw→Bool)` is faithful yet not
total — the foundational residue (`FlatOntologyClosure.self_covering_closure`).

> The ordinal tower (ε₀, Veblen) and the pointing residue are one
> self-covering closure read at two scales. The arc that began by refusing to
> posit a completed limit ends by showing the only thing that ever exceeds the
> finite act is the residue the finite act itself leaves — not an exterior but
> the next act. The hierarchy has no top because pointing has no exterior
> (`seed/AXIOM/05_no_exterior.md` §8.1).

## Open frontier

Graspability is not uniform. Algebraic reals complete their cut
**unconditionally** (φ: closed-form modulus `N=2k`). For e and π the modulus
re-enters as a *hypothesis* — a total LEM-free modulus would need a choice
principle `MonotonicBounded` refuses (✗, §180–194). The "depth = P-recursive
rank" identification and the `ω^ω`/`ε₀` readings rest on (C) classical
interpretation; the ladder above the (L)-pinned first rungs is not yet proven.
"π's data is not P-recursive" means "no known low-order recurrence," not a
theorem.

So: **a real is graspable without completeness — in that the trajectory
reaches pointable syntactic objects (cut, conic `Q=N`, depth integer, ordinal
coordinate, diagonal `diag f`).** For transcendentals that grasp is
modulus-gated, not unconditional, and the gate not closing is itself another
face of the residue.

## Provenance

Crystallised on branch `claude/tower-research-analysis-3uWqd` alongside the
capstone paper `theory/math/completeness_without_completeness.md`, of which
this essay is the on-demand trajectory form. Anchor chapters:
`theory/math/real213.md`, `completeness_relocated.md`, `probe_twist_conic.md`.
