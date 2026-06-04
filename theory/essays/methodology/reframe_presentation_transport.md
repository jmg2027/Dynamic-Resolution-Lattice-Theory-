# REFRAME: reading the same residue at the resolution where it separates

A reading that fails to `SEPARATE` (over-counts — its fiber is non-injective) is not a verdict on the
object.  Factor a shared invariant the object carries, read through the factor whose fiber is smallest,
and a solved `SEPARATE` fires.  The object is invariant; the resolution of the reading changes.

## 213-native answer

Separability is a property of the **pointing**, not of the residue.  `seed/AXIOM/06_lens_readings`
and the operating record (CLAUDE.md, *External-ruler smuggling*): a presentation is a residue-internal
pointing; depth — here, whether a reading distinguishes what the residue distinguishes — lives in the
pointing, witnessed in code by `Real213/PresentationDependence` (`crossDetSmall_is_presentation_dependent`,
`rcut_rescale`).  The residue is presentation-invariant.  So when one reading cannot `SEPARATE`, the move
is not to *improve the object* but to *transport to the pointing where the residue's own self-distinction
is readable*.  This is the fourth lift archetype, `REFRAME`, in the proof-ISA catalog
(`lean/E213/Lib/Math/Foundations/ProofISALifts.lean`, `lift_reframe`/`lift_reframe_modulus`), beside
`DIAGONAL`, `LOOP`, `ORBIT`.

## Derivation

`SEPARATE` is the instruction "a reading refines the identity Lens iff it is injective"
(`isa_separate = Lattice.refines_idLens_iff_injective`, `seed/PROOF_ISA.md`).  Take the Markov
configuration `(a,b,c)` as residue (`theory/math/analysis/markov_uniqueness.md`).  The reading `mod c`
sends a triple to its `√(−1)`-residue `u` — but for composite `c` with `≥ 2` distinct prime factors
`≡ 1 mod 4` this reading **over-counts** (`2^{ω}` roots): it does not refine the identity Lens, so
`SEPARATE` fails in place.  `SternBrocotMarkov.markovNum_subtree_size_interleaves` records the dual dead
end — no *order*-monovariant repairs the reading either (the size reading interleaves across the tree's
fork).

The transport: the residue carries the invariant `Δ = 9c²−4 = tr²−4·det` (the discriminant of every
Markoff node, `markov_node_disc`), a difference-Lens readout (`theory/essays/analysis/integers_as_difference_lens`).
It **factors**: `Δ = (3c−2)(3c+2)`.  Read mod a prime-power factor `M = 3c±2`, and the same residue's
`√(−1)`-data reappears with a *small* fiber: the prime-power square collapse forces `≤ 2` roots
(`MarkovPrimeFactor.sq_eq_collapse_pp`), so `SEPARATE` now fires.  The linear form reduces to a single
recoverable coordinate — the gap `b−a` mod `3c−2` (`MarkovUniqueness.zhang_linear_core`) or the sum `a+b`
mod `3c+2` — and `(c, coordinate)` fixes the pair (`zhang_quadratic`, `zhang_gap_determines_pair`).  The
result, `markov_max_unique_via_3c_pm2`, closes composite Markov numbers (`985`, `4181`, `610`, `195025`)
structurally — `REFLECT → READ → SEPARATE`, the discriminant naming its own factors from within.

The same move, one layer down, is CRT: factor the *modulus* `2·pᵏ = 2 × pᵏ` and read through each factor
(`MarkovPrimeFactor.two_roots_of_two_prime_pow`, the even `2·pᵏ` family).  CRT and the modulus shift are
one archetype — *factor an invariant, read through the prime-power factor where the fiber collapses* — at
the modulus layer and the discriminant layer.

## Dual function

Read classically, this is "a change of modulus" or "a clever substitution `c ↦ 3c±2`."  That packaging
hides the operative fact: the substitution is not a trick external to the problem but a **presentation of
the same residue**, and *which* substitutions work is not free invention — it is dictated by which factors
of the carried invariant are prime powers.  213's reading is sharper exactly here: the failure of `mod c`
and the success of `mod 3c±2` are not facts about two different problems but two pointings at one residue
whose separability sits in the pointing; the search for a working REFRAME *is* the search over the
invariant's factorisation, not over ad-hoc cleverness.

## Cross-frame connections

*External-ruler smuggling* (a presentation is residue-internal, depth lives in the pointing) +
`isa_separate` (refinement = injectivity) + the discriminant's self-factorisation `9c²−4 = (3c−2)(3c+2)`
(`REFLECT`, the object naming its own alternate readings) + `markovNum_subtree_size_interleaves` (the
in-place exhaustion REFRAME is dual to) — one fact at four resolutions: *a reading's reach is a property
of the reading, repaired not by force but by transport to the presentation the residue's invariant
already names.*

## Open frontier

REFRAME is **conditional**: it needs the invariant to have a prime-power factor.  At `c = 1325 = 5²·53`
both `3c−2 = 29·137` and `3c+2 = 41·97` are composite — no presentation collapses the fiber, and the
residual is not a missing reading but the class-number / fundamental-unit content of the order of
discriminant `9c²−4` (the open Markov / Lagrange frontier).  That residue is the open Frobenius core;
REFRAME locates exactly where transport stops and the genuine arithmetic begins.
