# The unimodular invariant — one `det = 1` drives the Stern-Brocot tree and the Markov recurrence

**Reproduced result.** Two number-theoretic domains, each long-closed and ∅-axiom:

  - the **Farey / Stern-Brocot mediant tree** — every node matrix `M_t = M_l·M_r` is in
    `SL₂(ℤ)`, i.e. `det₂(M_t) = 1` (`SternBrocotMarkov.mNode_det1`);
  - the **Markov triple recurrence** — Frobenius's slope-monotonicity and the
    Cayley–Hamilton Vieta jump `m' = 3m₁m₂ − m₃` (`SternBrocotMarkov.markoff_frobenius`,
    `markoff_vieta`).

The new content is the **proof that one invariant drives both**: `det₂ = 1`, propagated by
the single multiplicative law `det2_mul` (`det(MN) = det M · det N`). `UnimodularSynthesis.unimodular_drives_tree_and_markov`
carries the three readings as one object. ∅-axiom
(`lean/E213/Lib/Math/NumberSystems/Real213/Markov/UnimodularSynthesis.lean`, 1 PURE; the
reused lemmas are PURE).

## Why we picked it — one invariant, not a coincidence of two facts

The Stern-Brocot tree (continued-fraction approximation, Farey mediants) and the Markov
spectrum (the Markov/Hurwitz Diophantine recurrence) read as different subjects. The repo
proves each separately. But both rest on `SL₂(ℤ)` unimodularity, and that is a single
proven invariant — `det2_mul` is a pure `ℤ` polynomial identity (`ring_intZ`, not `decide`).
A cross-domain claim earns the word only when the shared structure is a proven map, never a
value-coincidence; here the map is the invariant itself, and each domain's structure is a
*consequence* of it. (Contrast the retracted "shared unit" entries in
`catalogs/cross-domain-identifications.md`, which were `decide` byte-identities across files,
not a shared engine.)

## Derivation — the invariant is the engine, the domains its readings

**The root.** `det2_mul` says the determinant is a multiplicative homomorphism `Mat2 → ℤ`.
From the two det-1 generators (`genL = [[2,1],[1,1]]`, `genR = [[3,4],[2,3]]`), every
interval bound is unimodular by induction (`mInterval_det`), so every node mediant is too
(`mNode_det1`): `det₂(M_l·M_r) = det₂ M_l · det₂ M_r = 1·1 = 1`. One law, the whole tree.

**Reading 1 — the Farey/Stern-Brocot tree.** `det₂(M_t) = 1` at every path *is* the Farey
adjacency invariant: neighbouring mediants have unit cross-determinant. This is the tree's
defining property (continued-fraction convergents, Stern-Brocot navigation).

**Reading 2 — Frobenius monotonicity.** The cross-determinant of a node against its left
bound, `M_l.a·(M_t).c − M_l.c·(M_t).a`, equals the right bound's `c`-entry `m_s` — *because*
it factors as `m_s · det₂ M_l = m_s · 1`. Since `m_s > 0`, this fixes the sign, giving the
strict slope-monotonicity (Zhang's Lemma 2) that is the residue-map injectivity behind
Markov-number uniqueness. The hypothesis Frobenius needs is exactly `det₂ M_l = 1` — supplied
by Reading 1.

**Reading 3 — the Vieta jump.** The left-child mediant's `c`-entry satisfies
`(M_l·M_t).c = tr(M_l)·(M_t).c − (M_r).c` — the Cayley–Hamilton recurrence
`M_l² = tr(M_l)·M_l − I`, valid *because* `det₂ M_l = 1` (the difference is
`(M_r).c·(1 − det M_l) = 0`). With the Markoff entry-shape `tr = 3·(·)_c` this is the Markov
equation jump `m' = 3m₁m₂ − m₃`. Again the hypothesis is `det₂ = 1`.

So Readings 2 and 3 are not independent theorems sitting beside Reading 1 — they are
*licensed by it*: the same `det₂ = 1`, which is `det2_mul` at the unimodular generators,
forces the tree's adjacency, the slope monotonicity, and the Markov jump. The invariant is
the engine; the two domains are its readings.

## Dual function — what the unification buys

Classically: `SL₂(ℤ)` acts on continued fractions and on the Markov spectrum, and
determinant multiplicativity is why both are governed by unimodularity. Read 213-native, it
is the operational content of "no exterior" (`seed/AXIOM/05_no_exterior.md` §5.1) for the
unimodular invariant: the same `1 = det₂` recurs across two readings because they are the
same residue, and the recurrence is a *proof* (the shared `det2_mul`), not a numeric
coincidence. It also gives the corpus a second cross-domain unification family beside the
incidence-algebra one (`count_duality.md`, `incidence_inversion.md`): there the shared object
was a Fubini/antipode on an incidence matrix; here it is determinant multiplicativity on
`SL₂(ℤ)`.

The invariant reaches further still, and that reach is also a theorem
(`unimodular_four_readings`): the *same* `det₂ = 1` is carried by four independent matrix
constructions — the Stern-Brocot mediant node, the **continuant** node (distinct matrices
`contMatProd`, unimodular by `det2_mul` from the det-1 continuant bounds `cInterval_det`), and
the **Minkowski `?`-cocycle** bounds (`minkowski_is_markov_valued_cocycle`, the
Eichler–Shimura-flavoured 1-cocycle valued in `SL₂(ℤ)`). Four constructions — Farey
approximation, continued fractions, the modular cocycle — one `det2_mul`.

Honest scope (`§8` falsifiability discipline). Each domain was already closed; this adds no
new tree, recurrence, or cocycle. It converts "these are all unimodular phenomena" from prose
into single theorems rooted in `det2_mul`. The open extension is the *period-polynomial* /
`H¹(SL₂(ℤ), V)` identification the Minkowski cocycle points at (an open frontier).

## Cross-frame connections

  - **Cassini multiplier law** (`CassiniUnimodular.det_step`/`det_closed`): the parametric
    `D(n) = qⁿ·D(0)` — the determinant of a 2nd-order recurrence scales by its shift-det `q`;
    the golden `q=1` (conserved) and swap `q=−1` (alternating) are its instances. The
    unimodular invariant here is the `q=1` conserved case on the Markoff spine.
  - **Markov uniqueness** (`MarkovUniqueness`, `MarkovInjectivity.slope_path_inj`): Reading 2
    (Frobenius monotonicity) is the engine behind the residue-map injectivity in the
    uniqueness programme.
  - **Incidence-algebra unifications** (`count_duality.md`, `incidence_inversion.md`): the
    other cross-domain family — Fubini double-count and the Möbius/antipode inversion on an
    incidence matrix. Together with this one they are the corpus's proven cross-domain maps:
    incidence algebra and `SL₂(ℤ)` unimodularity.

## Constructive accessibility

Point at it. The root law: `SternBrocotMarkov.det2_mul`. The tree propagation:
`mInterval_det`, `mNode_det1`. The two Markov readings: `markoff_frobenius`, `markoff_vieta`.
The capstone bundling all three from the one invariant:
`UnimodularSynthesis.unimodular_drives_tree_and_markov`. The four-construction reach:
`UnimodularSynthesis.unimodular_four_readings` (Stern-Brocot, continuant, Minkowski cocycle).
All ∅-axiom (`#print axioms` empty).
