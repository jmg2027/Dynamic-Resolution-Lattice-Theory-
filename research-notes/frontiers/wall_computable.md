# wall_computable — the Banach completeness wall, read through TTE / domain theory

**Date**: 2026-06-22.  **Status**: OPEN (diagnosis + proposed ∅-axiom engine, no Lean written yet).
**Angle**: computable analysis (Weihrauch Type-Two Effectivity) + Scott/Kleene domain theory.

**Files in play** (all build clean, ∅-axiom):
- `lean/E213/Lib/Math/Analysis/BanachFixedPoint.lean` — `Contraction`, `picard`,
  `picard_cauchy` (L154), `CompleteMetricModulus` (L183, with `lim`/`climconv`),
  `banach_fixed_point` (L202), `banach_unique` (L250).
- `lean/E213/Lib/Math/Probability/Limit/DyadicCompletion.lean` — `DyC L` (L54),
  `metC L` (L90), `telescope_tail`/`telescope_regular` (L153/L191), `stab`/`stabShift_regular`/
  `limPoint` (L222/L245/L255), `Φhat`/`Φhat_contraction` (L306/L316),
  `orbit_to_center_completion` (L354).
- `lean/E213/Lib/Math/Probability/Limit/ConvolveRescaleContraction.lean` —
  `crossDist_Φ` (L331), `Φ_contraction` (L345), `closeDy_center` (L433), `picard_Φ_eq` (L447),
  `orbit_to_center` (L471).

## The wall, stated precisely (and a correction to the file's own docstring)

`CompleteMetricModulus X` (BanachFixedPoint.lean:183-189) carries

```
lim     : (Nat → X) → X                       -- TOTAL, no Cauchy hypothesis on the argument
climconv : ∀ seq, (seq is modulus-Cauchy) → ∀ m, ∃ N, ∀ p ≥ N, close m (seq p) (lim seq)
```

`banach_fixed_point` consumes a `CompleteMetricModulus` and produces the located fixed point
`lim (picard T x0)`.  To run it on convolve-and-rescale we need
`CompleteMetricModulus (DyC L)`.  **`DyadicCompletion.lean`'s header docstring claims
`completeDy L : CompleteMetricModulus (DyC L)` and a `climconv` "3ε argument" are built — they
are not.** The file stops at `limPoint` (L255, the total stabilizing-diagonal point) and
`orbit_to_center_completion` (L354, the convolve-rescale content delivered *directly* on `closeC`,
bypassing the engine).  The header describes the intended endpoint; the convergence proof
`closeC m (limPoint S) — to — diagonal` linking `limPoint` back to `climconv` is the missing step.

Why the naive route is genuinely blocked, not merely unfinished: a *total*, choice-free
`lim : (Nat → DyC L) → DyC L` that converges for every Cauchy `seq` cannot be the plain diagonal
`(S n).seq n` — the diagonal of regular (identity-modulus) sequences need not be regular, because
reading "where does `S n` settle" requires its unbounded inner modulus.  This is exactly the
classical fact that the limit map on *bare* Cauchy sequences (no modulus attached) is not
computable. `stab` (L222) is the constructive repair: a decidable freeze (`closeDy` is `Decidable`,
L218) that forces the per-step bound `closeDy (k+1) (stab k) (stab (k+1))` *unconditionally*
(`stab_step`, L232), so `limPoint` is regular **for every `S`**. The freeze is the TTE move made
concrete (see below).

## (a) Names-not-points — and the repo already lives there

**TTE reframing.** In Type-Two Effectivity a real (or any completion point) is not an element of an
abstract quotient set; it *is* a **name** under an admissible representation `δ`: an infinite string
carrying its own convergence data. `lim` is computable precisely on *names*, never on the bare
quotient. The wall is then a **typing artifact**: `CompleteMetricModulus.lim` is typed
`(Nat → X) → X` — a function on *bare* sequences — when the honest, computable object is a function
on *names* = regular Cauchy sequences = `DyC L` itself.

`DyC L` (DyadicCompletion.lean:54) is literally an admissible-representation datum:

```
structure DyC (L : Nat) where
  seq : Nat → Dy
  reg : ∀ m p q, p ≥ m → q ≥ m → closeDy L m (seq p) (seq q)   -- identity modulus = Cauchy data carried
```

`reg` is the Bishop *regular* convention — the modulus is the identity, baked into the type, not
read off at runtime. So `seq`-with-`reg` is a name, and a map `DyC L → DyC L` (e.g. `Φhat`) is a
*realizer* on names. On names, "take the limit" is total and choice-free: that is the whole point of
the representation. The wall dissolves the moment `lim` is retyped to act on the carrier of names.

**This is native, not an import.** The repo's foundations already commit to the names-not-points
stance under its own vocabulary ("pointing" / "approximant" / "reached by none"):

- `seed/AXIOM/05_no_exterior.md` §5.5: *"every pointing is already complete … the act of pointing is
  already complete. No partial pointing exists."* A point is identified with the (complete) act of
  pointing — i.e. with its name — not with a pre-existing element.
- `theory/essays/foundations/reached_by_none.md` (esp. L26-28, L100-103): the real is *"reached by no
  Cauchy approximant"*; the methodology is **build µF (approximants) → name νF (the carrier the limits
  live on) → witness the non-surjection**, and *"reached-by-none, formalized, IS the object."* That is
  the admissible-representation stance verbatim: the object is its convergent process (the name on the
  νF carrier), and there is no fourth move that hands you a bare point. The Lean witness family is
  `Cauchy/DepthSelfReference.geom_escapes` ("no floor reached").
- `theory/essays/foundations/the_form_of_the_residue.md` L107, L118-123: limit names like `e`, `π`,
  `lim = 1` *"name the pointing, not a place beyond it"* — the modulus / approximant sequence is the
  computable operand; the limit-point never is. (CLAUDE.md "Limit/infinity deified" failure row: the
  modulus is what 213 calculates with.)
- `BanachFixedPoint.lean` already speaks this language in its own docstrings: the fixed point is
  *"reached by none — only the Cauchy limit"* (L201), *"located equality"* `close m x* (T x*)` at
  every scale rather than a propositional `=`.

So retyping `lim` to a name-map is not importing TTE onto 213 — it is naming, in computable-analysis
terms, a stance 213 fixed axiomatically. The diagnosis: **`CompleteMetricModulus.lim : (Nat→X)→X`
over-promises** (a total limit on bare sequences, classically non-computable); the honest object is
`limPoint`-style — total on `Nat → DyC L` (names of names), regular by construction. `DyC L` is the
admissible representation; `lim` on it is total and computable. The wall is the gap between the
over-typed wrapper and the name-typed truth, and `stab` already bridges most of it.

## (b) Domain-theoretic reframe: fixed point as the colimit of the Picard chain

A `Contraction M T` (BanachFixedPoint.lean:29) is, in domain-theoretic terms, an **ω-continuous**
self-map for the resolution-graded structure: the "information order" is *agreement up to scale `m`*,
and `Contraction` says one application advances every pair by one dyadic level
(`close (m+1) x y → close (m+2) (Tx) (Ty)`). The Picard chain `xₙ = picard T x0 n` (L33) is then an
**explicit ω-chain of approximations** whose "least upper bound" is the fixed point — Kleene's
fixed-point theorem in metric clothing: `fix(T) = ⊔ₙ Tⁿ(x0)`, except the join is a *located limit*
(reached by none) rather than a Scott lub of a flat-domain chain.

The decisive contrast with classical Banach: **no completeness axiom, no choice is invoked to
*assert* the limit exists** — the chain is given termwise (`picard` is a plain recursion), and its
convergence data is *computed*: `picard_cauchy` (L154) produces the modulus `N(m) = m` from the
single base gap `hbase`, via the uniform geometric tail `picard_tail` (L75). The "colimit" is not
summoned; it is the name `⟨picard T x0, derived-regularity⟩` itself. This is exactly the
domain-theoretic reading: the fixed point is a *directed colimit* of finite stages, and the colimit
is presented, not postulated.

The reusable abstraction `telescope_regular` (DyadicCompletion.lean:191) is already the engine's
heart: from per-step bounds `close (k+1) (f k) (f (k+1))` it derives the regular Cauchy spec — i.e.
**any geometrically-decaying chain is automatically a name**. This is the colimit-presentation lemma,
stated generically for `MetricModulus`, and it is what makes the Picard chain a `DyC`.

### Proposed reusable engine statement

Two complementary forms; the second is the one that retires the wall.

**Engine 1 — `picard_is_name` (chain → name, generic, X = name carrier).** For any
`MetricModulus`-carrier whose points are themselves names and which is closed under "diagonalize a
chain into a name" (the `limPoint` construction generalized), the Picard chain of a `Contraction`
*is* a name:

```
theorem picard_is_name {X} (M : MetricModulus X) {T} (hT : Contraction M T) (x0) (s)
    (hbase : M.close (s+1) (picard T x0 0) (picard T x0 1)) :
  ∀ m p q, p ≥ m → q ≥ m → M.close m (picard T x0 p) (picard T x0 q)
```

This is `picard_cauchy` repackaged into the *regular* (identity-modulus) shape via
`telescope_regular`'s argument — no `CompleteMetricModulus` needed. It says the orbit is admissibly
represented.

**Engine 2 — `fixed_point_of_contraction_via_name` (the wall-retiring statement).** Phrase
completeness as a *name-limit operator* rather than a bare-sequence `lim`. Add to (or replace in)
`CompleteMetricModulus`:

```
structure NameComplete (X) extends MetricModulus X where
  nlim  : (Nat → X) → X                                   -- total; X is the name carrier
  nstep : ∀ S k, close (k+1) ((nlim-stage) ...) ...       -- per-step regularity, à la stab_step
  nconv : ∀ S, IsCauchy S → ∀ m, ∃ N, ∀ p ≥ N, close m (S p) (nlim S)
```

with the headline:

```
theorem fixed_point_of_contraction_via_name {X} (C : NameComplete X) {T}
    (hT : Contraction C.toMetricModulus T) (x0 s)
    (hbase : C.close (s+1) (picard T x0 0) (picard T x0 1)) :
  ∀ m, C.close m (C.nlim (picard T x0)) (T (C.nlim (picard T x0)))
```

Proof skeleton: identical to `banach_fixed_point` (L202-237) — `picard_cauchy` gives Cauchy, `nconv`
gives convergence at `m+2`/`m+3`, contraction + quarter-triangle (`ctri`/`qtri`) closes the scale.
The *only* change is that `nlim` is honestly total because `X` is the name carrier (the `stab` freeze
is internalized as `nstep`), so the structure is *inhabitable on `DyC L` without fabrication*.

The work that remains to instantiate it on `DyC L` is the proof currently missing from the file:
**`climconv`/`nconv`** — show `limPoint L S` (L255) converges to `S` in `closeC` for Cauchy `S`. The
plan in the file's docstring (L20-27) is right: for genuinely Cauchy `S` the `stab` freeze
*eventually never triggers* (the inter-term tail eventually fits inside `1/2^(k+1)`), so `limPoint`
agrees with the plain diagonal `diagSeq` (L110) in the tail; and `diagSeq` already converges
(`diag_reg`, L116, plus a 3ε/quarter-triangle step on `Nat`). This is a finite `Nat`-arithmetic
argument — no choice.

## (c) Instantiation for Φ

With `NameComplete (DyC L)` discharged (i.e. `climconv` proven), the convolve-and-rescale fixed point
is the engine's output, not a hand-rolled `closeC` argument:

- `Φhat L : DyC L → DyC L` (L306) is the pointwise lift; `Φhat_contraction L` (L316) is a genuine
  `Contraction (metC L) (Φhat L)` — **the exact hypothesis `fixed_point_of_contraction_via_name`
  wants**, already proven ∅-axiom.
- Seed `inj L (p,0)` (L100); base gap from `closeDy_center`/`Φ_contraction`. The engine then yields
  `∀ m, closeC L m (nlim (picard (Φhat L) (inj L (p,0)))) (Φhat L (...))` — the Gaussian center as a
  *located Banach fixed point reached as the Picard name-limit*.
- `orbit_to_center_completion` (L354) currently proves the *content* (orbit → `inj L (0,0)` in
  `closeC`) **directly**, sidestepping the engine via `picard_Φhat_seq` + `orbit_to_center`. So the
  result is not blocked — only its routing *through the reusable Banach engine* is. Closing
  `climconv` upgrades the bespoke `orbit_to_center_completion` to an *instance* of one engine, which
  is the promotion-worthy form (one engine, reused — CLAUDE.md "layer-by-layer is a smell").

## (d) Honest ∅-axiom assessment — does the names route smuggle anything in?

**Verdict: it is genuinely choice-free, and the reason is that admissibility is paid for *in the type*,
not at runtime.**

- The classical non-computability of `lim` is about *bare* Cauchy sequences: extracting a limit needs
  the (unbounded, sequence-dependent) modulus, and choosing it uniformly is where AC/LPO/Markov sneak
  in. `DyC L` removes that: the modulus is the **identity** by the `reg` field (Bishop regular). No
  modulus is *chosen* — it is fixed by the representation. This is the load-bearing point and it is
  honest: regularity is a restriction on which sequences count as names, discharged by the *producer*
  (here `telescope_regular` / `picard_cauchy` compute it), never by an oracle at the limit site.
- `stab` (L222) uses `Decidable (closeDy …)` (L218) — a pure `Nat` `<` test, `Decidable`, not
  `Classical.dec`. The `by_cases` in `stab_step` (L237) is decidable-case, ∅-axiom. So the freeze
  introduces **no** `Classical.choice`/`propext`/`Quot.sound`.
- No `funext`: the constructions are `structure`/`def` data, equalities are `rfl` or `Nat` rewrites;
  `closeC` comparison is `∃ K, ∀ n ≥ K, …` (located), never a function-extensional `=`.
- **Where admissibility does cost something** (state it plainly, per the "no-exterior is under test"
  guard, `seed/AXIOM/05_no_exterior.md` §5): the price is **representation-dependence**. A `DyC L`
  name fixes the identity modulus; a sequence Cauchy with a *worse* modulus is simply *not a name*
  until re-indexed (speed-up) into regular form. That re-indexing is itself a computable, ∅-axiom
  operation, but it is a real step — "every Cauchy sequence converges" becomes "every Cauchy sequence
  *with its modulus* can be re-presented as a regular name, which converges." This is the
  presentation/real split the repo already isolated: `Real213/PresentationDependence`,
  `modulus_rescale_invariant`, `completability_is_intensional`
  (`research-notes/frontiers/completability/G169_intensional_completability_conjectures.md`). The
  completion (the cut) is presentation-invariant; the *probe* (which modulus) is presentation-relative.
  So nothing is smuggled — but the bare-sequence `climconv` quantifier `∀ seq, (seq Cauchy) → …` is
  doing slightly *less* than it looks: it is a statement about names with their carried modulus, and
  honesty requires saying the modulus is part of the input, not recovered for free.
- Net: `fixed_point_of_contraction_via_name` over `NameComplete` is ∅-axiom-compatible. The only
  unwritten obligation is the `Nat`-arithmetic `climconv`/`nconv` proof (freeze-eventually-stops +
  3ε), which the existing `diag_reg`/`telescope_regular`/`qtri` toolkit can discharge without any
  axiom. The wall was an *over-typing* (`lim` on bare sequences), not a missing truth.

## Headline proposal

The Banach wall is a typing artifact: `CompleteMetricModulus.lim : (Nat → X) → X` asks for a total,
choice-free limit on *bare* Cauchy sequences — classically non-computable — when the honest object is
a limit on **names** (regular Cauchy sequences carrying their own identity modulus), and `DyC L`
(DyadicCompletion.lean:54) *is* exactly that admissible representation. The repo already commits to
this names-not-points stance natively — `05_no_exterior.md` §5.5 ("every pointing is already
complete"), `reached_by_none.md` ("reached-by-none, formalized, IS the object") — so retyping `lim`
as a name-map is naming a 213 axiom in TTE terms, not importing TTE. Domain-theoretically a
`Contraction` is ω-continuous and its fixed point is the *presented* colimit of the explicit Picard
chain (`picard_cauchy`, BanachFixedPoint.lean:154; `telescope_regular`, DyadicCompletion.lean:191 =
the chain→name lemma) — Kleene's `⊔ₙ Tⁿ` as a located limit, summoned by no completeness axiom. I
propose a reusable `NameComplete` structure + `fixed_point_of_contraction_via_name` (same proof
skeleton as `banach_fixed_point`, but `lim` honestly total because `X` is the name carrier with the
`stab` freeze internalized), instantiated by the already-proven `Φhat_contraction`
(DyadicCompletion.lean:316). The one genuinely unwritten obligation is the missing `climconv` —
`limPoint` (L255) converges to a Cauchy `S` — a finite `Nat`-arithmetic 3ε/freeze-eventually-stops
argument, ∅-axiom; the only price of the names route is representation-dependence (the modulus is
part of the input), which the repo has already isolated and proven invariant on the cut
(`completability_is_intensional`).

File: `research-notes/frontiers/wall_computable.md`
