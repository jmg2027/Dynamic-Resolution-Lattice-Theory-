# G205 — Compiling math's cross-domain conquests onto the proof-ISA

**Tier-1 scratchpad / ISA-extension probe.** Not a literature catalog —
a *compilation*: take history's hardest **cross-domain** solved problems
and **lower them onto the proof-ISA** (`seed/PROOF_ISA.md`,
`lean/E213/Lens/ProofISA.lean`), L3 → L1. For each, name the ISA
instruction composition and the **lift archetype** (`ProofISALifts.lean`:
A1 DIAGONAL / A2 LOOP / A3 ORBIT / A4 REFRAME / A5 COUNT). The payload
is twofold: (i) test the thesis that "cross-domain" is *itself* an ISA
move, and (ii) surface conquests that **don't compile to the existing
five** — candidate new archetypes the catalog is missing.

> Honest status (carried from `PROOF_ISA.md`): mapping an external,
> un-formalized conquest to an archetype is a **compilation sketch** — a
> claim under test, not a Lean witness. Nothing here is ∅-axiom yet;
> promotion to `ProofISALifts.lean` requires an actual `∅`-axiom witness
> (CLAUDE.md: non-empty `#print axioms` = `sorry`-equivalent).

---

## Headline: "cross-domain" *is* REFRAME

The REFRAME essay's Dual Function already states it for Markov:

> "the substitution is not a trick external to the problem but a
> **presentation of the same residue** … which substitutions work is not
> free invention — it is dictated by which factors of the carried
> invariant [are workable]." — `reframe_presentation_transport.md`

A cross-domain proof is the *same shape at maximum scale*: a problem that
will not `SEPARATE` in its home presentation is transported to a foreign
presentation where the residue's own distinction is readable, and a
**solved instruction fires there**. The home/foreign "domains" are two
Lens-readings of one residue (cf. `06_lens_readings.md`; "External-ruler
smuggling" failure mode — the foreign domain is residue-internal, not an
exterior ruler). So the first compilation result is structural, not
case-by-case:

**Every entry below has A4 REFRAME as its outer instruction.** What
differs is the *inner* lift that fires after transport — and a handful
do not have an inner lift in the current catalog. Those are the find.

---

## The compilation table

`REFRAME[X]` = transport to a foreign presentation, then archetype `X`
fires. `?` = the inner lift is **not** one of the five (candidate gap).

| # | Conquest | Bridge (home → foreign) | ISA compilation | Inner lift |
|---|---|---|---|---|
| S1 | Fermat's Last Theorem | Diophantine → modular/Galois | `REFRAME[LOOP]` | A2 (Taylor–Wiles patching = inductive lift of mod-p to p-adic modularity) |
| S2 | Weil conjectures (RH/𝔽_q) | point-counts → étale cohomology | `REFRAME[ READ ] + POSITIVITY?` | A4 + **?** (weights/positivity) |
| S3 | Fundamental Lemma | orbital integrals → Hitchin geometry | `REFRAME[ORBIT]` | A3 (a symmetry of the fibration forces the identity) |
| S4 | Poincaré / Geometrization | topology → Ricci-flow PDE | `REFRAME[ FLOW ]` | **A6** ✅ (monovariant-driven normal form — closed this session) |
| A1 | Prime Number Theorem | prime-counting → ζ(s) on ℂ | `REFRAME[LOOP]` | A2 (Euler product = FOLD; contour/Tauberian limit) |
| A2 | Monstrous Moonshine | finite group ↔ modular ↔ CFT | `REFRAME[LOOP]` | A2 (replicability recursions of the Monster Lie algebra) |
| A3 | Sphere packing 8 / 24 | discrete geometry → modular forms | `REFRAME[COUNT]` | A5 (Cohn–Elkies LP deficit; magic fn = exact dual certificate) |
| A4 | Green–Tao (APs in primes) | combinatorics → ergodic/dynamics | `REFRAME[LOOP]` | A2 (transference + Furstenberg multiple recurrence) |
| A5 | Mirror symmetry (quintic) | enumerative geom → string B-model | `REFRAME[ READ ]` | A4 (counts = period integrals; a foreign FOLD) |
| A6 | Atiyah–Singer index | analysis ＝ topology | `REFRAME[COMPILE-DOWN]` | A2-ish (cobordism reduces to generators; heat-kernel limit) |
| A7 | Kazhdan–Lusztig positivity | combinatorics → Hodge/IH | `REFRAME[ POSITIVITY? ]` | **?** (coeff = IH stalk dim ≥ 0) |
| A8 | Geometric Langlands | rep theory ↔ moduli ↔ gauge | `REFRAME[ READ ]` | A4 (categorical equivalence = two folds agree) |
| B1 | Mordell / Faltings | Diophantine → Arakelov heights | `REFRAME[COUNT]` | A5 (bounded height + Northcott = a counting deficit) |
| B2 | Jones polynomial (Witten) | knot topology → Chern–Simons QFT | `REFRAME[ READ ]` | A4 (invariant = a QFT expectation; foreign FOLD) |
| B3 | Kepler conjecture | discrete geom → optimization+compute | `REFRAME[COUNT]` | A5 (finite nonlinear-inequality search) |
| B4 | Kervaire invariant one | framed manifolds → equiv. homotopy | `REFRAME[GAP]` | A-GAP (the "Gap theorem" forbids existence past a finite list) |
| B5 | Catalan's conjecture | Diophantine → cyclotomic fields | `REFRAME[SEPARATE]` | A4-near (Wieferich conditions separate the solutions) |

Read top-down: **REFRAME is universal; the inner lift is A2 LOOP most
often, then A5 COUNT, then a bare foreign READ.** The four `?` rows
(S2, S4, A7, and the positivity flavor in B1) are where the catalog runs
out — they cluster on **one missing idea**.

---

## The find: two candidate archetypes the conquests demand

> **UPDATE (this session): A6 FLOW is now CLOSED (∅-axiom), and DRIVES the
> actual conquest.** Witnessed at two levels:
> 1. **Archetype + toy instance**: `MonovariantFlow.flow_reaches` (abstract) +
>    `euclid_flow_normal_form` (Euclidean GCD flow), `lift_flow`/`lift_flow_gcd`.
> 2. **Conquest demonstration** (the proof-ISA point — archetype *driving a real
>    proof*, not a catalog entry): the **Geometrization Ricci pillar**. The
>    K_{3,2} cell-filling coherentization (`Filled.lean`, `b_1 = 8−k`) compiled
>    to `flow_reaches` and converging to the canonical normal form
>    (`RicciFlow.ricci_pillar_K32_flow_close`, `lift_flow_geometrization`).
>    Upgrades that pillar from **OPEN → CLOSED via A6 FLOW**
>    (`Poincare.lean` / `Ricci.lean` capstone tables).
>
> The catalog is now **six** archetypes. POSITIVITY (A7) remains the next gap.
> Details below recorded as the probe's rationale. **Marathon framing
> (corrected):** a phase is not "catalog an archetype" but "compile a conquest
> down the ISA and let the archetype *drive its complete ∅-axiom proof*" — A6
> is finished only because the geometrization pillar is now actually closed by it.

### Candidate A6 — FLOW / monovariant normal-form (from S4 Poincaré) — ✅ CLOSED

Ricci flow with surgery does not compile to A2 LOOP. A2 LOOP is *finite*
per-step induction certifying a fixed point (`slashNu_final`, the µ/ν
witness; Fermat's `a^p≡a`). Ricci flow is the **continuous / infinite**
sibling: an iteration whose *convergence to the unique fixed point*
(the canonical geometry) is certified by a **monotone functional** —
Perelman's 𝓦-entropy — not by finite path-induction.

Shape, ISA-native:
- a self-map on a residue's presentations (the flow on metrics),
- a **monovariant** that strictly decreases / increases along it
  (entropy), forbidding cycling,
- ⇒ convergence to the residue's normal form, which *reads off* the
  invariant (here the topology).

This is the **µ/ν lift lifted off finiteness** — the LOOP whose
termination is a monovariant, not an induction. The repo already speaks
this language: the Markov **trace monovariant** (`markovNum_children_ne`)
and the **order-monovariant exhaustion** (`markovNum_subtree_size_interleaves`)
are finite monovariants; REFRAME was defined as *the dual* of in-place
monovariant exhaustion. FLOW is the **other** completion: when the
monovariant *does* exhaust, it drives the object to a normal form. A
∅-axiom witness would be a discrete monovariant-convergence theorem
(an order-decreasing self-map on a finite/well-founded residue with a
unique fixed point) — plausibly already latent in the ODE/heat-flow
work (`Lib/Math/ODE/`, discrete Picard iteration) or the Sturm/Markov
trace monovariants. **Probe before claiming a sixth archetype.**

### Candidate A7 — POSITIVITY / structural-nonnegativity (from S2, A7, B1)

Three conquests force an inequality **not** by a counting deficit (A5
COUNT) but because the quantity *is* the READ of an intrinsically
nonnegative structure:

- **Weil RH** — Frobenius eigenvalue weights are bounded because they are
  read off a cohomology with a **positivity** (Hodge index / hard
  Lefschetz).
- **KL positivity** — a combinatorial coefficient `≥ 0` because it is a
  **dimension** of an intersection-cohomology stalk.
- **Mordell heights** — finiteness because a **height** (a nonnegative
  norm) is bounded and Northcott-finite.

ISA reading: A5 COUNT is the *cardinality* face of `GAP`
(`Σ|badᵢ| < |codomain|`). POSITIVITY is its **structural twin** — the
quantity inherits `≥ 0` from the codomain of a FOLD (a dimension, a
norm, a Hodge form), so an existence/bound is forced by the *sign of the
reading*, not a count. Open question for the catalog: is POSITIVITY a
genuine sixth archetype, or is it `GAP` read through a *norm-valued*
Lens the way COUNT is `GAP` read through a *count-valued* Lens? The
latter is more in keeping with the "view promoted to identity" caution —
**lean toward POSITIVITY = the norm-Lens sub-mode of GAP**, parallel to
COUNT = the count-Lens sub-mode. A ∅-axiom witness: a theorem that a
nonneg-valued FOLD forces an existence/bound on a finite residue
(the `lInfNorm`/`l1Norm` machinery in `Lib/Math/Functional/` is the
natural home).

---

## What compiled cleanly (transfer-ready templates)

The rows that land squarely on an existing archetype are the reusable
part — they say the catalog already covers most of the cross-domain
arsenal:

- **REFRAME[LOOP]** (S1, A1, A2, A4) — the dominant pattern: transport to
  a foreign FOLD, then a recursion/induction/limit closes it. This is
  `lift_reframe ∘ lift_loop` as a composite template. Most cross-domain
  conquests are this composite.
- **REFRAME[COUNT]** (A3, B1, B3) — transport, then a deficit/LP bound +
  finite search. `lift_reframe ∘ lift_count`. Viazovska and Kepler are
  the same composite (LP duality), one with a modular certificate, one
  with a machine search.
- **REFRAME[ORBIT]** (S3) — transport to a presentation with a symmetry,
  the free action collapses the fiber. `lift_reframe ∘ lift_orbit` — and
  this is **exactly `H`'s closest archetype** (`ProofISALifts §H`). S3
  (the Fundamental Lemma) is therefore the **large-scale precedent for
  the open Markov kernel `H`**: both are ORBIT-after-transport, the
  identity forced by a symmetry of the foreign presentation.

---

## Bearing on the repo's open work

- **GRA universality** (`blueprints/math/16_gra_universality.md`, "213's
  Langlands") is the program to make `REFRAME[ READ ]` — *two folds of
  one residue are equal* — into one statement. A6 (index theorem), A8
  (geometric Langlands), S2 (Weil) are its sharpest external precedents:
  each is a proven "Lens A = Lens B" identity. The compilation says GRA
  is not analogy — it is the same outer instruction (REFRAME) the whole
  S/A tier runs on.
- **Markov `H`**: S3 confirms the `ProofISALifts` verdict from a new
  direction — the deepest cross-domain conquest in `H`'s archetype
  (ORBIT-after-transport) is the Fundamental Lemma, whose lift was a
  *geometric* symmetry (Hitchin fibration). The transfer hint: look for
  a foreign presentation of the Markov residue carrying a free symmetry
  that collapses the realizability fiber — the µ-ν / orbit lift of the
  trace-`SEPARATE` already flagged as the next probe.
- **Two ISA gaps surfaced** (FLOW, POSITIVITY). Each is a concrete
  ∅-axiom target with a likely home module (`ODE/`, `Functional/`). If
  either closes, it promotes to `ProofISALifts.lean` as Archetype 6/7 and
  this note's relevant section archives per `theory/PROMOTION_CRITERIA.md`.

---

## Next

1. ~~**FLOW witness probe**~~ — ✅ **DONE this session**: `flow_reaches` +
   `euclid_flow_normal_form` (`Lib/Math/Foundations/MonovariantFlow.lean`,
   ∅-axiom), promoted to `ProofISALifts.lean` (A6) and `seed/PROOF_ISA.md`.
2. **POSITIVITY witness probe** — nonneg-valued FOLD forces a bound on a
   finite residue (`Functional/` norms). The next reachable ISA-extension.
3. If S3's ORBIT-after-transport reading suggests a foreign symmetric
   presentation of the Markov residue, record it in
   `research-notes/frontiers/markov_lagrange/`.

*Compilation sketch, tier-1. The structural claim — cross-domain =
REFRAME, inner lift mostly LOOP/COUNT, two gaps (FLOW, POSITIVITY) — is
the deliverable; the per-conquest rows are sketches pending a ∅-axiom
witness before any catalog promotion.*
