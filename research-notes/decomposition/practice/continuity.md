# Decomposition: continuity / topology (open sets, limits)

*213-decomposition of continuity, the open set, and the limit point, per `../README.md`.*
*Directly continues `practice/derivative.md` — that note showed `L` carries a **resolution**
parameter (step-1 vs. modulus). This note tests the hypothesis that **topology is the calculus
of which readings survive the resolution dial**: continuity = the resolution-parameter promoted
to a condition.*

## The decomposition

- **Construction `C`** — the **dyadic refinement tree**: a point is not a primitive, it is a
  *bracket-pointing* — a `DyadicBracket` `[numA/2^e, numB/2^e]` that narrows as the exponent `e`
  grows. The "space" is the construction of these nested brackets; a point is the residue of a
  refinement sequence, never a held object (this is the `Real213` cut: a `Nat → Nat → Bool`
  membership function read at every depth, with completeness almost trivial because the cut *is*
  the sequence — `CauchyComplete.lean:44` `CauchyCutSeq.limit`). A function `f` is, exactly as in
  `derivative.md`, a reading-over-a-construction: a value (itself a bracket-pointing) hung at each
  input bracket. Nothing "topological" has entered — only "a narrowing value at each narrowing
  input".

- **Reading `L`** — the **resolution-reading promoted to a comparison**: read `C` at depth `k`,
  i.e. project the bracket-tree to "agreement up to `1/2^k`". This is *the same resolution dial*
  `derivative.md` put on `L₋`, now used not to take a difference but to *compare two readings*:
  do `x` and `y` agree at depth `k`? In Lean this comparison is `MetricModulus.close k x y`
  (`UniformLimitContinuous.lean:51` `MetricModulus`; `closeN` at `:287`). Continuity is the
  **condition that this reading commutes with refinement**: refining the *output* resolution to
  `k` is forced by refining the *input* resolution to `ω k`. That forcing function `ω : Nat → Nat`
  is the whole content — `ContinuousWithModulus MD MV f ω := ∀ m x y, MD.close (ω m) x y →
  MV.close m (f x) (f y)` (`UniformLimitContinuous.lean:98`). The bare data is
  `Topology.Continuity.IsContinuousModulus` (`Continuity.lean:28`): a `modulus : Nat → Nat` with
  `modulus_pos : ∀ k, modulus k ≥ k`. **There is no ε, no δ, no ℝ⁺ — continuity *is* the modulus,
  the resolution-dial made into a Nat→Nat refinement law.**

  - An **open set** is then this reading's *fibre stable under refinement*: a region you can keep
    refining and never leave. 213 builds it as `DyadicOpen := List DyadicBracket`
    (`DyadicOpen.lean:28`) — a finite union of brackets, finite *by construction*
    (`dyadic_open_finite`, `DyadicOpen.lean:64`); size is additive under union (`size_union`,
    `:54`). "Open" is exactly "a list of refinement-stable brackets", and compactness is automatic
    because the cover already *is* a finite `List` (Heine–Borel trivial, per `INDEX.md`).
  - A **limit point** is the **residue of a refinement sequence**: the bracket-pointing that no
    finite depth reaches but the modulus narrows to — the `Real213` cut itself. "The limit is
    never the operand; the modulus is" (`derivative.md`; CLAUDE.md "Limit/infinity deified").

- **Residue** — what the resolution-comparison reading forces but cannot capture. The limit point:
  reached by no finite depth `k`, only narrowed by `ω`. The Bishop move makes this honest — the
  modulus is carried *as data* (`HasModulus.lean:38` `structure HasModulus … N : Nat → Nat → Nat`;
  `isOrderCauchy_of_hasModulus`, `:44`), bypassing the LEM-bound `∀(m,k) ∃N` closure. So "the
  point at the limit" is the residue of the comparison-reading, and 213 computes only with its
  finite signature `N`/`ω`, never the limit.

## Re-seeing

```
   x close at depth k   =  ⟨ bracket-tree (refinement of C) | L_res = "agree up to 1/2^k" ⟩
   continuity of f      =  the CONDITION  ⟨C | L_res⟩ commutes with refinement:
                              MD.close (ω m) x y  →  MV.close m (f x) (f y)
                              (operand = the modulus ω : Nat → Nat, never "the limit")
   open set             =  L_res's refinement-stable fibre  =  List DyadicBracket (finite)
   limit point          =  Residue(L_res) = the refinement sequence's residue = the Real213 cut
   compactness          =  the cover IS a finite List → finite subcover is rfl
```

So continuity, openness and the limit point are **one reading at work** — the resolution-dial
`L_res` of `derivative.md`, here used to *compare* rather than *difference*. Continuity is that
dial turned into a law (`ω` commuting refinement); an open set is the dial's stable fibre; a limit
point is the dial's residue. Topology is the study of *which readings survive the dial* — exactly
the hypothesis under test.

## Revelation (collapse + residue-surfaced, with one honest conceptual leg)

The collapse is **continuity = the resolution-parameter made into a condition**, and it is
Lean-real on the structural side: the *same* `Nat → Nat` modulus object carries continuity
(`IsContinuousModulus`, `Continuity.lean:28`), the uniform-limit theorem's `ω`
(`ContinuousWithModulus`, `UniformLimitContinuous.lean:98`), the derivative
(`derivative.md`'s `DifferentiableAt.modulus`), Ricci flow, BracketCauchy and the α_em ζ-modulus
— unified at theorem level by `ModulusStructure.four_way_modulus_framework`
(`ModulusStructure.lean:185`) over one `IsModulusStructure` (`:55`). That is the payoff the
README demands: **continuity is not a new analytic primitive added on top of the points; it is the
resolution-dial of the derivative-note, re-aimed from differencing to comparison, and frozen into
the commutation law `MD.close (ω m) → MV.close m`.** "Open" collapses to a refinement-stable
finite bracket-list (`DyadicOpen`, no σ-algebra/Choice), and "limit point" is *surfaced as the
residue* of a refinement sequence — the `Real213` cut — computed by its finite modulus `N`
(`HasModulus`), never grasped (the "Limit/infinity deified" failure stated positively). **Honest
gap:** the bridge from the *modulus condition* to *open-set / limit-point as fibre/residue of that
same condition* is argued conceptually here — Lean has each piece (modulus continuity, `DyadicOpen`
fibres, cut-residue) as separate ∅-axiom facts, but there is **no single theorem** stating
"`f` continuous ⟺ preimage of every `DyadicOpen` is `DyadicOpen`". That equivalence is the
conceptual-only leg.

## Lean grounding — which legs are certified, which are conceptual (honest)

**Certified (verified to exist; docstrings / INDEX assert ∅-axiom — `Topology/INDEX.md`:
"62 atomic facts, all `#print axioms` ∅"):**

- *Continuity = a Nat→Nat modulus (no ε/δ).* `Topology/Continuity.lean:28`
  `structure IsContinuousModulus … modulus : Nat → Nat, modulus_pos`; `idContinuous` (`:37`),
  `constContinuous` (`:47`), `composeContinuous` (`:56`) with `compose_modulus_eq` (`:64`):
  modulus composes by sequential refinement `δ_g ∘ δ_f`. This is the core "resolution dial = a
  condition" claim, machine-level.
- *Continuity commutes-with-refinement, full statement + a real theorem.*
  `Analysis/UniformLimitContinuous.lean:98` `def ContinuousWithModulus … ∀ m x y, MD.close (ω m)
  x y → MV.close m (f x) (f y)`; `:136` `theorem uniform_limit_continuous` (the constructive 3ε
  theorem: limit of uniformly-continuous functions is continuous with *computed* modulus
  `Ω m = ω_(r(m+2))(m+2)`); `:380` `id_continuousWithModulus`. **This is the strongest anchor** —
  the commutation law is a proved theorem, not a definition only.
- *Modulus arithmetic.* `Topology/ContinuityArith.lean:27` `sumModulus`/`:37` `productModulus`,
  `sumModulus_pos` (`:45`), `productModulus_pos` (`:51`) — `f+g`, `f·g` stay continuous; modulus
  algebra is pure Nat.
- *Open set = finite bracket union (no σ-algebra/Choice).* `Topology/DyadicOpen.lean:28`
  `DyadicOpen := List DyadicBracket`; `dyadic_open_finite` (`:64`); `size_union` (`:54`).
- *Limit point = residue of a refinement sequence; cut-completeness almost trivial.*
  `Analysis/CauchyComplete.lean:44` `CauchyCutSeq.limit`, `:48` `CauchyCutSeq.limit_eq_at`.
  Banach fixpoint with computed (not assumed-completeness) modulus: `BanachFixedPoint.lean:202`
  `banach_fixed_point`, `:250` `banach_unique`.
- *Modulus carried as data (Bishop), bypassing LEM — the finite generator of the residue.*
  `Analysis/Modulus/HasModulus.lean:38` `structure HasModulus … N : Nat → Nat → Nat`;
  `isOrderCauchy_of_hasModulus` (`:44`).
- *The 4-way modulus unification (the collapse certificate).*
  `Topology/ModulusStructure.lean:55` `IsModulusStructure`; `:185`
  `four_way_modulus_framework` (continuity ∧ Ricci ∧ BracketCauchy ∧ α_em-ζ share one
  `Nat → Nat`). `:139` `three_way_modulus_framework`.
- *Connectedness = finite-list adjacency.* `Topology/Connectedness.lean:36` `Chain`,
  `chain_finite` (`:65`), `chain_self_iff_degenerate` (`:54`).

**Conceptual-only (honest — Lean is thin or absent here):**

- *Continuity ⟺ preimage-of-open-is-open.* The classical topological *definition* of continuity
  (preimage of every open is open) is **not** stated as a theorem against `IsContinuousModulus`
  and `DyadicOpen`. 213 has both objects ∅-axiom-clean and *separately*; the equivalence that
  would make "open set = the stable fibre of the continuity reading" a proved collapse is **not in
  Lean**. This is the load-bearing conceptual leg of the Revelation.
- *`IsContinuousModulus` is partly declarative.* Its docstring (`Continuity.lean:32–34`) states
  the pointwise witness "deferred to a per-cut equality witness" — the structure carries
  `modulus` + `modulus_pos` but the full `close (ω k) → close k` law lives in the *Analysis*
  file (`ContinuousWithModulus`), not the *Topology* one. The two are the same data
  (INDEX: "same data as `IsSmooth.linearityModulus`") but not yet welded by a Lean lemma; the
  weld is asserted in prose, not proved.
- *Limit-point-as-residue and open-fibre-as-residue.* That a *limit point* is precisely
  `Residue(L_res)` and an *open set* precisely `L_res`'s refinement-stable fibre is the
  decomposition's reading; Lean certifies the cut/limit object and the `DyadicOpen` object, not
  their identification *as residue/fibre of the continuity reading*. Conceptual framing on
  verified objects.

So the **modulus-as-the-content-of-continuity leg is fully Lean-certified** (structure +
composition + the proved uniform-limit commutation theorem + 4-way unification); **open sets,
limit points, connectedness, compactness each exist ∅-axiom-clean**; the **bridge that fuses them
into one reading** (continuity ⟺ open-preimage; open = fibre; limit = residue *of the same dial*)
is **conceptual-only**. Stated honestly: 213 proves *continuity is a Nat→Nat resolution modulus*
and proves *the limit of continuous functions stays continuous with a computed modulus*; it has
the open set and the limit-point cut as clean separate objects; it does **not yet** have the
single theorem welding "resolution-stable reading" to "open / continuous / limit" as one.

> Axiom-purity note: cited files' docstrings + `Topology/INDEX.md` assert ∅-axiom
> ("62 atomic facts, all `#print axioms` ∅"). I did not re-run `tools/scan_axioms.py` in this
> environment; the purity claim rests on the in-file docstrings + INDEX, not a fresh scan.

## Note for the technique — does this promote 'resolution' to L's central parameter?

**Yes — decisively, and it is now Lean-anchored as a *cross-domain* parameter, not a one-note
trick.** `derivative.md` introduced `resolution` on a *single* reading (`L₋` at step-1 vs.
modulus). Continuity shows the parameter is **the organizing axis of an entire discipline**:
topology *is* the calculus of resolution-stability. The dial appears three ways at once:

| Use of the resolution dial `L_res` | 213 object | Lean anchor |
|---|---|---|
| compare two readings at depth `k` | `MetricModulus.close k` | `UniformLimitContinuous.lean:51` |
| **dial commutes with refinement** (condition) | continuity `ω` | `Continuity.lean:28`, `UniformLimitContinuous.lean:98,136` |
| dial's **stable fibre** | open set `DyadicOpen` | `DyadicOpen.lean:28` |
| dial's **residue** | limit point / `Real213` cut | `CauchyComplete.lean:44`, `HasModulus.lean:38` |

The shape-refinement the README should record: **`resolution` is not just a parameter *on* a
reading — it is the parameter whose three derived questions ("does it commute?", "what's the
stable fibre?", "what's the residue?") *are* the three primitives of topology** (continuous map,
open set, limit point). And the `four_way_modulus_framework` theorem
(`ModulusStructure.lean:185`) is the strongest existing evidence that this is real and not
re-skin: the *same* `Nat → Nat` modulus object is proved to carry continuity, the derivative's
resolution, Ricci flow, and the α_em ζ-convergence — one dial, four domains. The honest caveat
for the technique: 213 has elevated *continuity-as-modulus* to theorem and *unified the modulus
across domains*, but has **not** elevated the *open-preimage characterization* — so the claim
"topology = the calculus of resolution-stability" is **certified at the modulus/continuity core
and conceptual at the open-set/preimage perimeter.** That perimeter is the next fresh
decomposition target (a Lean `continuous_iff_preimage_dyadicopen` would close it).
