# G174 — π as the continuous-symmetry image of the residue (φ/π two-faces conjecture)

**Tier 1 (volatile, conceptual).**  A 213-native ontology thread off the π-non-holonomicity
marathon (`G170`, `G173`).  Originating intuition (Mingu Jeong, 2026-06): *"π는 단위(원) 그
자체 — 어떤 코도메인에서 봐도 축을 이루는 그 자체이자 축 그 자체. 도달 불가능이 당연.
잔여 그 자체가 π 아닐런지."*  This note tests it against the framework, keeps the defensible
core, and flags the one category error.

**Status: conceptual conjecture, NOT a theorem.**  No ∅-axiom claim is made here beyond the
already-proven anchors it cross-references.

## The claim, decomposed

1. π is "the axis itself" — in any codomain the axis-forming-thing and the axis.
2. π's unreachability (transcendence; conjectured CF non-holonomicity) is therefore natural.
3. π *is* the residue (잔여) itself.

## What survives the test (1 + 2)

The residue's defining property is **non-surjectability**: it is outside the image of *every*
view (`Lens.FlatOntologyClosure.object1_not_surjective`, `self_covering_closure` — `G152`).
Naming the ceiling is a diagonalisation, and **diagonalisation IS the residue's signature
operation** (`ResolutionLimit.cantor_general`; `DepthCeilingResidue` ties it to the depth
ladder).

π's frontier is the CF-Lens shadow of exactly this:

  - **Transcendence** (Lindemann, cited): no *algebraic* Lens captures π.
  - **Non-holonomicity** (conjectured; the genuine tier now ∅-axiom-inhabited by `(n!)ⁿ` in
    `NonHolonomicWitness`, with π conjectured to share it): no *P-recursive* Lens captures π's
    CF.

So "π escapes every finite/discrete reading" is the *Lens-level reflection* of "the residue is
outside every view's image."  Claims (1)+(2) are structurally sound: π sits at the
maximal-non-closure pole, the diagonalisation pole — as residue-*like* as a Lens output gets.

## Where it must stop (3) — the "View promoted to identity" failure mode

CLAUDE.md failure catalog: *declaring one reading what the residue IS* is a failure mode.

  - The residue is **가리킴 이전** (`G29`) — pre-Lens, not a number.
  - π is **already a Lens output**: the ratio/measure-Lens reading of perfect rotational
    symmetry (the circle).  π is a number.

"π = 잔여" promotes the continuous-symmetry Lens to the residue's identity, contradicting
`object1_not_surjective` (the residue is outside *every* view, including the ratio-Lens whose
output is π).  So the honest form is **π = the residue's image under the continuous-symmetry
Lens**, not π = the residue.

## The refined form — φ and π are two faces of the residue's self-reference

`05_no_exterior.md` §5.2 (Nat-style / Bool-style self-reference) and §5.7 (frozen / dynamic)
already carry two structurally-distinct forms of the *same* self-reference.  φ and π are their
Lens-images:

| | φ | π |
|---|---|---|
| self-reference form | **fixed point** (Nat-style / Lambek): `P(φ)=φ` converges | **period / return** (Bool-adjacent): the closing constant of rotation; no fixed point |
| §5.7 reading | frozen (settles) | dynamic (returns) |
| CF role | regularity **floor** (`LagrangeExtremes`: all-1s, `QuasiPolyCF 1`, `√5` Lagrange min) | regularity **pole** (non-holonomic, conjectured) |
| repo entry path | self-reference fixed point (`Mobius213`, `P(x)=(2x+1)/(x+1)`) | **rotation/symmetry only** — `crystallographic_cosines` (`2cos(2πk/6)`), `ModularElliptic` elliptic orders `{4,6}`, DRLT `δ = π/φ²` |

**The repo already enacts the intuition.**  In the codebase π enters *only* through the
rotation/symmetry axis (roots of unity, Eisenstein `ztrace`, elliptic orders, the CKM phase) —
never as an object reached by a CF/recurrence Lens.  φ enters through the self-reference fixed
point and is the CF regularity floor.  Neither is the residue; each is one self-reference face.

## The genuine pushback — "어떤 코도메인에서 봐도" is conditional

Tested: π is the axis of **archimedean / continuous-symmetry** codomains (`U(1)`, `SO(2)`,
period `2πi` of `exp`).  In purely **discrete / p-adic** codomains the rotational π does not
appear the same way.  By the repo's own evidence the *more* codomain-universal residue-image is
**φ** — it recurs in the discrete algebra tower (Moufang-failure rate `1 − ½·φ^{-rank}`,
exact over `ℤ[√5]`), in physics constants, *and* in self-reference.  π is universal across
**continuous-symmetry** codomains specifically — which is exactly π's reign, so the intuition
holds *within its proper domain* and overreaches outside it.

## Conjecture C-π1 (the corrected statement)

> π is **the residue's image under the continuous-rotational-symmetry Lens**.  Its escape from
> every discrete/algebraic/P-recursive Lens (transcendence; conjectured non-holonomicity) is
> the *in-Lens reflection* of the residue's non-surjectability (`object1_not_surjective`) — a
> diagonalisation, the residue's signature operation.  π is **not** the residue (the residue is
> outside every view, π included); π and φ are the **period** and **fixed-point** faces of the
> one self-reference, neither of which is the residue itself.

Corollary (why π's non-holonomicity is hard *and* expected): the residue is, by construction,
not the limit of any finite reading; a faithful continuous-symmetry image should inherit that
non-closure.  But this is a *reason to expect* the result, not a proof — and crucially it does
**not** route through growth (π's partial quotients are not super-factorial; `(n!)ⁿ` is, which
is why `(n!)ⁿ` is reachable ∅-axiom and π is not — `G173` C11).  The residue-image reading
predicts the obstruction is *shape* (FGS-type diagonalisation), not *size*.

## Refinement (Mingu, 2026-06): "π = φ seen through the continuous-codomain Lens"

Stronger and *more precise* than the original — and it survives the test, because φ and π
**cannot** be algebraically related (φ degree 2, π transcendental), so the only possible bridge
IS a continuous Lens.  The bridge is concrete and classical:

  - **`φ = 2cos(π/5)`** (decagon) and **`2cos(2π/5) = 1/φ = φ−1`** (pentagon).  The cosine =
    the trace of a rotation = the continuous-symmetry Lens.  So the golden ratio literally *is*
    the continuous-rotation Lens read on the (crystallographically forbidden) 5-fold axis.
  - Inverting gives a genuine **φ → π computation**: `π = 5·arccos(φ/2) = 5·∫_{φ/2}^1 dt/√(1−t²)`
    — the arc-length (continuous) Lens of the algebraic point `φ/2` yields `π/5`.
  - Golden→π also appears via **Fibonacci/Lucas Machin-type arctan identities**
    (`π/4 = Σ arctan(1/F_{2k+1})`, telescoping the Fibonacci arctan addition law) — π assembled
    from the golden (Fibonacci) sequence through the arctan (continuous) Lens.

**Honest tempering (falsifiability discipline).**  As a *computation of π* this is real but
**elementary and known**, not a fast/novel algorithm: `arccos`/`arctan`/arc-length are
precisely where π is "already" injected (they are the continuous Lens), so the value is
*conceptual unification* — π is the continuous-Lens image of φ — **not** algorithmic novelty.
Do not sell "a new way to compute π."  What is genuinely new is the *213 reading*: π is the
period/elliptic face and φ the fixed-point/hyperbolic face of one self-reference, related by the
continuous Lens (cosine / Wick rotation `cos(iθ)=cosh θ`), with the φ↔π split = the
hyperbolic↔elliptic conjugacy split in `SL(2,ℝ)` (golden Möbius `[[2,1],[1,1]]` hyperbolic,
`ModularElliptic` orders `{4,6}` elliptic).

**New ∅-axiom anchor** (`Real213/PentagonGoldenTrace.lean`, 4 PURE): the algebraic skeleton of
`φ = 2cos(π/5)`.  In `ℤ[φ]`: `phi_quad` (`φ²=φ+1`), `pentagon_trace_quad`
(`(φ−1)²+(φ−1)=1` — the pentagon trace `2cos(2π/5)` is the conjugate golden root),
`pentagon_trace_unit` (`φ·(φ−1)=1` — the pentagon trace is `1/φ`).  This certifies the
*value* the rotation Lens returns on the forbidden 5-axis (φ and `1/φ`); the *angle* `π/5`
(transcendental) is the irreducibly continuous remainder — exactly the boundary the framework
can and cannot cross.

## Conjecture C-π2 (the continuous-Lens bridge)

> The map "fixed-point image ↦ period image" of the residue's self-reference is realised by the
> continuous-rotation Lens: `φ ↦ 2cos⁻¹` / arc-length sends the golden fixed point to `π/5`
> (`φ = 2cos(π/5)`).  φ is the hyperbolic (cosh, `[[2,1],[1,1]]`) face; π the elliptic (cos,
> rotation) face; the Lens between them is Wick rotation `cos(iθ)=cosh θ`.  The φ→π
> "computation" (`π = 5·arccos(φ/2)`, Fibonacci–Lucas arctan series) is the operational shadow
> — real, classical, slow; its content is unification, not a new algorithm.  The
> ∅-axiom-reachable part is the *algebraic value* (`PentagonGoldenTrace`); the transcendental
> angle is the residue's continuous remainder, unreachable by any discrete Lens (which is, once
> more, `object1_not_surjective` in the rotation Lens).

## ∅-axiom anchors (already proven; this note adds no new Lean beyond `PentagonGoldenTrace`)

  - `Mobius213` — `P(φ)=φ`, the self-reference fixed point (φ face).
  - `CayleyDickson/Integer/ImaginaryQuadraticUnitTrichotomy.crystallographic_cosines` —
    `2cos(2πk/6)`; `Real213/ModularElliptic` — elliptic orders `{4,6}` (π / rotation face).
  - `Real213/LagrangeExtremes` — φ floor / π pole, the two CF poles, already side by side.
  - `Cauchy/NonHolonomicWitness.superFact_nonHolonomic` — the genuine non-holonomic tier
    (the pole is now an inhabited tier, with π conjectured to share it).
  - `Lens.FlatOntologyClosure.{object1_not_surjective, self_covering_closure}`,
    `ResolutionLimit.cantor_general` — residue = outside every view = diagonalisation.
  - `Real213/PentagonGoldenTrace.{phi_quad, pentagon_trace_quad, pentagon_trace_unit}` —
    the golden value of the forbidden 5-fold rotational trace (`φ = 2cos(π/5)` algebraic
    skeleton); the φ-half of the φ↔π continuous-Lens bridge, ∅-axiom.
