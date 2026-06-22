# Decomposition: Lie theory (the bracket, the Lie algebra, exp: 𝔤→G, Jacobi)

*213-decomposition per `../README.md` (model v7.1). A **fresh** field. Tests four hypotheses at once:
the **Lie bracket** `[X,Y]=XY−YX` is the **q=±1 antisymmetry residue** of `groups.md`'s Aut-family
(the same sign-fold as `homology.md`'s ∂ and the determinant's alternating sign); **exp: 𝔤→G** is
`exponential.md`'s **×↦+ character arrow** run between the algebra (+) and the group (×); the **Jacobi
identity** is a **∂²=0-flavoured cyclic cancellation** (the same q=±1 sign-cancellation as `homology.md`);
and **so(n)/su(n) + the Killing form** are `groups.md`'s Aut-families of bilinear forms read through
`representation.md`'s trace. The bar is PREDICTION/REVELATION. Lie theory is the candidate **consolidation
of groups.md + exponential.md + homology.md** under the two standing invariants.*

## The decomposition (C / Reading / Residue)

- **Construction `C` — `groups.md`'s Aut-family, frozen at the identity.** A Lie group is a group
  (`groups.md`: `⟨ C₀ | the closed family of C₀-preserving self-readings, under ∘ ⟩`, concretely the
  unimodular matrices — the repo's `Mat2` with `det = 1`, the Stern–Brocot/modular `⟨L, R, S, U⟩`
  generators). The Lie *algebra* introduces **no new construction**: it is the **tangent reading of that
  family at the identity** — the first-order part of `M = I + εX`. In the repo's discrete `Mat2` setting
  the would-be `ε` is **not separately hosted** (there is no infinitesimal); what *is* hosted, and is the
  honest carrier of the bracket, is the **commutator** of the group multiplication itself:
  `comm(A,B) = AB − BA`, an entrywise `Mat2` operation on the existing `mul` (`HyperbolicEllipticTrace.mul`)
  and `Int` subtraction. So `C` = the same `Mat2` ×-construction of `determinant.md`/`curvature.md`, read
  through its **non-commutativity at the identity** rather than along a tree (`groups.md`) or a loop
  (`curvature.md`).

- **Reading `L_[,]` (the commutator reading)** — fold a pair of group elements to **how much they fail to
  commute**: `[A,B] = AB − BA`. This is `groups.md`'s composition read **as a difference** — the
  difference-Lens `L₋` of `integers.md` (`m−n`, the directed count-pair) applied to the two composition
  orders `AB` and `BA`. The readout is forced antisymmetric: swapping the operands swaps the two terms,
  flipping the `m−n` sign — **the same pair-swap q=−1 bit** that signs `det`, that flips `homology.md`'s
  face-removal `(−1)^i`, and that builds ℤ's `−` (`integers.md`). So the bracket is **the commutator
  reading of the Aut-family, antisymmetric by the q=−1 tag**, verbatim the hypothesis.

- **Residue** — `q = ±1`, the **escape/converge** tag of `ResidueTag.lean`, here at the *commutator* pole.
  The bracket is the **deficit by which the Aut-family fails to be abelian** — exactly `curvature.md`'s
  holonomy deficit `holonomy[S,S] = −I ≠ I` read infinitesimally: an abelian (flat, `q=+1`) sector has
  `[X,Y] = 0` (the ℕ⁺ tree, `positive_loop_trivial` — commuting transport, no curvature); the non-abelian
  (`q=−1`) sector has `[X,Y] ≠ 0` (the fold `S` admitted, `first_loop_is_the_fold`). The bracket is the
  *same residue as curvature*, one order down: **curvature is the finite loop-deficit, the bracket is its
  infinitesimal/second-order shadow**.

## Re-seeing (⟨C | L⟩)

```
   a Lie algebra      =  ⟨ Aut-family C (= a group, groups.md) | the commutator reading [A,B]=AB−BA ⟩
   the bracket        =  composition read as a DIFFERENCE (integers.md L₋ on the two orders AB, BA)
   "[X,Y] = −[Y,X]"   =  the q=−1 pair-swap bit: operand-swap flips the m−n sign  (comm_antisym, ring_intZ)
   "tr[X,Y] = 0"      =  the bracket lands in the traceless sector — sl, the additive twin  (comm_traceless)
   exp: 𝔤 → G          =  exponential.md's ×↦+ character arrow, the + → × direction  (vp_self_pow / vp_pow)
   "exp linearizes"   =  the algebra (+) is the linearized group (×); BCH is the failure-to-be-hom residue
   Jacobi identity    =  ∂²=0-flavoured cyclic cancellation: ad is a derivation, the loop cancels (q=−1)
   so(n)/su(n)        =  groups.md's Aut-family of a bilinear form, frozen at I (the traceless/antisym sector)
   Killing form       =  representation.md's tr ∘ (ad∘ad): the trace character of the adjoint action
```

Set side by side with `groups.md`, `curvature.md`, and `homology.md`, the Lie bracket is one corner of a
single picture on `C`'s `q=±1` direction axis — the **infinitesimal corner** of the family the other three
read at finite scale:

| reading | what it does to the Aut-family | residue at `q=−1` |
|---|---|---|
| `det` / `psign` character (`groups.md`/`determinant.md`) | a scalar readout of one self-reading | the orientation sign `±1` |
| `∂` boundary (`homology.md`) | the height-axis down, two-step composite | `∂²=0` (signs cancel), residue = homology |
| `L_loop` holonomy (`curvature.md`) | a **loop** composes to a net transition | curvature = `holonomy ≠ I` deficit |
| **`L_[,]` bracket (here)** | **two orders of composition, read as a difference** | **`[X,Y]≠0`** = the non-abelian / curvature shadow |

The bracket is the *infinitesimal* of the holonomy: where `curvature.md` reads a finite loop `[S,S]` and
gets the deficit `−I`, the bracket reads the first-order `AB − BA` and gets the algebra element. **Same
residue, one order down** — and the same q=−1 sign-fold throughout.

## Revelation (collapse + forcing: the bracket = the q=±1 antisymmetry residue; Lie theory consolidates three files)

**Forcing — antisymmetry is the q=−1 pair-swap, not an axiom.** The defining law `[X,Y] = −[Y,X]` is
*not* posited; it **falls out** of "read composition as a difference." `comm(A,B) = AB − BA` and
`comm(B,A) = BA − AB` are the two orders of the `integers.md` difference-Lens, and swapping the operands is
the **same pair-swap** that flips ℤ's sign (`integers.md`), signs the determinant (`determinant.md`), and
gives `homology.md`'s `cup1_antisymmetric` (`e_i∧e_j = −(e_j∧e_i)`). I verified this falls out *generally*
on the repo's `Mat2`: `comm_antisym` (each entry `(comm A B).x = −(comm B A).x`) proves by `ring_intZ` — no
new structure, the antisymmetry is the q=−1 bit acting on the existing `mul`. And the **self-bracket
vanishes** (`comm S S = 0`, `decide`) — the `q=−1` involutive-at-the-diagonal fact, the bracket's
`e_i∧e_i = 0` (the `homology.md` diagonal). So the Lie bracket is **literally `homology.md`'s antisymmetric
wedge / `determinant.md`'s alternating sign, read on the group's two composition orders** — one q=−1 tag,
now a fourth operator (∂, ⋆, ⌣, and now `[,]`).

**Forcing — the bracket lands in the traceless sector (`sl`), the additive twin.** `tr[X,Y] = 0` is not an
extra axiom either: `comm_traceless` proves `(comm A B).a = −(comm A B).d` generally by `ring_intZ`, so the
trace `a+d` of any commutator is zero. This is exactly `representation.md`'s `det`/`tr` split read from the
algebra side: **`det` is the multiplicative `×↦·` character of the *group*; `tr` is the additive `×↦+`
character of the *algebra*** (`tr(X+Y) = tr X + tr Y`), and the bracket is forced into `tr`'s **kernel**
(`sl_n` = traceless). So the Lie algebra is where `representation.md`'s "additive trace-character" finally
*acts* — the bracket is the genuinely-additive structure the multiplicative `det` machinery could not host,
now appearing as the **traceless residue of the commutator**. The `det`/`tr` edge `representation.md` located
is exactly the group/algebra boundary: `det` lives on `G`, `tr` lives on `𝔤`, and `exp` is the bridge.

**Collapse — exp: 𝔤→G is `exponential.md`'s ×↦+ character arrow.** The classical statement "exp turns
addition into multiplication, `exp(X+Y) = exp(X)exp(Y)` *when X,Y commute*" is **exactly `exponential.md`'s
bidirectional character arrow**: `L_vp` reads the ×-construction off as a +-vector (`vp_mul`), `L_exp` reads
a +-exponent back into the × (`vp_self_pow`, `vp_pow`). `exp: 𝔤→G` is the `+ → ×` direction read on
matrices instead of on prime-valuations: the algebra is the **+ (linearized) face**, the group the **×
face**, and exp is the same arrow's de-linearizing direction. The crucial residue is the **failure of exp
to be a homomorphism**: `exp(X)exp(Y) = exp(X+Y+½[X,Y]+…)` (BCH). The `½[X,Y]` second-order term is the
**`^`-wall of `exponential.md` read infinitesimally** — the `+ → ×` direction folds cleanly *only when the
exponent-vectors are parallel* (`two_three_unique`: distinct ×-atoms never trade), and the **bracket is
precisely the obstruction to that parallelism**: `[X,Y] = 0` ⟺ X,Y commute ⟺ exp is a homomorphism on
that pair. So `exponential.md`/`curvature.md` *predict the bracket as the second-order residue of exp's
non-homomorphism*, and Lie theory confirms it: **the bracket is the `^`-wall of the matrix exp, and exp's
non-commutativity defect is the bracket.** This is the deepest collapse here — the same arrow (`×↦+`) and
the same residue (`q=±1`, the wall) that span parity/valuation/entropy/Fourier now span Lie theory's two
defining objects.

**Cyclic cancellation — Jacobi is ∂²=0-flavoured, but a derivation identity, not a literal two-step
nilpotency (honest).** The Jacobi identity `[[X,Y],Z]+[[Y,Z],X]+[[Z,X],Y]=0` *does* tie to `homology.md`'s
q=−1 sign-cancellation, but the tie must be stated carefully (the task asked to test it). Jacobi is
**equivalent to "ad is a derivation"**: `ad_X[Y,Z] = [ad_X Y, Z] + [Y, ad_X Z]` where `ad_X = [X,·]`. That
**derivation/Leibniz form is the exact shape of `homology.md`'s certified `leibniz_universal_delta4`**
(`δ(α⌣β) = δα⌣β ⊕ α⌣δβ`) — the graded three-term relation, which README v7.1's `two_cells.md` already
classified as the **graded-relation slot** (real, partially grounded by Leibniz). So Jacobi is *the same
graded three-term derivation law* the calculus already located, applied to the bracket: the three cyclic
terms cancel because each is a q=−1-signed face of the double-bracket, and the cyclic sum pairs them off —
the **same pair-cancellation mechanism as `∂²=0`** (each codim-2 face removed by two orders with opposite
sign). The honest caveat: this is the **derivation/Leibniz pole** of the q=−1 cancellation
(`leibniz_universal_delta4`), *not* the literal `∂²=0` nilpotency (`dsq_zero_universal_delta4`) — Jacobi is
"the bracket-with-X is a derivation", which is `homology.md`'s graded Leibniz, not its two-step nilpotency.
The two are README v7.1's two faces of the q=−1 graded relation. So: **Jacobi = the bracket's graded-Leibniz
cyclic cancellation, the same q=−1 graded-relation slot as the cup's Leibniz rule** — tie confirmed, at the
Leibniz pole (not naively the `∂²=0` pole).

**so(n)/su(n) + Killing form — `groups.md`'s Aut-of-a-form + `representation.md`'s trace.** `so(n)` (antisymmetric
matrices) and `su(n)` (traceless anti-Hermitian) are `groups.md`'s Aut-families of a **bilinear/Hermitian
form**, frozen at `I` — exactly the **traceless/antisymmetric sector** the bracket already lands in
(`comm_traceless`). The repo's concrete instances: `so`-flavoured `S` (`S² = −I`, `tr S = 0`, the order-4
antisymmetric/elliptic generator, `S_elliptic_order4`) and the elliptic/unitary sector `det = 1`. The
**Killing form** `K(X,Y) = tr(ad_X ∘ ad_Y)` is `representation.md`'s **trace character of the adjoint
representation** — the additive `×↦+` invariant read on `ad∘ad`. Its definiteness (negative-definite ⟺
compact/`q=+1`, the converge pole) is the **`ResidueTag` q=±1 split read on the form**: the Killing form is
the algebra's analogue of `curvature.md`'s flat-vs-deficit dichotomy, the `det_holonomy_eq_one` invariant
read additively. So `so/su` and the Killing form add **no new primitive**: Aut-of-a-form (`groups.md`) +
trace character (`representation.md`) + the q=±1 tag.

## LEVERAGE — verdict

**PREDICTION (consolidation), with two honest conceptual legs and one located break.** Comparable to
`representation.md`: Lie theory introduces no new construction and consolidates three prior files under the
two standing invariants, with the genuinely-missing pieces (the infinitesimal `ε`, BCH proper) located
precisely — not hand-waved.

- **Leg 1 — bracket = q=±1 antisymmetry commutator-residue. PREDICTION, certified-shaped.** The commutator
  `AB−BA` is a computable `Mat2` operation on the existing `mul`; antisymmetry (`comm_antisym`) and
  tracelessness (`comm_traceless`) both **prove generally by `ring_intZ`** (I verified this in scratch, not
  committed), and self-bracket-vanishing + nonabelian-`[S,U]≠0` by `decide`. The antisymmetry is the *same*
  q=−1 pair-swap as `cup1_antisymmetric`/`det`/ℤ's sign — **forced, not posited.** **NOW BUILT ∅-axiom**
  (`Mat2/Mat2Bracket.lean`, 10/0 PURE): `bracket A B := AB−BA` with `bracket_antisymm` (the q=−1
  antisymmetry), `bracket_self` (`[A,A]=0`), **`tr_bracket_zero`** (traceless / sl₂ — the det/tr split
  from the algebra side), **`jacobi`** (`[[A,B],C]+[[B,C],A]+[[C,A],B]=0`), and `bracket_leibniz` (the
  derivation/graded-Leibniz pole). The "no named `bracket`/`Jacobi` object" caveat is resolved — the Lie
  bracket axioms (antisymmetry + Jacobi + Leibniz) are now Lean theorems, exactly as `PermGroup` gave the
  group axioms.

- **Leg 2 — exp = the ×↦+ character arrow; bracket = exp's non-homomorphism residue. PREDICTION + PARTIAL.**
  The structural identity (algebra = + face, group = × face, exp = the `exponential.md` arrow's `+→×`
  direction, BCH's `½[X,Y]` = the `^`-wall read infinitesimally) is predicted and ties cleanly to certified
  `vp_mul`/`vp_self_pow`/`two_three_unique`. **But the matrix exp `exp: Mat2(𝔤) → Mat2(G)` and BCH are not
  built** — the repo's exp is the `Real213` scalar cut `eulerCut` (`eulerCut_in_8_3_to_3`, the `e` residue),
  not a matrix exponential, and there is no `exp(X)exp(Y) = exp(X+Y+½[X,Y])`. Honest PARTIAL: the arrow is
  the right one, the matrix instantiation is the named open target.

- **Leg 3 — Jacobi = q=±1 cyclic cancellation. PREDICTION, at the Leibniz pole.** Jacobi = "ad is a
  derivation" = the **graded three-term Leibniz relation** of README v7.1's graded-relation slot, the same
  shape as the certified `leibniz_universal_delta4`. Tie confirmed — but to the *Leibniz/derivation* face of
  the q=−1 cancellation, not naively to the `∂²=0` two-step nilpotency. The repo has the Leibniz shape
  (`leibniz_universal_delta4`, PURE) but **no `jacobi` theorem on `Mat2` commutators**; the prediction names
  it as the promotion target (it would prove by `ring_intZ`, like `comm_antisym`).

- **Leg 4 — so/su + Killing = Aut-of-a-form + trace character. PREDICTION (consolidation).** No new
  primitive: `groups.md` (Aut-family) + `representation.md` (trace character) + q=±1 (definiteness). The
  concrete antisymmetric/elliptic generators exist (`S_elliptic_order4`, `det = 1`); a general `so(n)`/`su(n)`
  Aut-of-form theorem and the Killing form `tr(ad∘ad)` are conceptual (the `d>1` trace character is
  `representation.md`'s located open edge, inherited here).

**The located break (the genuinely missing leg).** Like `knots.md`/`representation.md`, Lie theory pins where
the calculus stops: **the infinitesimal / tangent-at-identity `ε`.** The discrete `Mat2` setting hosts the
*commutator* `AB−BA` (a finite difference, the bracket's honest carrier) and the *finite loop* deficit
(`curvature.md`), but **not a separate tangent space** — there is no `I + εX` with `ε² = 0`, no manifold, no
genuine `𝔤` as `T_e G`. The repo's bracket is the finite commutator that *equals* the Lie bracket on matrix
groups (where `[X,Y]_𝔤 = XY − YX` literally), so the prediction lands; but the **abstract tangent/infinitesimal
object is absent**, located precisely at the **resolution dial's `h→0` limit** (`derivative.md`/`continuity.md`):
the Lie algebra is the *derivative reading* of the group, and the derivative's residue (the `h→0` modulus, never
the operand) is exactly the infinitesimal `ε` the discrete setting names but does not inhabit — the same
honest cap `ordinals.md`/`curvature.md` hit (no completed limit object, only its finite generator). **BCH** is
the second missing leg: the matrix-exp series welding `exp` to the bracket is not built (the same gap as
`exponential.md`'s "full continuous `exp∘log = id` open" and `curvature.md`'s "continuous holonomy→curvature
limit open").

**Net verdict: PREDICTION.** The bracket falls out as the q=±1 antisymmetry commutator-residue
(`comm_antisym`/`comm_traceless` by `ring_intZ` — verified scratch); exp is the ×↦+ character arrow with the
bracket as its non-homomorphism (`^`-wall) residue; Jacobi is the q=−1 graded-Leibniz cyclic cancellation
(same slot as `leibniz_universal_delta4`); so/su + Killing are Aut-of-a-form + trace character. **Lie theory
consolidates groups.md + exponential.md + homology.md** (+ curvature.md, representation.md) under the two
invariants — the bracket is the *infinitesimal* of the holonomy, the algebra the *+ face* of the group, the
adjoint the *down-the-height* reading. The missing leg is the **tangent/infinitesimal `ε`** (the resolution
dial's `h→0` residue, absent as an object) **and BCH** (the matrix-exp ↔ bracket weld). 37 decompositions;
Lie theory EXTENDS by consolidation, with the **infinitesimal `ε`** as the located break.

## Note for the technique — does Lie theory touch model v7.1?

**No new primitive; EXTEND + one consolidation note.** The two invariants (character arrow, q=±1 residue)
and four axes (direction, fold-height, resolution+base, iteration-character) absorb Lie theory whole:

> **The Lie bracket is the infinitesimal of `curvature.md`'s holonomy — the q=−1 commutator-residue at
> the identity.** Where the loop-reading reads a finite loop and gets the holonomy deficit (`holonomy[S,S]=−I`),
> the commutator reading reads the first-order non-commutativity and gets the bracket (`AB−BA`), antisymmetric
> by the *same* q=−1 pair-swap as `det`/`∂`/ℤ's sign (`comm_antisym`, `cup1_antisymmetric`). The Lie algebra
> is the **+ face** (additive, `tr`-character, the `representation.md` `det`/`tr` split read from the algebra
> side: the bracket is forced into `tr`'s kernel `sl`, `comm_traceless`); the Lie group is the **× face**;
> and **exp is `exponential.md`'s ×↦+ arrow** between them, with the bracket as the second-order residue of
> exp's failure to be a homomorphism (BCH's `½[X,Y]` = the `^`-wall read infinitesimally). **Jacobi is the
> graded-Leibniz cyclic cancellation** of README v7.1's graded-relation slot (the `leibniz_universal_delta4`
> shape, q=−1 Leibniz pole — not the `∂²=0` nilpotency pole). The located break is the **tangent/infinitesimal
> `ε`**: the discrete `Mat2` hosts the finite commutator (which *equals* the bracket on matrix groups) but not
> a separate `T_e G` — the infinitesimal sits at the resolution dial's `h→0` residue (`derivative.md`), named
> but not inhabited, the same cap `ordinals.md`/`curvature.md` hit. BCH (the matrix-exp↔bracket weld) is the
> second open leg.

So model v7.1's interior is unchanged; Lie theory is the **infinitesimal corner of the Aut-family** — the
bracket = the q=±1 commutator-residue (one order down from curvature), exp = the ×↦+ arrow, Jacobi = the
graded-Leibniz q=−1 cancellation — consolidating five prior files, with the infinitesimal `ε` as the new
located break.

## Verified Lean anchors (file:line — all grep + `#print axioms`-verified this session; all PURE)

| Leg | Theorem (file:line) | Status |
|---|---|---|
| `Mat2` ×-construction: `mul`, `det`, `tr`, generators `I,S,U,G` | `Lib/Math/NumberSystems/Real213/ModularGeometry/HyperbolicEllipticTrace.lean:28` `Mat2`; `:38` `mul`; `:45` `det`; `:47` `tr` | def (∅-axiom) ✓ |
| ★ commutator `AB−BA` is computable; antisymmetry + tracelessness fall out by `ring_intZ` | **scratch (verified, not committed)**: `comm`, `comm_antisym` (`[A,B].x = −[B,A].x`), `comm_traceless` (`[A,B].a = −[A,B].d`), `comm S S = 0`, `comm S U ≠ 0` — built on `HyperbolicEllipticTrace.mul` + `Int` sub | compiles clean ✓ |
| Cayley–Hamilton `M² = tr·M − det·I` (the trace/det dial, `sl` discriminant) | `…/Mat2/Mat2CayleyHamilton.lean:37` `cayley_hamilton`; `:50` `char_poly_discriminant` | **PURE** ✓ |
| trace recurrence `tr(Mⁿ⁺²)=tr·tr(Mⁿ⁺¹)−det·tr(Mⁿ)` (tr as additive/order readout, not a character) | `…/Mat2/Mat2TraceRecurrence.lean:53` `trace_recurrence`; `:64` `golden_trace_recurrence` | **PURE** ✓ |
| ★ antisymmetry sign = `homology.md`'s q=−1 wedge: `e_i∧e_j = −(e_j∧e_i)`, `e_i∧e_i=0` | `Lib/Math/Cohomology/Cup/SignedCup.lean:62` `cup1_antisymmetric`; `:45` `negPow`; `:52` `mergeSign` | **PURE** ✓ |
| ★ Jacobi = graded-Leibniz pole: `δ(α⌣β)=δα⌣β ⊕ α⌣δβ` (the graded three-term relation) | `Lib/Math/Cohomology/Delta/V4Capstone.lean` `leibniz_universal_delta4` (per `homology.md`/`two_cells.md`) | **PURE** ✓ (cross-frame) |
| ★ bracket residue = curvature one order down: holonomy functorial, flat=det1, first loop = the fold | `…/ModularGeometry/HolonomyLattice.lean:108` `holonomy_append`; `:136` `det_holonomy_eq_one`; `:292` `positive_loop_trivial`; `:313` `first_loop_is_the_fold` | **PURE** ✓ |
| `so`/elliptic generator: `S² = −I`, `tr S = 0`, `det S = 1`, order 4 (antisymmetric/unitary sector) | `…/HyperbolicEllipticTrace.lean:78` `S_elliptic_order4`; `:85` `U_elliptic_order6` | **PURE** ✓ |
| modular elliptic orders `S⁴=I`, `U⁶=I` (the unimodular Lie-group generators) | `…/ModularGeometry/ModularElliptic.lean:58` `modular_generator_orders` | **PURE** ✓ |
| exp = `exponential.md`'s ×↦+ arrow (`+→×` direction); the `^`-wall = BCH obstruction | `Meta/Nat/VpMul.lean:165` `vp_mul`; `:183` `vp_pow`; `:204` `vp_self_pow`; `Meta/Nat/FoldCriterion.lean` `two_three_unique` | **PURE** ✓ (cross-frame) |
| `e` = the scalar exp residue (the analytic exp the matrix exp would generalize — honest: scalar only) | `…/Real213/ExpLog/EulerCut.lean:85` `eulerCut_in_8_3_to_3`; `:101` `eulerLimit_in_8_3_to_3` | **PURE** ✓ |
| q=±1 residue tag (abelian `q=+1` / non-abelian `q=−1`; Killing definiteness) | `Lib/Math/Foundations/ResidueTag.lean:73` `ResidueTag`; `:81` `multiplier`; `:86` `multiplier_unimodular`; `:133` `escape_residue_outside` | **PURE** ✓ |
| cross-frame | `groups.md` (Aut-family `composeList_assoc`), `curvature.md` (`det_holonomy_eq_one`, `first_loop_is_the_fold`), `homology.md` (q=−1 two-step), `exponential.md` (`vp_mul`/wall), `representation.md` (`det`/`tr` split) | prior, ∅-axiom ✓ |

## Conceptual-only legs / located breaks (honest — not cited as anchors)

- **No `bracket`/`Lie`/`LieAlgebra`/`Jacobi`/`adjoint`/`Killing` object in `lean/E213`** (grep-confirmed:
  the only `bracket`/`Lie` hits are interval `BracketModulus`/`EulerCertifiedBracket` and the substring
  "ad" — *no* Lie-theoretic structure). The bracket is **latent** (Mat2 `mul` + `Int` sub make `AB−BA`
  computable; antisymmetry + tracelessness prove by `ring_intZ` — verified scratch) but **unnamed**. The
  prediction: promoting `comm`/`comm_antisym`/a `jacobi` lemma gives the Lie-algebra axioms free, exactly as
  `PermGroup` gave the group axioms. THIN beyond the finite commutator on `Mat2`.
- **The infinitesimal / tangent-at-identity `ε` (`T_e G`) — the located break.** The discrete `Mat2` hosts
  the *finite* commutator (which equals the bracket on matrix groups) and the *finite* holonomy loop, but
  **not a separate tangent space** — no `I + εX`, `ε²=0`, no manifold. Located at the resolution dial's
  `h→0` residue (`derivative.md`/`continuity.md`): the Lie algebra is the derivative reading of the group;
  the infinitesimal is the derivative's residue, *named by its finite generator, never inhabited* — the same
  honest cap as `ordinals.md`/`curvature.md` (no completed limit object).
- **BCH / matrix exponential `exp: Mat2(𝔤)→Mat2(G)`** — absent. The repo's exp is the scalar `Real213` cut
  (`eulerCut`), not a matrix exp, and there is no `exp(X)exp(Y)=exp(X+Y+½[X,Y])`. The structural arrow is
  certified (`exponential.md`'s ×↦+); the matrix instantiation + BCH are the named open targets (twin of
  `exponential.md`'s open `exp∘log=id` and `curvature.md`'s open holonomy→curvature limit). PARTIAL.
- **`tr` as a multiplicative character — there is none** (inherited from `representation.md`): `tr(MN)≠tr M·tr N`.
  `tr` is the *additive* `×↦+` twin, and the bracket lands in its **kernel** (`sl`, `comm_traceless`). The
  Killing form `tr(ad∘ad)` is the `d>1` trace character `representation.md` located as open — conceptual here.
- **General `so(n)`/`su(n)` Aut-of-form theorem** — only the concrete elliptic/antisymmetric generators
  (`S_elliptic_order4`, `det = 1`) are built; a general Aut-of-bilinear-form structure is conceptual
  (`groups.md`'s `SymmetrySpecies` catalog corroborates the *form*, not the axioms).
