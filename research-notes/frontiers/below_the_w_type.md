# Below the W-type — the Π/universe floor, and the residue as the second-order climb

**Status**: open multi-session team-research frontier (opened 2026-06-24). Baton for the
program "go more fundamental than the W-type." Continues `the_trusted_base.md` (which
peeled to the single W-type `Tree` + structural recursion + definitional equality).

## The directive

> 더욱 더 펀더멘탈 레벨까지 내려가서 멀티 에이전트 + 멀티 세션 논의 및 팀 연구.
> (Descend to an even more fundamental level; multi-agent, multi-session team research.)

`the_trusted_base.md` reached the floor "one W-type `Tree`, structural recursion, the
kernel's definitional equality." This note attacks *below* that: the inductive former
itself, the conversion checker, and the minimal home for the residue diagonal.

## The debate (three deeper perspectives, each reading the corpus)

- **Minimal-type-theory architect**: a Church/Böhm-Berarducci encoding `CTree := ∀ X, X →
  X → (X → X → X) → X` removes the `inductive Tree` *declaration* (only Π + impredicativity),
  but it is a **swap, not a peel** — it trades a named inductive for an impredicative
  universe-Π of *higher* strength, and the **dependent eliminator / induction principle is
  NOT derivable** (System-F junk; needs parametricity), which is exactly what *all* of Raw's
  reasoning runs on. Ranking of "more fundamental" targets: **λΠ/LF** (Tree as a signature
  with no computation rules) peels the most — it drops ι-reduction, the recursor, and large
  elimination — at the cost of all computation becoming explicit derivation.
- **Definitional-equality specialist**: re-expressing the `rfl`-computations as explicit
  propositional rewrites **relocates** the conversion work, it does not remove it — checking
  the explicit witnesses is itself β, and `Tree.rec`-ι is needed to type them. The
  irreducible residue is `{β for application, ι on Tree.rec, Prop-proof-irrelevance}`. The
  peelable surface is measurable via a **non-trivial-`rfl` census** (count `Eq.refl` nodes
  whose two sides are not syntactically identical) and an **`@[irreducible]` replay test**
  (mark `Tree.cmp`/`canonical` irreducible; every break is a genuine defeq-reliance site).
- **Rewriting/combinatory foundations**: the distinguishing is the **free term algebra** over
  `{a:0, b:0, slash:2}` — first-order. The structural facts (`slash_ne_a`, `isPart_wf`,
  `no_infinite_descent`) need only a signature + no-confusion schemas + **one structural
  induction schema** — a ~200-line Metamath/Post/λΠ checker, no CIC. **But the residue
  theorem is a Cantor diagonal on `Object1 : Raw → (Raw → Bool)`** — `f x x` and `∀ f : Raw →
  Bool` are *unstatable* below the function space. So 213's foundation **stratifies**: Tier A
  (first-order tree algebra + descent) vs Tier B (the residue, forced up to the power object).
  And the unencodable surplus that forces the climb *is* the residue.

## The two experiments (machine-verified)

### Experiment A — Church-encode the distinguishing (is "below inductive" a peel?)

Built `CTree` (impredicative, no `inductive`), `a/b/slash`, and proved no-confusion
`slash a b ≠ a` — by folding into `Bool` as the discriminator. Measured with
`cic_footprint.py`:

| | closure | inductives | axioms |
|---|---|---|---|
| Church `cslash_ne_ca` | **25** | `Bool, Eq, False` (**no `Tree`**) | ∅ |
| inductive `Raw.slash_ne_a` | 96 | `Bool, Tree, Ordering, Subtype, …` | ∅ |

**Result — "swap, not peel," and the swap is below the tool's resolution.** The Church
version is *smaller in constants and `Tree` is gone* — but its cost, the impredicative `∀ X :
Type`, is a Π/universe phenomenon the **constant-footprint tool cannot see**, so it still
scores MINIMAL-STRUCTURAL. No-confusion needed no parametricity axiom (it folds into `Bool` —
the discriminator is *relocated* into an inductive, not eliminated). And the dependent
eliminator — what Raw's reasoning actually needs — is not derivable for the encoding. So
Church encoding is a **dead end for the proof content**, and a demonstration that *the
constant footprint is blind to impredicativity*.

### Experiment B — the stratification, made a re-checkable verdict

`cic_footprint.py` extended with a **higher-order detector** (`tier`): does the
*statement-level* type-closure quantify over a **function-into-data** (a power object like
`Raw → Bool`, e.g. via `Function.Surjective`) as opposed to a relation-into-Prop (`_ → _ →
Prop`, e.g. `WellFounded`)? Validated against the known split:

| target | tier |
|---|---|
| `isPart_wf`, `slash_ne_a`, `IsPart`, `no_infinite_descent` | **TIER-A** (first-order) |
| `object1_not_surjective`, `object1_injective`, `self_covering_closure` | **TIER-B** (power-object climb) |

The residue theorem is **mechanically detected** as the unique climb to the function space —
the first-order/second-order seam is now a re-checkable number, not a slogan. (Caveat: this
is a *statability/expressibility* axis, not a TCB-shrinking claim — same as the
`the_trusted_base.md` discipline.)

## The deep finding (the convergent meta-result)

The constant-footprint instrument (axioms / recursors / inductives / Nat) was the right tool
for the **constant skeleton** — and it bottomed out at MINIMAL-STRUCTURAL. But "more
fundamental than the W-type" lives **one layer down, in the Π/universe structure**:
- **impredicativity** (Church encoding's `∀ X : Type` — Experiment A), and
- **function-space quantification** (the residue's `∀ f : Raw → Bool` — Experiment B),

both **invisible to constant-counting**, because both are Π/universe phenomena, not
constants. The new `tier` column makes the *function-space seam* measurable; the
*impredicativity/universe* and *defeq* axes are named but not yet instrumented.

And the 213-native payoff: **the residue theorem sits exactly at the first-order/second-order
boundary, and the boundary is not incidental — it is where the distinguishing's self-cover is
forced to climb to the power object.** `the_trusted_base.md` said the kernel is the residue's
*form* read on verification; here the residue is the *content* read on expressibility: the
Cantor-unpointable surplus (`Object1` not surjective) is exactly what cannot be brought down
to the first-order tree algebra. The climb is forced by the residue; the residue is the name
of the climb. (Honest guard, per the failure-mode catalog: this is **form/structure
agreement** measured by the tier detector — Tier A is first-order, the residue alone is
Tier B — not a claim that "the function space *is* the residue object." View, not identity.)

## Next-session handoff (the team-research baton)

Concrete, machine-checkable, ranked:

1. **λΠ / Metamath second-checker for Tier A** (the only legitimate trust move —
   checker-*diversity*, per `the_trusted_base.md`): emit `{a,b,slash}` + no-confusion +
   structural-induction schema + `slash_ne_a` + bounded `no_infinite_descent` in a ~200-line
   first-order checker, independent of CIC. Exhibits the "tiny TCB" claim instead of asserting
   it. **Falsifiable prediction**: every `Theory/Raw/` structural theorem ports; the
   `Cantor`/`FlatOntologyClosure` cone does **not** (it needs the power object) — and that
   stop-line coincides exactly with the `tier` detector's TIER-A/TIER-B split.
2. **Instrument the two blind axes** the constant-tool misses:
   - **non-trivial-`rfl` census** + `@[irreducible]` replay → the defeq-reliance surface as a
     number (the conversion residue `{β, ι-on-Tree.rec, proof-irrelevance}`);
   - **universe/impredicativity column** → flag `∀ X : Type`-as-data (would catch Experiment
     A's Church swap that `tier`/constants miss).
3. **Push Tier classification across the whole corpus** → a map of which theorems are
   first-order (Tier A) vs need the power object (Tier B). Expectation: 213's *structural*
   content is overwhelmingly Tier A; the genuine second-order content is the residue cone and
   its consumers. This *measures* "how much of 213 needs more than a tiny checker."

## Round 2 — the residue is the Lawvere fork; self-application sits ABOVE the distinguishing

Continued debate (Lawvere/fixed-point logician, λ-calculus/self-application specialist,
213-philosopher + skeptic). Three results, one of them self-correcting.

**(a) The residue = Lawvere's fixed-point theorem — and it is already formalized.** The
prior rounds did not know the repo already contains `Lens/Foundations/OneDiagonal.lean`
(11/11 PURE): `lawvere_fixed_point (f : A → A → B) (surj) (t : B → B) : ∃ b, t b = b`,
proof `obtain ⟨a,ha⟩ := surj (fun a => t (f a a)); ⟨f a a, …⟩` — the kernel term being
**`f a a`, self-application**. Cantor (`cantor_via_lawvere`, B=Bool, t=`not`), the residue
(`residue_is_lawvere_diagonal` = `object1_not_surjective`, A=Raw), and Russell/Liar/Tarski
(`russell_liar_no_surjection`, Prop/Iff form) are *three instances of one diagonal*
(`one_diagonal_generates`). The engine premise — `not` is fixed-point-free
(`bnot_self_ne`) — **is** §5.2's Bool-style self-reference, verbatim. `ResidueTag.lean`
generalizes to the ±1 two-pole tag: escape (q=−1: Cantor/Gödel/residue, no fixed point) vs
converge (q=+1: φ/Banach, contraction). So the trusted-base / below-the-W-type frontier
connects to existing foundational Lean: **Cantor = residue = §5.2 Bool-self-reference is a
theorem, not a slogan.**

**(b) The β-floor below the Π/universe layer.** Lawvere's `f a a` is the same *diagonal
kernel* as the Y-combinator's `x x` (one β-redex: "substitute the diagonal into itself");
they diverge only in discipline — Lawvere is total/terminating (the surjection hands you the
index `a`; one `congrFun ha a` step), Y diverges. So the residue's irreducible
*computational* content is exactly **one diagonal abstraction `fun a => t (f a a)` + one
β-instantiation**. A substitution-only (Metamath) checker cannot *reduce* this β-step; it
must **axiomatize** it as an instantiation schema. That single diagonal redex — at the
function space — is the floor below the Π/universe layer Round 1 found.

**(c) The self-correction (the round's sharpest result).** The tempting deeper thesis —
*"self-application / the fork is more primitive than the distinguishing; distinguishing is a
reading of the converge/escape outcome"* — is **false, and refuted by this program's own
`tier` detector.** Measured:

| target | tier |
|---|---|
| `isPart_wf`, `slash_ne_a`, `no_distinguishing_on_subsingleton` (the distinguishing + its precondition) | **TIER-A** (first-order) |
| `lawvere_fixed_point`, `residue_is_lawvere_diagonal`, `residue_needs_distinguishing` (self-application / the fork) | **TIER-B** (power-object climb) |

Lawvere lives in a cartesian-closed category — it *needs* the function space `B^A` (here
`Raw → Bool`), which is `Object1`, a Lens reading of the **already-given** distinguishing.
So self-application presupposes the power object, which is TIER-B — *above* the
distinguishing (TIER-A), not below. The circularity ("use a structure the distinguishing
generates to claim it precedes the distinguishing") is **measured by the TIER-A/TIER-B
seam**, not merely argued. And `OneDiagonal` §5–6 proves the dependency directly:
`residue_needs_distinguishing` (subsingleton value space ⟹ every `t` converges ⟹ *no escape,
no residue*) and `no_distinguishing_on_subsingleton` (the slash cannot fire without a
distinct pair). **The distinguishing is the precondition that gives the fork two branches;
it is not the fork's product.**

**Honest surviving verdict.** Once the distinguishing has run far enough to force the climb
to the power object (TIER-B), its self-cover `Object1` is self-applying, and Lawvere's fork —
escape (fixed-point-free `t`, the residue) vs converge (contraction, φ/Banach) — is the one
mechanism organizing both forms of §5.2 self-reference, the residue being the escape branch.
This *deepens §5.2 from taxonomy to theorem*. **Dropped as overclaim** (failure-mode
catalog): "self-application is the floor beneath the distinguishing" (refuted by the tier
seam + `residue_needs_distinguishing`); "distinguishing IS the fork outcome"
(View-promoted-to-identity); "the substrate stabilizes" as a ground (deifies φ — the
convergence is a located modulus-limit, reached by none).

**Tooling deposit.** Fixed a `tier`-detector false positive: a Prop hypothesis `(∀ x y,
x = y)` has final-codomain `Eq x y` (an `.app`, a *proposition*) which the old check
mis-read as "function-into-data." The detector is now **env-aware** (a `.const` codomain
flags only if it is a Type-valued, not Prop-valued, inductive; an `.app` proposition never
flags), so TIER-A/TIER-B is sharp (`no_distinguishing_on_subsingleton` now correctly TIER-A).

**Next (carried):** route `cantor_general` / `object1_not_surjective` through the
`lawvere_fixed_point` engine (currently inline-duplicated) — needs moving the generic
Lawvere lemmas upstream of `Cantor.lean` to avoid an import cycle; pure refactor, makes the
unification load-bearing in the proof graph. Plus the β-redex / non-trivial-`rfl` census
(blind-axis #2): predict exactly one diagonal redex per residue-cone theorem.

## Cross-refs

- `lean/E213/Lens/Foundations/OneDiagonal.lean` (the Lawvere engine, 11 PURE — residue =
  Cantor = Russell = one diagonal; §5–6 = the distinguishing-is-precondition refutation),
  `lean/E213/Lib/Math/Foundations/ResidueTag.lean` (the ±1 escape/converge tag).

- `the_trusted_base.md` (Round 6: the constant-footprint auditor + the §5.1-legal verdict).
- `the_genesis_seam.md` Round 5 (the `Nat`-free Raw layer; the `ordNoConf` technique).
- `lean/E213/Lens/Foundations/FlatOntologyClosure.lean` (`object1_not_surjective`, `Object1 :
  Raw → (Raw → Bool)` — the Tier-B witness), `Lens/Cardinality/Cantor.lean` (the diagonal),
  `Lens/Foundations/PredicateSelfEncoding.lean` (definable predicates round-trip — the
  first-order-encodable part; the surplus is the residue).
- `tools/cic_footprint.py` (now with the `tier` higher-order detector).
