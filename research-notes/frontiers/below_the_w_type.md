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

## Cross-refs

- `the_trusted_base.md` (Round 6: the constant-footprint auditor + the §5.1-legal verdict).
- `the_genesis_seam.md` Round 5 (the `Nat`-free Raw layer; the `ordNoConf` technique).
- `lean/E213/Lens/Foundations/FlatOntologyClosure.lean` (`object1_not_surjective`, `Object1 :
  Raw → (Raw → Bool)` — the Tier-B witness), `Lens/Cardinality/Cantor.lean` (the diagonal),
  `Lens/Foundations/PredicateSelfEncoding.lean` (definable predicates round-trip — the
  first-order-encodable part; the surplus is the residue).
- `tools/cic_footprint.py` (now with the `tier` higher-order detector).
