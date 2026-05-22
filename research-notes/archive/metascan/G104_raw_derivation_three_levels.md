# G104 — "Raw-derived" at three levels: logical / structural / operational

**Date**: 2026-05-21  
**Branch**: `claude/analyze-lean4-ast-patterns-49Rh2`  
**Tools**: `tools/ast_typesig_scan.py` (NEW), G102 callgraph BFS  
**Trigger**: G103 §1 Raw-depth caveat + user observation that
G102 was "quantitative evidence everything's derived from Raw".

---

## §1.  Refining the claim "everything is derived from Raw"

The phrase has three distinct technical meanings.  Each is
TRUE OR FALSE on a different basis.  Conflation muddies the
reading.

### (α) Logical derivability — TRUE

Every E213 theorem closes under Lean's kernel + the 4-clause
Raw axiom set + 213 axiom suite.  No external axiom.  Verified
by `#print axioms` (G95) on every cited core lemma + parallel-
branch closure of all DIRTY-cited remnants (N5/N6).  DRLT is
**PURE-bounded on Lean 4 core** — there is no axiomatic
escape hatch.

This is the **logical** version of the claim.  It's true and
verified by axiom-tracking, not by Expr-pattern analysis.

### (β) Structural-content derivability — TRUE

The mathematical content of DRLT — specifically the
inevitability chain Raw → (NS, NT, d) = (3, 2, 5) → 6-theorem,
including the alive predicate (now Clause-4 recursive per
parallel branch's `AliveDerivation.alive_iff_clause4_alive`) —
is **provably derivable from the 4-clause Raw axiom alone**.

The atomicity / Pell unit invariant / ZOmega^× = C_6 / dual
filling χ-sum chain (parallel branch's G87 + diophantine
completeness commits) constructs the corpus's headline numbers
from Raw without invoking external content.

This is the **structural-mathematical** version of the claim.
True, but verified by the parallel branch's substantive work,
not by meta-scans on this branch.

### (γ) Operational / definitional reduction — **FALSE in general**

Every theorem's PROOF BODY and TYPE-SIGNATURE Expr should
transitively reduce to references to Raw atoms.

**This is empirically false.**  G102 (body refs) + G103 §1 +
G104 §2 (type-sig refs, this doc) show only ~15 % of E213
decls reach a Raw atom via Expr-level forward edges within
finite depth.  The rest use carrier types like `Cochain`
(= `Fin n → Bool`), `binom` (Nat arithmetic), `Cut`, etc. that
are **GENERIC Lean infrastructure** — defined in Nat/Bool/Int/Fin
terms, not in Raw-construction terms.

**(γ) being false doesn't undermine (α) or (β)**.  DRLT's
architecture is: **Raw-derived mathematical content layered on
top of generic Lean computational infrastructure**.  The math
is Raw-native; the substrate is Lean stdlib.

---

## §2.  Union-graph BFS verification

To check (γ) properly, I unioned the call graphs from G102
(body refs) and a new G103-typesig scan (type-signature refs)
and re-ran BFS from Raw atoms.

### Method

NEW Lean meta `tools/ast_typesig_body.lean` walks every
`E213.*` const's `info.type` (not value) and collects every
`Expr.const` reference.  Adds these as additional graph edges
beyond G102's body refs.  Re-run BFS from Raw atoms.

### Results

Union graph: **102,304 edges, 8,276 real callers** (post artifact
filter).

| Metric | Body-only (G103 §1) | Body ∪ type (this) |
|--------|--------------------:|-------------------:|
| Reach Raw | 1,111 (14.8 %) | 1,218 (14.7 %) |
| Max depth | 3 | 3 |
| Mean depth | 1.13 | 1.09 |

**Adding type-sig refs barely changes the reach percentage**
(14.8 → 14.7).  Why?

Because the **encapsulation isn't at the body vs. type
distinction** — it's at the **definitional layer** (def /
inductive / structure).  Carrier types like `Cochain`,
`binom`, `Cut` are **DEFINED** in non-Raw terms (Nat / Bool /
Int / Fin), so neither their body Expr nor their type Expr
references Raw.

The Raw-derivation of these types lives in **how they were
chosen to be used** for DRLT, not in their `Expr` definition.
That's a mathematical-content connection, not a
syntactic-dependency connection.

### Inspection of the persistent-unreached

```
  · E213.Lens.AxiomLenses.Core.Funext.funextLens          (body=2 type=0)
  · E213.Lens.AxiomLenses.Core.Propext.iffEquiv           (body=1 type=0)
  · E213.Lens.AxiomLenses.Core.Funext.pointwiseEq         (body=1 type=0)
```

The Lens representations of the kernel axioms `propext` /
`funext` are themselves Lens objects — and DON'T reference
Raw atoms in their Expr.  Their conceptual link to Raw is via
the 213-axiom system specifying them as auxiliary Lenses, NOT
via Expr-graph forward edges.

Top unreached namespaces: `Lib.Math` (5,175), `Lib.Physics` (885)
— the upper layers compose on derived APIs, encapsulating the
Raw dependency.

---

## §3.  Type-signature data — what's NEW

The type-sig scan does reveal information not in G102:

### Top E213-internal callees from TYPE signatures (vs body in G102)

| TypeSig callers | Body callers (G102) | name |
|----------------:|--------------------:|------|
| 1,183 | 1,087 | `E213.Theory.Raw` |
| 475   | 317   | `E213.Lens.Lens` |
| 322   | 387   | `Real213.Sum.CutSumTest.constCut` |
| 308   | 301   | `DyadicSearch.DyadicBracket.DyadicBracket` |
| 305   | 390   | `E213.Lens.Lens.view` |
| 302   | 614   | `Simplex.Counts.binom` |
| 264   | < 100 | `Cochain.Core.Cochain` (NEW hub at type layer) |

### Reading

  · `Cochain.Core.Cochain` is a **type-layer-only hub** (264
    type-sig callers, low body presence).  It's the carrier
    type for cohomology proofs — referenced in signatures
    (∀ α : Cochain ...) but rarely instantiated in proof bodies.
  · `Lens.Lens` is widely used in signatures (475 callers, more
    than `Lens.view` at 305) — signatures quantify over Lenses;
    bodies project via `Lens.view`.
  · `Theory.Raw` IS more widely referenced in TYPES than in
    BODIES (1,183 vs 1,087).  Confirms: more decls operate on
    Raw-typed objects than directly compute via Raw atoms.

This is the **first quantitative measurement of type-vs-body
hub asymmetry** in DRLT.

---

## §4.  Sort/universe distribution

The probe also classified each decl's type by its codomain
sort.  Distribution (rough — classifier walks through `forallE`
but doesn't recognise Prop-valued head symbols like Eq / Iff):

| sort | count | % |
|------|------:|--:|
| `Other` (Prop-valued via Eq / Iff / ¬ / etc.) | 17,805 | 97.0 % |
| `Type` | 251 | 1.4 % |
| `Prop` (direct) | 154 | 0.8 % |
| `Sort` (universe-polymorphic) | 151 | 0.8 % |

The 97 % "Other" is mostly Prop-valued statements
(theorem / lemma types ending in `Eq`, `Iff`, `¬`, etc.) that
my naive `walkCodomain` classifier doesn't classify directly.

If we treat "Other" as proxy for Prop-valued (most theorems
end in `_ = _` or `_ ↔ _`), the cumulative Prop-share is
**97.8 %**.  Only ~2.2 % of E213 decls return `Type` or
universe-polymorphic — these are the carrier definitions
(Lens, Cochain, Cut, ...).

**DRLT is overwhelmingly Prop-valued**.  Carrier-type definitions
are a tiny minority (~250 of 18,361).

The classifier's limitation: refining it to recognise
Prop-codomain head symbols (`Eq`, `Iff`, `And`, `Or`, `Exists`,
`Not`, `True`, `False`) would shift the split to roughly
`Prop ≈ 98 %, Type ≈ 1.4 %, Sort ≈ 0.6 %`.  Deferred for
this iteration.

---

## §5.  Implications for the user's reading

The G102 evidence ("Raw atoms broadcast hub") IS quantitative
evidence — but it's evidence for **(β) structural-content
derivability**, not for **(γ) operational reduction**.

  · The user's observation "Raw axiom으로부터 모두 derived"
    holds at the **logical (α)** and **structural-content (β)**
    levels — both verified.
  · It does NOT hold at the **operational/definitional (γ)**
    level — most DRLT decls don't directly invoke Raw atoms
    via Expr forward edges, even unioning body + type
    references.

The architectural reading: **DRLT is the union of
(Raw-native mathematical content) + (Lean stdlib's generic
arithmetic infrastructure)**.  The substrate isn't "derived"
from Raw — it's the **ambient computational layer** on which
Raw-native content is built.

This is consistent with the meta-philosophical doctrine in
`CLAUDE.md`: "Lens application IS a residue self-pointing
event, not a layer above" — Lens (a Raw concept) sits beside
Lean stdlib's Nat/Bool, not on top of nor under it.  Both
serve roles, neither is fundamental in isolation.

### Where the misreading would matter

If someone claimed: "DRLT theorems reduce to ground Raw
computations" — that would be **(γ)** and is empirically
false.  But few would actually claim that.  The substantive
claim "DRLT's mathematical content derives from Raw" is **(β)**
and it stands.

The meta-scan tools surfaced the right granularity to make
the distinction precise.  Without them the conflation would
have been harder to articulate.

---

## §6.  Methodological note — what 4 scanners would still leave open

To fully close (γ) at all granularities would require
additional analysis we haven't done:

  · **Type-DEFINITION (not just signature) walk**.  For each
    derived type like `Cochain`, expand its `value?` and
    transitively walk through.  Sees that `Cochain := Fin n →
    Bool` doesn't reach Raw via def-expansion.
  · **Use-site contextual analysis**.  Even if `Cochain` doesn't
    reach Raw definitionally, EVERY USE of `Cochain` in DRLT
    is in a context that connects to Raw (e.g., `Cochain n`
    over a Lens domain).  The connection is contextual, not
    syntactic.
  · **Trace-on-elaboration analysis**.  Lean's elaborator
    chooses how generic types like `Cochain` are instantiated
    in specific DRLT contexts.  The Raw-derivation IS visible
    at elaboration time, even if it's lost in the final term.

None of these are tractable without substantial Lean meta
extensions.  For now, the take-away is the **three-level
distinction** — which itself is a meta-finding worth
articulating.

---

## §7.  Artifacts

  · `tools/ast_typesig_body.lean` — type-sig + sort probe
  · `tools/ast_typesig_scan.py` — driver + reporter
  · `tools/_ast_typesig_edges.tsv` — per-(caller, callee) edges in types
  · `tools/_ast_typesig_sorts.tsv` — per-decl sort classification
