# The `shapeLens` functor itself — a deep-research synthesis

*Tier 1 (research-notes), volatile.  Answers Mingu Jeong's request "이 렌즈
혹은 펑터 자체에 대해 딥 리서치 해줘" — deep research on the `shapeLens` /
functor as such, not on individual readings.  Synthesises three research-agent
passes (RA-A category-theoretic, RA-B sequences/genus, RA-C 213-native /
formalization).  Caveat carried throughout: the `shapeLens` is one reading-genus;
its outputs are Lens outputs (§2.5), the residue is outside its image
(`object1_not_surjective`).  This note characterises the **functor**, not the
residue.*

The `shapeLens` (naming: Mingu Jeong; see `INDEX.md` "Naming") = the genus
"geometrize the slash as incidence: a point per object, a line per relation."
Three questions are answered below: (1) **what categorical object is it**,
(2) **what does its canonical (complete) generation grow like, and where does it
leave the plane**, (3) **is it a 213 `Lens`, and is the single-ℕ fork the same
forcing as `PairForcing`**.

---

## 1.  Category-theoretic identity (RA-A): the free-complete-graph monad

Read the slash as "every pair of distinct objects is adjacent" and recurse: each
relation (line) becomes a fresh object (point) that joins everything.  This is
exactly the **complete-graph reflector**

> `C : Grph → Cmpl`,  `G ↦ K_{|V(G)|}`  (saturate: add every missing edge),

the left adjoint to the inclusion `Cmpl ↪ Grph` of complete graphs (a full
reflective subcategory).  Its associated **monad** `T = C` on `Grph` is
**idempotent** (`T² ≅ T`: saturating a complete graph changes nothing), so its
algebras are precisely the complete graphs — the fixed points of saturation.

The genus's *generative engine* (each line → a point joined to all) is the
**free** functor of this adjunction iterated: from `n` points the unique
non-redundant step is `K_n ↦ K_{n+1}` (the new point joins all `n`).  So the
canonical `shapeLens` orbit is `K_2, K_3, K_5, K_{12}, …` — always a complete
graph, the 1-skeleton of the simplex (`complete_graph_rule.md`).

**Why this matters for 213.**  "Idempotent reflector / free-then-forget" is the
categorical shadow of the *algebraic* (free, no-glue) end of the
combining-map dial: `mu_nu_coincidence.md` already records that the complete-graph
reading is the canonical **algebraic** cell (`μF ≅ νF`, static = dynamic),
because the free reading adds no contraction/glue, so the ω-chain converges at ω.
The reflector being idempotent **is** "no further glue is created by saturation"
— the same fact one categorical level up.

**Honest limits (RA-A + RA-C agree).**  The repo has *initial-algebra* universal
properties (`raw_initial`, `Lens.initiality`) but **no** category / functor /
adjunction infrastructure, and the one `Graph`/`Category` pair that exists
(`Lib/Math/Algebra/GRA/`) is the unrelated depth-functor construction.  Building
`Grph`, `Cmpl`, the inclusion and the left adjoint as Lean structures (with
naturality) is a large, Mathlib-shaped effort that buys little: the *content* —
every pair adjacent; saturation idempotent — is captured ∅-axiom by a
`Raw → (Raw → Raw → Bool)` fold plus an idempotence theorem.  So: **do not
formalize the adjunction qua adjunction**; formalize the reflector *fixed point*
(see §4, Target A).

---

## 2.  Growth and genus (RA-B): doubly-exponential, planar ceiling exact

### 2.1  The orbit and its closed-form recurrence

Synchronous canonical generation (every line of the previous cycle spawns a point
at once) gives point counts

```
2, 3, 5, 12, 68, 2280, 2 598 062, …
```

with the clean two-term recurrence (equivalent to the `INDEX.md` form
`n_{k+1} = n_k + [C(n_k,2) − C(n_{k−1},2)]`):

> **`n_{k+1} = C(n_k + 1, 2) − C(n_{k−1}, 2)`**.

Asymptotically it is **doubly exponential**: `n_k ~ 2 · c^(2^k)` with the
Aho–Sloane-type constant `c ≈ 1.24602083…` (each cycle roughly squares the count,
`n_{k+1} ≈ n_k²/2`).  This pins the "explosion" quantitatively
(`shapelens_grotesque.py`): the first unrenderable shape is `K_68` (cycle 4,
≈333 000 crossings), two cycles past the planar threshold.

### 2.2  The skip of 4 is forced

`2 → 3` adds one point (single growth axis); at 3 the synchronous rule adds `+2`
at once, landing on **5**, skipping 4.  RA-B confirms the skip is **forced**, not
chosen: the only way to reach 4 is a *desynchronised* (one-at-a-time) path, which
is a different (chosen-linear) Lens, not the canonical synchronous orbit.  So
`4 = K_4` (the planar tetrahedron) is never visited by the canonical genus.

### 2.3  Genus / planarity — the exact hit and the suggestive one

- `K_n` planar ⟺ `n ≤ 4`; **the genus γ(K_n) jumps `0 → 1` at exactly `n = 5`**
  (Ringel–Youngs: `γ(K_n) = ⌈(n−3)(n−4)/12⌉`).  So `d = N_S + N_T = 5` makes
  `K_5` the *first* non-planar complete graph (= planar ceiling `4` + 1).
- `K_{m,n}` planar ⟺ `min(m,n) ≤ 2`, and **`γ(K_{m,2}) ≡ 0` for all `m`**
  (`K_{m,2}` is always planar).  213 has `N_T = 2`, so `K_{3,2} = K_{N_S,N_T}` is
  the *last* planar complete bipartite graph; the `det=0` degenerate `K_{3,3}`
  (`Mobius213K33Bridge`) is the *first* non-planar.

**Honest grading (unchanged from `kuratowski_atomicity.md`):** `N_T = 2 =` the
`K_{m,n}` planarity ceiling is an **exact equality** (strong); `d = 5 =` complete
planar ceiling `+ 1` is **partly small-number coincidence** (planarity thresholds
and atomic counts are both small).  Both Kuratowski forbidden graphs (`K_5`,
`K_{3,3}`) are 213 numbers — suggestive, recorded, not asserted as derivation.

### 2.4  The erased adjacency: `L(K_n) = J(n,2)`

The companion "each line becomes a vertex" map has adjacency = the **line graph**
`L(K_n)`, which is the **Johnson graph `J(n,2)`** (the triangular graph `T(n)`):
two edges of `K_n` adjacent ⟺ they share a vertex.  This is precisely the
relational structure the complete-graph *reflector erases* (it remembers only the
vertex count `|V|`, discarding which edges meet).  Pretty and exact, but isolated:
RA-C flags it has no downstream consumer in the repo (Target C, skip).

### 2.5  Order-ideal count is a clean binomial transform

The configuration count `I(V,s) = Σ_k C(s,k) · 2^(V·k) · 2^(C(k,2))`
(`5, 145, 72 304 608 555 084 001`) is a **binomial transform** of `2^(V·k+C(k,2))`
— already ∅-axiom in `ConfigLatticeCount.lean` (now 24 PURE: concrete `cycle1/2/3`
plus the general `cfgIdeals_zero/one`, `cfgIdeals_pos`, `cfgIdeals_dominant`,
`cfgIdeals_mono_V`).

---

## 3.  Is it a 213 `Lens`?  And is the fork = `PairForcing`? (RA-C)

### 3.1  Yes — and the codomain already exists

**A 213 `Lens` is exactly a `Raw.fold` into a `HasDistinguishing` codomain.**  The
machinery is all present: `Theory/Raw/Fold.lean` (`Raw.fold`, `fold_slash_rel`),
`Lens/LensCore.lean` (`Lens`, `Lens.view = Raw.fold`), `Lens/SemanticAtom.lean`
(`HasDistinguishing`, `universalMorphism`, `raw_initial`), `Lens/Initiality.lean`.

The codomain realizing "point = object, line = relation" is **already named** in
`Lens/FlatOntology.lean`: `abbrev Relation := Raw → Raw → Bool` (the §6.3 flat
ontology).  "Point = object" = the `Object1 : Raw → (Raw → Bool)` reading;
"line = relation" = a value in `Relation`.  So the `shapeLens`'s natural codomain
is an **incidence / adjacency predicate** — *not* a fresh simplicial-set / nerve
type (none exists, none is needed: the 1-skeleton `K_n` is exactly a symmetric
`Raw → Raw → Bool`).

**Honest two-layer caveat** (already in `free_graph_structure.md`): the slash
`a/b` is a symmetric *ternary* incidence `{a, b, a/b}`; reducing it to a *binary*
adjacency is itself a sub-Lens choice, and "complete" (every distinct pair
adjacent) is the *maximal* end of that dial.  So the `shapeLens` is honestly two
stacked readings: (slash → incidence predicate), then (incidence → its
complete-graph saturation).  That second arrow is the reflector of §1.

### 3.2  The single-ℕ fork vs `PairForcing` — **independent, not the same forcing**

This is the sharpest finding, and it corrects the open question in
`shapelens_fork_atomicity.md` ("are they the same forcing in two readings?").
**Verdict: no — they share no premise; they are two independent characterizations
that coincide on the answer 5.**

- **Arithmetic / Diophantine forcing** (`Theory/Atomicity/{Five,PairForcing,
  ArityForcing,CombinatorialArity}.lean`): fixes `(N_S,N_T) = (3,2)` from
  coprimality + parity + a *unique-alive-decomposition* count
  (`count p q = half p · half q = 1 ↔ (p,q) = (2,3)`; `atomic_iff_five`: `5` the
  unique `n` with a unique alive `n = 2a+3b`), with arity 2 the unique
  non-degenerate arity over `Fin 2` (pigeonhole).  It then *derives* `5 = 2 + 3`.
  It never mentions graphs, planarity, posets, or "K_4 skipped".

- **The shapeLens fork** (`shapelens_fork_atomicity.md` + `configuration_lattice.md`
  + `kuratowski_atomicity.md`): fixes `5` **directly** as a structural threshold —
  the first cycle whose configuration poset has an antichain of width ≥ 2
  (single-ℕ ends), equivalently the first non-planar `K_n` (skipping `K_4`),
  equivalently the 4-simplex skeleton — *without any reference to `(2,3)`*.

The arithmetic route fixes `(2,3)` and derives `5`; the topological route fixes
`5` and never sees `(2,3)`.  A *proof* that the fork-characterization implies the
arithmetic atomic shape would be a **genuine new theorem**, not a re-reading.
Until then: claiming "same forcing" is **unsupported**; they are two routes that
**agree on 5**, which is itself the interesting (open) bridge claim.

### 3.3  Nothing in the fork story is ∅-axiom yet

`configuration_lattice.md` §Open is explicit: only the *count* `I(V,s)` is
formalized.  The poset `P(V,s)`, the antichain-width / "first width-≥2" claim,
confluence, and the event structure are **not** in Lean.  So the conjecture's
central object — the fork antichain — currently has **no Lean witness at all**.

---

## 4.  What to formalize (RA-C, ranked by value / effort)

**Target A — `shapeLens` as a flat-ontology fold + reflector fixed point
(RECOMMENDED; light; non-redundant). — DONE (2026-06-05, 20 PURE).**
Implemented as `lean/E213/Lib/Math/Geometry/ShapeLens.lean` (placed under
`Lib/Math/Geometry/` as the genus *parent* of the species rather than under
`Lens/`, to keep the Lib-on-Lens dependency direction; it still imports the core
`Lens.FlatOntology`/`Lens.LensCore` for the codomain + `Lens`).  `shapeLens :
Lens FlatOntology.Relation` (`shapeLens_is_fold` = the "it is a Lens" fact);
reflector `saturate` with `saturate_idem` (idempotent monad) + `saturate_complete`
(complete adjacency = fixed point), pointwise to avoid funext; bridges
`genus_edges_eq_edgesK`, `k32_subgraph_of_complete`, `genus_minus_split`,
`genus_config_count_atomic`.  Original sketch:  (1) Exhibit the genus as
`universalMorphism (Relation)` reading the slash as "every distinct pair adjacent"
(reuse `SemanticAtom`); (2) **reflector idempotence** `saturate (saturate g) =
saturate g` over a finite decidable vertex carrier — the *content* of "C is a
reflector / the monad is idempotent" without the adjunction; (3) bridge `decide`
lemmas tying it to the three **species** (`SimplexSelfForm.edgesK` edge count;
`K32Adjacency.adj` bipartite restriction; `ConfigLatticeCount.cfgIdeals`).
Non-redundant: no current file states the complete adjacency *as a Lens reading*
nor states reflector idempotence — they only count edges/configs.  This **names
the genus** as the parent of the three existing species.

**Target B — fork antichain width over the config poset (MEDIUM; the real
conjecture).**  Define `P(V,s)` (height-2, decidable, `Fin`-indexed) and prove
`maxAntichainWidth (P(V,1)) = 1` and `maxAntichainWidth (P(V,2)) ≥ 2` — the first
width-≥2 antichain at `s = 2` (the `3 → 5` cycle): the first ∅-axiom witness of
"single-ℕ ends at the fork."  Needs a small antichain/poset layer, bounded by
`decide` over small finite posets.

**Target C — `L(K_n) = J(n,2)` (SKIP).**  True, pretty, but no downstream consumer;
an isolated `decide`-cell.

**Do NOT do:** the full reflective-subcategory adjunction, a `Grph`/`Cmpl`
category layer, or a simplicial-set/nerve type — all heavy, Mathlib-shaped; the
useful content is reachable via Target A.  (`mu_nu_coincidence.md` already records
that mechanizing "algebraic ⟺ ι iso" is blocked by the absence of
ω-cocontinuous-functor notions in a Mathlib-free Lean — the categorical route is
known-expensive.)

---

## 5.  One-paragraph bottom line

The `shapeLens` **is** a 213 `Lens` — a `Raw.fold` into the flat-ontology
`Relation = Raw → Raw → Bool` codomain — and its canonical (complete) reading is
the **free-complete-graph reflector** `C : Grph → Cmpl`, an *idempotent monad*
whose orbit `K_2, K_3, K_5, K_{12}, …` grows doubly-exponentially
(`n_{k+1} = C(n_k+1,2) − C(n_{k−1},2)`, `n_k ~ 2·c^(2^k)`, `c ≈ 1.24602083`),
forcibly skips `K_4`, and leaves the plane at exactly `K_5` (`γ(K_n): 0→1` at `5`;
`γ(K_{m,2}) ≡ 0` makes `N_T = 2` the *exact* bipartite ceiling).  The single-ℕ
fork is an **independent** characterization of 5 that agrees with `PairForcing` on
the answer but shares no premise — "same forcing" is unsupported, and bridging the
two would be a real theorem.  Cleanest new ∅-axiom work: **name the genus** and
prove reflector idempotence (Target A, light); the fork's own antichain (Target B)
has no Lean witness yet.  All of this is the *functor's* structure; the residue it
reads stays outside its image (self-check #0).
