# LEDGER — bilingual glossary (internal ↔ classical)

Every internal term of the rederivation mapped to its nearest classical
object and the classical theorems imported or reproduced. The point of
the ledger (program memo, process rule 2): internal vocabulary is a moat
against external audit; this table is the device that catches a known
result renamed as a new one. Collected from the three theory documents;
consult each for the proof-level detail.

## Core objects

| Internal term | Nearest classical object | Theorems imported / reproduced | Source |
|---|---|---|---|
| `Tree` (F-obj carrier), atoms `a,b`, `pair{x,y}` | free term algebra on 2 constants + a symmetric anti-reflexive binary constructor; unordered-pair normal form | constructor injectivity/distinctness (∅-axiom Lean `Tree.lean`); normal forms under a total term order | SPEC §1; `order_invariance.md` T1–T4 |
| `object1 : Tree → Tree → Bool`, self-indication | the indicator/characteristic function `x ↦ (x = r)` (Saussurean *valeur*: identity by difference) | faithfulness (injective, ∅-axiom); image = single-point indicators | `Object1.lean` |
| residue / `object1_not_surjective` | Cantor diagonal; Lawvere fixed-point schema (Cantor, Russell, Gödel, Turing, Tarski as one move) | diagonal `p x = ¬ f x x` outside every self-cover (∅-axiom, no `funext`) | `Object1.lean` |
| the two events `link`/`resolve` | a labelled transition system; Petri-net-like enabling | — (definitions) | SPEC §2 |

## Order-invariance (Q1)

| Internal term | Nearest classical object | Theorems imported / reproduced | Source |
|---|---|---|---|
| Persistence + Diamond lemmas | strong confluence / diamond property (Keller 1976; Huet 1980); local commutation | Church–Rosser via tiling; **Newman's lemma assessed and *not* used** (no termination assumed) | `order_invariance.md` §3–§4 |
| causal poset **D**, downsets, executed sets | poset; order ideals; Birkhoff representation | reachable states ↔ finite downsets form a distributive lattice | §5, Cor 5.8 |
| runs = linear extensions | linear extensions; topological sort; Szpilrajn (finite) | finite posets have linear extensions | Thm 5.7, 7.1 |
| maximal run / ω-labeling | ω-type linear extension / natural labeling (causal-set literature) | countable poset, finite principal ideals ⇒ ω-extension (proved inline) | Lemma 6.3 |
| weak fairness | weak (justice) fairness (Manna–Pnueli) | fairness ⇔ completeness; stability collapses strong→weak | §6 |
| configurations | Winskel prime event structures (conflict-free) | conflict-free ES ↔ poset; configurations = downsets | §9.2 |
| (compared, matched only degenerately) | Mazurkiewicz trace monoid | trace equivalence = dependence-poset equality | §9.3 |
| (compared) | antimatroids / poset antimatroids (Korte–Lovász–Schrader) | intersection-closed antimatroids = poset antimatroids | §9.4 |

## Grading obstruction (Q2, Q3)

| Internal term | Nearest classical object | Theorems imported / reproduced | Source |
|---|---|---|---|
| height `h`, rank function, graded poset, cover vs **chord** | graded posets (Stanley EC I §3.1); transitive reduction | "graded ⟺ all saturated ⊥-chains equal-length" (reproved); rank forced along covers | `grading_obstruction.md` §2, §4 |
| stratification | potential/consistent labeling of a DAG / precedence graph | existence ⟺ all source-to-node path lengths equal (reproved as Thm 3.3) | §3 |
| `Grad(D)`, initial/terminal | coslice (under) category; universal properties | identity initial in a coslice (**flagged deflationary**); non-existence proofs bespoke | §6 |
| `σ`-gauge dilemma | symmetry breaking; invariant maps constant on orbits | elementary group action on a poset | Lemma 6.6 |
| tree counts by leaf-count | **OEIS A063894** (2 atoms, distinct unordered children); Somos g.f. | recurrence from T1; hand-checked to n=8; unique match | §7 |
| layer widths by depth | **OEIS A103410 = A002658** (planted 3-trees by height) | `N`-recurrence; 1-gen/2-gen equality proved | §7 |
| cumulative census | **OEIS A108225** | recurrence equivalence along the orbit | §7 |
| **rejected** candidate | Wedderburn–Etherington **A001190** | differs on both counts (atoms, self-pair) — recorded to preempt misidentification | §7 |
| doubly-exponential growth | quadratic-map recurrences (Aho–Sloane 1973) | sandwich bounds proved inline | §7 |
| comb / caterpillar | path-like binary trees | `2^{k−1}` count; `λ = δ+1` on combs | §5 |
| level = generation | breadth-first closure stages of an inductive datatype | `gen = depth` (Prop 5.1) | §5 |

## Event-primary / duality (Q4)

| Internal term (F-ev) | Nearest classical object | Imported/used theorems | Source |
|---|---|---|---|
| `Ev`, `D` (design P) | free term algebra / initial algebra of a polynomial functor | structural recursion, constructor injectivity | `event_primary_design.md` §3 |
| `Operand = Pole ⊕ D` | disjoint sum; poles = the two roles of the primordial contrast | — | §3 |
| `Φ`, `β`, forward/reflect | (bi)simulation, forward–backward simulation, LTS isomorphism (Milner; Lynch–Vaandrager) | soundness of simulation for reachability transfer | §7 |
| Design S rejection | occurrence identification = quotient by positional equivalence | quotient constructions (**rejected** under the no-quotient rule R6) | §2.2 |

## Provenance

OEIS entries A063894, A108225, A103410, A002658, A001190 fetched and
checked 2026-07-06 via the configured proxy. No theorem rests on
machine output: every enumerator witness is re-derived by hand in the
prose. Lean facts (`Tree.lean`, `Object1.lean`, `Grading.lean`) are
∅-axiom (`#print axioms` empty; 58 theorems checked).
