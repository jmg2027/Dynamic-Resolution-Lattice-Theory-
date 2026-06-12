# Proof-engineering templates — how 213 makes everything `rfl`/`decide`-able

The companion to `proof_pattern_census.md`.  The census measured *what* the proof
distribution is (decide+rw dominant, residue-rooted, form-converges/content-diverges).
This file reverse-engineers the *craft*: the design techniques that make claims close by
`rfl`/`decide`, the reduction templates that massage a goal into closeable shape, and the
near-universal **code-structure template** every file is written to.

One discipline underlies all of it: **push every claim down to a *computation*** — make the
objects Bool-valued, closed-universe, and definitionally-matching, so the proof is a
*reduction* (`rfl`) or a *finite decision* (`decide`); and where a black-box closer would
pull `propext`/`Quot.sound`, replace it with a *structural* one.  This is the engineering
form of the proof-level Trajectory Principle (`census §5`): nothing collapses to a black box.

All counts are corpus-wide (`lean/E213`, 1980 files); regenerable like the census.

---

## Part I — the four enabling moves (make `rfl`/`decide` *applicable*)

**1. Bool-valued reflection — the central move (1,899 `→ Bool` / `: Bool` defs).**
Predicates are written as *computable `Bool` functions*, not `Prop`.  Then a claim `P x` is
stated as `P x = true`, which the kernel *computes* — closed by `rfl` (if it reduces) or
`decide` (finite search).  Canonical: `Lens/Bool213/Raw.lean` encodes truth itself as
computation — `T := Raw.a`, `F := Raw.b`, `isBool : Raw → Bool`, `booleanProj` (the
`Raw.fold T F and` catamorphism).  Because the predicate *is* a function, "proving" it is
*running* it.  (This is why §6 of the census found `Bool.casesOn` the #1 recursor at 1,681
and `Decidable.casesOn` #4 at 562 — Bool-reflection is the substrate.)

**2. Closed-universe encoding (no external types → everything computes).**  External
objects are encoded as `Raw` shapes so operations stay `Raw → Raw` and *evaluate*: Bool as
two atoms (move 1), `Nat213` as a count-Lens, cohomology cochains as `Fin n → Bool`.  The
decidability that powers `decide` comes from **`Theory.instDecidableEqRaw` (4,459 cites)** +
**`deriving DecidableEq` (80)** — not hand-written instances (only 8).  Once a type has
decidable equality (Raw does, structurally, via `Tree`), every finite proposition over it is
`decide`-able for free.  (`deriving` is the lever; `deriving Repr` (50) is the debug
companion.)

**3. Definitional-match design (engineer the def so `rfl`/`cases <;> rfl` closes).**  The
defs are *shaped* so the cases reduce definitionally.  `Cohomology/Infrastructure/BoolXORFold`
is the exemplar: its recursive `psiNatPos` uses base case `v 0` (**"not `false`** — keeps
definitional match with the `Fin (n+1)`-cochain lifts"), so the AC identity closes by
`cases a <;> cases b <;> cases c <;> cases d <;> rfl` — pure finite enumeration, *"without
needing `funext` (and thus without `Quot.sound`)"* (its own docstring).  `abbrev` (207) and
`@[reducible]` (22) keep definitions transparent so `rfl`/`decide` reduce *through* them;
`@[simp]` is barely used (24) — normalization is by design, not by a simp-set.

**4. Finite enumeration (quantify over a finite domain so the closer can sweep).**  ∀-claims
are pushed onto finite domains (`Bool`, `Fin n`, Bool-tuples) so `decide`/`cases <;> rfl`
enumerates.  `cases _ <;> ... <;> rfl` is the bounded-enumeration closer; `<;> decide` (514)
and `<;> rfl` (347) close case-bundles uniformly.  (Methodology Pattern #2: where Lean-core
won't synthesise `Decidable (∀ f : Fin n → Bool, P f)`, lift via an explicit pointwise
`mkFn b0 … b_{n-1}` and `decide` over the `2^n` Bool tuple — equivalent by elementwise
`rfl`.)

## Part II — the reduction templates (massage a goal into closeable shape)

When a goal is not *yet* `rfl`/`decide`-shaped, a small fixed set of moves reshapes it:

| template | count | what it does |
|---|---:|---|
| `show …` / `change …` → `rfl`/`decide` | 6,212 `show` | restate the goal as the defeq *computable* form the kernel can reduce |
| `unfold …` → `decide` | exposes the computable core of a `def` so `decide` can run |
| `rw [chain]` / `ring_nat`/`ring_intZ` → `rfl` | 793 `…; rfl` | normalize (hand-rolled ring, §1 census) until both sides are defeq |
| `cases`/`rcases` … `<;> rfl` \| `<;> decide` | 861 | split a finite goal, close every branch by the same closer |

The skeleton is always *reshape → reduce/decide* — never an opaque `simp`/`ring`/`omega`
(suppressed: 158 / 0 / 116).  This is the surface form of the census's `have→show→rw→exact`
forward-explicit skeleton.

## Part III — the propext-free closers (the ∅-axiom substitutes)

The naive `rfl`/`decide`/`simp` often pull `propext` or `Quot.sound` through
`DecidableEq`-iff lemmas or `funext`.  The corpus systematically replaces them with
*structural* closers that stay strict ∅-axiom — this is the discipline that keeps `decide`
honest:

| ∅-axiom closer | count | replaces |
|---|---:|---|
| `noConfusion` (constructor disjointness) | 489 | `decide`/`simp` for `≠` and constructor-contradiction (e.g. `T_ne_F` via `congrArg Subtype.val` + `Tree.noConfusion`) |
| `decide_eq_true` / `of_decide_eq_true` | 251 / 97 | the `Bool`↔`Prop` bridge used *forward* (avoids `decide_eq_true_eq`, which is propext) |
| `Int.NonNeg` constructor inversion (Pattern #8) | 82 | Lean-core `Int` ordering lemmas (all propext-tainted) |
| `congrArg Subtype.val` | 25 | unwrap the canonical-form `Subtype` to its `Tree`, then `noConfusion` |

So even the "trivial" closers are hand-chosen for axiom-cleanliness: `noConfusion` not
`decide` for `≠`; `of_decide_eq_true` not `decide_eq_true_eq`; `Int.NonNeg` `cases` not
`omega`.  The strict-∅-axiom regime is enforced *at the closer level*.

## Part IV — the code-structure template (how files are written)

Near-universal, enforced by convention (and the org-audit skill):

```
import E213.<API surface>                    -- never reach into Theory.Raw.* submodules; use .API
/-!
# <Namespace> — <one-line what>
<prose: the Lens meaning; STRICT ∅-AXIOM tag; cites to seed/AXIOM/§ where relevant>
-/
namespace E213.<Path.Matching.Namespace>     -- path = namespace
open E213.<deps> (selective)                 -- one open block, top of file
/-! ## §1 — <section> -/
def …                                         -- Bool-valued / closed-universe (Part I)
/-- <docstring> -/ theorem foo … := by <reshape → decide/rfl>
/-! ## §2 — … -/
…
/-- ★★★ **<capstone>.** <bundles the file's results> -/
theorem …_capstone : <A ∧ B ∧ …> := ⟨…⟩      -- the conjunction capstone
end E213.<Path>
```

Measured adherence:
- **1,978 / 1,980 files** open with a module docstring `/-!` (99.9 %).
- **3,814** `/-! ## §` section markers (avg ~2/file); the section-graded layout is standard.
- **15,265 ★** importance-grade markers — the pervasive `★ / ★★ / ★★★` convention ranks
  theorems (★★★ = the file's load-bearing / capstone result, ★ = supporting).
- **466 files** carry a `capstone` decl — a conjunction theorem (`⟨…, …, …⟩`) bundling the
  file's results into one citable statement (this is *why* `∧` is 10,781 in the census and
  anonymous `⟨⟩` ≈ one per theorem: the capstone-bundle convention).
- **1,847** open a namespace matching their path; **74** cite `seed/AXIOM` in the docstring.
- Docstring tags: `STRICT ∅-AXIOM`, the `Lens meaning:` line, and a `theory/<mirror>` or
  `seed/AXIOM/§` reference are the standard prose furniture.

## Part V — domain file archetypes (the recurring per-domain templates)

Each domain has a stereotyped file shape, all bottoming out in `decide`/`rfl`:

**Physics — the atomic-bracket archetype** (`Lib/Physics/Nuclear/DeuteronBinding.lean`,
exemplar): docstring gives the DRLT formula + observed value + atomic decomposition; then
`def E_d_num := NS * NT` (the observable as an *atomic-primitive expression*),
`theorem E_d_num_eq_6 := by decide` (verify it computes to the atom),
`theorem E_d_bracket : 2000 < 2224 ∧ 2224 < 2500 := by decide` (the prediction bracket — all
concrete `Nat`), `theorem …_simplicial : … ∧ NS=3 ∧ NT=2 ∧ d=5 := by decide` (the
atomic-source capstone).  *Everything is concrete `Nat` arithmetic, so every line is
`decide`* — this is precisely why Physics is 55 % `by decide` (census §3).  (The bracket is on
the observed literal — the `reflexivity_gap.md` caveat — but the *template* is the point here.)

**Number systems — the approximant-sequence archetype** (`Real213/PhiConvergence.lean`):
build the approximant sequence (`pellDen…`), then `…_strictly_increasing` →
`bracket_width_shrinks` → `convergents_nest` → `…_is_unique_nested_limit`.  The template is
*monotone + nested + shrinking → unique limit*, with the **forward direction closing
universally** and the backward only under compatible-denominator hypotheses (Lesson 7).  Cut
predicates are `Nat → Nat → Bool` (Part I move 1), so per-level checks are `decide`.

**Atomicity — the pure-ℕ forcing archetype** (`Theory/Atomicity/PairForcing.lean`): define
the arithmetic predicates (`Decomp`, `IsAlive`, `Atomic`, `half`, `count` — `Prop`/`Nat`,
*never touching Raw*), prove small `private` helper iffs by `cases`/induction
(`half_eq_one_iff : half p = 1 ↔ p = 2 ∨ p = 3`), assemble the forcing iff
(`count_eq_one_iff`).  The forcing chain (NS,NT,d)=(3,2,5) lives entirely in computable ℕ
(census foundations finding) so the leaves are `decide`/`rfl`.

**Cohomology — the enumeration archetype**: define the complex / cochain space as
`Fin (binom n k) → Bool`, compute Betti numbers, close by `decide` / `cases <;> decide` over
the finite cochain space (the marathon-anatomy `decide`/`cases`-dominant cluster, census §7).

## Part VI — the deepest move: algebra automation that *bottoms out in `rfl`*

`ring_nat`/`ring_intZ` (714 + 720 uses) are not Mathlib's `ring`; they are **reflection
tactics** (`Meta/Nat/PolyNatMTactic.lean`).  The `elab` (1) reads the goal `lhs = rhs : Nat`,
(2) **reifies** both sides into a `PE` polynomial-expression AST over a shared atom list, (3)
computes a canonical normal form `PE.norm` (sorted monomial list), and (4) closes with
**`mkEqRefl (PE.norm peL)`** — the two reified normal forms are equal *by `rfl`* exactly when
the identity holds — then `poly_idM` transports that `rfl` back to the original goal.

So even ring-equality is reduced to **`rfl` on a reified normal form**.  This is the purest
instance of the whole discipline: rather than trust an opaque `ring`, the corpus *reflects*
the algebra into a datatype, *computes* the normal form, and lets `rfl` certify it — strict
∅-axiom, decidable, transparent.  `(a+b)*(a+b) = a*a + 2*(a*b) + b*b` is proved by reifying
both sides to the same monomial-list and `rfl`.  The hand-rolled ring is "truth = computation"
applied to its own automation.

## Part VII — the capstone-bundle template, the ★ grading, and Fin-encoding transfer

**The capstone is a ~7-fact conjunction** (284 capstone theorems, mean **7.1 conjuncts**,
max 38).  The file-closing template is: bundle the file's results into one citable
`theorem …_capstone : A ∧ B ∧ … := ⟨pa, pb, …⟩`.  This single convention *generates* two
census-level facts: the corpus's `∧` count (10,781) and the ≈one-anonymous-`⟨⟩`-per-theorem
ratio (the capstone tuple).  Distribution: most capstones bundle 3–8 facts; the long tail
(20–38 conjuncts) are the big "pure observables" / "tower-drops" capstones.  A capstone is
how a 213 file says "here is everything this file established, in one handle."

**The ★ grading is a 3-tier importance convention** — 15,265 ★ characters corpus-wide, in
`★` (supporting) / `★★` (major) / `★★★` (load-bearing / the capstone).  It is documentation,
not Lean, but it is *pervasive and consistent* (≈8 ★ per file), and it is how a reader (or
the next session) navigates a file to its load-bearing result without reading every proof.

**A fifth enabling move — Fin-encoding transfer.**  Beyond `deriving DecidableEq` (Part I
move 2), finite structured types borrow decidability by being made defeq to `Fin n`:
`instance : DecidableEq Sym3 := inferInstanceAs (DecidableEq (Fin 6))`,
`… Sym2 := … (Fin 2)`, `C2_6 := … (Fin 64)`, `Vertex := … (Fin 5)`,
`Aut_K := … (Sym3 × Sym2 × C2_6)` (`Lib/Physics/Symmetry/AutKType.lean`,
`AtomicBase/Existence.lean`).  Encode a finite group/index type as `Fin n` (or a product of
them) and *all* of `DecidableEq` + decidable-∀ + enumeration transfer for free — so claims
over them are `decide`.  The *only* genuinely hand-written `DecidableEq` in the corpus is
**`Raw`** itself (`Theory/Raw/Core.lean:28`, because Raw is a `Subtype { t : Tree // canonical }`)
and its `RawBy cmp` variant; the p-adic `Zp.unit0_decidable` is the one notable hand-written
non-finite `Decidable`.  So decidability has exactly three sources: hand-write it once for
`Raw`, `deriving` it for data types (80), or transfer it from `Fin n` for finite structures.

## The one-line synthesis

> 213 is engineered so that **truth is computation**: objects are Bool-valued and
> closed-universe, defs are shaped to reduce definitionally, quantifiers are pushed onto
> finite domains — so a proof is a *reduction* (`rfl`) or a *finite decision* (`decide`),
> and the few non-trivial closers are hand-chosen *structural* ones (`noConfusion`,
> `Int.NonNeg`, `Subtype.val`) to stay strict ∅-axiom.  The file template (docstring → `§`
> sections → ★-graded lemmas → ★★★ capstone) is the human-navigability layer over that one
> uniform computational substrate.  *Making everything `rfl`/`decide`-able is not a proof
> style — it is a design discipline applied at the definition layer*, and the proof layer
> (census) is its downstream shadow.

---

## Regeneration

```sh
rg -c 'deriving DecidableEq' lean/E213 -g '*.lean' | awk -F: '{s+=$2}END{print s}'   # 80
rg -c '→ Bool|: Bool\b' lean/E213 -g '*.lean' | awk -F: '{s+=$2}END{print s}'        # ~1899
rg -o '★' lean/E213 -g '*.lean' | wc -l                                              # 15265
rg -l '^/-!' lean/E213 -g '*.lean' | wc -l                                           # 1978
for c in noConfusion of_decide_eq_true Int.NonNeg; do printf "%-18s " $c; rg -o "$c" lean/E213 -g '*.lean'|wc -l; done
```

## Open threads

- **Quantify the reshape→close templates per layer** — does Physics (55 % decide) use
  `show→decide` more than Meta (rw-engine)?  (Pairs with census §3.)
- **The capstone-bundle anatomy** — average conjunct count of the 466 capstones; do they
  cite only same-file lemmas (true bundles) or pull cross-file (synthesis capstones)?
- **`deriving DecidableEq` coverage** — which inductive types *lack* it and therefore force
  hand-written `decide`-substitutes (the 8 manual `Decidable` instances).
