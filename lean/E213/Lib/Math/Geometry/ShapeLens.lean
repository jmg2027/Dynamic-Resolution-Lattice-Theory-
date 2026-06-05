import E213.Theory.Raw.API
import E213.Lens.LensCore
import E213.Lens.FlatOntology
import E213.Lib.Math.Geometry.AngleStructure.SimplexSelfForm
import E213.Lib.Math.Geometry.BipartiteDecomp.K32Adjacency
import E213.Lib.Math.Geometry.BipartiteDecomp.ConfigLatticeCount

/-!
# `shapeLens` — the geometric-realization genus (∅-axiom)

The `shapeLens` (naming: Mingu Jeong) is the *genus* "read the slash geometrically:
a point per object, a line per relation."  This file **names** that genus — the
parent object the three existing species (`SimplexSelfForm` edge count,
`K32Adjacency` bipartite restriction, `ConfigLatticeCount` configuration count)
are readings *of* — and proves the one structural fact none of the species states:
the **complete-graph reflector is idempotent** (its monad is idempotent).

Deep-research synthesis: `research-notes/geometric/shapelens_functor.md` (the
`shapeLens` = the free-complete-graph reflector `C : Grph → Cmpl`, an idempotent
monad).  Per RA-C's recommendation this records the *reflector fixed point*
(completeness = idempotent saturation) rather than building the categorical
adjunction (heavy, Mathlib-shaped, and the absence of ω-cocontinuous-functor
notions in a Mathlib-free Lean blocks it — `mu_nu_coincidence.md`).

## What is recorded

1. **It is a `Lens`.**  `shapeLens : Lens (Raw → Raw → Bool)` is a literal term —
   a `Raw.fold` into the §6.3 flat-ontology codomain `FlatOntology.Relation`
   (`Lens/FlatOntology.lean`, "point = object" = `Object1`, "line = relation" =
   `Relation`).  Its combine is the **complete join** `completeJoin`.
2. **Reflector idempotence.**  `saturate` (add every missing edge) is idempotent
   (`saturate_idem`); the complete adjacency `completeAdj` is its fixed point
   (`saturate_complete`).  This is the content of "C is a reflector / the monad
   `T = C` is idempotent" without the adjunction.  Stated **pointwise** (function
   equality would be funext = `Quot.sound`-dirty), exactly as `raw_initial`.
3. **Genus → species bridges.**  `decide`/`rfl` lemmas exhibiting the three
   species as readings of this genus: the complete graph's edge count *is*
   `SimplexSelfForm.edgesK`; the bipartite `K32Adjacency.adj` is a *subgraph* of
   the complete adjacency (the §6.2 split keeps the cross pairs, drops the
   within-kind ones); the configuration count at the atomic stage is
   `ConfigLatticeCount.cfgIdeals 5 7`.

The complete reading is the **maximal** end of the connection-criterion dial:
`completeJoin` saturates every distinct pair regardless of the substructure, so
the only datum it retains off the diagonal is the vertex carrier — the homogeneity
that makes `K_∞ ≡ point` (§6.5).  All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Geometry.ShapeLens

open E213.Theory (Raw)
open E213.Lens (Lens)

/-! ## §1 — the complete-graph reflector and its idempotence -/

/-- The complete adjacency on a decidable-equality carrier: **every distinct pair
    is adjacent** (the maximal end of the connection dial). -/
def completeAdj {V : Type} [DecidableEq V] (u v : V) : Bool := decide (u ≠ v)

/-- The reflector `C : Grph → Cmpl` at the adjacency level: **add every missing
    edge** (`G ↦ K_{|V|}`).  Off the diagonal it forces adjacency; on the diagonal
    it leaves the input untouched. -/
def saturate {V : Type} [DecidableEq V] (g : V → V → Bool) : V → V → Bool :=
  fun u v => g u v || completeAdj u v

/-- The genus's **combine** = the complete join: union the two subgraphs and
    complete the join across.  Because the complete reading is maximal, this
    saturates every distinct pair regardless of `g, h` — the substructure is
    forgotten off the diagonal (`K_∞ ≡ point`, §6.5). -/
def completeJoin {V : Type} [DecidableEq V] (g h : V → V → Bool) : V → V → Bool :=
  fun u v => g u v || h u v || completeAdj u v

/-- ★ **The complete graph has every distinct pair adjacent.** -/
theorem completeAdj_complete {V : Type} [DecidableEq V] {u v : V} (h : u ≠ v) :
    completeAdj u v = true := by
  unfold completeAdj; exact decide_eq_true h

/-- ★ **No self-loops.**  `completeAdj` is irreflexive. -/
theorem completeAdj_irrefl {V : Type} [DecidableEq V] (u : V) :
    completeAdj u u = false := by
  unfold completeAdj; exact decide_eq_false (fun hne => hne rfl)

/-- ★★ **Reflector idempotence** (`T² ≅ T`): saturating twice = saturating once.
    Stated pointwise to avoid funext (`Quot.sound`).  This is the idempotent-monad
    fact — the content of "C is a reflector" — captured ∅-axiom. -/
theorem saturate_idem {V : Type} [DecidableEq V] (g : V → V → Bool) (u v : V) :
    saturate (saturate g) u v = saturate g u v := by
  unfold saturate
  cases hd : completeAdj u v <;> cases g u v <;> rfl

/-- ★★ **The complete graph is the reflector's fixed point** (the `T`-algebras are
    the complete graphs): `saturate completeAdj = completeAdj`, pointwise. -/
theorem saturate_complete {V : Type} [DecidableEq V] (u v : V) :
    saturate (completeAdj (V := V)) u v = completeAdj u v := by
  unfold saturate; cases hd : completeAdj u v <;> rfl

/-- ★ **The combine is the saturating (complete) join**: across any distinct pair
    `completeJoin g h` is adjacent, whatever the operand subgraphs — the reflector
    acting at the combine level. -/
theorem completeJoin_saturates {V : Type} [DecidableEq V] (g h : V → V → Bool)
    {u v : V} (huv : u ≠ v) : completeJoin g h u v = true := by
  unfold completeJoin
  rw [completeAdj_complete huv]
  cases g u v <;> cases h u v <;> rfl

/-! ## §2 — the genus as a `Lens` (a `Raw.fold` into the flat-ontology codomain) -/

/-- The empty adjacency — a single object, no relation (the atom reading). -/
def emptyRel : Raw → Raw → Bool := fun _ _ => false

/-- ★ **The `shapeLens` genus.**  A `Lens` into the §6.3 flat-ontology
    `Relation = Raw → Raw → Bool` (`Lens/FlatOntology.lean`): atoms read as the
    empty relation, the slash read as the complete join.  Being a term of type
    `Lens _` *is* the statement "the `shapeLens` is a `Lens` / a `Raw.fold`." -/
def shapeLens : Lens E213.Lens.FlatOntology.Relation :=
  ⟨emptyRel, emptyRel, completeJoin⟩

/-- ★ The genus's view is exactly `Raw`'s catamorphism into the relation algebra. -/
theorem shapeLens_is_fold (r : Raw) :
    shapeLens.view r = r.fold emptyRel emptyRel completeJoin := rfl

/-- ★ The atoms read as the empty relation. -/
theorem shapeLens_view_a : shapeLens.view Raw.a = emptyRel := rfl
theorem shapeLens_view_b : shapeLens.view Raw.b = emptyRel := rfl

/-! ## §3 — genus → species bridges (the three species are readings of this genus)

Counts taken over a finite vertex label set (`Nat`), matching the species cells
(`K32Adjacency` and `edgesK` are `Nat`-indexed); the genus reflector above is
carrier-polymorphic, instantiated here at `Nat`. -/

/-- Edges of `g` over a finite vertex list `vs` (ordered pairs `u < v`). -/
def edgeCountOn (g : Nat → Nat → Bool) (vs : List Nat) : Nat :=
  (vs.map (fun u => (vs.filter (fun v => decide (u < v) && g u v)).length)).foldr (· + ·) 0

/-- The atomic 5 vertices `{0,1,2,3,4}` (= the 4-simplex skeleton `K_5`). -/
def v5 : List Nat := [0, 1, 2, 3, 4]

/-- ★ **Genus → `SimplexSelfForm`.**  The complete graph on the atomic 5 vertices
    has `edgesK 5 = 10` edges — the genus's edge count *is* the species `edgesK`. -/
theorem genus_edges_eq_edgesK :
    edgeCountOn (fun u v => completeAdj u v) v5
      = E213.Lib.Math.Geometry.AngleStructure.SimplexSelfForm.edgesK 5 := by decide

/-- ★ **Genus ⊇ `K32Adjacency`.**  Every bipartite edge is a complete edge: the
    §6.2 `K_{3,2}` adjacency is a *subgraph* of the complete adjacency (the
    bipartite split is a restriction of the maximal/complete reading). -/
theorem k32_subgraph_of_complete :
    v5.all (fun u => v5.all (fun v =>
      !E213.Lib.Math.Geometry.BipartiteDecomp.K32Adjacency.adj u v
        || completeAdj u v)) = true := by decide

/-- ★ **The split drops the within-kind edges.**  Complete `K_5` has `10` edges;
    the bipartite restriction keeps only the `6` cross pairs — the `4` within-kind
    edges are exactly what the §6.2 split removes (cf.
    `K32Adjacency.simplex_minus_within`). -/
theorem genus_minus_split :
    edgeCountOn (fun u v => completeAdj u v) v5 = 10
    ∧ edgeCountOn (fun u v =>
        E213.Lib.Math.Geometry.BipartiteDecomp.K32Adjacency.adj u v) v5 = 6 := by
  decide

/-- ★ **Genus → `ConfigLatticeCount`.**  The configuration count of the genus's
    generative cycle at the atomic stage `(V,s) = (5,7)`. -/
theorem genus_config_count_atomic :
    E213.Lib.Math.Geometry.BipartiteDecomp.ConfigLatticeCount.cfgIdeals 5 7
      = 72304608555084001 :=
  E213.Lib.Math.Geometry.BipartiteDecomp.ConfigLatticeCount.cycle3

/-! ## §4 — master -/

/-- ★★★ **Master.**  The `shapeLens` genus, ∅-axiom: it is a `Lens` (a `Raw.fold`
    into the flat-ontology `Relation`); its complete-graph reflector is idempotent
    with the complete adjacency as fixed point (the idempotent monad); and the
    three species (`edgesK`, `K32Adjacency.adj`, `cfgIdeals`) are readings of it —
    the genus's edge count is `edgesK 5`, the bipartite graph is a subgraph of the
    complete one, and the atomic configuration count is `cfgIdeals 5 7`. -/
theorem shape_lens_master :
    (∀ r : Raw, shapeLens.view r = r.fold emptyRel emptyRel completeJoin)
    ∧ (∀ (V : Type) [DecidableEq V] (g : V → V → Bool) (u v : V),
        saturate (saturate g) u v = saturate g u v)
    ∧ (∀ (V : Type) [DecidableEq V] (u v : V),
        saturate (completeAdj (V := V)) u v = completeAdj u v)
    ∧ (edgeCountOn (fun u v => completeAdj u v) v5
        = E213.Lib.Math.Geometry.AngleStructure.SimplexSelfForm.edgesK 5)
    ∧ (v5.all (fun u => v5.all (fun v =>
        !E213.Lib.Math.Geometry.BipartiteDecomp.K32Adjacency.adj u v
          || completeAdj u v)) = true) :=
  ⟨shapeLens_is_fold,
   fun _ _ g u v => saturate_idem g u v,
   fun _ _ u v => saturate_complete u v,
   genus_edges_eq_edgesK,
   k32_subgraph_of_complete⟩

end E213.Lib.Math.Geometry.ShapeLens
