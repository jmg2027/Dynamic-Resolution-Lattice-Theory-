import E213.Theory.Raw.API

/-!
# König's lemma — where ∅ stalls (the boundary marker, ∅-axiom conditional)

Compiling **König's lemma** (an infinite, finitely-branching tree has an
infinite path) down the proof-ISA (`seed/PROOF_ISA.md`).  Unlike the
probabilistic / linear-algebra / parity methods — which each closed ∅-axiom —
this one is *expected to stall*, and the value is in locating the stall exactly.

The compilation splits cleanly:

  - **the path-construction is LOOP** — given, at each infinite node, a chosen
    child that stays infinite, *iterate forever*.  This is internal (plain
    recursion), built ∅-axiom below as `konig_conditional`.
  - **the stall is a DECIDE the residue cannot supply** — to *get* that choice
    you must decide "is the subtree below this node infinite", a `Π⁰₁`
    (co-r.e.) predicate that is **not internally decidable**.  "At least one
    child is infinite" is classically `¬(both finite)`, but as a *function
    picking which child* it is an `LLPO`-instance — the exterior the no-exterior
    discipline (`seed/AXIOM/05_no_exterior.md` §5.1) forbids importing.

So König compiles to **LOOP ∘ ⟦DECIDE InfBelow⟧**, and `⟦DECIDE InfBelow⟧` is
the boundary: the first reproduced technique whose missing move *is* the
exterior, not an unbuilt internal step.  The conditional below makes this
precise — everything *given the oracle* is ∅-axiom; the oracle (`step`,
`hstep`) is exactly the un-dischargeable hypothesis.

## Relation to the residue's own infinite descent (`Theory/Raw/CoResidue`)

This is *not* the residue's first infinite object — and that sharpens the
boundary.  `CoResidue` already builds genuine infinite descent **constructively**:
`CoShape := List Bool → Bool` is this file's `T`; `allBranch := fun _ => true`
is the infinite complete self-pointing with **no leaf** (`allBranch_no_leaf`),
and `spineL` is an explicit infinite path — both *given by definition*, escaping
every finite Raw (`raw_ne_allBranch`).  `InfBelow`'s `∀ n, ∃ depth-n …` shape is
`MuNuMirror.{ascent_unbounded, depth_cofinal}`; `walk` is the anamorphism `ana`.

So the residue **has** constructive infinite paths (its own escape, `spineL`).
What König needs is different: for an **arbitrary external** tree, *decide which*
path is infinite.  The stall is therefore not "no infinite path" — it is the
**decision about a foreign structure**.  The residue's infinity is internal and
self-given; only the external `InfBelow`-decision is the import.

Companion "why" / boundary note: `theory/essays/proof_isa/konig_boundary.md`.
-/

namespace E213.Lib.Math.Combinatorics.KonigConditional

/-- The descent oracle: at each node, which child bit to take. -/
abbrev Oracle := List Bool → Bool

/-- The path built by iterating the oracle from the root. -/
def walk (step : Oracle) : Nat → List Bool
  | 0 => []
  | k + 1 => walk step k ++ [step (walk step k)]

/-- **The LOOP (internal).**  If the oracle preserves "infinite-below" (`Inf`)
    and the root is infinite-below, every node on the walk is infinite-below —
    by plain induction.  No choice, no decision: this is the part the residue
    *can* do. -/
theorem walk_inf (step : Oracle) (Inf : List Bool → Prop)
    (hstep : ∀ s, Inf s → Inf (s ++ [step s])) (root : Inf []) :
    ∀ k, Inf (walk step k)
  | 0 => root
  | k + 1 => hstep (walk step k) (walk_inf step Inf hstep root k)

/-- ★ **König, conditional on the oracle (∅-axiom).**  Given a `step` oracle
    that keeps the walk infinite-below (`hstep`) and an infinite root, the
    infinite path exists: a `node : ℕ → List Bool` starting at the root, every
    node in the tree (`Inf ⟹ mem`), each extending the previous by one bit.

    The hypotheses `step`/`hstep` are the **entire** non-constructive content:
    discharging them from "the tree is infinite" needs a decision for `Inf`
    (infinite-below), which is the residue-external `DECIDE` — the stall. -/
theorem konig_conditional
    (T : List Bool → Bool) (step : Oracle) (Inf : List Bool → Prop)
    (hInfMem : ∀ s, Inf s → T s = true)
    (hstep : ∀ s, Inf s → Inf (s ++ [step s])) (root : Inf []) :
    ∃ node : Nat → List Bool,
      node 0 = [] ∧
      (∀ k, T (node k) = true) ∧
      (∀ k, node (k + 1) = node k ++ [step (node k)]) :=
  ⟨walk step, rfl,
   fun k => hInfMem _ (walk_inf step Inf hstep root k),
   fun _ => rfl⟩

/-- "Infinite below `s`": descendants of every length — the predicate the stall
    cannot decide.  (`InfBelow T [] = T` is infinite; the König hypothesis.) -/
def InfBelow (T : List Bool → Bool) (s : List Bool) : Prop :=
  ∀ n, ∃ s', s'.length = n ∧ T (s ++ s') = true

/-- The classically-trivial, constructively-unavailable step the oracle needs:
    *an infinite node has an infinite child*.  Stated, **not** proved — proving
    it as a `Bool`-valued choice is the `LLPO` import that marks the boundary.
    (Its `∨` is decided by deciding `InfBelow`, which is `Π⁰₁`.) -/
def InfChildExists (T : List Bool → Bool) : Prop :=
  ∀ s, InfBelow T s → InfBelow T (s ++ [false]) ∨ InfBelow T (s ++ [true])

/-! ## König's infinity, located in the residue (the νF bridge)

The narrative above states `T = CoShape` and `walk = ana`; this section makes the
identification *theorems*.  The infinite branch König's lemma decides about is a
**νF inhabitant** (`SlashNu`) — the residue's own escape — and is reached by **no
finite Raw**.  So "which Raw chunk is the König infinity?" has a proved answer:
*none* — the infinity is the escape (reached by no finite Raw), never a finite Raw.
This is the code form of "∞ must be walked (kept a transition), never frozen into
a finite value": the branch is held as the bit-stream the oracle generates, and
its completion is a νF escape, not a finite object. -/

open E213.Theory.Raw.CoResidue
open E213.Theory (Raw)

/-- The bit-stream of the König branch: the bit the oracle picks at each stage. -/
def konigBranch (step : Oracle) : Nat → Bool := fun k => step (walk step k)

/-- ★ **König's infinite branch IS a residue escape.**  The branch's bit-stream
    packages as an exact slash-νF co-tree (`SlashNu`) — the residue's own escape
    family (`CoResidue.boolSpineSlashNu`).  The infinite branch is not foreign to
    the residue; it is one of the residue's own infinite self-pointings. -/
def konigBranchNu (step : Oracle) : SlashNu := boolSpineSlashNu (konigBranch step)

/-- The König branch is a genuine slash-νF co-tree: consistent and anti-reflexive. -/
theorem konig_branch_is_nu (step : Oracle) :
    Consistent (konigBranchNu step).val ∧ AntiRefl (konigBranchNu step).val :=
  (konigBranchNu step).property

/-- ★ **The König infinity is reached by no finite Raw.**  The branch-escape
    differs (as a labelled co-tree) from every finite Raw's embedding
    (`rawToSlashNu`), by `boolSpine_escapes`.  This is the proved answer to "which
    Raw chunk is the infinity": none — it is the escape, no finite Raw. -/
theorem konig_infinity_no_finite_raw (step : Oracle) (r : Raw) :
    (rawToSlashNu r).val ≠ (konigBranchNu step).val :=
  fun h => boolSpine_escapes (konigBranch step) r.val h.symm

/-- ★★ **The König infinity, located in the residue (capstone).**  Given the König
    hypotheses (an oracle keeping the walk infinite-below, an infinite root), the
    infinite branch is a νF inhabitant that (a) lies in the tree `T` at every
    finite stage and (b) is reached by no finite Raw.  So the object König's
    `DECIDE` must adjudicate is the residue's escape (νF) — never a finite Raw,
    never a frozen value.  The stall is a decision *about* this escape, not a
    failure to *have* it. -/
theorem konig_infinity_is_nu_escape
    (T : List Bool → Bool) (step : Oracle) (Inf : List Bool → Prop)
    (hInfMem : ∀ s, Inf s → T s = true)
    (hstep : ∀ s, Inf s → Inf (s ++ [step s])) (root : Inf []) :
    (∀ k, T (walk step k) = true)
    ∧ (∀ r : Raw, (rawToSlashNu r).val ≠ (konigBranchNu step).val) :=
  ⟨fun k => hInfMem _ (walk_inf step Inf hstep root k),
   fun r => konig_infinity_no_finite_raw step r⟩

end E213.Lib.Math.Combinatorics.KonigConditional
