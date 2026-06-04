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

end E213.Lib.Math.Combinatorics.KonigConditional
