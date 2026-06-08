import E213.Lib.Math.Logic.KonigBridge

/-!
# Reverse Mathematics 213 — GB-cont5: global WKL ⟺ Heine–Borel (the ∅-axiom half)

Marathon field 17 (`blueprints/math/17_reverse_math_213.md`).

Reverse math: `WKL₀ ⟺ Heine–Borel` over `RCA₀`.  On the residue carrier the **local** step
is done (`KonigConditional.infChildExists_iff_finiteSubcover`) and local child selection is
LLPO (`llpo_infChildExistsN`).  The **global** equivalence has a clean ∅-axiom half and a
strictly-stronger half:

  - **∅-axiom half (here):** an infinite path ⟹ unbounded (`infPath_imp_infB`), and dually
    bounded ⟹ no infinite path (`bounded_imp_not_infPath`).
  - **WKL-strength half (not ∅-axiom):** unbounded ⟹ an infinite path (WKL proper).  This is
    where WKL is *strictly stronger than LLPO*: local selection is LLPO, but **assembling a
    global path from the per-node selections needs dependent choice** to iterate.  The
    oracle-conditional path engine is `KonigConditional.konig_conditional` (PURE) — the
    oracle is exactly that choice content.
-/

namespace E213.Lib.Math.Logic

/-- An infinite path through the tree `T`: a length-`k` node at each stage, all in `T`. -/
def HasInfPath (T : List Bool → Bool) : Prop :=
  ∃ node : Nat → List Bool,
    node 0 = [] ∧ (∀ k, T (node k) = true) ∧ (∀ k, (node (k + 1)).length = (node k).length + 1)

/-- `T` is bounded: some depth `N` is entirely outside `T`. -/
def Bounded (T : List Bool → Bool) : Prop :=
  ∃ N, ∀ s : List Bool, s.length = N → T s = false

/-- A path's `k`-th node has length `k`. -/
theorem path_node_len (node : Nat → List Bool) (h0 : node 0 = [])
    (hlen : ∀ k, (node (k + 1)).length = (node k).length + 1) :
    ∀ k, (node k).length = k
  | 0     => congrArg List.length h0
  | k + 1 => (hlen k).trans (congrArg (fun m => m + 1) (path_node_len node h0 hlen k))

/-- ★ **An infinite path ⟹ unbounded-below** (`InfB T []`), ∅-axiom.  At each depth `n` the
    path supplies a length-`n` node in `T`, so `existsLevel T [] n = true`. -/
theorem infPath_imp_infB (T : List Bool → Bool) (hp : HasInfPath T) : InfB T [] :=
  hp.elim (fun node h n =>
    exists_imp_existsLevel T n []
      ⟨node n, path_node_len node h.1 h.2.2 n, h.2.1 n⟩)

/-- ★ **Bounded ⟹ no infinite path**, ∅-axiom — the contrapositive direction of
    Heine–Borel that needs no omniscience.  A bound at depth `N` kills the path's `N`-th
    node. -/
theorem bounded_imp_not_infPath (T : List Bool → Bool) (hb : Bounded T) : ¬ HasInfPath T :=
  fun hp => hb.elim (fun N hN =>
    hp.elim (fun node h =>
      Bool.noConfusion ((h.2.1 N).symm.trans (hN (node N) (path_node_len node h.1 h.2.2 N)))))

/-! ## The WKL-strength half — conditional on the selection oracle (the choice content)

WKL proper (unbounded ⟹ an infinite path) is *not* ∅-axiom: assembling a global path needs
**dependent choice** to iterate the per-node selection.  As everywhere in this marathon, the
cost is carried as an **explicit hypothesis** — the `step` oracle and its `hstep`
"selection stays infinite-below" — keeping the theorem PURE.  Per node, `hstep` is exactly
what `llpo_infChildExistsN` justifies (LLPO gives `InfB s → InfB s0 ∨ InfB s1`); turning
that disjunction into the `step` *function* for all `s` at once is the choice step. -/

/-- `(l ++ [x]).length = l.length + 1`, propext-free. -/
theorem length_snoc : ∀ (l : List Bool) (x : Bool), (l ++ [x]).length = l.length + 1
  | [],     _ => rfl
  | _ :: l, x => congrArg (fun m => m + 1) (length_snoc l x)

/-- ★★ **WKL proper, conditional on the selection oracle (∅-axiom).**  Given a `step`
    oracle that keeps the walk infinite-below (`hstep`) and an infinite-below root, an
    infinite path exists.  The oracle is the dependent-choice content (its per-node
    correctness is `llpo_infChildExistsN`); with it, WKL holds, completing the global
    `WKL ⟺ Heine–Borel` picture (the ∅-axiom half above is unconditional). -/
theorem wkl_of_oracle (T : List Bool → Bool) (step : List Bool → Bool)
    (hstep : ∀ s, InfB T s → InfB T (s ++ [step s])) (root : InfB T []) : HasInfPath T := by
  obtain ⟨node, h0, hT, hrec⟩ :=
    E213.Lib.Math.Combinatorics.KonigConditional.konig_conditional T step (InfB T)
      (fun s h => h 0) hstep root
  exact ⟨node, h0, hT, fun k =>
    (congrArg List.length (hrec k)).trans (length_snoc (node k) (step (node k)))⟩

end E213.Lib.Math.Logic
