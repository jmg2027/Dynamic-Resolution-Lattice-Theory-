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

end E213.Lib.Math.Logic
