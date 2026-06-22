import E213.Lib.Math.Foundations.UniverseChain.RawRecurrence

/-!
# RivalArity — the binary distinguishing is non-interchangeable with a unary rival (∅-axiom)

The structured-rival exclusion (`research-notes/frontiers/the_descent_leg.md`, leg-3 open middle):
a *negation-first* / unary rival primitive — one (or finitely many) generators with a **unary**
operation — generates a structure whose depth-`≤ n` count is **linear** in `n` (each level adds a
bounded number of elements: `g, neg g, neg² g, …`).  213's primitive `Raw.slash` is **binary** and
requires **distinctness**, so its depth-`≤ n` count obeys the **super-linear** recurrence
`|S_n| = 2 + C(|S_{n-1}|, 2)` (`RawRecurrence.rawCount`: 2, 3, 5, 12, 68, 2280): each level adds an
*unordered distinct pair* of the previous level — quadratic growth, the signature of branching.

The two generation recurrences are therefore **different** (`+1`-step vs `C(·,2)`-step) and the
binary count **strictly dominates** any linear rival (`rawCount n ≥ n + 2 > n + 1`).  So the
distinguishing primitive is *non-interchangeable* with a unary (negation-first) rival: the rival
cannot reproduce 213's graded structure — it grows too slowly, lacking the branching that the binary
distinctness forces.  ∅-axiom.

This is the *structured*-rival companion to `OneDiagonal.no_distinguishing_on_subsingleton` (the
*degenerate* rival, which cannot fire the slash at all): here the rival fires, but a *unary* fire
generates only a line where the binary distinguishing generates a (super-linearly growing) tree.
-/

namespace E213.Lib.Math.Foundations.UniverseChain.RivalArity

open E213.Lib.Math.Foundations.UniverseChain.RawRecurrence (choose2 rawCount rawCount_succ)

/-- A unary (negation-first) rival's depth-`≤ n` count: **linear**.  One generator under a unary
    operation yields `g, neg g, …, negⁿ g` — `n + 1` elements.  (Any finite-generator unary rival is
    likewise linear; `n + 1` is the one-generator case and suffices for the domination below.) -/
def unaryCount (n : Nat) : Nat := n + 1

/-- `choose2 k ≥ k - 1` — the branching step is at least linear (and super-linear for `k ≥ 3`). -/
theorem choose2_ge_pred : ∀ k : Nat, k - 1 ≤ choose2 k
  | 0 => by decide
  | 1 => by decide
  | m + 2 => by
      show m + 1 ≤ choose2 (m + 1) + (m + 1)
      exact Nat.le_add_left (m + 1) (choose2 (m + 1))

/-- ★ **The binary distinguishing count is super-linear**: `n + 2 ≤ rawCount n` for all `n` — it
    stays strictly above any unary (linear) rival.  Induction on the recurrence: the `C(·,2)`
    branching step adds at least `rawCount n - 1 ≥ n + 1`. -/
theorem rawCount_ge : ∀ n : Nat, n + 2 ≤ rawCount n
  | 0 => by decide
  | n + 1 => by
      have ih : n + 2 ≤ rawCount n := rawCount_ge n
      -- branching step ≥ rawCount n - 1 ≥ (n+2) - 1 = n + 1   ((n+2)-1 = n+1 definitionally)
      have h1 : rawCount n - 1 ≤ choose2 (rawCount n) := choose2_ge_pred (rawCount n)
      have h2 : n + 1 ≤ rawCount n - 1 := Nat.sub_le_sub_right ih 1
      have h3 : n + 1 ≤ choose2 (rawCount n) := Nat.le_trans h2 h1
      -- rawCount (n+1) = 2 + choose2 (rawCount n) ≥ 2 + (n+1) = (n+1) + 2
      rw [rawCount_succ, Nat.add_comm (n + 1) 2]
      exact Nat.add_le_add_left h3 2

/-- ★★★ **Non-interchangeability of the binary distinguishing with a unary rival.**  Three facts:
    (1) the unary rival has a **constant `+1`** generation step (linear);
    (2) 213's binary distinguishing has the **`C(·,2)` branching step** (super-linear,
        `rawCount_succ`);
    (3) the binary count **strictly dominates** the unary rival at *every* level
        (`unaryCount n < rawCount n`).
    So a negation-first / unary rival primitive *cannot* reproduce 213's graded structure — the
    distinguishing primitive is non-interchangeable with it.  Together with
    `OneDiagonal.no_distinguishing_on_subsingleton` (the degenerate rival cannot fire at all), this
    closes the unary corner of the structured-rival exclusion. -/
theorem binary_non_interchangeable_with_unary :
    (∀ n, unaryCount (n + 1) = unaryCount n + 1)
    ∧ (∀ n, rawCount (n + 1) = 2 + choose2 (rawCount n))
    ∧ (∀ n, unaryCount n < rawCount n) := by
  refine ⟨fun n => rfl, rawCount_succ, fun n => ?_⟩
  calc unaryCount n = n + 1 := rfl
    _ < n + 2 := Nat.lt_succ_self (n + 1)
    _ ≤ rawCount n := rawCount_ge n

end E213.Lib.Math.Foundations.UniverseChain.RivalArity
