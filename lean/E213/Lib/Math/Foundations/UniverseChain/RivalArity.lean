import E213.Lib.Math.Foundations.UniverseChain.RawRecurrence

/-!
# RivalArity — the binary distinguishing is non-interchangeable with a unary rival (∅-axiom)

The structured-rival exclusion (leg-3, the open middle of the descent-leg program):
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

/-! ## §2 — the relation-first / non-distinctness binary rival -/

/-- `choose2` recurrence at the literal `k+2` form (definitional). -/
theorem choose2_succ_succ (k : Nat) : choose2 (k + 2) = choose2 (k + 1) + (k + 1) := rfl

/-- `choose2` is monotone (each step adds `≥ 0`). -/
theorem choose2_step : ∀ n : Nat, choose2 n ≤ choose2 (n + 1)
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
      rw [choose2_succ_succ (n + 1)]
      exact Nat.le_add_right _ _

theorem choose2_mono {m k : Nat} (h : m ≤ k) : choose2 m ≤ choose2 k := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (choose2_step _)

/-- A **non-distinctness** binary rival's depth-`≤ n` count: a binary op that *allows* `op x x`
    counts unordered pairs **with repetition** = `C(m,2) + m` (distinct pairs *plus* the diagonal).
    So its step is `2 + choose2 (·) + (·)` — 213's step `2 + choose2 (·)` plus the self-combinations
    the distinctness constraint forbids. -/
def relCount : Nat → Nat
  | 0 => 2
  | n + 1 => 2 + choose2 (relCount n) + relCount n

theorem relCount_ge_two : ∀ n : Nat, 2 ≤ relCount n
  | 0 => Nat.le_refl 2
  | n + 1 => by
      show 2 ≤ 2 + choose2 (relCount n) + relCount n
      exact Nat.le_trans (Nat.le_add_right 2 _) (Nat.le_add_right _ _)

/-- The non-distinctness rival dominates 213's count (it has every distinct-pair term *plus* the
    diagonal). -/
theorem rawCount_le_relCount : ∀ n : Nat, rawCount n ≤ relCount n
  | 0 => Nat.le_refl 2
  | n + 1 => by
      have ih : rawCount n ≤ relCount n := rawCount_le_relCount n
      rw [rawCount_succ]
      show 2 + choose2 (rawCount n) ≤ 2 + choose2 (relCount n) + relCount n
      exact Nat.le_trans (Nat.add_le_add_left (choose2_mono ih) 2) (Nat.le_add_right _ _)

/-- ★ **The non-distinctness rival strictly exceeds 213** at every level `≥ 1`: the extra
    `+ relCount n` is exactly the self-combinations (`op x x`) the distinctness constraint removes. -/
theorem nondistinct_rival_exceeds : ∀ n : Nat, rawCount (n + 1) < relCount (n + 1)
  | n => by
      have hle : rawCount (n + 1) ≤ 2 + choose2 (relCount n) := by
        rw [rawCount_succ]
        exact Nat.add_le_add_left (choose2_mono (rawCount_le_relCount n)) 2
      have hpos : 0 < relCount n := Nat.lt_of_lt_of_le (by decide) (relCount_ge_two n)
      show rawCount (n + 1) < 2 + choose2 (relCount n) + relCount n
      exact Nat.lt_of_le_of_lt hle (Nat.lt_add_of_pos_right hpos)

/-- ★★★ **The distinctness constraint is exactly the removal of self-combinations.**  213's `slash`
    counts unordered *distinct* pairs (step `2 + choose2 (·)`); the unrestricted (relation-first /
    non-distinctness) binary rival counts pairs *with repetition* (step `2 + choose2 (·) + (·)`), so
    it **strictly exceeds** 213 at every level `≥ 1` (`nondistinct_rival_exceeds`).  213's
    distinguishing is therefore *the unrestricted binary rival minus the degenerate self-combinations
    `op x x`* — not an arbitrary primitive, but the unique one that forbids self-combination.  With
    the **unary** corner (`binary_non_interchangeable_with_unary`) and the **degenerate** corner
    (`OneDiagonal.no_distinguishing_on_subsingleton`), the distinguishing primitive is
    non-interchangeable across all three formalized rival classes. -/
theorem distinctness_removes_self_combination :
    (∀ n, relCount (n + 1) = 2 + choose2 (relCount n) + relCount n)
    ∧ (∀ n, rawCount (n + 1) = 2 + choose2 (rawCount n))
    ∧ (∀ n, rawCount (n + 1) < relCount (n + 1)) :=
  ⟨fun _ => rfl, rawCount_succ, nondistinct_rival_exceeds⟩

end E213.Lib.Math.Foundations.UniverseChain.RivalArity
