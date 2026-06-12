import E213.Meta.Tactic.List213

/-!
# ListLocate213 — the strict locating primitive, pushed onto the list

(this session) `StrictLocate213.locate_strict` (`E213/Meta/Nat/StrictLocate213.lean`)
founds identity on ℕ by a **strict** sandwich: `a < e < a + 2 ⟹ e = a + 1`,
no `≤` and no `=` in the hypotheses, `=` the output, the 2-gap ceiling doing
the pointing.  This file pushes that primitive back down onto the **list /
cons structure** ℕ was counted off of (`UnitList.count`, `UnitList.fromNat`).

The list-native strict order is **proper extension**: `m` properly extends `l`
when `m = l ++ t` for some **nonempty** `t` — a strict prefix order with *no
equality slot* (`t ≠ []` is what makes it strict).  `locate_list` is then the
list-native `locate_strict`: the unique list strictly between `la` and its
**next-next** `la ++ [x, y]` is `la ++ [x]`.  Bounds are strict proper
extensions (no `≤`, no `=`); the located list is the output (`=` only in the
conclusion).  It **projects** to `locate_strict` on lengths (`properExt_length`):
`+1` / `+2` in ℕ are *one* / *two* conses on the list — discrete location is
the same sandwich one rung down.

Location is unique **because a list is linear — each cons has one tail**
(`cons_tail_unique`): "the next" is determined.  On a **tree**
(`BinTree.node`, two children — `BinTree213.node_not_assoc`) the successor
*branches*; "the next" is ambiguous and strict location fails.  This is the
same linear/branching divide as `+`/`×` (commute, transposable grid) vs `^`
(non-commute, branching tree — the `^`-wall, `numbersystem_square` frontier).
And discrete vs continuum is ONE sandwich, not two probes: the gap **closes**
at the next-next (here) versus an infinite nesting that only **limits**
(`Real213` cuts) — same strict-sandwich form, different gap behaviour.

All ∅-axiom; bare inductions / `cons.inj` / `noConfusion`, and the PURE
`List213.append_assoc` / `length_append` (core `List.*` carry `propext`).
The `la`-cancellation is the local PURE `append_cancel` (bare induction).
-/

namespace E213.Meta.Nat.ListLocate213

open E213.Tactic.List213 (length_append)

/-- **The list-native strict order.**  `m` *properly extends* `l`: `m` is `l`
    with a **nonempty** tail glued on.  Strict prefix order, no equality slot —
    `t ≠ []` is exactly what excludes `m = l`.  This is the list's own `<`,
    the role `a < b` plays in `StrictLocate213`. -/
def properExt {α : Type _} (l m : List α) : Prop := ∃ t, t ≠ [] ∧ m = l ++ t

/-- **Left-cancellation of append** (PURE, bare induction on the prefix).
    `List213` has `append_assoc` / `length_append` but no cancellation; this
    is the cons-by-cons peel that `locate_list` needs.  Core's analogue routes
    through `propext`; this one is `cons.inj`-only. -/
theorem append_cancel {α : Type _} :
    ∀ (la A B : List α), la ++ A = la ++ B → A = B
  | [],      _, _, h => h
  | _ :: la, A, B, h => append_cancel la A B (List.cons.inj h).2

/-- **A cons has one tail** — the linearity that makes location work.
    `x :: l = x :: l' ⟹ l = l'`: a cons determines its single successor
    tail (`cons.inj`).  This uniqueness is exactly what a tree lacks: a
    `BinTree.node l r` (`BinTree213`) has **two** children, so "the next" is
    ambiguous (`BinTree213.node_not_assoc`) and strict location fails on the
    branching substrate.  Linear (one tail) ⟹ unique successor ⟹ strict
    location; branching (two children) ⟹ no unique successor ⟹ no location. -/
theorem cons_tail_unique {α : Type _} (x : α) (l l' : List α) :
    x :: l = x :: l' → l = l' := fun h => (List.cons.inj h).2

/-- **The proper-prefix order projects to the ℕ strict order.**  If `m`
    properly extends `l`, then `l.length < m.length` — the nonempty tail
    contributes positive length (PURE `List213.length_append`).  So the
    list sandwich of `locate_list` maps onto the ℕ sandwich of
    `StrictLocate213.locate_strict`: a proper extension *is* a strict
    `+ (≥1)` on lengths. -/
theorem properExt_length {α : Type _} (l m : List α)
    (h : properExt l m) : l.length < m.length := by
  obtain ⟨t, ht, hm⟩ := h
  cases t with
  | nil => exact absurd rfl ht
  | cons a t' =>
      have hlen : m.length = l.length + (t'.length + 1) := by
        rw [hm, length_append]; rfl
      rw [hlen]
      exact Nat.lt_add_of_pos_right (Nat.succ_pos _)

/-- ★★ **The strict locating primitive, on the list itself.**  The unique
    list strictly between `la` and its **next-next** `la ++ [x, y]` is
    `la ++ [x]`.  Both bounds are strict **proper extensions**
    (`properExt`, nonempty tail) — no `≤`, no `=` in the hypotheses; the
    located list is the output (`=` only in the conclusion).  This is
    `StrictLocate213.locate_strict` pushed onto the cons structure: `+1`/`+2`
    there are *one*/*two* conses here.

    Proof: `le = la ++ t` (t ≠ []) from `h1`; `la ++ [x, y] = le ++ s`
    (s ≠ []) from `h2`.  Substituting and left-cancelling `la`
    (`append_cancel`) gives `[x, y] = t ++ s` with `t, s` nonempty.  A
    nonempty-split of a length-2 list forces `t = [x]`, hence
    `le = la ++ [x]`. -/
theorem locate_list {α : Type _} (la : List α) (x y : α) (le : List α)
    (h1 : properExt la le) (h2 : properExt le (la ++ [x, y])) :
    le = la ++ [x] := by
  obtain ⟨t, ht, hle⟩ := h1
  obtain ⟨s, hs, hsplit⟩ := h2
  -- la ++ [x, y] = le ++ s = (la ++ t) ++ s = la ++ (t ++ s)
  have hcat : la ++ [x, y] = la ++ (t ++ s) := by
    rw [hsplit, hle, E213.Tactic.List213.append_assoc]
  have hts : [x, y] = t ++ s := append_cancel la [x, y] (t ++ s) hcat
  -- t nonempty: t = a :: t'
  cases t with
  | nil => exact absurd rfl ht
  | cons a t' =>
      -- [x, y] = (a :: t') ++ s = a :: (t' ++ s)
      have hxy : x :: [y] = a :: (t' ++ s) := hts
      have hxa : x = a := (List.cons.inj hxy).1
      have hrest : [y] = t' ++ s := (List.cons.inj hxy).2
      -- s nonempty ⟹ t' must be [] (else [y] would have length ≥ 2)
      cases t' with
      | nil =>
          -- t = [a] = [x]; le = la ++ [a] = la ++ [x]
          rw [hle, hxa]
      | cons b t'' =>
          -- [y] = b :: (t'' ++ s); cons.inj ⟹ [] = t'' ++ s, so s = [],
          -- contradicting s ≠ []
          have hnil : ([] : List α) = t'' ++ s := (List.cons.inj hrest).2
          cases t'' with
          | nil =>
              -- [] = s, contradicting hs
              exact absurd hnil.symm hs
          | cons _ _ => exact List.noConfusion hnil

end E213.Meta.Nat.ListLocate213
