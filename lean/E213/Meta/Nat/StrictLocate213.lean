import E213.Meta.Nat.PureNat

/-!
# StrictLocate213 — locating a unique element with strict bounds only

(originator, this session) The sandwich that *founds* identity must use
**strict** order `<` (precedence, "right after"), never `≤`.  `≤` already
contains `=` — `a ≤ b ↔ a < b ∨ a = b` — so a `≤`-sandwich presupposes the
very `=` it pretends to derive: circular, and the sandwich is then
pointless ("if you use an inequality that includes equality, why bother with the sandwich").

With no number concept and no `=`, the only way to point at a specific list
element is "**the element right after `a` and right before `b`**", and that
pointing is **unique exactly when `b` is `a`'s next-next** (`b = a + 2`):
then the open interval `(a, b)` holds exactly one slot, `a + 1`.  Strict
bounds + a 2-gap ceiling locate a unique element with **no `=` in the
hypotheses**; `=` is the **output** (the located slot's identity), and `≤`
is **derived** (`a ≤ b ↔ a < b + 1`), never primitive.

This is exactly what `Int213.eq_of_sandwich` already encodes
(`a + x < b + 1 ∧ b < a + x + 1`, the 2-gap around `b`); this module states
the bare primitive in the originator's own form: `a < e < a+2 ⟹ e = a+1`.

All ∅-axiom.
-/

namespace E213.Meta.Nat.StrictLocate213

/-- ★★ **The strict locating primitive.**  Given strict `a < e < b` with
    `b` exactly `a`'s next-next (`b = a + 2`), the located element is the
    successor: `e = a + 1`.  No `≤` and no `=` appear in the hypotheses —
    pure precedence (`<`) and the 2-gap ceiling do the pointing; `=` is the
    output.  This is "the element right after `a`, right before its
    next-next, is unique". -/
theorem locate_strict {a e b : Nat} (hb : b = a + 2)
    (h1 : a < e) (h2 : e < b) : e = a + 1 := by
  subst hb
  exact Nat.le_antisymm (Nat.le_of_lt_succ h2) h1

/-- ★ **The pointing is unique.**  Any two elements caught in the strict
    2-gap `(a, a+2)` coincide — the strict bounds locate a *single* slot.
    The `=` in the conclusion is the output of pointing, never an input. -/
theorem unique_between {a e e' : Nat}
    (h1 : a < e) (h2 : e < a + 2) (h1' : a < e') (h2' : e' < a + 2) :
    e = e' :=
  (locate_strict rfl h1 h2).trans (locate_strict rfl h1' h2').symm

/-- `≤` is **derived** from strict `<`, not primitive: `a ≤ b ↔ a < b + 1`.
    A `≤`-sandwich is a strict sandwich with the equality slot already
    folded in — which is precisely why *founding* `=` needs the strict
    form, and why `eq_of_sandwich`'s hypotheses are strict. -/
theorem le_iff_lt_succ (a b : Nat) : a ≤ b ↔ a < b + 1 :=
  ⟨Nat.lt_succ_of_le, Nat.le_of_lt_succ⟩

end E213.Meta.Nat.StrictLocate213
