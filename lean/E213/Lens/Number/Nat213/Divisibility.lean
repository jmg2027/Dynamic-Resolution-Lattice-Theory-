import E213.Lens.Number.Nat213.Peano

/-!
# Lens.Number.Nat213.Divisibility — a discipline computed OVER the Raw-generated ℕ₊ (∅-axiom)

The **descent leg** (`research-notes/frontiers/the_descent_leg.md`): the corrected 진의 asks that a
classical discipline be *generated from the distinguishing*, not re-derived over Lean's `Nat` and
bridged.  `Nat213.Peano` is the Raw-generated positive naturals — `one := Raw.a`,
`succ := slashOrSelf · Raw.b` (the successor *is* the distinguishing operation), with its own
`add`/`mul` and the no-zero/no-subtraction/no-absorption shape *forced* by the primitive
(`no_additive_identity_at_one`, `no_closed_subtraction`, `no_absorbing_element`).

This file is the first **discipline** (elementary divisibility) proven **entirely over `Nat213`** —
`dvd` is defined by `Nat213`'s own `mul`, and every theorem's statement and proof stay on `Nat213`
with **no detour through Lean `Nat`**.  It is the first concrete leg-2 deposit: a number-theoretic
preorder computed on the distinguishing's own counting object.  ∅-axiom.

The structure is genuinely shaped by the primitive: divisibility here is a preorder with bottom
`one` (`one_dvd`, since `Raw` has the atom) but — unlike ℕ-with-0 — **no top** and no zero to absorb,
matching `Peano`'s forced no-absorption.
-/

namespace E213.Lens.Number.Nat213.Divisibility

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213
  (mul one mul_one one_mul mul_assoc mul_comm)

/-- **Divisibility over the Raw-generated ℕ₊**: `a ∣ b` iff `b = a · c` for some `c : Nat213`,
    using `Nat213`'s own multiplication.  No Lean `Nat`. -/
def Dvd (a b : Nat213) : Prop := ∃ c : Nat213, b = mul a c

/-- `1` divides everything — divisibility has a bottom, the atom-count floor (`Raw` has ≥ 1 atom). -/
theorem one_dvd (a : Nat213) : Dvd one a := ⟨a, (one_mul a).symm⟩

/-- Reflexivity: `a ∣ a` (witness `one`). -/
theorem dvd_refl (a : Nat213) : Dvd a a := ⟨one, (mul_one a).symm⟩

/-- `a ∣ a · b` — the right factor is divisible. -/
theorem dvd_mul_right (a b : Nat213) : Dvd a (mul a b) := ⟨b, rfl⟩

/-- `b ∣ a · b` — the left factor is divisible (via `mul_comm`). -/
theorem dvd_mul_left (a b : Nat213) : Dvd b (mul a b) := ⟨a, mul_comm a b⟩

/-- Transitivity: `a ∣ b → b ∣ c → a ∣ c` (compose witnesses by `mul_assoc`). -/
theorem dvd_trans {a b c : Nat213} (hab : Dvd a b) (hbc : Dvd b c) : Dvd a c := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hbc
  exact ⟨mul x y, by rw [hy, hx, mul_assoc]⟩

/-- If `a ∣ b` then `a ∣ b · c` — divisibility is preserved by multiplying the dividend. -/
theorem dvd_mul_of_dvd_left {a b : Nat213} (h : Dvd a b) (c : Nat213) : Dvd a (mul b c) := by
  obtain ⟨x, hx⟩ := h
  exact ⟨mul x c, by rw [hx, mul_assoc]⟩

/-- If `a ∣ b` then `a ∣ c · b` — preserved by multiplying on the left too. -/
theorem dvd_mul_of_dvd_right {a b : Nat213} (h : Dvd a b) (c : Nat213) : Dvd a (mul c b) := by
  obtain ⟨x, hx⟩ := h
  exact ⟨mul c x, by rw [hx, mul_comm c (mul a x), mul_assoc, mul_comm x c]⟩

/-- ★★★ **Divisibility is a preorder on the Raw-generated ℕ₊, with bottom `one` and no zero.**
    The first elementary discipline (divisibility) computed entirely over `Nat213` — the
    distinguishing's own counting object — with the no-absorbing-zero shape forced by the primitive
    (`Peano.no_absorbing_element`).  The descent leg made concrete for one discipline. -/
theorem divisibility_preorder_with_bottom :
    (∀ a : Nat213, Dvd a a)
    ∧ (∀ a b c : Nat213, Dvd a b → Dvd b c → Dvd a c)
    ∧ (∀ a : Nat213, Dvd one a) :=
  ⟨dvd_refl, fun _ _ _ => dvd_trans, one_dvd⟩

end E213.Lens.Number.Nat213.Divisibility
