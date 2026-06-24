import E213.Lens.Number.Nat213.Peano
import E213.Lens.Number.Nat213.Order

/-!
# Lens.Number.Nat213.Divisibility — a discipline computed OVER the Raw-generated ℕ₊ (∅-axiom)

The **descent leg** (narrative: `theory/essays/foundations/raw_and_lens_explained.md`): the corrected
true intent asks that a classical discipline be *generated from the distinguishing*, not re-derived over
Lean's `Nat` and
bridged.  `Nat213.Peano` is the Raw-generated positive naturals — `one := Raw.a`,
`succ := slashOrSelf · Raw.b` (the successor *is* the distinguishing operation), with its own
`add`/`mul` and the no-zero/no-subtraction/no-absorption shape *forced* by the primitive
(`no_additive_identity_at_one`, `no_closed_subtraction`, `no_absorbing_element`).

This file is the first **discipline** (elementary divisibility) proven **entirely over `Nat213`** —
`dvd` is defined by `Nat213`'s own `mul`, and every theorem's statement *and proof* stay on `Nat213`
with **no detour through Lean `Nat`**: the whole dependency cone is `toNat`-free, verified
mechanically (the descent-leg "toNat-cone bet", the `the_descent_leg` frontier).  The
one cancellation it needs (`dvd_antisymm` → `mul_left_cancel`) is taken from `Order` — the **native**
version (trichotomy + distributivity, mirroring `Order.mul_self_inj`), not `Peano`'s earlier
`toNat`-laundered one.  It is the first concrete leg-2 deposit: a number-theoretic preorder computed
on the distinguishing's own counting object, generated all the way down.  ∅-axiom.

The structure is genuinely shaped by the primitive: divisibility here is a preorder with bottom
`one` (`one_dvd`, since `Raw` has the atom) but — unlike ℕ-with-0 — **no top** and no zero to absorb,
matching `Peano`'s forced no-absorption.
-/

namespace E213.Lens.Number.Nat213.Divisibility

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213
  (mul one succ add mul_one one_mul mul_assoc mul_comm succ_ne_one
   mul_succ_right add_assoc add_one_right)
-- `mul_left_cancel` is taken from `Order` (the **native**, toNat-free cancellation),
-- not from `Peano` (whose version laundered through Lean `Nat`).  This keeps the
-- entire divisibility dependency cone toNat-free — see the descent-leg bet.
open E213.Lens.Number.Nat213.Order (lt lt_irrefl lt_trans mul_left_cancel)

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

/-- **A product is `one` only if both factors are** — over the Raw-generated ℕ₊.  Forced by the
    no-zero structure: a `succ`-headed factor makes the product `succ`-headed (`add` of a positive
    is always a successor), hence `≠ one` (`succ_ne_one`).  A genuine number-theoretic fact on
    `Nat213`, not Lean `Nat`. -/
theorem mul_eq_one {x y : Nat213} (h : mul x y = one) : x = one ∧ y = one := by
  cases x with
  | one => exact ⟨rfl, by rwa [one_mul] at h⟩
  | succ x' =>
      exfalso
      cases y with
      | one => rw [mul_one] at h; exact succ_ne_one x' h
      | succ y' => exact succ_ne_one _ h

/-- ★★★ **Antisymmetry**: `a ∣ b → b ∣ a → a = b` — so divisibility is a **partial order** on the
    Raw-generated ℕ₊, not merely a preorder.  The proof routes through `mul_left_cancel` (every
    `Nat213` is cancellable — positivity, no zero-divisor) and `mul_eq_one`: `a = a·(x·y)` forces
    `x·y = one`, hence `x = one`, hence `b = a`.  Entirely over `Nat213`. -/
theorem dvd_antisymm {a b : Nat213} (hab : Dvd a b) (hba : Dvd b a) : a = b := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hba
  -- a = mul b y = mul (mul a x) y = mul a (mul x y); each ←-rewrite hits a unique pattern.
  have ha : mul a (mul x y) = a := by rw [← mul_assoc, ← hx, ← hy]
  have ha2 : mul a (mul x y) = mul a one := by rw [ha, mul_one]
  have hxy : mul x y = one := mul_left_cancel ha2
  obtain ⟨hx1, _⟩ := mul_eq_one hxy
  have hb : b = a := by rw [hx, hx1, mul_one]
  exact hb.symm

/-- **A divisor is no larger than its dividend**: `a ∣ t → a = t ∨ a < t` (the native `Nat213`
    order `lt`).  Purely over `Nat213` — `c = one` gives equality (`mul_one`); `c = succ c'` gives
    `t = a + a·c'` (`mul_succ_right`), i.e. `a < t`.  Divisibility refines the additive order. -/
theorem dvd_imp_eq_or_lt {a t : Nat213} (h : Dvd a t) : a = t ∨ lt a t := by
  obtain ⟨c, hc⟩ := h
  cases c with
  | one => left; rw [hc, mul_one]
  | succ c' => right; exact ⟨mul a c', by rw [hc, mul_succ_right]⟩

/-- ★★★ **No top**: no `t` is divisible by every `Nat213`.  Divisibility over the Raw-generated ℕ₊
    has a bottom (`one`) but **no top** — the shape *forced* by the primitive: every element is
    exceeded by its successor (`add_one_right`), the distinguishing's counting never closing
    (cf. `Peano.no_absorbing_element`).  Unlike a bounded divisibility lattice, this order is open
    upward.  Entirely over `Nat213`. -/
theorem dvd_no_top : ¬ ∃ t : Nat213, ∀ a : Nat213, Dvd a t := by
  intro ⟨t, ht⟩
  have htlt : lt t (succ t) := ⟨one, add_one_right t⟩
  rcases dvd_imp_eq_or_lt (ht (succ t)) with heq | hlt
  · rw [heq] at htlt; exact lt_irrefl t htlt
  · exact lt_irrefl t (lt_trans htlt hlt)

/-- ★★★ **Divisibility is a preorder on the Raw-generated ℕ₊, with bottom `one` and no zero.**
    The first elementary discipline (divisibility) computed entirely over `Nat213` — the
    distinguishing's own counting object — with the no-absorbing-zero shape forced by the primitive
    (`Peano.no_absorbing_element`).  The descent leg made concrete for one discipline. -/
theorem divisibility_preorder_with_bottom :
    (∀ a : Nat213, Dvd a a)
    ∧ (∀ a b c : Nat213, Dvd a b → Dvd b c → Dvd a c)
    ∧ (∀ a b : Nat213, Dvd a b → Dvd b a → a = b)
    ∧ (∀ a : Nat213, Dvd one a) :=
  ⟨dvd_refl, fun _ _ _ => dvd_trans, fun _ _ => dvd_antisymm, one_dvd⟩

end E213.Lens.Number.Nat213.Divisibility
