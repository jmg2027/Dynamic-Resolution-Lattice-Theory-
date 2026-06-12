import E213.Meta.Nat.PureNat

/-!
# Iterate213 — the diagonal climb is iteration, and the count slot is multiplicative

`HyperAssoc` shows the hyperoperation tower (`append→+→×→^`) carries
associativity and commutativity through `×` and loses both at `^`, leaving
one surviving ghost: `(aᵇ)ᶜ = a^(b·c)`.  This file says *why that ghost
exists*, from the only structure the climb has — **iteration**.

Each rung is the previous one iterated a counted number of times:

* `add_eq_iter`  : `a + b = iter Nat.succ b a` — successor, `b` times;
* `mul_eq_iter`  : `a * b = iter (· + a) b 0` — add-`a`, `b` times, from `0`;
* `pow_eq_iter`  : `a ^ b = iter (· * a) b 1` — mul-by-`a`, `b` times, from `1`.

The climb is therefore nothing but a single combinator `iter f n` applied
at successive flavours of `f`.  And the **iteration-count slot** — the `n`
in `iter f n` — carries two laws, derived from list-style induction alone:

* `iter_add` : `iter f (m + n) x = iter f m (iter f n x)` — the
  **counter-append law**: composing two iterations *adds* their counts.
  This is the count slot's own `+` (the rung-below append shadow,
  `UnitList.add_comm_from_append`, one level abstracted).
* `iter_mul` : `iter f (m * n) x = iter (iter f n) m x` — the
  **multiplicative core**: *nesting* an iteration inside an iteration
  *multiplies* the counts.  Proved by induction on `m` from `iter_add`.

So the count slot is intrinsically **multiplicative**: nesting is `×` on
counts.  That is the engine of the climb — and it is exactly why the climb
can only reach the `×`-flavoured tower and stalls at `^` against the
×-atom wall (frontier `numbersystem_square.md`, "tree ↔ wall loop" /
"operation space is not a line").

The surviving ghost is now a *shadow of `iter_mul` one rung up*:
`(aᵇ)ᶜ = a^(b·c)` (`pow_pow_eq_pow_mul`) is `iter_mul` read through
`pow_eq_iter` — nesting the mul-by-`a` iteration `c` times around its
`b`-fold version multiplies the counts to `b·c`.  The `^`-level
"associativity" law *is* the count-multiplication law one rung down; it
linearizes `^` to `×` on the exponent precisely because the count slot's
only composition law beyond append is multiplication.

The contrast pins the necessity: an **idempotent** climb-operator builds
no tower.  If `f (f x) = f x` then `iter f (n+1) x = f x` for all `n`
(`iter_idem`): the count slot collapses past one step, so there is nothing
for `iter_mul` to multiply.  Concretely the `∪`-climb (`max a`, with
`a∪a=a`) is trivial on its diagonal (`max_iter_trivial`) — the diagonal
climb is multiplicative only where the rung-operator is *not* idempotent.

All ∅-axiom; `iter` is defined here (no `Function.iterate`), and every law
is bare structural induction.  The negative/contrast facts use no `decide`.
-/

namespace E213.Meta.Nat.Iterate213

/-! ## 1. The iteration combinator -/

/-- `iter f n x` applies `f` to `x` exactly `n` times.

    Convention: recurse on the count by **peeling the successor on the
    inside** — `iter f (n+1) x = iter f n (f x)`.  This is the convention
    under which `iter_add` and `iter_mul` fall out cleanest: `iter_add`
    needs only `iter` to commute one application past a block of `n`, which
    is immediate by induction on `m`; and then `iter_mul` is a one-line
    induction feeding each `iter f n` into the next via `iter_add`. -/
def iter {α : Type _} (f : α → α) : Nat → α → α
  | 0,     x => x
  | n + 1, x => iter f n (f x)

/-- Unfold at zero count: no applications. -/
theorem iter_zero {α : Type _} (f : α → α) (x : α) : iter f 0 x = x := rfl

/-- Unfold at successor: peel one application on the inside. -/
theorem iter_succ {α : Type _} (f : α → α) (n : Nat) (x : α) :
    iter f (n + 1) x = iter f n (f x) := rfl

/-- Peel one application on the **outside**: `iter f (n+1) x = f (iter f n x)`.
    Both peels agree — the count is order-blind on a single `f` — proved by
    induction on `n` (the inside-peel is definitional, this is its mirror). -/
theorem iter_succ_outside {α : Type _} (f : α → α) :
    ∀ (n : Nat) (x : α), iter f (n + 1) x = f (iter f n x)
  | 0,     x => rfl
  | n + 1, x => by
      show iter f (n + 1) (f x) = f (iter f (n + 1) x)
      rw [iter_succ_outside f n (f x)]
      rfl

/-! ## 2. ★ The counter-append law — the count slot is additive -/

/-- ★ **Counter-append law**: composing iterations *adds* their counts.
    `iter f (m + n) x = iter f m (iter f n x)` — running `n` steps then `m`
    more is running `m+n` steps.  Free, by induction on `m`.  This is the
    count slot's own `+`, the append shadow (`UnitList`) one level up. -/
theorem iter_add {α : Type _} (f : α → α) :
    ∀ (m n : Nat) (x : α), iter f (m + n) x = iter f m (iter f n x)
  | 0,     n, x => by
      show iter f (0 + n) x = iter f 0 (iter f n x)
      rw [Nat.zero_add]
      rfl
  | m + 1, n, x => by
      show iter f (m + 1 + n) x = iter f (m + 1) (iter f n x)
      rw [show m + 1 + n = (m + n) + 1 from by
            rw [Nat.add_assoc, Nat.add_comm 1 n, ← Nat.add_assoc]]
      rw [iter_succ_outside f (m + n) x, iter_add f m n x,
          iter_succ_outside f m (iter f n x)]

/-! ## 3. ★★ The multiplicative core — the count slot is multiplicative -/

/-- ★★ **Multiplicative core**: *nesting* iterations *multiplies* their
    counts.  `iter f (m * n) x = iter (iter f n) m x` — applying the
    whole `n`-fold block `m` times is the `(m·n)`-fold iteration.  Proved
    by induction on `m`, each step splitting `(m+1)·n = m·n + n` with
    `iter_add` and folding the freed `n`-block into the outer `iter`.

    This is the intrinsic multiplicativity of the count slot: the only
    composition law beyond append (`iter_add`) is multiplication under
    nesting.  It is the engine of the whole climb. -/
theorem iter_mul {α : Type _} (f : α → α) :
    ∀ (m n : Nat) (x : α), iter f (m * n) x = iter (iter f n) m x
  | 0,     n, x => by
      show iter f (0 * n) x = iter (iter f n) 0 x
      rw [Nat.zero_mul]
      rfl
  | m + 1, n, x => by
      show iter f ((m + 1) * n) x = iter (iter f n) (m + 1) x
      rw [Nat.succ_mul, iter_add f (m * n) n x, iter_mul f m n (iter f n x)]
      rfl

/-! ## 4. The hyperoperation rungs ARE iteration -/

/-- `+` is the successor iterated: `a + b = iter Nat.succ b a` (apply
    `succ` to `a`, `b` times).  By induction on the count `b`. -/
theorem add_eq_iter : ∀ (a b : Nat), a + b = iter Nat.succ b a
  | a, 0     => rfl
  | a, b + 1 => by
      show a + (b + 1) = iter Nat.succ (b + 1) a
      rw [iter_succ_outside, ← add_eq_iter a b]
      rfl

/-- `×` is add-`a` iterated from `0`: `a * b = iter (· + a) b 0` (add `a`,
    `b` times, starting at `0`).  By induction on the count `b`. -/
theorem mul_eq_iter : ∀ (a b : Nat), a * b = iter (· + a) b 0
  | a, 0     => rfl
  | a, b + 1 => by
      show a * (b + 1) = iter (· + a) (b + 1) 0
      rw [iter_succ_outside, ← mul_eq_iter a b, Nat.mul_succ]

/-- `^` is mul-by-`a` iterated from `1`: `a ^ b = iter (· * a) b 1`
    (multiply by `a`, `b` times, starting at `1`).  By induction on the
    count `b`. -/
theorem pow_eq_iter : ∀ (a b : Nat), a ^ b = iter (· * a) b 1
  | a, 0     => rfl
  | a, b + 1 => by
      show a ^ (b + 1) = iter (· * a) (b + 1) 1
      rw [iter_succ_outside, ← pow_eq_iter a b, Nat.pow_succ]

/-! ## 5. ★ The surviving ghost AS an `iter_mul` instance

The inner block first: multiplying by `a`, `c` times, is multiplying by
`a^c`.  This is the bridge that turns nested iteration back into a tower. -/

/-- The inner `(· * a)`-block reads out as a power: `iter (· * a) c y =
    y * a^c`.  Multiplying by `a`, `c` times, is multiplying by `a^c`.  By
    induction on `c`. -/
theorem iter_mul_block : ∀ (a c y : Nat), iter (· * a) c y = y * a ^ c
  | a, 0,     y => by rw [iter_zero, Nat.pow_zero, Nat.mul_one]
  | a, c + 1, y => by
      show iter (· * a) (c + 1) y = y * a ^ (c + 1)
      rw [iter_succ_outside, iter_mul_block a c y, Nat.pow_succ,
          PureNat.mul_assoc]

/-- Powers distribute over a product: `(x * y)^c = x^c * y^c` (pure — the
    core `Nat.mul_pow` carries `propext`).  By induction on `c`, regrouping
    with `PureNat.mul_mul_mul_comm`. -/
theorem mul_pow_pure : ∀ (x y c : Nat), (x * y) ^ c = x ^ c * y ^ c
  | _, _, 0     => by
      rw [Nat.pow_zero, Nat.pow_zero, Nat.pow_zero, Nat.mul_one]
  | x, y, c + 1 => by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow_pure x y c,
          PureNat.mul_mul_mul_comm]

/-- ★ The surviving ghost `(aᵇ)ᶜ = a^(b·c)` derived **as an `iter_mul`
    instance**, not re-proved from `pow_mul`.

    Read `^` through `pow_eq_iter`: `a^(b·c)` is the `(b·c)`-fold iteration
    of mul-by-`a`, and `iter_mul` rewrites that doubled count into the
    nested iteration `iter (iter (· * a) c) b 1`.  Peeling the outer
    `b`-iteration (`iter_succ_outside`) and reading each inner `c`-block as
    `· * a^c` (`iter_mul_block`) reassembles `(a^b)^c`.  The
    count-multiplicativity (`iter_mul`) is what surfaces at the `^` level as
    `^`'s only surviving associativity-shaped law — and it lands on `×` (the
    count `b·c`), never on `^`.  That is why the tower folds one rung down. -/
theorem pow_pow_eq_pow_mul (a b c : Nat) : (a ^ b) ^ c = a ^ (b * c) := by
  rw [pow_eq_iter a (b * c), iter_mul (· * a) b c 1]
  -- goal: (a^b)^c = iter (iter (· * a) c) b 1
  induction b with
  | zero =>
      show (a ^ 0) ^ c = iter (iter (· * a) c) 0 1
      rw [Nat.pow_zero, Nat.one_pow, iter_zero]
  | succ k ih =>
      show (a ^ (k + 1)) ^ c = iter (iter (· * a) c) (k + 1) 1
      rw [iter_succ_outside, ← ih]
      -- goal: (a^(k+1))^c = iter (· * a) c ((a^k)^c)
      rw [iter_mul_block, Nat.pow_succ, mul_pow_pure]

/-- `^`'s exponent-additivity `a^(b+c) = a^b * a^c`, derived **through
    `iter_add`** via `pow_eq_iter`: splitting the count `b+c` composes the
    two iteration blocks (`iter_add`), and composition of mul-by-`a` blocks
    reads out as multiplication of the powers (`iter_mul_block`).  The
    `iter_add` shadow alongside the `iter_mul` shadow above. -/
theorem pow_add_from_iter (a b c : Nat) : a ^ (b + c) = a ^ b * a ^ c := by
  rw [pow_eq_iter a (b + c), iter_add (· * a) b c 1,
      iter_mul_block a b (iter (· * a) c 1), ← pow_eq_iter a c, Nat.mul_comm]

/-! ## 6. ★ The contrast — idempotent climbs build no tower -/

/-- ★ An **idempotent** action collapses past one step: if `f (f x) = f x`
    then `iter f (n+1) x = f x` for every count `n`.  Iterating it builds
    NO tower — the count slot has nothing to multiply, so the diagonal
    climb is trivial.  By induction on `n` using the outside-peel. -/
theorem iter_idem {α : Type _} (f : α → α) (hf : ∀ x, f (f x) = f x) :
    ∀ (n : Nat) (x : α), iter f (n + 1) x = f x
  | 0,     x => rfl
  | n + 1, x => by
      rw [iter_succ_outside, iter_idem f hf n x, hf x]

/-- `Nat.max` unfolds to its `if`-form (definitional; the core
    `Nat.max_def` carries `propext`, so we state the `rfl` directly). -/
theorem max_unfold (a x : Nat) : Nat.max a x = if a ≤ x then x else a := rfl

/-- `Nat.max a` is **idempotent**: `max a (max a x) = max a x`.  Proved
    purely from the `if`-form by the decidable case split on `a ≤ x` (no
    `Classical`: `a ≤ x` is decidable, and the core `Nat.max_self` /
    `Nat.max_assoc` carry `propext`). -/
theorem max_idem (a x : Nat) : Nat.max a (Nat.max a x) = Nat.max a x := by
  rw [max_unfold a x]
  by_cases h : a ≤ x
  · rw [if_pos h, max_unfold a x, if_pos h]
  · rw [if_neg h, max_unfold a a, if_pos (Nat.le_refl a)]

/-- The `∪`-climb is trivial on its diagonal: `Nat.max a` is idempotent
    (`max_idem`), so iterating it any positive number of times gives the same
    single step `max a x`.  This is `a ∪ a = a`: the diagonal climb is
    multiplicative only where the rung-operator is *not* idempotent —
    `max`/`∪` builds no tower. -/
theorem max_iter_trivial (a : Nat) :
    ∀ (n x : Nat), iter (Nat.max a) (n + 1) x = Nat.max a x :=
  iter_idem (Nat.max a) (max_idem a)

end E213.Meta.Nat.Iterate213
