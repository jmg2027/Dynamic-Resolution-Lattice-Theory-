import E213.Meta.Nat.NoOrderModP
import E213.Meta.Int213.Order

/-!
# OrderWrap — a translation-invariant order exists exactly when nothing wraps

This is the **cross-domain bridge** between two facts that until now lived
apart:

* `Int213.Order` / `OrderMul` — ℤ carries a translation-invariant strict
  order (`lt_irrefl`, `lt_trans`, `add_lt_add_right`, the sign trichotomy
  `int_sign`): the un-wrapped counting line extended by sign keeps its order.
* `Nat.NoOrderModP.no_wrapping_order` — the circle `1, 2, …, p` carries *no*
  such order: walking the successor lands back on the start, forcing `1 < 1`.

They are the **two sides of one fact**.  A "successor structure" is a triple
`(M, s, a)`: a carrier `M`, a successor map `s : M → M`, and a basepoint `a`.
Its orbit is `a, s a, s (s a), …`.  A **translation-invariant strict-order
witness** (`OrderWitness`) is a relation that is irreflexive, transitive,
preserved by `s` on both sides, and seeds the edge `a < s a`.

The single schema:

  * ★★★ `no_order_of_wrap` — if the orbit **wraps** (`orbit s a n = a` for some
    `n > 0`), then **no** `OrderWitness` exists.  Walking the seed edge through
    `s` reaches `a < a`, which irreflexivity forbids.

The two instances:

  * `intOrderWitness` + `int_orbit_no_wrap` — ℤ with `s = (·+1)`, `a = 0`:
    a witness *does* exist (its `<`), and the orbit `0,1,2,…` never returns to
    `0` (`int_orbit_no_wrap`).  No wrap ⇒ the schema yields no contradiction ⇒
    the order survives.
  * `modp_no_order` — the circle `1..p` with `s = next p`, `a = 1`: the orbit
    *does* wrap (`orbit p = 1`), so by the schema no witness exists.  This
    re-derives `no_wrapping_order` as a corollary of the general fact.

**The price the `^`-wall's escape pays** (frontier `slot_tower_crossdomain.md`
§2): you *can* fold the line into `mod p` to make every power solvable
(discrete logs always exist on a cyclic group), but folding *is* wrapping, and
wrapping is exactly what destroys the order the line had.

All decls ∅-axiom: bare recursion / induction, the inductive `Int.NonNeg`
order layer, and the decidable test `x < p`.  No `0`/`%` smuggled into the
circle (its points start at `1`), no Mathlib, no `Classical`.
-/

namespace E213.Meta.OrderWrap

open E213.Meta.Int213.Order (lt_irrefl lt_trans add_lt_add_right le_refl)

/-! ## §1 — the successor structure and its orbit -/

/-- The orbit of basepoint `a` under successor `s`: `orbit 0 = a`, then keep
    applying `s`.  It runs `a, s a, s (s a), …`. -/
def orbit {M : Type} (s : M → M) (a : M) : Nat → M
  | 0     => a
  | k + 1 => s (orbit s a k)

/-- A **translation-invariant strict-order witness** on `(M, s, a)`: a relation
    that never holds reflexively, chains, is preserved by `s` on both sides, and
    seeds the edge `a < s a`.  ℤ's `<` is one (`intOrderWitness`); the circle
    `1..p` admits none (`modp_no_order`). -/
structure OrderWitness (M : Type) (s : M → M) (a : M) where
  /-- the order relation, read `R x y` as "x is below y". -/
  R : M → M → Prop
  /-- nothing is below itself. -/
  irrefl : ∀ x, ¬ R x x
  /-- below is chainable. -/
  trans  : ∀ x y z, R x y → R y z → R x z
  /-- the successor preserves the order on both sides. -/
  transl : ∀ x y, R x y → R (s x) (s y)
  /-- the seed edge: the basepoint is below its successor. -/
  start  : R a (s a)

/-! ## §2 — the single schema: a wrap kills every witness -/

/-- Each orbit step is one `R`-edge: `R (orbit k) (orbit (k+1))`.  The first
    is `start` (`orbit 0 = a`, `orbit 1 = s a`); each next edge is the previous
    one pushed through `s` on both sides by `transl`. -/
theorem edge {M : Type} (s : M → M) (a : M) (w : OrderWitness M s a) :
    ∀ k, w.R (orbit s a k) (orbit s a (k + 1))
  | 0     => w.start
  | k + 1 => w.transl (orbit s a k) (orbit s a (k + 1)) (edge s a w k)

/-- Chain the edges from the basepoint: `R a (orbit (k+1))` for every `k`
    (`orbit 0 = a`). -/
theorem reach {M : Type} (s : M → M) (a : M) (w : OrderWitness M s a) :
    ∀ k, w.R a (orbit s a (k + 1))
  | 0     => edge s a w 0
  | k + 1 =>
      w.trans a (orbit s a (k + 1)) (orbit s a (k + 1 + 1))
        (reach s a w k) (edge s a w (k + 1))

/-- ★★★ **A wrap destroys every translation-invariant order.**  If the orbit
    of `(M, s, a)` returns to the basepoint after `n > 0` steps
    (`orbit s a n = a`), then no `OrderWitness` exists.

    Walking the seed edge `n` times reaches `R a (orbit n) = R a a`, which
    irreflexivity forbids.  This is the abstract content shared by the circle
    `1..p` (which wraps) and witnessed-against by ℤ (which does not). -/
theorem no_order_of_wrap {M : Type} (s : M → M) (a : M) (w : OrderWitness M s a)
    {n : Nat} (hn : 0 < n) (hwrap : orbit s a n = a) : False := by
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ m =>
      have hloop : w.R a (orbit s a (m + 1)) := reach s a w m
      rw [hwrap] at hloop
      exact w.irrefl a hloop

/-! ## §3 — instance ℤ: a witness exists, and the line never wraps -/

/-- The successor on ℤ adds one. -/
private def isucc (x : Int) : Int := x + 1

/-- ℤ's strict order is a translation-invariant order witness on `(ℤ, +1, 0)`:
    irreflexive (`lt_irrefl`), transitive (`lt_trans`), preserved by `+1`
    (`add_lt_add_right`), with the seed `0 < 0 + 1`. -/
def intOrderWitness : OrderWitness Int isucc 0 where
  R x y := x < y
  irrefl := lt_irrefl
  trans  := fun _ _ _ hxy hyz => lt_trans hxy hyz
  transl := fun x y hxy => add_lt_add_right hxy 1
  start  := by
    -- `0 < isucc 0` is `(0+1) ≤ isucc 0`; since `isucc 0 ≡ 0+1`, that is `le_refl`.
    show (0 : Int) < isucc 0
    exact le_refl (isucc 0)

/-- The ℤ orbit of `0` under `+1` is just the counting line: `orbit n = n`. -/
theorem int_orbit_eq : ∀ k : Nat, orbit isucc 0 k = Int.ofNat k
  | 0     => rfl
  | k + 1 => by
      show isucc (orbit isucc 0 k) = Int.ofNat (k + 1)
      rw [int_orbit_eq k]
      show Int.ofNat k + 1 = Int.ofNat (k + 1)
      rfl

/-- ★ **The counting line never wraps.**  For `n > 0` the ℤ orbit `orbit n = n`
    is never `0`.  So `no_order_of_wrap` produces no contradiction for ℤ — the
    order `intOrderWitness` survives precisely because nothing wraps. -/
theorem int_orbit_no_wrap : ∀ n : Nat, 0 < n → orbit isucc 0 n ≠ 0
  | 0,     hn => absurd hn (Nat.lt_irrefl 0)
  | n + 1, _  => by
      rw [int_orbit_eq]
      intro h
      exact Nat.noConfusion (Int.ofNat.inj (h : Int.ofNat (n + 1) = Int.ofNat 0))

/-! ## §4 — instance ℤ/p: the circle wraps, so no witness exists -/

open E213.Meta.Nat.NoOrderModP (next orbit_wrap)

/-- The abstract orbit on `(Nat, next p, 1)` agrees with `NoOrderModP.orbit p`
    — both start at `1` and step by `next p`. -/
theorem orbit_modp_eq (p : Nat) :
    ∀ k, orbit (next p) 1 k = E213.Meta.Nat.NoOrderModP.orbit p k
  | 0     => rfl
  | k + 1 => by
      show next p (orbit (next p) 1 k) = next p (E213.Meta.Nat.NoOrderModP.orbit p k)
      rw [orbit_modp_eq p k]

/-- ★★ **The circle `1..p` admits no translation-invariant order.**  Its orbit
    wraps (`orbit p = 1`, `orbit_wrap`), so `no_order_of_wrap` rules out every
    `OrderWitness`.  This re-derives `NoOrderModP.no_wrapping_order` as a
    corollary of the general schema.

    Needs `2 ≤ p` so the circle has at least two points (and the seed edge
    `1 < next p 1 = 2` is genuine). -/
theorem modp_no_order (p : Nat) (hp : 2 ≤ p) (w : OrderWitness Nat (next p) 1) :
    False := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp
  have hwrap : orbit (next p) 1 p = 1 := by
    rw [orbit_modp_eq p p]; exact orbit_wrap p hp
  exact no_order_of_wrap (next p) 1 w hp0 hwrap

end E213.Meta.OrderWrap
