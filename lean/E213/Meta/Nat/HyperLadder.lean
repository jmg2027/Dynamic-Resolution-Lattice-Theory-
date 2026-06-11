import E213.Meta.Nat.Iterate213

/-!
# HyperLadder — the number tower is one recursion turning the count-clock

`Iterate213` proves each rung of the tower is iteration against the count
slot `Nat`: `add_eq_iter`, `mul_eq_iter`, `pow_eq_iter`.  Those three are the
positive spine — but three separately-stated theorems do not *exhibit* the
tower as **one object**.  This file does: a single recursion `hyperop` whose
only engine is `iter` (the count-Lens `Nat`), with `+`, `×`, `^` falling out
as `hyperop 1`, `hyperop 2`, `hyperop 3`.

  * `hyperop` — `hyperop 0 a b = b + 1` (successor); `hyperop (k+1) a b =
    iter (hyperop k a) b (seed k a)`: **each rung is the previous rung
    iterated `b` times** from the level's right-unit `seed k a`.
  * `hyperop_succ` — that recursion, named (`rfl`): the rung-`(k+1)` operation
    *is* the count `b` iterating the rung-`k` operation.
  * `hyperop_zero/one/two/three` — `b+1`, `a+b`, `a*b`, `a^b`.

**The §5(a) frontier claim, made formal** (`slot_tower_crossdomain.md`).  The
tower is `hyperop`: a single `Nat`-recursion (the level `k`) whose body is a
single `Nat`-iteration (the count `b` through `iter`).  Both indices are the
*same* count-Lens — "operation-ness = iteration against the one count-clock".
There is no rung that escapes `iter`; the ladder is the count iterating on
itself.  The reading of this `Nat`-clock as *the §10.1 ℕ-induction cost* and
as *ORIGIN_RAW's lockstep clock* is the narrative gloss, **not** a separate
Lean equation (stating that as a theorem would be vacuous); the honest formal
content is this one recursion.

**The funext landmine** (why `iter_congr`).  Matching the flavour functions
across rungs (`hyperop 1 a = (· + a)` etc.) by `funext`/`rw`-on-functions
pulls `Quot.sound` — *axiom-dirty*.  The whole file routes flavour-matching
through the **pointwise** `iter_congr` (induction on the count, no funext),
so every theorem stays ∅-axiom.  `Nat.add_comm`/`Nat.mul_comm` (PURE in core)
supply the only re-association: `iter` accumulates `(· + a)` on the right
where the lower rung reads `a + ·` on the left — the same number, the
commutativity of the rung below.

All decls ∅-axiom: bare recursion + induction on `Nat`, the `iter` engine of
`Iterate213`, and the PURE core `Nat.add_comm`/`Nat.mul_comm`.
-/

namespace E213.Meta.Nat.HyperLadder

open E213.Meta.Nat.Iterate213 (iter iter_succ add_eq_iter mul_eq_iter pow_eq_iter)

/-! ## §1 — pointwise iteration congruence (the funext-free keystone) -/

/-- ★★ **Pointwise congruence for `iter`.**  If `f` and `g` agree at every
    point, they iterate to the same value — proved by induction on the count,
    with **no `funext`** (which would pull `Quot.sound`).  This is the lemma
    that keeps the whole ladder ∅-axiom: flavour-matching the rungs is done
    through this, never by rewriting one function into another. -/
theorem iter_congr {α : Type _} {f g : α → α} (h : ∀ x, f x = g x) :
    ∀ (n : Nat) (x : α), iter f n x = iter g n x
  | 0,     _ => rfl
  | n + 1, x => by
      rw [iter_succ f n x, iter_succ g n x, h x]
      exact iter_congr h n (g x)

/-! ## §2 — the ladder -/

/-- The level-`k` **right unit** (the seed `iter` starts from): `b ↦ a` at
    level `0` (so `hyperop 1 a 0 = a`), `0` at level `1` (`a·0 = 0`), `1` at
    every level `≥ 2` (`a^0 = 1`, and the tetration unit). -/
def seed : Nat → Nat → Nat
  | 0,     a => a
  | 1,     _ => 0
  | _ + 2, _ => 1

/-- **The hyperoperation ladder.**  Level `0` is the successor `b + 1`
    (it ignores `a`); each higher level iterates the previous one `b` times
    from that level's `seed`.  The only engine is `iter` (the count-clock
    `Nat`); the level index `k` is a second `Nat`-recursion. -/
def hyperop : Nat → Nat → Nat → Nat
  | 0,     _, b => b + 1
  | k + 1, a, b => iter (hyperop k a) b (seed k a)

/-- ★★★ **The ladder recursion, named.**  Rung `k+1` *is* the count `b`
    iterating rung `k` from the level seed.  `rfl` — this is the definition,
    surfaced as the structural statement "each operation is the previous one
    counted".  The whole tower is this one line. -/
theorem hyperop_succ (k a b : Nat) :
    hyperop (k + 1) a b = iter (hyperop k a) b (seed k a) := rfl

/-! ## §3 — the rungs: successor, +, ×, ^ -/

/-- Level `0`: the successor (zeration), ignoring the base. -/
theorem hyperop_zero (a b : Nat) : hyperop 0 a b = b + 1 := rfl

/-- ★ **Level `1` is addition.**  `hyperop 1 a b = iter (·+1) b a = a + b`:
    the successor iterated `b` times from `a` (`add_eq_iter`).  `hyperop 0 a`
    is the successor pointwise (`x+1 = Nat.succ x`), matched by `iter_congr`. -/
theorem hyperop_one (a b : Nat) : hyperop 1 a b = a + b := by
  show iter (hyperop 0 a) b (seed 0 a) = a + b
  rw [add_eq_iter a b]
  exact iter_congr (fun _ => rfl) b a

/-- ★★ **Level `2` is multiplication.**  `hyperop 2 a b = iter (hyperop 1 a) b 0
    = a * b`: add-`a` iterated `b` times from `0` (`mul_eq_iter`).  `hyperop 1 a x
    = a + x` (level 1) and `mul_eq_iter` reads `x + a`; `Nat.add_comm` bridges
    them pointwise through `iter_congr`. -/
theorem hyperop_two (a b : Nat) : hyperop 2 a b = a * b := by
  show iter (hyperop 1 a) b (seed 1 a) = a * b
  rw [mul_eq_iter a b]
  exact iter_congr (fun x => by rw [hyperop_one]; exact Nat.add_comm a x) b 0

/-- ★★ **Level `3` is exponentiation.**  `hyperop 3 a b = iter (hyperop 2 a) b 1
    = a ^ b`: multiply-by-`a` iterated `b` times from `1` (`pow_eq_iter`).
    `hyperop 2 a x = a * x` (level 2) and `pow_eq_iter` reads `x * a`;
    `Nat.mul_comm` bridges them pointwise through `iter_congr`. -/
theorem hyperop_three (a b : Nat) : hyperop 3 a b = a ^ b := by
  show iter (hyperop 2 a) b (seed 2 a) = a ^ b
  rw [pow_eq_iter a b]
  exact iter_congr (fun x => by rw [hyperop_two]; exact Nat.mul_comm a x) b 1

end E213.Meta.Nat.HyperLadder
