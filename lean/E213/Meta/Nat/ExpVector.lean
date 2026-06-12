import E213.Meta.Nat.VpSeparation
import E213.Meta.Nat.VpMul
import E213.Meta.Nat.HyperLadder

/-!
# ExpVector — the number system that fits the tower's vector-linear structure

`vp_pow` says `^` is **scalar multiplication** on the prime-exponent coordinate
(`vp_p(a^k) = k · vp_p(a)`), and `vp_mul` says `×` is **vector addition**
(`vp_p(a·b) = vp_p(a) + vp_p(b)`).  So the system the tower *natively* wants is
the **exponent lattice**: numbers as prime-indexed exponent vectors, with `×`
as `+` and `^` as scalar `·`.  This file builds it.

The catch, and why it is a **setoid** not a quotient type: proving two exponent
vectors *equal as functions* needs `funext`, which is `Quot.sound`-dirty.  So
the system carries **pointwise equality** `vecEq` (a `Prop`, exactly the
`cutEq`/`ZpSeqEquiv` pattern), never `=` on functions — and stays ∅-axiom.

  * `ExpVec`, `vecAdd`, `vecSmul`, `vecEq` — the carrier and its operations.
  * `toVec` — the readout `ℕ⁺ → ExpVec`, `n ↦ (vp_p n)_p`.
  * ★ `toVec_mul` — `×` **becomes vector addition** (`vp_mul`).
  * ★ `toVec_pow` — `^` **becomes scalar multiplication** (`vp_pow`).
  * ★★ `toVec_faithful` — the readout is **injective** (`vp_separation`): the
    embedding `(ℕ⁺, ×, ^) ↪ (ExpVec, +, ·)` is faithful.
  * `toVec_finite_support` — every vector is **finitely supported**
    (`vp_eq_zero_of_gt`: zero at primes `> n`).

**Ontology note** (`theory/math/numbersystems/slot_arithmetic.md` §1).  In 213
**the tuple *is* the number**; the exponent vector is not a *readout of a primary
`ℕ`* but the **slot-presentation** of the multiplicative number itself (UFD makes
it faithful = canonical, `toVec_faithful`).  `toVec` is therefore the *iso*
between the `ℕ`-presentation and the slot-presentation of one number — not a
projection of a more-real `ℕ`.  ("`ℤ/ℚ/ℝ` are number systems" is *not* the 213
view — they name the operation-history of the axes / are flattening Lens
readouts; `ℤ` is the difference-Lens readout, itself non-faithful.)

**What this answers** (frontier `general_theory_metaanalysis.md` D′).  The
vector-linear system *exists* and is exactly the faithful, finite-support slot
that makes the **prime-exponent (multiplicative) slot the unique faithful-finite
readout** (C5).  In it the tower is linear: `×` = `+`, `^` = scalar `·`.  The
`^`-**wall dissolves into
linear algebra**: `logₐ b` is "find the scalar `k` with `vecSmul k (toVec a) =
toVec b`", solvable iff the two vectors are **collinear** (`FoldCriterion.
fold_iff_collinear`) — no transcendence here; that **migrates to the
archimedean place** (`ln p` ℚ-independent), outside this lattice.  Above `^`,
tetration is *still* scalar `·` but the scalar is a tower-value (a germ at real
height) — the linear form survives, the scalar does not.

All ∅-axiom: pointwise (`vecEq`, no `funext`), riding `vp_mul`/`vp_pow`/
`vp_separation`/`vp_eq_zero_of_not_dvd`.
-/

namespace E213.Meta.Nat.ExpVector

open E213.Meta.Nat.VpMul (IsPrime213 vp_mul vp_pow)
open E213.Meta.Nat.Valuation (vp)
open E213.Meta.Nat.VpSeparation (vp_separation vp_eq_zero_of_not_dvd)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-- A prime axis of the lattice. -/
abbrev Prime213 := {p : Nat // IsPrime213 p}

/-- The exponent-vector carrier: an exponent at each prime axis. -/
def ExpVec := Prime213 → Nat

/-- **Pointwise equality** — a setoid relation, *not* `funext`.  The
    `cutEq`/`ZpSeqEquiv` pattern that keeps the system ∅-axiom. -/
def vecEq (v w : ExpVec) : Prop := ∀ p, v p = w p

/-- **Vector addition** — what `×` becomes. -/
def vecAdd (v w : ExpVec) : ExpVec := fun p => v p + w p

/-- **Scalar multiplication** — what `^` becomes. -/
def vecSmul (k : Nat) (v : ExpVec) : ExpVec := fun p => k * v p

/-- The readout: a positive number to its prime-exponent vector. -/
def toVec (n : Nat) : ExpVec := fun p => vp p.val n

/-! ### `vecEq` is an equivalence (setoid laws) -/

theorem vecEq_refl (v : ExpVec) : vecEq v v := fun _ => rfl
theorem vecEq_symm {v w : ExpVec} (h : vecEq v w) : vecEq w v := fun p => (h p).symm
theorem vecEq_trans {u v w : ExpVec} (h1 : vecEq u v) (h2 : vecEq v w) :
    vecEq u w := fun p => (h1 p).trans (h2 p)

/-! ### The tower is linear on the lattice -/

/-- ★ **`×` becomes vector addition.**  `toVec (a·b) = toVec a + toVec b`
    (pointwise) — this is `vp_mul` read on every prime axis. -/
theorem toVec_mul {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    vecEq (toVec (a * b)) (vecAdd (toVec a) (toVec b)) :=
  fun p => vp_mul p.property ha hb

/-- ★ **`^` becomes scalar multiplication.**  `toVec (a^k) = k · toVec a`
    (pointwise) — this is `vp_pow` read on every prime axis.  The structural
    root of the `^`-wall: `^` acts *linearly* on the lattice. -/
theorem toVec_pow {a : Nat} (ha : 0 < a) (k : Nat) :
    vecEq (toVec (a ^ k)) (vecSmul k (toVec a)) :=
  fun p => vp_pow p.property ha k

/-- ★★ **The embedding is faithful.**  `toVec a = toVec b ⇒ a = b` — the
    readout is injective (`vp_separation`, unique factorization).  So
    `(ℕ⁺, ×, ^) ↪ (ExpVec, vecAdd, vecSmul)` is a *faithful* homomorphism: the
    multiplicative numbers genuinely *are* their exponent vectors. -/
theorem toVec_faithful {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (h : vecEq (toVec a) (toVec b)) : a = b :=
  vp_separation ha hb (fun p hp => h ⟨p, hp⟩)

/-- **Every vector is finitely supported.**  `toVec n` is `0` at each prime
    above `n` (`vp_eq_zero_of_not_dvd`: a prime `> n` cannot divide it).  So this
    slot lands in the **faithful + finite** cell — the C5 reason the
    prime-exponent (multiplicative) slot is the unique faithful-finite readout. -/
theorem toVec_finite_support {n : Nat} (hn : 0 < n) (p : Prime213)
    (hlt : n < p.val) : toVec n p = 0 :=
  vp_eq_zero_of_not_dvd p.property hn
    (fun hdvd => absurd hlt (Nat.not_lt.mpr (le_of_dvd_pos p.val n hn hdvd)))

/-! ### `^` acts linearly on the lattice — and `↑↑` does not (where the algebra stops)

`toVec_pow` recovers the algebra `^` lost at the wall: in the exponent lattice
`^` *is* scalar multiplication, `toVec (a^k) = k · toVec a` — the scalar is the
**exponent `k`** (linear in the height).  This is why the lattice is the
"algebra above `×`": `×`=`+`, `^`=scalar`·`, clean ℤ-module linear algebra.

One rung up it **breaks**: tetration acts on the lattice as scalar
multiplication too, but the scalar is the **tower-value below, not the height** —
so it is *not* linear in `b`, and there is no clean module / no canonical algebra
(matching the Abel-equation non-uniqueness, frontier D).  This is the lattice
witness of "the algebra recovers through `^`, and only through `^`". -/

open E213.Meta.Nat.HyperLadder (hyperop hyperop_climb hyperop_three)

/-- ★★ **`↑↑` is non-linear on the lattice: its scalar is the tower-value.**
    `toVec (a↑↑(b+1)) = (a↑↑b) · toVec a` — tetration scales `toVec a` by the
    *previous tower value* `hyperop 4 a b`, not by the height `b+1` (contrast
    `toVec_pow`, where `^` scales by the exponent itself).  So `^` is the last
    rung acting *linearly* on the exponent lattice; above it the "scalar" is a
    tower-germ, and the module structure (the recovered algebra) ends. -/
theorem toVec_tetration {a : Nat} (ha : 0 < a) (b : Nat) :
    vecEq (toVec (hyperop 4 a (b + 1))) (vecSmul (hyperop 4 a b) (toVec a)) := by
  have h : hyperop 4 a (b + 1) = a ^ (hyperop 4 a b) := by
    have hc := hyperop_climb 3 a b
    rwa [hyperop_three] at hc
  rw [h]
  exact toVec_pow ha (hyperop 4 a b)

/-- The contrast, concretely: `2^3` scales by `3` (the exponent), but `2↑↑3`
    scales by `4 = 2↑↑2` (the tower value, ≠ the height `3`). -/
theorem tetration_scalar_concrete :
    vp 2 (2 ^ 3) = 3 ∧ vp 2 (hyperop 4 2 3) = 4 := by decide

end E213.Meta.Nat.ExpVector
