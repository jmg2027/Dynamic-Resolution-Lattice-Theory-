import E213.Lib.Math.Combinatorics.LymInequality

/-!
# Bollobás' set-pair inequality (∅-axiom engine + the cross-intersection heart)

**The named theorem (L3).**  Bollobás (1965): if `(A_1,B_1), …, (A_m,B_m)` are
pairs of subsets of `[n]` with `A_i ∩ B_i = ∅` for all `i` and `A_i ∩ B_j ≠ ∅`
for all `i ≠ j` (cross-intersecting), and `|A_i| = a`, `|B_i| = b` are uniform,
then

  `m ≤ C(a + b, a)` .

The bound is **independent of `n`** — the celebrated feature.

**The compilation (`seed/PROOF_ISA.md`).**  Bollobás is the *same* `COUNT`
double-count engine as Sperner/LYM, on a different incidence: rows are the pairs,
columns are the orderings `π` of `[n]`, and the entry is "`π` favours pair `i`"
= every element of `A_i` precedes every element of `B_i` in `π`.  The
cross-intersecting hypothesis makes **each ordering favour ≤ 1 pair** (the
column cap), so `Σ_i #{π favouring i} ≤ n!` — this is `lym_double_count`,
*verbatim*.  Dividing by the per-pair favour-count `#{π favouring i} =
n!·a!·b!/(a+b)!` gives `m ≤ (a+b)!/(a!·b!) = C(a+b,a)`.

**What is the new content vs. Sperner.**  The engine (`lym_double_count`) and the
arithmetic (`binom_mul_fact`) are reused unchanged.  The genuinely new piece is
the **column cap**: that cross-intersection forces each ordering to favour at
most one pair.  Its proof is an **antisymmetry of the ordering** — if `π`
favoured both `i` and `j` (`i ≠ j`), then picking `x ∈ A_i ∩ B_j` and
`y ∈ A_j ∩ B_i` gives `x` before `y` (from favouring `i`) *and* `y` before `x`
(from favouring `j`), forcing `x = y`, whence `x ∈ A_i ∩ B_i = ∅`,
contradiction.  This file builds the `before` relation, its antisymmetry, the
`favours` predicate over the `SpernerChains` ordering model, and discharges the
column cap (`bollobas_cap`).

## What is closed (∅-axiom)

  · `before_antisymm` — the ordering is antisymmetric: `before c x y` and
    `before c y x` force `x = y` (no `Nodup` needed).
  · `favours_before` — favouring `(A,B)` yields `before c x y` for every
    `x ∈ A`, `y ∈ B`.
  · `bollobas_cap` — **the column cap (the new heart)**: under cross-intersection
    + per-pair disjointness, each ordering favours ≤ 1 pair.
  · `bollobas_sum` — the **engine**, unconditional: `Σ_i #{π favouring i} ≤ n!`
    (= `lym_double_count` on the favour-incidence).
  · `bollobas` — **the named bound, modulo the favour-count**: with the exact
    count `V·(a+b)! = n!·a!·b!` as a hypothesis (the honest open rung — the
    geometric ordering count, not yet discharged), `m ≤ C(a+b,a)`.

**The favour-count** `#{π : all A before all B} = C(n,a+b)·a!·b!·(n−a−b)!`, i.e.
`V·(a+b)! = n!·a!·b!` (the analogue of `SpernerChains.chain_low`), is discharged in
`BollobasCount` (`favourCount_lower`), so `bollobas_uniform` — `m ≤ C(a+b,a)`,
`n`-independent — holds unconditionally.  The **column cap — the content of
Bollobás — is the new heart, closed here.**

Companion essay: `theory/essays/proof_isa/lym_inequality.md` (Bollobás section).
-/

namespace E213.Lib.Math.Combinatorics.BollobasSetPair

open E213.Lib.Math.Combinatorics.Sperner
open E213.Lib.Math.Combinatorics.SpernerChains
open E213.Lib.Math.Combinatorics.Permutations (fact perms)
open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Tactic.NatHelper renaming mul_assoc → nmul_assoc, mul_left_comm → nmul_left_comm

/-! ## §1 — the ordering relation `before` and its antisymmetry

`before c x y` = scanning the ordering `c` left to right, `x` is met strictly
before `y`.  Antisymmetry — the engine of the column cap — holds with no
`Nodup` assumption: if both `x` before `y` and `y` before `x`, the first symbol
to appear pins `x = y`. -/

/-- `x` appears strictly before `y` in the ordering `c`. -/
def before : List Nat → Nat → Nat → Bool
  | [], _, _ => false
  | z :: zs, x, y =>
      bif Nat.beq z x then elemNat y zs
      else bif Nat.beq z y then false
      else before zs x y

/-- Reduction: head equals `x` ⟹ `x` before `y` iff `y` is in the tail. -/
theorem before_x {z x y : Nat} (zs : List Nat) (h : Nat.beq z x = true) :
    before (z :: zs) x y = elemNat y zs := by
  show (bif Nat.beq z x then elemNat y zs
        else bif Nat.beq z y then false else before zs x y) = elemNat y zs
  rw [h]; rfl

/-- Reduction: head equals `y` (and not `x`) ⟹ `x` is not before `y`. -/
theorem before_y {z x y : Nat} (zs : List Nat)
    (hx : Nat.beq z x = false) (hy : Nat.beq z y = true) :
    before (z :: zs) x y = false := by
  show (bif Nat.beq z x then elemNat y zs
        else bif Nat.beq z y then false else before zs x y) = false
  rw [hx, hy]; rfl

/-- Reduction: head is neither ⟹ recurse on the tail. -/
theorem before_rec {z x y : Nat} (zs : List Nat)
    (hx : Nat.beq z x = false) (hy : Nat.beq z y = false) :
    before (z :: zs) x y = before zs x y := by
  show (bif Nat.beq z x then elemNat y zs
        else bif Nat.beq z y then false else before zs x y) = before zs x y
  rw [hx, hy]; rfl

/-- ★ **Antisymmetry of the ordering.**  `before c x y` and `before c y x`
    force `x = y` — the relation is a strict order, no `Nodup` needed.  This is
    the engine of the column cap. -/
theorem before_antisymm : ∀ (c : List Nat) (x y : Nat),
    before c x y = true → before c y x = true → x = y
  | [], _, _, h, _ => Bool.noConfusion h
  | z :: zs, x, y, hxy, hyx => by
      cases hzx : Nat.beq z x with
      | true =>
          cases hzy : Nat.beq z y with
          | true => rw [← Nat.eq_of_beq_eq_true hzx, ← Nat.eq_of_beq_eq_true hzy]
          | false =>
              rw [before_y zs hzy hzx] at hyx
              exact Bool.noConfusion hyx
      | false =>
          cases hzy : Nat.beq z y with
          | true =>
              rw [before_y zs hzx hzy] at hxy
              exact Bool.noConfusion hxy
          | false =>
              rw [before_rec zs hzx hzy] at hxy
              rw [before_rec zs hzy hzx] at hyx
              exact before_antisymm zs x y hxy hyx

/-! ## §2 — the `favours` predicate over the ordering model

`favours n c A B` = every true-position of `A` is before every true-position of
`B` in the ordering `c` (positions read off `idxList n`, as in `SpernerChains`).
The two-level `listAll` is a `Bool`-valued universal quantifier over the
position lists. -/

/-- `Bool`-valued universal quantifier over a `List Nat` (propext-free). -/
def listAll (p : Nat → Bool) : List Nat → Bool
  | [] => true
  | x :: xs => p x && listAll p xs

theorem listAll_mem {p : Nat → Bool} :
    ∀ {l : List Nat}, listAll p l = true → ∀ x, x ∈ l → p x = true
  | [], _, _, hx => nomatch hx
  | a :: l, h, x, hx => by
      cases hp : p a with
      | false =>
          have h2 : (p a && listAll p l) = true := h
          rw [hp] at h2; exact Bool.noConfusion h2
      | true =>
          have hrest : listAll p l = true := by
            have h2 : (p a && listAll p l) = true := h
            rw [hp] at h2; exact h2
          cases hx with
          | head => exact hp
          | tail _ hx' => exact listAll_mem hrest x hx'

/-- `c` favours the pair `(A,B)`: all of `A` precedes all of `B`. -/
def favours (n : Nat) (c : List Nat) (A B : List Bool) : Bool :=
  listAll (fun x => listAll (fun y => before c x y) (truePos B (idxList n)))
          (truePos A (idxList n))

/-- Favouring `(A,B)` yields `before c x y` for each `x ∈ A`, `y ∈ B`. -/
theorem favours_before {n : Nat} {c : List Nat} {A B : List Bool}
    (h : favours n c A B = true) {x y : Nat}
    (hx : x ∈ truePos A (idxList n)) (hy : y ∈ truePos B (idxList n)) :
    before c x y = true :=
  listAll_mem (listAll_mem h x hx) y hy

/-! ## §3 — the column cap (the new heart)

Cross-intersection forces each ordering to favour at most one pair.  This is the
only place Bollobás differs from Sperner; everything below is the shared engine. -/

/-- The membership-set of a pair's first / second component (true-positions). -/
def inA (n : Nat) (p : List Bool × List Bool) : List Nat := truePos p.1 (idxList n)
def inB (n : Nat) (p : List Bool × List Bool) : List Nat := truePos p.2 (idxList n)

/-- Per-pair disjointness `A_i ∩ B_i = ∅`. -/
def PairDisjoint (n : Nat) (F : List (List Bool × List Bool)) : Prop :=
  ∀ p, p ∈ F → ∀ x, x ∈ inA n p → x ∈ inB n p → False

/-- Cross-intersection `A_i ∩ B_j ≠ ∅` and `A_j ∩ B_i ≠ ∅` for distinct pairs. -/
def CrossIntersecting (n : Nat) (F : List (List Bool × List Bool)) : Prop :=
  ∀ p, p ∈ F → ∀ q, q ∈ F → p ≠ q →
    (∃ x, x ∈ inA n p ∧ x ∈ inB n q) ∧ (∃ y, y ∈ inA n q ∧ y ∈ inB n p)

/-- Two pairs favoured by the same ordering, with cross-intersection, coincide:
    the contradiction is `before c x y` ∧ `before c y x` ⟹ `x = y ∈ A_i ∩ B_i`. -/
theorem favours_eq {n : Nat} {c : List Nat} {p q : List Bool × List Bool}
    (hpd : ∀ x, x ∈ inA n p → x ∈ inB n p → False)
    (hc1 : ∃ x, x ∈ inA n p ∧ x ∈ inB n q)
    (hc2 : ∃ y, y ∈ inA n q ∧ y ∈ inB n p)
    (hp : favours n c p.1 p.2 = true) (hq : favours n c q.1 q.2 = true) : False := by
  obtain ⟨x, hxpA, hxqB⟩ := hc1
  obtain ⟨y, hyqA, hypB⟩ := hc2
  have hbxy : before c x y = true := favours_before hp hxpA hypB
  have hbyx : before c y x = true := favours_before hq hyqA hxqB
  have hxy : x = y := before_antisymm c x y hbxy hbyx
  rw [hxy] at hxpA
  exact hpd y hxpA hypB

open E213.Lib.Math.Combinatorics.SpernerChains (lcount_le_one_of)

/-- ★ **The column cap.**  Under cross-intersection + per-pair disjointness, each
    ordering `c` favours at most one pair of `F`.  *This is the content of
    Bollobás* — the only step beyond the shared LYM engine. -/
theorem bollobas_cap {n : Nat} {F : List (List Bool × List Bool)}
    (hdisj : PairDisjoint n F) (hcross : CrossIntersecting n F) (hnd : F.Nodup) :
    ∀ c, c ∈ perms (idxList n) → lcount (fun p => favours n c p.1 p.2) F ≤ 1 := by
  intro c _
  refine lcount_le_one_of ?_ hnd
  intro p hp q hq hfp hfq
  by_cases hpq : p = q
  · exact hpq
  · exact absurd
      (favours_eq (hdisj p hp) (hcross p hp q hq hpq).1 (hcross p hp q hq hpq).2 hfp hfq)
      (fun h => h)

/-! ## §4 — the engine and the named bound

`bollobas_sum` is `lym_double_count` on the favour-incidence: unconditional,
∅-axiom.  `bollobas` cancels the per-pair favour-count against `binom_mul_fact`
to read off `m ≤ C(a+b,a)`; the count itself (`V·(a+b)! = n!·a!·b!`) is the
honest open rung. -/

/-- ★ **The Bollobás engine** (= LYM on the favour-incidence), unconditional:
    `Σ_{p∈F} #{orderings favouring p} ≤ n!`. -/
theorem bollobas_sum {n : Nat} {F : List (List Bool × List Bool)}
    (hdisj : PairDisjoint n F) (hcross : CrossIntersecting n F) (hnd : F.Nodup) :
    sumOver (fun p => lcount (fun c => favours n c p.1 p.2) (perms (idxList n))) F
      ≤ fact n := by
  have h := lym_double_count F (perms (idxList n))
              (fun p c => favours n c p.1 p.2) (bollobas_cap hdisj hcross hnd)
  rw [chains_length] at h
  exact h

/-- `C(a+b,a)·a!·b! = (a+b)!` — the binomial identity with the complement size
    `(a+b)−a` reduced to `b`. -/
theorem binom_ab (a b : Nat) : binom (a + b) a * (fact a * fact b) = fact (a + b) := by
  have hsub : ∀ a b : Nat, (a + b) - a = b := by
    intro a b
    induction a with
    | zero => rw [Nat.zero_add, Nat.sub_zero]
    | succ k ih => rw [Nat.succ_add, Nat.succ_sub_succ_eq_sub]; exact ih
  have h := binom_mul_fact (a + b) a (Nat.le_add_right a b)
  rw [hsub a b] at h
  exact h

/-- ★★ **Bollobás' set-pair inequality (named), modulo the favour-count.**  For a
    cross-intersecting, per-pair-disjoint family `F` with `|A_i| = a`, `|B_i| = b`
    uniform, *if* each pair is favoured by `V` orderings where
    `V·(a+b)! = n!·a!·b!` (the exact geometric count — the honest open rung), then

      `|F| ≤ C(a + b, a)` ,

    independent of `n`.  The column cap (cross-intersection ⟹ ≤ 1 per ordering)
    is proven; the cancellation is `binom_mul_fact`. -/
theorem bollobas {n a b V : Nat} {F : List (List Bool × List Bool)}
    (hdisj : PairDisjoint n F) (hcross : CrossIntersecting n F) (hnd : F.Nodup)
    (hV : V * fact (a + b) = fact n * (fact a * fact b))
    (hcount : ∀ p, p ∈ F →
        V ≤ lcount (fun c => favours n c p.1 p.2) (perms (idxList n))) :
    F.length ≤ binom (a + b) a := by
  -- engine + per-pair count ⟹ `|F| · V ≤ n!`
  have hFV : F.length * V ≤ fact n := by
    calc F.length * V
        = sumOver (fun _ => V) F := by rw [sumOver_const]; exact Nat.mul_comm _ _
      _ ≤ sumOver (fun p => lcount (fun c => favours n c p.1 p.2) (perms (idxList n))) F :=
          sumOver_le (fun p hp => hcount p hp)
      _ ≤ fact n := bollobas_sum hdisj hcross hnd
  -- multiply by `(a+b)!`, substitute the count, and cancel `n!·a!·b!`
  have hpos : 0 < fact n * (fact a * fact b) :=
    Nat.mul_pos (fact_pos n) (Nat.mul_pos (fact_pos a) (fact_pos b))
  have step : (F.length * V) * fact (a + b) ≤ fact n * fact (a + b) :=
    Nat.mul_le_mul_right _ hFV
  rw [nmul_assoc, hV, ← binom_ab a b] at step
  -- step : F.length * (n!·a!·b!) ≤ n! * (C(a+b,a) · (a!·b!))
  have hrhs : fact n * (binom (a + b) a * (fact a * fact b))
      = binom (a + b) a * (fact n * (fact a * fact b)) := nmul_left_comm _ _ _
  rw [hrhs] at step
  -- step : F.length · K ≤ C(a+b,a) · K  with K = n!·a!·b! > 0; cancel K on the left
  have step2 : (fact n * (fact a * fact b)) * F.length
      ≤ (fact n * (fact a * fact b)) * binom (a + b) a := by
    rw [Nat.mul_comm (fact n * (fact a * fact b)) F.length,
        Nat.mul_comm (fact n * (fact a * fact b)) (binom (a + b) a)]
    exact step
  exact Nat.le_of_mul_le_mul_left step2 hpos

/-! ## §5 — the favour-count target: the rung's arithmetic, discharged

The remaining rung of `bollobas` is the geometric favour-count `V`.  Its *value*
is forced: `V = C(n,a+b)·a!·b!·(n−a−b)!` (choose the `a+b` slots hosting `A∪B`,
order `A` into the first `a` and `B` into the next `b`, order the rest).  This
section proves that value satisfies `bollobas`'s arithmetic hypothesis
`V·(a+b)! = n!·a!·b!` (`favourCount_mul`), so the rung collapses to a *single
clean geometric inequality* — `bollobas_of_count` below.  What remains for a
future session is purely the injection `favourCountTarget ≤ #{favouring}` (the
ordering analogue of `SpernerChains.chain_low`), with no arithmetic bookkeeping
left to do. -/

/-- The forced favour-count value: `C(n,a+b)·a!·b!·(n−a−b)!` = the number of
    orderings of `[n]` with all of `A` before all of `B` (`|A|=a`, `|B|=b`). -/
def favourCountTarget (n a b : Nat) : Nat :=
  binom n (a + b) * (fact a * fact b * fact (n - (a + b)))

/-- ★ **The rung's arithmetic.**  The forced favour-count satisfies `bollobas`'s
    cancellation hypothesis: `favourCountTarget · (a+b)! = n!·a!·b!`.  Proven from
    `binom_mul_fact` (`C(n,a+b)·(a+b)!·(n−a−b)! = n!`) by rearrangement. -/
theorem favourCount_mul {n a b : Nat} (hab : a + b ≤ n) :
    favourCountTarget n a b * fact (a + b) = fact n * (fact a * fact b) := by
  show binom n (a + b) * (fact a * fact b * fact (n - (a + b))) * fact (a + b)
      = fact n * (fact a * fact b)
  have hac : (fact a * fact b * fact (n - (a + b))) * fact (a + b)
      = (fact (a + b) * fact (n - (a + b))) * (fact a * fact b) := by
    rw [nmul_assoc (fact a * fact b) (fact (n - (a + b))) (fact (a + b)),
        Nat.mul_comm (fact (n - (a + b))) (fact (a + b)),
        Nat.mul_comm (fact a * fact b) (fact (a + b) * fact (n - (a + b)))]
  rw [nmul_assoc (binom n (a + b)) (fact a * fact b * fact (n - (a + b))) (fact (a + b)),
      hac, ← nmul_assoc (binom n (a + b)) (fact (a + b) * fact (n - (a + b))) (fact a * fact b),
      binom_mul_fact n (a + b) hab]

/-- ★★ **Bollobás, modulo only the geometric favour-count.**  With the arithmetic
    discharged (`favourCount_mul`), the named bound `|F| ≤ C(a+b,a)` follows from
    the *single* clean inequality `C(n,a+b)·a!·b!·(n−a−b)! ≤ #{orderings favouring
    the pair}` — the lone remaining rung (the `chain_low` analogue). -/
theorem bollobas_of_count {n a b : Nat} {F : List (List Bool × List Bool)}
    (hdisj : PairDisjoint n F) (hcross : CrossIntersecting n F) (hnd : F.Nodup)
    (hab : a + b ≤ n)
    (hcount : ∀ p, p ∈ F →
        favourCountTarget n a b ≤ lcount (fun c => favours n c p.1 p.2) (perms (idxList n))) :
    F.length ≤ binom (a + b) a :=
  bollobas hdisj hcross hnd (favourCount_mul hab) hcount

end E213.Lib.Math.Combinatorics.BollobasSetPair
