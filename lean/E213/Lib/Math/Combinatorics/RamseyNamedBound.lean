import E213.Lib.Math.Combinatorics.Sperner
import E213.Lib.Math.Combinatorics.RamseyLowerBound

/-!
# Erdős' Ramsey lower bound `R(k,k) > N`, named (∅-axiom)

The last open rung of the proof-ISA COUNT series, now closed.  The engine is the
probabilistic-method schema `CountExistence.erdos_schema`; this file builds the
concrete `K_N` edge model that instantiates it.

A 2-colouring of `K_N` is a `Bool` vector over the `C(N,2)` edges.  For each
`k`-subset `S` of the `N` vertices, the "`S` is monochromatic" event constrains
the `C(k,2)` edges inside `S` (to one shared colour, `2` ways), so it holds on
`2·2^{C(N,2)−C(k,2)}` of the colourings (`matchesC_count`).  There are `C(N,k)`
such events (`Sperner.layer_size`).  Feeding `t = C(N,k)`,
`c = 2·2^{C(N,2)−C(k,2)}`, `n = C(N,2)` into `erdos_schema`, its hypothesis
`t·c < 2ⁿ` is `2·C(N,k) < 2^{C(k,2)}` — and the conclusion is a 2-colouring of
`K_N` with **no monochromatic `K_k`**, i.e. `R(k,k) > N`.

The crux is the count of edges inside `S` = `C(|S|,2)` — `pairsCount_eq`, the
Pascal step `binom_succ_2` applied to "each new vertex pairs with all previous".

Subset count side reused from Sperner: `kLayer N k` (the `k`-subsets),
`kLayer_card = C(N,k)`.
-/

namespace E213.Lib.Math.Combinatorics.RamseyNamedBound

open E213.Lib.Math.Combinatorics.BoolEnum
open E213.Lib.Math.Combinatorics.CountExistence (bcount_or_le erdos_schema)
open E213.Lib.Math.Combinatorics.RamseyLowerBound (matchesC countNone matchesC_count)
open E213.Lib.Math.Combinatorics.Sperner (cardB kLayer kLayer_card cardEq)
open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Tactic.List213 (length_map exists_of_mem_map mem_map_of_mem mem_filter)
open E213.Tactic.NatHelper (add_sub_cancel_right add_sub_of_le)
open E213.Tactic.NatHelper renaming mul_assoc → nmul_assoc, mul_left_comm → nmul_left_comm

/-! ## §1 — the edge pattern and its internal-edge count -/

/-- Edges inside `S`: pairs of `true`-positions.  `pairsCount S = C(|S|₁, 2)`. -/
def pairsCount : List Bool → Nat
  | [] => 0
  | false :: S => pairsCount S
  | true :: S => cardB S + pairsCount S

/-- ★ Edges inside `S` number `C(cardB S, 2)` — each `true` pairs with all
    earlier `true`s, the Pascal step. -/
theorem pairsCount_eq : ∀ S, pairsCount S = binom (cardB S) 2
  | [] => rfl
  | false :: S => pairsCount_eq S
  | true :: S => by
      show cardB S + pairsCount S = binom (cardB S + 1) 2
      rw [pairsCount_eq S, E213.Lib.Math.Combinatorics.Binomial.binom_succ_2]

/-- The constraint row for vertex `0` against `S`: `some col` on each edge to a
    `true` of `S` (if vertex `0` is in the set, `b = true`), `none` otherwise. -/
def edgeRow (b col : Bool) (S : List Bool) : List (Option Bool) :=
  S.map (fun bj => bif (b && bj) then some col else none)

/-- The full edge pattern for `S`: row by row. -/
def edgePattern (col : Bool) : List Bool → List (Option Bool)
  | [] => []
  | b :: S => edgeRow b col S ++ edgePattern col S

theorem countNone_append : ∀ (a b : List (Option Bool)),
    countNone (a ++ b) = countNone a + countNone b
  | [], b => (Nat.zero_add (countNone b)).symm
  | none :: a, b => by
      show countNone (a ++ b) + 1 = (countNone a + 1) + countNone b
      rw [countNone_append a b, Nat.add_right_comm]
  | some _ :: a, b => countNone_append a b

theorem countNone_edgeRow_false (col : Bool) : ∀ S, countNone (edgeRow false col S) = S.length
  | [] => rfl
  | _ :: S => by
      show countNone (none :: edgeRow false col S) = S.length + 1
      show countNone (edgeRow false col S) + 1 = S.length + 1
      rw [countNone_edgeRow_false col S]

theorem countNone_edgeRow_true (col : Bool) : ∀ S,
    countNone (edgeRow true col S) + cardB S = S.length
  | [] => rfl
  | true :: S => by
      show countNone (some col :: edgeRow true col S) + (cardB S + 1) = S.length + 1
      show countNone (edgeRow true col S) + (cardB S + 1) = S.length + 1
      rw [← Nat.add_assoc, countNone_edgeRow_true col S]
  | false :: S => by
      show countNone (none :: edgeRow true col S) + cardB S = S.length + 1
      show (countNone (edgeRow true col S) + 1) + cardB S = S.length + 1
      rw [Nat.add_right_comm, countNone_edgeRow_true col S]

theorem edgePattern_length (col : Bool) : ∀ S, (edgePattern col S).length = binom S.length 2
  | [] => rfl
  | b :: S => by
      show (edgeRow b col S ++ edgePattern col S).length = binom (S.length + 1) 2
      rw [E213.Tactic.List213.length_append, edgePattern_length col S,
          show (edgeRow b col S).length = S.length from length_map S _,
          E213.Lib.Math.Combinatorics.Binomial.binom_succ_2]

/-- ★ `#none = #edges − #internal = C(|S|,2) − C(cardB S, 2)`, additively. -/
theorem countNone_edgePattern (col : Bool) : ∀ S,
    countNone (edgePattern col S) + pairsCount S = binom S.length 2
  | [] => rfl
  | b :: S => by
      show countNone (edgeRow b col S ++ edgePattern col S) + pairsCount (b :: S)
            = binom (S.length + 1) 2
      rw [countNone_append, E213.Lib.Math.Combinatorics.Binomial.binom_succ_2]
      cases b with
      | false =>
          show (countNone (edgeRow false col S) + countNone (edgePattern col S)) + pairsCount S
                = S.length + binom S.length 2
          rw [countNone_edgeRow_false col S, Nat.add_assoc, countNone_edgePattern col S]
      | true =>
          show (countNone (edgeRow true col S) + countNone (edgePattern col S))
                + (cardB S + pairsCount S) = S.length + binom S.length 2
          rw [Nat.add_add_add_comm, countNone_edgeRow_true col S, countNone_edgePattern col S]

/-! ## §2 — the per-event count -/

/-- The "`S` is monochromatic" event: the internal edges are all one colour
    (all `false` or all `true`). -/
def monoEvent (S l : List Bool) : Bool :=
  matchesC (edgePattern false S) l || matchesC (edgePattern true S) l

/-- ★ Each monochromatic event holds on at most `2·2^{C(|S|,2)−C(|S|₁,2)}` of the
    edge-colourings — the `C(cardB S, 2)` internal edges fixed to one shared
    colour, `2` ways. -/
theorem monoEvent_count (S : List Bool) :
    bcount (monoEvent S) (allBoolLists (binom S.length 2))
      ≤ 2 * 2 ^ (binom S.length 2 - binom (cardB S) 2) := by
  have hcn : ∀ col, countNone (edgePattern col S)
              = binom S.length 2 - binom (cardB S) 2 := by
    intro col
    have h := countNone_edgePattern col S
    have e : countNone (edgePattern col S) = binom S.length 2 - pairsCount S := by
      rw [← h, add_sub_cancel_right]
    rw [e, pairsCount_eq S]
  have hcount : ∀ col, bcount (matchesC (edgePattern col S)) (allBoolLists (binom S.length 2))
                  = 2 ^ (binom S.length 2 - binom (cardB S) 2) := by
    intro col
    have key := matchesC_count (edgePattern col S)
    rw [edgePattern_length col S] at key
    rw [hcn col] at key
    exact key
  have hor := bcount_or_le (matchesC (edgePattern false S)) (matchesC (edgePattern true S))
                (allBoolLists (binom S.length 2))
  rw [hcount false, hcount true] at hor
  show bcount (fun l => matchesC (edgePattern false S) l || matchesC (edgePattern true S) l)
        (allBoolLists (binom S.length 2)) ≤ 2 * 2 ^ (binom S.length 2 - binom (cardB S) 2)
  rw [Nat.two_mul]
  exact hor

/-- Binomial monotone in the upper index: `k ≤ N → C(k,m) ≤ C(N,m)`. -/
theorem binom_mono_fst (m k : Nat) : ∀ {N : Nat}, k ≤ N → binom k m ≤ binom N m := by
  intro N h
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (E213.Lib.Math.Combinatorics.Binomial.binom_le_binom_succ _ _)

/-! ## §3 — the named bound -/

/-- Propext-free `m < n → m·k < n·k` for `k > 0`. -/
private theorem mul_lt_mul_right_clean {m n k : Nat} (hk : 0 < k) (h : m < n) :
    m * k < n * k := by
  have h1 : (m + 1) * k ≤ n * k := Nat.mul_le_mul_right k h
  have h2 : m * k < (m + 1) * k := by
    rw [E213.Lib.Math.Combinatorics.Binomial.add_mul_pure, Nat.one_mul]
    exact Nat.lt_add_of_pos_right hk
  exact Nat.lt_of_lt_of_le h2 h1

/-- Propext-free `a^(m+n) = a^m · a^n`. -/
private theorem pow_add_clean (a m : Nat) : ∀ n, a ^ (m + n) = a ^ m * a ^ n
  | 0 => by rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | n + 1 => by
      rw [Nat.add_succ, Nat.pow_succ, pow_add_clean a m n, nmul_assoc, ← Nat.pow_succ]

/-- ★★ **Erdős' Ramsey lower bound `R(k,k) > N`.**  If `2·C(N,k) < 2^{C(k,2)}`,
    there is a 2-colouring of the `C(N,2)` edges of `K_N` with **no monochromatic
    `k`-clique** — every `k`-subset `S` has both colours among its internal
    edges (`monoEvent S l = false`).  Instantiating `N < 2^{k/2}` gives
    `R(k,k) > 2^{k/2}`.  The last proof-ISA COUNT rung, ∅-axiom. -/
theorem ramsey_lower (N k : Nat) (hkN : k ≤ N) (h : 2 * binom N k < 2 ^ binom k 2) :
    ∃ l, l ∈ allBoolLists (binom N 2) ∧ ∀ S, S ∈ kLayer N k → monoEvent S l = false := by
  have hPE : binom k 2 ≤ binom N 2 := binom_mono_fst 2 k hkN
  have hppos : 0 < 2 ^ (binom N 2 - binom k 2) := Nat.pos_pow_of_pos _ (by decide)
  -- per-event uniform bound
  have hc : ∀ p, p ∈ (kLayer N k).map monoEvent →
      bcount p (allBoolLists (binom N 2)) ≤ 2 * 2 ^ (binom N 2 - binom k 2) := by
    intro p hp
    obtain ⟨S, hS, rfl⟩ := exists_of_mem_map hp
    have hmf := mem_filter hS
    have hSlen : S.length = N := length_of_mem_allBoolLists hmf.1
    have hScard : cardB S = k := Nat.eq_of_beq_eq_true hmf.2
    have hb := monoEvent_count S
    rw [hSlen, hScard] at hb
    exact hb
  -- the deficit inequality
  have hlt : ((kLayer N k).map monoEvent).length * (2 * 2 ^ (binom N 2 - binom k 2))
              < 2 ^ binom N 2 := by
    rw [length_map, kLayer_card]
    calc binom N k * (2 * 2 ^ (binom N 2 - binom k 2))
          = (2 * binom N k) * 2 ^ (binom N 2 - binom k 2) := by
            rw [nmul_left_comm (binom N k) 2 (2 ^ (binom N 2 - binom k 2)), nmul_assoc]
      _ < 2 ^ binom k 2 * 2 ^ (binom N 2 - binom k 2) :=
            mul_lt_mul_right_clean hppos h
      _ = 2 ^ binom N 2 := by
            rw [← pow_add_clean, add_sub_of_le hPE]
  obtain ⟨l, hlmem, hall⟩ :=
    erdos_schema ((kLayer N k).map monoEvent) (binom N 2)
      (2 * 2 ^ (binom N 2 - binom k 2)) hc hlt
  exact ⟨l, hlmem, fun S hS => hall (monoEvent S) (mem_map_of_mem monoEvent hS)⟩

end E213.Lib.Math.Combinatorics.RamseyNamedBound
