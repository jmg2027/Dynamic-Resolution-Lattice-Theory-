import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Lib.Math.NumberTheory.FactorialLcmIdentity
import E213.Meta.Nat.NatRing213
import E213.Meta.Nat.PolyNatMTactic

/-!
# The Handshake Lemma  (∅-axiom, division-free double counting)

A finite simple graph on `n` vertices is an adjacency `adj : Nat → Nat → Bool`
that is **symmetric** (`adj u v = adj v u`) and **irreflexive** (`adj v v = false`),
read on vertices `< n`.

* `deg v       = Σ_{u<n} (adj v u).toNat`     (neighbour count of `v`)
* `degSum      = Σ_{v<n} deg v`               (the degree sum)
* `orderedPairSum = Σ_{v<n} Σ_{u<n} (adj v u).toNat`  (each edge counted twice, ordered)
* `edgeCount   = Σ_{v<n} Σ_{u<v} (adj v u).toNat`     (each edge counted once: unordered)

The shallow identity `degSum = orderedPairSum` is `rfl`-grade.  The content is the
**triangular split**:

> for a *symmetric* weight `g v u = g u v` with *zero diagonal* `g v v = 0`,
> `Σ_{v<N} Σ_{u<N} g v u = 2 · Σ_{v<N} Σ_{u<v} g v u`.

This upgrades `TauParity.doubleSum_parity` (a mod-2 statement) to the **exact `= 2·`
form**, from which `degree_sum_even` and `degree_sum_eq_two_mul_edges` follow.

The split is proved by induction on `N` via `doubleSum_succ` (peel the top vertex):
its row and column each contribute `Σ_{u<N} g N u` and are equal by symmetry, while
the diagonal `g N N = 0` vanishes — yielding exactly `+ 2·(Σ_{u<N} g N u)` per step.
-/

namespace E213.Lib.Math.Combinatorics.Handshake

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_congr sumTo_add_func)
open E213.Lib.Math.NumberTheory.FactorialLcmIdentity (sumTo_const_zero)

/-! ## §1 — the abstract symmetric double-sum / triangular split -/

/-- Full `N×N` ordered double sum `Σ_{v<N} Σ_{u<N} g v u`. -/
def doubleSum (N : Nat) (g : Nat → Nat → Nat) : Nat :=
  sumTo N (fun v => sumTo N (fun u => g v u))

/-- Lower-triangle sum `Σ_{v<N} Σ_{u<v} g v u` (the unordered pairs `u<v`). -/
def triSum (N : Nat) (g : Nat → Nat → Nat) : Nat :=
  sumTo N (fun v => sumTo v (fun u => g v u))

/-- The diagonal `Σ_{v<N} g v v`. -/
def diagSum (N : Nat) (g : Nat → Nat → Nat) : Nat :=
  sumTo N (fun v => g v v)

/-- Peeling the top vertex `N`: row+column over the old block, plus the corner. -/
theorem doubleSum_succ (N : Nat) (g : Nat → Nat → Nat) :
    doubleSum (N + 1) g
      = doubleSum N g
        + sumTo N (fun v => g v N)
        + (sumTo N (fun u => g N u) + g N N) := by
  show sumTo (N + 1) (fun v => sumTo (N + 1) (fun u => g v u))
      = sumTo N (fun v => sumTo N (fun u => g v u))
        + sumTo N (fun v => g v N)
        + (sumTo N (fun u => g N u) + g N N)
  rw [sumTo_succ N (fun v => sumTo (N + 1) (fun u => g v u))]
  rw [show sumTo (N + 1) (fun u => g N u) = sumTo N (fun u => g N u) + g N N from
        sumTo_succ N (fun u => g N u)]
  rw [sumTo_congr N (fun v => sumTo (N + 1) (fun u => g v u))
        (fun v => sumTo N (fun u => g v u) + g v N)
        (fun v _ => sumTo_succ N (fun u => g v u))]
  rw [← sumTo_add_func N (fun v => sumTo N (fun u => g v u)) (fun v => g v N)]

/-- `triSum (N+1) g = triSum N g + Σ_{u<N} g N u` (the new top row contributes
    its strictly-lower part `Σ_{u<N}`). -/
theorem triSum_succ (N : Nat) (g : Nat → Nat → Nat) :
    triSum (N + 1) g = triSum N g + sumTo N (fun u => g N u) := by
  show sumTo (N + 1) (fun v => sumTo v (fun u => g v u))
      = sumTo N (fun v => sumTo v (fun u => g v u)) + sumTo N (fun u => g N u)
  rw [sumTo_succ N (fun v => sumTo v (fun u => g v u))]

/-- ★★★ **Exact triangular split**: for a *symmetric* weight `g v u = g u v` with
    *zero diagonal* `g v v = 0`, the full ordered double sum is **twice** the
    lower-triangle sum.  `Σ_{v<N}Σ_{u<N} g v u = 2 · Σ_{v<N}Σ_{u<v} g v u`. -/
theorem doubleSum_eq_two_mul_triSum
    (g : Nat → Nat → Nat)
    (hsymm : ∀ v u, g v u = g u v)
    (hdiag : ∀ v, g v v = 0) :
    ∀ N, doubleSum N g = 2 * triSum N g
  | 0 => rfl
  | N + 1 => by
    rw [doubleSum_succ N g, triSum_succ N g]
    -- the column over old rows equals the row over old columns, by symmetry
    have hcross : sumTo N (fun v => g v N) = sumTo N (fun u => g N u) :=
      sumTo_congr N _ _ (fun v _ => hsymm v N)
    rw [hcross, hdiag N, doubleSum_eq_two_mul_triSum g hsymm hdiag N]
    -- goal: 2*triSum N g + C + (C + 0) = 2*(triSum N g + C)   with C = Σ_{u<N} g N u
    generalize triSum N g = T
    generalize sumTo N (fun u => g N u) = C
    show 2 * T + C + (C + 0) = 2 * (T + C)
    rw [Nat.add_zero, Nat.mul_add, Nat.two_mul C, Nat.add_assoc (2 * T) C C]

/-! ## §2 — graph instance: adjacency, degree, edge count -/

/-- A finite simple graph: symmetric, irreflexive adjacency on vertices `< n`. -/
structure SimpleGraph where
  /-- adjacency relation as a Boolean predicate -/
  adj : Nat → Nat → Bool
  /-- symmetry: `u ~ v ↔ v ~ u` -/
  symm : ∀ u v, adj u v = adj v u
  /-- irreflexivity: no self-loops -/
  irrefl : ∀ v, adj v v = false

/-- The symmetric Nat-weight of a graph: `g v u = (adj v u).toNat`. -/
def weight (G : SimpleGraph) (v u : Nat) : Nat := (G.adj v u).toNat

/-- The weight is symmetric (graph symmetry). -/
theorem weight_symm (G : SimpleGraph) (v u : Nat) : weight G v u = weight G u v := by
  show (G.adj v u).toNat = (G.adj u v).toNat
  rw [G.symm v u]

/-- The weight has zero diagonal (irreflexivity): `(adj v v).toNat = false.toNat = 0`. -/
theorem weight_diag (G : SimpleGraph) (v : Nat) : weight G v v = 0 := by
  show (G.adj v v).toNat = 0
  rw [G.irrefl v]; rfl

/-- Degree of vertex `v` in an `n`-vertex graph: neighbour count `Σ_{u<n} (adj v u).toNat`. -/
def deg (G : SimpleGraph) (n v : Nat) : Nat := sumTo n (fun u => weight G v u)

/-- Degree sum `Σ_{v<n} deg v`. -/
def degSum (G : SimpleGraph) (n : Nat) : Nat := sumTo n (fun v => deg G n v)

/-- Edge count (unordered): `Σ_{v<n} Σ_{u<v} (adj v u).toNat`. -/
def edgeCount (G : SimpleGraph) (n : Nat) : Nat := triSum n (weight G)

/-! ## §3 — the handshake theorems -/

/-- Shallow identity: the degree sum equals the ordered-pair double sum (by `rfl`,
    unfolding `deg`/`degSum`/`doubleSum`). -/
theorem degSum_eq_doubleSum (G : SimpleGraph) (n : Nat) :
    degSum G n = doubleSum n (weight G) := rfl

/-- ★★ **`degree_sum_eq_two_mul_edges`** — the exact `= 2·|E|` handshake:
    `Σ_{v<n} deg v = 2 · (Σ_{v<n} Σ_{u<v} (adj v u).toNat)`. -/
theorem degree_sum_eq_two_mul_edges (G : SimpleGraph) (n : Nat) :
    degSum G n = 2 * edgeCount G n := by
  rw [degSum_eq_doubleSum]
  exact doubleSum_eq_two_mul_triSum (weight G) (weight_symm G) (weight_diag G) n

/-- ★★★ **`degree_sum_even`** — the handshake lemma's famous consequence:
    the degree sum is **even**, `2 ∣ Σ_{v<n} deg v`.  Explicit witness
    `⟨edgeCount, …⟩` (no `decide`-on-dvd propext leak). -/
theorem degree_sum_even (G : SimpleGraph) (n : Nat) : 2 ∣ degSum G n :=
  ⟨edgeCount G n, degree_sum_eq_two_mul_edges G n⟩

/-! ## §4 — graph builder + concrete smokes (axiom-clean) -/

/-- `decide (v = a) && decide (v = b) = false` when `a ≠ b` (a vertex can't carry two
    distinct labels) — the diagonal-killer for explicit edge tables, propext-free
    (cases on decidable equality, no `Decidable`-prop `by_cases`). -/
theorem distinct_label_diag {a b : Nat} (hab : a ≠ b) (v : Nat) :
    (decide (v = a) && decide (v = b)) = false := by
  cases Nat.decEq v a with
  | isFalse h => rw [decide_eq_false h]; rfl
  | isTrue h => subst h; rw [decide_eq_false (fun e => hab e), Bool.and_false]

/-- Symmetrize any `base` relation: `adj v u = base v u || base u v`.  Manifestly
    symmetric (`Bool.or_comm`); irreflexive whenever `base v v = false`. -/
def mkGraph (base : Nat → Nat → Bool) (hbase : ∀ v, base v v = false) : SimpleGraph where
  adj v u := base v u || base u v
  symm u v := by
    show (base u v || base v u) = (base v u || base u v)
    rw [Bool.or_comm]
  irrefl v := by
    show (base v v || base v v) = false
    rw [hbase v]; rfl

/-- Triangle `K₃` base: directed edges `0→1, 1→2, 0→2`; symmetrized → all pairs in
    `{0,1,2}` adjacent.  Degrees `2,2,2`, sum `6 = 2·3`. -/
def K3base (v u : Nat) : Bool :=
  (decide (v = 0) && decide (u = 1)) ||
  (decide (v = 1) && decide (u = 2)) ||
  (decide (v = 0) && decide (u = 2))

theorem K3base_diag (v : Nat) : K3base v v = false := by
  show ((decide (v = 0) && decide (v = 1)) || (decide (v = 1) && decide (v = 2))
        || (decide (v = 0) && decide (v = 2))) = false
  rw [distinct_label_diag (by decide) v, distinct_label_diag (by decide) v,
      distinct_label_diag (by decide) v]; rfl

def K3 : SimpleGraph := mkGraph K3base K3base_diag

theorem K3_handshake_smoke :
    deg K3 3 0 = 2 ∧ deg K3 3 1 = 2 ∧ deg K3 3 2 = 2
    ∧ degSum K3 3 = 6 ∧ edgeCount K3 3 = 3 := by decide

/-- Star `S₃` base: center `0` joined to leaves `1,2,3` (directed `0→k`); symmetrized.
    Degrees `3,1,1,1`, sum `6 = 2·3`. -/
def Star3base (v u : Nat) : Bool :=
  decide (v = 0) && (decide (u = 1) || decide (u = 2) || decide (u = 3))

theorem Star3base_diag (v : Nat) : Star3base v v = false := by
  show (decide (v = 0) && (decide (v = 1) || decide (v = 2) || decide (v = 3))) = false
  cases Nat.decEq v 0 with
  | isFalse h => rw [decide_eq_false h]; rfl
  | isTrue h =>
    subst h
    rw [decide_eq_false (by decide : (0:Nat) ≠ 1),
        decide_eq_false (by decide : (0:Nat) ≠ 2),
        decide_eq_false (by decide : (0:Nat) ≠ 3)]; rfl

def Star3 : SimpleGraph := mkGraph Star3base Star3base_diag

theorem Star3_handshake_smoke :
    deg Star3 4 0 = 3 ∧ deg Star3 4 1 = 1 ∧ deg Star3 4 2 = 1 ∧ deg Star3 4 3 = 1
    ∧ degSum Star3 4 = 6 ∧ edgeCount Star3 4 = 3 := by decide

/-- Path `P₃` base: edges `0-1, 1-2` (directed); symmetrized.  Degrees `1,2,1`,
    sum `4 = 2·2` edges. -/
def P3base (v u : Nat) : Bool :=
  (decide (v = 0) && decide (u = 1)) || (decide (v = 1) && decide (u = 2))

theorem P3base_diag (v : Nat) : P3base v v = false := by
  show ((decide (v = 0) && decide (v = 1)) || (decide (v = 1) && decide (v = 2))) = false
  rw [distinct_label_diag (by decide) v, distinct_label_diag (by decide) v]; rfl

def P3 : SimpleGraph := mkGraph P3base P3base_diag

theorem P3_handshake_smoke :
    deg P3 3 0 = 1 ∧ deg P3 3 1 = 2 ∧ deg P3 3 2 = 1
    ∧ degSum P3 3 = 4 ∧ edgeCount P3 3 = 2 := by decide

end E213.Lib.Math.Combinatorics.Handshake
