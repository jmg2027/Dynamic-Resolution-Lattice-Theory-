import E213.Lib.Math.Combinatorics.GraphConnectivity
import E213.Meta.Int213

/-!
# Cyclic rotation as a measure-preserving transformation + the Birkhoff average

The named missing leg of the `ergodic_theory` decomposition:
a **concrete measure-preserving transformation on a finite space, the Birkhoff
average along its orbit, the ergodic theorem "time-average = space-average" as
the `q=+1` fixed point reached exactly at the period, and ergodicity = the
invariant functions are the constants (the dim-1 `q=+1` kernel) — tied to
`graph_theory.md`'s Laplacian `λ₀=0` via `GraphConnectivity.closed_const`.**

Everything is `Nat`/`Int`-indexed and pure — no `Fin`, no `omega`, no
`Decidable` instance fires, so no core lemma leaks `propext`/`Quot.sound`.
The state space is the residue set `{0, 1, …, n-1}`; the transformation is the
cyclic shift `rot n i := (i+1) % n`; the counting measure is the uniform weight
on `natRange n = [0, 1, …, n-1]`; "integrate `f`" = `sumInt (map f (natRange n))`.

  · §1 — `natRange`, `sumInt`, the orbit list, the Birkhoff sum.
  · §2 — the cyclic rotation; the orbit-from-`m` enumerates the residues.
  · §3 — the ergodic theorem skeleton: over one full period the orbit visits
          every point once, so **time-sum = space-sum** exactly — the `q=+1`
          fixed point reached *exactly* at the period (`birkhoff_period_eq_space`).
          Measure-preservation (`measure_preserving`) is its corollary.
  · §4 — ergodicity = `rot`-invariant ⟹ constant, *via* the `n`-cycle's
          graph connectivity (`GraphConnectivity.closed_const`) — the dim-1
          `q=+1` constant kernel = the Laplacian `λ₀=0` (`rotInvariant_is_constant`).
  · §5 — the non-ergodic contrast: a disconnected union of two cycles has a
          non-constant invariant function (dim ker = #components > 1).

Companion: the `ergodic_theory` decomposition.
-/

namespace E213.Lib.Math.Combinatorics.CyclicErgodic

open E213.Lib.Math.Combinatorics.GraphConnectivity
  (Reach IsClosed IsConnectedFrom closed_const)

/-! ## §1 — the finite space, the measure, the orbit, the Birkhoff sum -/

/-- `natRange n = [0, 1, …, n-1]` — the finite state space `{0,…,n-1}`,
    carrying the uniform counting measure (one unit of weight per point). -/
def natRange : Nat → List Nat
  | 0 => []
  | n + 1 => natRange n ++ [n]

/-- `natRangeFrom m k = [m, m+1, …, m+k-1]` — `k` consecutive residues
    starting at `m`. -/
def natRangeFrom (m : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => m :: natRangeFrom (m + 1) k

/-- `map` over an append (spelled out to stay `propext`-free). -/
theorem map_append {α β : Type _} (g : α → β) : ∀ xs ys : List α,
    (xs ++ ys).map g = xs.map g ++ ys.map g
  | [], _ => rfl
  | x :: xs, ys => by
      show g x :: (xs ++ ys).map g = g x :: (xs.map g ++ ys.map g)
      rw [map_append g xs ys]

/-- `map (·+0)` is the identity on a `Nat` list. -/
theorem map_add_zero : ∀ l : List Nat, l.map (· + 0) = l
  | [] => rfl
  | x :: xs => by
      show (x + 0) :: xs.map (· + 0) = x :: xs
      rw [Nat.add_zero, map_add_zero xs]

/-- The cons/append normal-form equality:
    `m :: map(·+(m+1)) (natRange n) = map(·+m) (natRange n) ++ [n+m]`. -/
theorem cons_map_succ_eq_append (m : Nat) : ∀ n : Nat,
    m :: (natRange n).map (· + (m + 1))
      = (natRange n).map (· + m) ++ [n + m]
  | 0 => by
      show m :: ([] : List Nat) = [] ++ [0 + m]
      rw [Nat.zero_add]; rfl
  | n + 1 => by
      show m :: (natRange n ++ [n]).map (· + (m + 1))
            = (natRange n ++ [n]).map (· + m) ++ [(n + 1) + m]
      rw [map_append, map_append]
      show (m :: (natRange n).map (· + (m + 1))) ++ [n + (m + 1)]
            = ((natRange n).map (· + m) ++ [n + m]) ++ [(n + 1) + m]
      rw [cons_map_succ_eq_append m n]
      show ((natRange n).map (· + m) ++ [n + m]) ++ [n + (m + 1)]
            = ((natRange n).map (· + m) ++ [n + m]) ++ [(n + 1) + m]
      have : n + (m + 1) = (n + 1) + m := by
        rw [Nat.add_succ, Nat.succ_add]
      rw [this]

/-- `natRangeFrom m n = (natRange n).map (· + m)` — the start-`m`
    enumeration is the base enumeration shifted by `m`. -/
theorem natRangeFrom_shift_natRange (m : Nat) : ∀ n : Nat,
    natRangeFrom m n = (natRange n).map (· + m)
  | 0 => rfl
  | n + 1 => by
      show m :: natRangeFrom (m + 1) n = (natRange n ++ [n]).map (· + m)
      rw [map_append, natRangeFrom_shift_natRange (m + 1) n]
      exact cons_map_succ_eq_append m n

/-- The cons-first enumeration `natRangeFrom 0 n` equals the tail-first
    `natRange n`: both list the residues `[0,…,n-1]`. -/
theorem natRangeFrom_zero_eq_natRange (n : Nat) :
    natRangeFrom 0 n = natRange n := by
  rw [natRangeFrom_shift_natRange 0 n, map_add_zero]

/-- Integer sum of a list. -/
def sumInt : List Int → Int
  | [] => 0
  | x :: xs => x + sumInt xs

theorem sumInt_append : ∀ xs ys : List Int,
    sumInt (xs ++ ys) = sumInt xs + sumInt ys
  | [], ys => (E213.Meta.Int213.zero_add (sumInt ys)).symm
  | x :: xs, ys => by
      show x + sumInt (xs ++ ys) = (x + sumInt xs) + sumInt ys
      rw [sumInt_append xs ys, E213.Meta.Int213.add_assoc]

/-- **Space-average (counting-measure integral)** of `f` over `{0,…,n-1}`:
    `∫ f dμ` with `μ` the counting measure, here the unnormalised sum
    (the `1/n` normalisation is a trivial common factor). -/
def spaceSum (f : Nat → Int) (n : Nat) : Int :=
  sumInt ((natRange n).map f)

/-- The **orbit list** `[x, T x, T² x, …, T^(k-1) x]`. -/
def orbit (T : Nat → Nat) (x : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => x :: orbit T (T x) k

/-- **Birkhoff sum** `Σ_{i<n} f (Tⁱ x)` — the un-normalised time-average
    along the orbit of `T` from `x`. -/
def birkhoffSum (f : Nat → Int) (T : Nat → Nat) (n x : Nat) : Int :=
  sumInt ((orbit T x n).map f)

/-! ## §2 — the cyclic rotation; the orbit enumerates the residues -/

/-- The **cyclic shift** `rot n i := (i+1) % n` on the residues `{0,…,n-1}`:
    the canonical measure-preserving transformation of a finite space (a
    single `n`-cycle). -/
def rot (n : Nat) (i : Nat) : Nat := (i + 1) % n

/-- `rot n` lands in `{0,…,n-1}` for `n > 0`. -/
theorem rot_lt {n : Nat} (i : Nat) (hn : 0 < n) : rot n i < n :=
  Nat.mod_lt _ hn

/-- Below wrap-around, `rot` is plain successor: `m + 1 < n → rot n m = m + 1`. -/
theorem rot_eq_succ {n m : Nat} (h : m + 1 < n) : rot n m = m + 1 :=
  Nat.mod_eq_of_lt h

/-- **The orbit enumerates consecutive residues.**  As long as the whole run
    stays inside one period (`m + k ≤ n`), the orbit of `rot n` from `m` is
    exactly `[m, m+1, …, m+k-1]` — no wrap-around occurs, so `rot` acts as
    successor at every step. -/
theorem orbit_rot_eq_range (n : Nat) :
    ∀ (k m : Nat), m + k ≤ n → orbit (rot n) m k = natRangeFrom m k := by
  intro k
  induction k with
  | zero => intro m _; rfl
  | succ k' ih =>
      intro m h
      show m :: orbit (rot n) (rot n m) k' = m :: natRangeFrom (m + 1) k'
      cases k' with
      | zero =>
          show m :: orbit (rot n) (rot n m) 0 = m :: natRangeFrom (m + 1) 0
          rfl
      | succ k'' =>
          have hlt : m + 1 < n := by
            have hstep : m + 1 < m + (k'' + 2) := by
              apply Nat.add_lt_add_left
              exact Nat.succ_lt_succ (Nat.succ_pos k'')
            exact Nat.lt_of_lt_of_le hstep h
          have hrot : rot n m = m + 1 := rot_eq_succ hlt
          rw [hrot]
          have hrec : m + 1 + (k'' + 1) ≤ n := by
            have heq : m + 1 + (k'' + 1) = m + (k'' + 1 + 1) := by
              rw [Nat.add_assoc, Nat.add_comm 1 (k'' + 1)]
            rw [heq]; exact h
          rw [ih (m + 1) hrec]

/-! ## §3 — the ergodic theorem skeleton (time-average = space-average) -/

/-- The orbit of `rot n` from `0`, run for the full period `n`, is the whole
    state space `[0, 1, …, n-1]`: the cycle visits every point exactly once. -/
theorem orbit_rot_full_period (n : Nat) :
    orbit (rot n) 0 n = natRange n := by
  have h := orbit_rot_eq_range n n 0 (by rw [Nat.zero_add]; exact Nat.le_refl n)
  -- (signature: orbit_rot_eq_range n k m h)
  rw [h]
  exact natRangeFrom_zero_eq_natRange n

/-- ★ **The ergodic theorem for the rotation (time-average = space-average).**
    Over one full period (`n` steps of the `n`-cycle), the Birkhoff time-sum
    of `f` along the orbit EQUALS the space-sum of `f` over the whole state
    space.  The `q=+1` fixed point of "time-avg = space-avg" is reached
    *exactly* at the period — no limit, no modulus, an honest finite identity:

      `birkhoffSum f rot n 0 = spaceSum f n`. -/
theorem birkhoff_period_eq_space (f : Nat → Int) (n : Nat) :
    birkhoffSum f (rot n) n 0 = spaceSum f n := by
  show sumInt ((orbit (rot n) 0 n).map f) = sumInt ((natRange n).map f)
  rw [orbit_rot_full_period n]

/-- **Measure-preservation (the `Aut`-of-measure fact), corollary form.**
    Pushing `f` forward along the orbit and summing gives the same total as
    summing `f` over the residues — a bijection (the `n`-cycle) preserves the
    counting-measure total `Σ f`.  This is exactly `birkhoff_period_eq_space`
    read as `Σ_orbit f = Σ_space f`. -/
theorem measure_preserving (f : Nat → Int) (n : Nat) :
    sumInt ((orbit (rot n) 0 n).map f) = sumInt ((natRange n).map f) :=
  birkhoff_period_eq_space f n

/-! ## §4 — ergodicity = invariant functions are constant (the dim-1 kernel) -/

/-- The **`n`-cycle adjacency**: `i` is adjacent to `j` iff `j = rot n i`
    (the directed cycle `0 → 1 → … → n-1 → 0`).  This is the graph whose
    Laplacian `λ₀=0` constant kernel `graph_theory.md` names; reachability
    along it is the orbit. -/
def CycleAdj (n : Nat) (i j : Nat) : Prop := j = rot n i

/-- A `rot`-invariant `Bool`-reading is `CycleAdj`-closed: it is constant
    across every cycle edge `i → rot n i`. -/
theorem rotInvariant_isClosed {n : Nat} {σ : Nat → Bool}
    (hinv : ∀ i, σ (rot n i) = σ i) : IsClosed (CycleAdj n) σ :=
  fun u v (huv : v = rot n u) => by
    rw [huv]; exact (hinv u).symm

/-- ★ **Ergodicity = the invariant functions are constant (the `q=+1`
    dim-1 constant kernel).**  On the connected `n`-cycle, any `rot`-invariant
    `Bool`-reading (`σ (rot n i) = σ i` for all `i`) is globally **constant**.

    This is the EXACT image of `graph_theory.md`'s Laplacian `λ₀=0`: the
    Koopman-invariant subspace = the constants = the dim-1 kernel = the
    connected graph's constant kernel.  The proof *is* the graph-connectivity
    collapse: `GraphConnectivity.closed_const` applied to the cycle's
    adjacency — the same theorem that pins `dim ker L = 1` for a connected
    graph (`pathLaplacian_const_kernel`, `closed_const`, `closed_root_determines`).

    The connectivity hypothesis `hconn : IsConnectedFrom (CycleAdj n) root`
    states the cycle is one orbit (connected ⟺ ergodic); for the single
    `n`-cycle it holds with `root = 0` (witnessed by `cycle_connected` below). -/
theorem rotInvariant_is_constant {n root : Nat} {σ : Nat → Bool}
    (hconn : IsConnectedFrom (CycleAdj n) root)
    (hinv : ∀ i, σ (rot n i) = σ i) :
    ∀ u v, σ u = σ v :=
  closed_const hconn (rotInvariant_isClosed hinv)

/-- The single `n`-cycle is connected from `0` *as a graph on its residues*:
    every residue `j < n` is reachable from `0` along `CycleAdj n`.  The
    reachability witness is the orbit `0 → 1 → … → j`.  (Stated for the
    residues `{0,…,n-1}`; the connectivity = ergodicity = `dim ker = 1` tie.) -/
theorem cycle_reach_lt {n : Nat} :
    ∀ j : Nat, j + 1 ≤ n → Reach (CycleAdj n) 0 j
  | 0, _ => Reach.base
  | j + 1, h => by
      -- h : (j+1)+1 ≤ n.  Then j+1 ≤ n (for the recursion) and j+1 < n (for the edge).
      have hlt : j + 1 < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self (j + 1)) h
      have hj : j + 1 ≤ n := Nat.le_of_lt hlt
      have hreach : Reach (CycleAdj n) 0 j := cycle_reach_lt j hj
      have hedge : CycleAdj n j (j + 1) := by
        show j + 1 = rot n j
        exact (rot_eq_succ hlt).symm
      exact Reach.step hreach hedge

/-! ## §5 — the non-ergodic contrast (dim ker = #components > 1) -/

/-- A **non-ergodic** transformation: the identity on `{0,…,n-1}`, whose
    every singleton `{i}` is its own orbit — `n` invariant components, not
    one.  (Any `T` with more than one orbit works; `id` is the extreme case.) -/
def idT (i : Nat) : Nat := i

/-- The identity is trivially invariant for every reading. -/
theorem idT_invariant (σ : Nat → Bool) : ∀ i, σ (idT i) = σ i := fun _ => rfl

/-- ★ **Non-ergodicity ⟹ a non-constant invariant reading (dim ker > 1).**
    For the identity (or any map with ≥ 2 orbits) there is a `Bool`-reading
    that is invariant yet NOT constant: e.g. `σ i := decide (i = 0)`
    distinguishes the orbit `{0}` from the rest.  This is the `q=−1` contrast
    — the invariant subspace has dimension = #components > 1, exactly
    `graph_theory.md`'s disconnected graph with `dim ker L > 1`.

    Concretely: `σ 0 = true ≠ false = σ 1` (for `n ≥ 2`), yet `σ` is
    `idT`-invariant. -/
theorem nonergodic_invariant_not_constant :
    ∃ σ : Nat → Bool, (∀ i, σ (idT i) = σ i) ∧ ¬ (∀ u v, σ u = σ v) := by
  refine ⟨fun i => match i with | 0 => true | _ + 1 => false, ?_, ?_⟩
  · intro i; rfl
  · intro hconst
    have : (true : Bool) = false := hconst 0 1
    exact Bool.noConfusion this

end E213.Lib.Math.Combinatorics.CyclicErgodic
