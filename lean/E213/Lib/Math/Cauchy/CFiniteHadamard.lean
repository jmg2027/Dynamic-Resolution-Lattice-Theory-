import E213.Lib.Math.Cauchy.CFiniteRing
import E213.Lib.Math.Linalg213.CharPolyAdj

/-!
# CFiniteHadamard — the C-finite Hadamard (pointwise) product `cfiniteZ_mul`

The last open ring operation: `CFiniteZ s → CFiniteZ t → CFiniteZ (s·t)`.  The `pq` products
`w(n)_{(a,b)} = s(n+a)·t(n+b)` are closed under the shift (a Kronecker companion `M`), so
`w(n+1) = M·w(n)`; integer Cayley–Hamilton (`Linalg213.CharPolyAdj.ch_recurrence`) then gives the
monic order-`pq` recurrence for the first component `u = s·t`, and `cfiniteZ_of_shiftRec` closes it.

This file builds: the **grid-sum decomposition** (`sumZ` over `iota (p*q)` = double sum over the
`p×q` grid), the Kronecker companion, and the assembly.  All ∅-axiom.
-/

namespace E213.Lib.Math.Cauchy.CFiniteHadamard

open E213.Lib.Math.Linalg213.Permutation (sumZ iota)
open E213.Lib.Math.Linalg213.Laplace (sumZ_append map_append')
open E213.Lib.Math.Linalg213.PermClosure (map_map')
open E213.Lib.Math.Linalg213.CayleyHamilton (sumZ_singleton)

/-! ## §1 — clean list helpers + the grid-sum decomposition -/

/-- `L ++ [] = L` (propext-free; core's `List.append_nil` is `propext`-tainted). -/
theorem append_nil' {α : Type} : ∀ (L : List α), L ++ [] = L
  | []     => rfl
  | a :: l => by show a :: (l ++ []) = a :: l; rw [append_nil' l]

/-- Associativity of `++` (propext-free; core's `List.append_assoc` is `propext`-tainted). -/
theorem append_assoc' {α : Type} : ∀ (L M N : List α), (L ++ M) ++ N = L ++ (M ++ N)
  | [],     _, _ => rfl
  | a :: l, M, N => by
    show a :: ((l ++ M) ++ N) = a :: (l ++ (M ++ N))
    rw [append_assoc' l M N]

/-- `iota (m + q) = iota m ++ [m, m+1, …, m+q−1]`. -/
theorem iota_add (m : Nat) : ∀ (q : Nat),
    iota (m + q) = iota m ++ (iota q).map (fun b => m + b)
  | 0     => by
    show iota m = iota m ++ ([] : List Nat)
    rw [append_nil']
  | q + 1 => by
    show iota (m + q) ++ [m + q] = iota m ++ ((iota q ++ [q]).map (fun b => m + b))
    rw [iota_add m q, map_append', append_assoc']
    rfl

/-- ★ **Grid-sum decomposition**: a sum over `iota (p*q)` is the double sum over the `p×q`
    grid under the index `(a,b) ↦ a*q + b`. -/
theorem sumZ_grid (q : Nat) (g : Nat → Int) : ∀ (p : Nat),
    sumZ ((iota (p * q)).map g)
      = sumZ ((iota p).map (fun a => sumZ ((iota q).map (fun b => g (a * q + b)))))
  | 0     => by rw [Nat.zero_mul]; rfl
  | p + 1 => by
    rw [Nat.succ_mul, iota_add (p * q) q, map_append', sumZ_append, sumZ_grid q g p,
        show iota (p + 1) = iota p ++ [p] from rfl, map_append', sumZ_append,
        map_map' (fun b => p * q + b) g,
        show (([p] : List Nat).map (fun a => sumZ ((iota q).map (fun b => g (a * q + b)))))
           = [sumZ ((iota q).map (fun b => g (p * q + b)))] from rfl,
        sumZ_singleton]

end E213.Lib.Math.Cauchy.CFiniteHadamard
