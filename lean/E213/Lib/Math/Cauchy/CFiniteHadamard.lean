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

/-! ## §2 — a clean (∅-axiom) flat↔grid index bijection

Core `Nat./`/`Nat.%` are well-founded-recursive (propext/`Quot.sound`-tainted), so the decode
`J ↦ (J/q, J%q)` is rebuilt as a **fuel-structural** `divmod` using only clean `Nat.sub`. -/

/-- Quotient of `J` by `q` (fuel-structural; `qof J q J = J / q`). -/
def qof : Nat → Nat → Nat → Nat
  | 0,        _, _ => 0
  | fuel + 1, q, J => if J < q then 0 else qof fuel q (J - q) + 1

/-- Remainder of `J` by `q` (fuel-structural; `rof J q J = J % q`). -/
def rof : Nat → Nat → Nat → Nat
  | 0,        _, J => J
  | fuel + 1, q, J => if J < q then J else rof fuel q (J - q)

/-- ★ **Division algorithm** (with enough fuel): `qof·q + rof = J` and `rof < q`. -/
theorem divmod_spec (q : Nat) (hq : 0 < q) : ∀ (fuel J : Nat), J < q * (fuel + 1) →
    qof fuel q J * q + rof fuel q J = J ∧ rof fuel q J < q
  | 0,        J, hf => by
    rw [Nat.mul_one] at hf
    refine ⟨?_, hf⟩
    show 0 * q + J = J
    rw [Nat.zero_mul, Nat.zero_add]
  | fuel + 1, J, hf => by
    by_cases h : J < q
    · refine ⟨?_, ?_⟩
      · show (if J < q then 0 else qof fuel q (J - q) + 1) * q
           + (if J < q then J else rof fuel q (J - q)) = J
        rw [if_pos h, if_pos h, Nat.zero_mul, Nat.zero_add]
      · show (if J < q then J else rof fuel q (J - q)) < q
        rw [if_pos h]; exact h
    · have hqJ : q ≤ J := Nat.le_of_not_lt h
      have hf' : J - q < q * (fuel + 1) := by
        have hadd : (J - q) + q < q * (fuel + 1) + q := by
          rw [E213.Tactic.NatHelper.sub_add_cancel hqJ,
              show q * (fuel + 1) + q = q * (fuel + 1 + 1) from (Nat.mul_succ q (fuel + 1)).symm]
          exact hf
        exact Nat.lt_of_add_lt_add_right hadd
      obtain ⟨ih1, ih2⟩ := divmod_spec q hq fuel (J - q) hf'
      refine ⟨?_, ?_⟩
      · show (if J < q then 0 else qof fuel q (J - q) + 1) * q
           + (if J < q then J else rof fuel q (J - q)) = J
        rw [if_neg h, if_neg h, Nat.succ_mul,
            Nat.add_right_comm (qof fuel q (J - q) * q) q (rof fuel q (J - q)), ih1,
            E213.Tactic.NatHelper.sub_add_cancel hqJ]
      · show (if J < q then J else rof fuel q (J - q)) < q
        rw [if_neg h]; exact ih2

/-- `J < q·(J+1)` for `q ≥ 1` — enough fuel to decode any `J`. -/
theorem lt_mul_succ_self {q : Nat} (hq : 0 < q) (J : Nat) : J < q * (J + 1) := by
  rw [Nat.mul_succ]
  exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left J hq) (Nat.lt_add_of_pos_right hq)

/-- Decoded row index `a = J / q`. -/
def decA (q J : Nat) : Nat := qof J q J
/-- Decoded column index `b = J % q`. -/
def decB (q J : Nat) : Nat := rof J q J

/-- ★ **Decode reconstructs**: `decA·q + decB = J` and `decB < q`. -/
theorem dec_spec {q : Nat} (hq : 0 < q) (J : Nat) :
    decA q J * q + decB q J = J ∧ decB q J < q :=
  divmod_spec q hq J J (lt_mul_succ_self hq J)

end E213.Lib.Math.Cauchy.CFiniteHadamard
