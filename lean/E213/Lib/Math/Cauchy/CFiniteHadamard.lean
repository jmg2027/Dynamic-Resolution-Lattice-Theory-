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
open E213.Lib.Math.Linalg213.PermClosure (map_map' map_eq_of_mem sumZ_map_smul lt_of_mem_iota)
open E213.Lib.Math.Linalg213.CayleyHamilton (sumZ_singleton sumZ_map_smul_right sumZ_iota_delta_lt)
open E213.Lib.Math.Cauchy.CFiniteRing (shiftSum ShiftRecZ)
open E213.Lib.Math.PolyZ (one_mul')

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

/-- **Uniqueness of division**: the quotient is determined by `x·q + r = a·q + s` with `r,s < q`. -/
theorem divmod_unique (q : Nat) : ∀ (x a r s : Nat),
    x * q + r = a * q + s → r < q → s < q → x = a
  | 0,     0,     _, _, _, _,  _  => rfl
  | 0,     a + 1, r, s, h, hr, _  => by
    rw [Nat.zero_mul, Nat.zero_add] at h
    have qler : q ≤ r := by
      rw [h]; exact Nat.le_trans (Nat.le_mul_of_pos_left q (Nat.succ_pos a)) (Nat.le_add_right _ s)
    exact absurd (Nat.lt_of_le_of_lt qler hr) (Nat.lt_irrefl q)
  | x + 1, 0,     r, s, h, _,  hs => by
    rw [Nat.zero_mul, Nat.zero_add] at h
    have qles : q ≤ s := by
      rw [← h]; exact Nat.le_trans (Nat.le_mul_of_pos_left q (Nat.succ_pos x)) (Nat.le_add_right _ r)
    exact absurd (Nat.lt_of_le_of_lt qles hs) (Nat.lt_irrefl q)
  | x + 1, a + 1, r, s, h, hr, hs => by
    rw [Nat.succ_mul, Nat.succ_mul, Nat.add_right_comm (x * q) q r,
        Nat.add_right_comm (a * q) q s] at h
    rw [divmod_unique q x a r s (E213.Tactic.NatHelper.add_right_cancel h) hr hs]

/-- ★ **Encode roundtrip (row)**: `decA q (a·q + b) = a` for `b < q`. -/
theorem decA_encode {q : Nat} (hq : 0 < q) (a b : Nat) (hb : b < q) :
    decA q (a * q + b) = a := by
  obtain ⟨h1, h2⟩ := dec_spec hq (a * q + b)
  exact divmod_unique q (decA q (a * q + b)) a (decB q (a * q + b)) b h1 h2 hb

/-- ★ **Encode roundtrip (column)**: `decB q (a·q + b) = b` for `b < q`. -/
theorem decB_encode {q : Nat} (hq : 0 < q) (a b : Nat) (hb : b < q) :
    decB q (a * q + b) = b := by
  obtain ⟨h1, _⟩ := dec_spec hq (a * q + b)
  rw [decA_encode hq a b hb] at h1
  exact E213.Tactic.NatHelper.add_left_cancel h1

/-! ## §4 — the (factored) Kronecker companion and the vector recurrence -/

/-- `shiftSum` as a `sumZ` over `iota`. -/
theorem shiftSum_eq_sumZ (b s : Nat → Int) (n : Nat) : ∀ (k : Nat),
    shiftSum b s k n = sumZ ((iota k).map (fun i => b i * s (n + i)))
  | 0     => rfl
  | k + 1 => by
    show shiftSum b s k n + b k * s (n + k) = sumZ ((iota (k + 1)).map (fun i => b i * s (n + i)))
    rw [shiftSum_eq_sumZ b s n k, show iota (k + 1) = iota k ++ [k] from rfl, map_append',
        sumZ_append,
        show ([k] : List Nat).map (fun i => b i * s (n + i)) = [b k * s (n + k)] from rfl,
        sumZ_singleton]

/-- The `s`-shift row of the companion: shift if interior, the recurrence row at the `s`-boundary. -/
def Ms (p : Nat) (α : Nat → Int) (a a' : Nat) : Int :=
  if a + 1 < p then (if a + 1 = a' then 1 else 0) else α a'

/-- The `t`-shift row. -/
def Mt (q : Nat) (β : Nat → Int) (b b' : Nat) : Int :=
  if b + 1 < q then (if b + 1 = b' then 1 else 0) else β b'

/-- The product vector `w(n)_J = s(n + J/q)·t(n + J%q)`. -/
def Wvec (s t : Nat → Int) (q : Nat) : Nat → Nat → Int :=
  fun n J => s (n + decA q J) * t (n + decB q J)

/-- The Kronecker companion `M_{JK} = M_s(decA J, decA K)·M_t(decB J, decB K)`. -/
def Mmat (p q : Nat) (α β : Nat → Int) : Nat → Nat → Int :=
  fun J K => Ms p α (decA q J) (decA q K) * Mt q β (decB q J) (decB q K)

/-- ★ **The `s`-row reproduces the shift**: `Σ_{a'<p} M_s(a,a')·s(n+a') = s(n+a+1)`. -/
theorem Ms_sum {p : Nat} {α : Nat → Int} {s : Nat → Int} {n : Nat}
    (hp : ShiftRecZ p α s) {a : Nat} (ha : a < p) :
    sumZ ((iota p).map (fun a' => Ms p α a a' * s (n + a'))) = s (n + a + 1) := by
  by_cases h : a + 1 < p
  · rw [map_eq_of_mem (fun a' => Ms p α a a' * s (n + a')) (fun a' => if a + 1 = a' then s (n + a') else 0)
          (fun a' _ => by
            show (if a + 1 < p then (if a + 1 = a' then 1 else 0) else α a') * s (n + a')
               = if a + 1 = a' then s (n + a') else 0
            rw [if_pos h]
            by_cases h2 : a + 1 = a'
            · rw [if_pos h2, if_pos h2, one_mul']
            · rw [if_neg h2, if_neg h2, E213.Meta.Int213.zero_mul]),
        sumZ_iota_delta_lt (fun a' => s (n + a')) (a + 1) p h, Nat.add_assoc n a 1]
  · have hap : a + 1 = p := Nat.le_antisymm (Nat.succ_le_of_lt ha) (Nat.le_of_not_lt h)
    rw [map_eq_of_mem (fun a' => Ms p α a a' * s (n + a')) (fun a' => α a' * s (n + a'))
          (fun a' _ => by
            show (if a + 1 < p then (if a + 1 = a' then 1 else 0) else α a') * s (n + a') = α a' * s (n + a')
            rw [if_neg h]),
        ← shiftSum_eq_sumZ α s n p, ← hp n, Nat.add_assoc n a 1, hap]

/-- ★ **The `t`-row reproduces the shift**: `Σ_{b'<q} M_t(b,b')·t(n+b') = t(n+b+1)`. -/
theorem Mt_sum {q : Nat} {β : Nat → Int} {t : Nat → Int} {n : Nat}
    (hq : ShiftRecZ q β t) {b : Nat} (hb : b < q) :
    sumZ ((iota q).map (fun b' => Mt q β b b' * t (n + b'))) = t (n + b + 1) := by
  by_cases h : b + 1 < q
  · rw [map_eq_of_mem (fun b' => Mt q β b b' * t (n + b')) (fun b' => if b + 1 = b' then t (n + b') else 0)
          (fun b' _ => by
            show (if b + 1 < q then (if b + 1 = b' then 1 else 0) else β b') * t (n + b')
               = if b + 1 = b' then t (n + b') else 0
            rw [if_pos h]
            by_cases h2 : b + 1 = b'
            · rw [if_pos h2, if_pos h2, one_mul']
            · rw [if_neg h2, if_neg h2, E213.Meta.Int213.zero_mul]),
        sumZ_iota_delta_lt (fun b' => t (n + b')) (b + 1) q h, Nat.add_assoc n b 1]
  · have hbq : b + 1 = q := Nat.le_antisymm (Nat.succ_le_of_lt hb) (Nat.le_of_not_lt h)
    rw [map_eq_of_mem (fun b' => Mt q β b b' * t (n + b')) (fun b' => β b' * t (n + b'))
          (fun b' _ => by
            show (if b + 1 < q then (if b + 1 = b' then 1 else 0) else β b') * t (n + b') = β b' * t (n + b')
            rw [if_neg h]),
        ← shiftSum_eq_sumZ β t n q, ← hq n, Nat.add_assoc n b 1, hbq]

end E213.Lib.Math.Cauchy.CFiniteHadamard
