import E213.Lib.Math.Cohomology.Fractal.ConfigCountModular
import E213.Lib.Math.DyadicFSM.Forward.ForwardPeriodicity
import E213.Meta.Nat.MulMod213
import E213.Meta.Tactic.NatHelper

/-!
# Configuration-count eventual periodicity at coprime (d, p)

Universal `∃ T n₀, ∀ n ≥ n₀, configCountD d (n + T) % p = configCountD d n % p`
under the FLT hypothesis `d^(p-1) % p = 1 % p` and `2 ≤ p`.

Strategy (forward-only pigeonhole on the exponent layer):

  · The map `n ↦ d^n % (p-1)` is a Markov chain on `Fin (p-1)`:
    `(d^(n+1)) % (p-1) = ((d^n % (p-1)) * d) % (p-1)` by mul_mod.
  · Pigeonhole on the first `p` terms (`Fin p → Fin (p-1)`,
    needs `p - 1 < p` i.e. `p ≥ 1`) gives a collision
    `d^i % (p-1) = d^j % (p-1)` with `0 ≤ i < j ≤ p - 1`.
  · Forward propagation of the recurrence: if state collides at
    `i, j` then `state (n + (j - i)) = state n` for all `n ≥ i`.
  · Compose with `configCountD_mod_pure` to lift the period.

Distinct from `MulOrderPigeonhole.exists_modPow_period`, which
requires a modular inverse to conclude `modPow p a N = 1 % p`
(purely periodic).  This file gives the **forward-only** result
applicable at any coprime pair without needing an inverse —
covers eventually-constant cases like `(5, 11)` where
`gcd(5, p - 1) ≠ 1`.

STRICT ∅-AXIOM (no `omega`, only explicit `NatHelper.*` lemmas).
-/

namespace E213.Lib.Math.Cohomology.Fractal.EventualPeriodicity

open E213.Lib.Math.Cohomology.Fractal.ConfigCount (configCountD)
open E213.Lib.Math.Cohomology.Fractal.ConfigCountModular (configCountD_mod_pure)
open E213.Lib.Math.DyadicFSM.Forward.ForwardPeriodicity
  (pigeonhole_collision collTest_imp_val_eq)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure)
open E213.Tactic.NatHelper (sub_pos_of_lt sub_add_cancel add_sub_of_le
  le_sub_of_add_le)

/-! ## §1 Exponent-layer state -/

/-- The exponent-layer state: `expSeq d m n := d^n % m`.  Markov
    chain in `Fin m` (when `0 < m`); transitions via
    `expSeq d m (n+1) = (expSeq d m n * d) % m`. -/
def expSeq (d m n : Nat) : Nat := d ^ n % m

/-- `expSeq d m n < m` for `0 < m`. -/
theorem expSeq_lt (d m : Nat) (hm : 0 < m) (n : Nat) : expSeq d m n < m :=
  Nat.mod_lt _ hm

/-- `expSeq` recurrence: `expSeq d m (n+1) = (expSeq d m n * d) % m`.
    Direct corollary of `d^(n+1) = d^n * d` (Nat.pow definitional)
    + `mul_mod_left_pure`. -/
theorem expSeq_succ (d m n : Nat) :
    expSeq d m (n + 1) = (expSeq d m n * d) % m := by
  show d ^ (n + 1) % m = (d ^ n % m * d) % m
  exact mul_mod_left_pure (d ^ n) d m

/-! ## §2 Pigeonhole on `Fin p → Fin (p-1)`

For `p = p' + 2` (i.e. `p ≥ 2`), `p - 1 = p' + 1 ≥ 1` and
`p - 1 < p` are both kernel-direct via `Nat.lt_succ_self` and
`Nat.succ_le_succ (Nat.zero_le _)`. -/

/-- Encode `expSeq d (p-1) i.val ∈ Fin (p - 1)` for the
    pigeonhole argument.  Requires `1 ≤ p - 1`. -/
def expSeqFin (d p : Nat) (hp : 1 ≤ p - 1) (i : Fin p) : Fin (p - 1) :=
  ⟨expSeq d (p - 1) i.val, expSeq_lt d (p - 1) hp i.val⟩

/-- ★ **Exponent-layer collision** (pigeonhole on `Fin p → Fin (p-1)`):
    for `p = p' + 2`, two indices `i < j < p` give the same
    `expSeq d (p - 1)` value. -/
theorem expSeq_collision (d p' : Nat) :
    ∃ i j, i < p' + 2 ∧ j < p' + 2 ∧ i < j
      ∧ expSeq d (p' + 2 - 1) i = expSeq d (p' + 2 - 1) j := by
  have hpm1_pos : 1 ≤ p' + 2 - 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hlt : p' + 2 - 1 < p' + 2 := Nat.lt_succ_self _
  obtain ⟨i, hi, j, hj, hij, hcoll⟩ :=
    pigeonhole_collision hlt (expSeqFin d (p' + 2) hpm1_pos)
  have hval_eq : (expSeqFin d (p' + 2) hpm1_pos ⟨i, hi⟩).val
              = (expSeqFin d (p' + 2) hpm1_pos ⟨j, hj⟩).val :=
    collTest_imp_val_eq (expSeqFin d (p' + 2) hpm1_pos) i j hi hj hcoll
  exact ⟨i, j, hi, hj, hij, hval_eq⟩

/-! ## §3 Forward propagation

If `expSeq d m i = expSeq d m (i + T)`, then for every `k`,
`expSeq d m (i + k + T) = expSeq d m (i + k)`.  Induction on `k`. -/

/-- ★ **Forward propagation lemma**: collision propagates via the
    Markov recurrence.  Induction on the index shift `k`. -/
theorem expSeq_period_propagate (d m i T : Nat)
    (h_coll : expSeq d m i = expSeq d m (i + T)) :
    ∀ k, expSeq d m (i + k + T) = expSeq d m (i + k)
  | 0 => by
      show expSeq d m (i + T) = expSeq d m i
      exact h_coll.symm
  | k + 1 => by
      have ih : expSeq d m (i + k + T) = expSeq d m (i + k) :=
        expSeq_period_propagate d m i T h_coll k
      have h_lhs_idx : i + (k + 1) + T = (i + k + T) + 1 :=
        Nat.succ_add (i + k) T
      have h_rhs_idx : i + (k + 1) = (i + k) + 1 := rfl
      have h_lhs : expSeq d m (i + (k + 1) + T)
                 = (expSeq d m (i + k + T) * d) % m := by
        have := expSeq_succ d m (i + k + T)
        exact h_lhs_idx ▸ this
      have h_rhs : expSeq d m (i + (k + 1))
                 = (expSeq d m (i + k) * d) % m := by
        have := expSeq_succ d m (i + k)
        exact h_rhs_idx ▸ this
      have h_swap : (expSeq d m (i + k + T) * d) % m
                  = (expSeq d m (i + k) * d) % m :=
        congrArg (fun x => (x * d) % m) ih
      exact h_lhs.trans (h_swap.trans h_rhs.symm)

/-! ## §4 Existence of period at the exponent layer -/

/-- ★★★ **Exponent-layer eventual periodicity**: for `p = p' + 2`,
    there exist `T ≥ 1` and `n₀ ≤ p - 1` such that
    `expSeq d (p - 1) (n + T) = expSeq d (p - 1) n` for every
    `n ≥ n₀`.  Combines `expSeq_collision` + `expSeq_period_propagate`. -/
theorem expSeq_eventually_periodic (d p' : Nat) :
    ∃ T n₀, 1 ≤ T ∧ n₀ ≤ p' + 2 - 1 ∧
      ∀ n, n₀ ≤ n →
        expSeq d (p' + 2 - 1) (n + T) = expSeq d (p' + 2 - 1) n := by
  obtain ⟨i, j, _, hj, hij, hcoll⟩ := expSeq_collision d p'
  refine ⟨j - i, i, sub_pos_of_lt hij, ?_, ?_⟩
  · have hi_lt : i < p' + 2 := Nat.lt_trans hij hj
    have hi_succ : i + 1 ≤ p' + 2 := hi_lt
    exact le_sub_of_add_le hi_succ
  · intro n hn
    have hji : i + (j - i) = j := add_sub_of_le (Nat.le_of_lt hij)
    have h_coll' : expSeq d (p' + 2 - 1) i
                 = expSeq d (p' + 2 - 1) (i + (j - i)) :=
      hcoll.trans (congrArg (expSeq d (p' + 2 - 1)) hji.symm)
    have hni : n - i + i = n := sub_add_cancel hn
    have hpro : expSeq d (p' + 2 - 1) (i + (n - i) + (j - i))
              = expSeq d (p' + 2 - 1) (i + (n - i)) :=
      expSeq_period_propagate d (p' + 2 - 1) i (j - i) h_coll' (n - i)
    have h_in : i + (n - i) = n :=
      (Nat.add_comm i (n - i)).trans hni
    have h_in_T : i + (n - i) + (j - i) = n + (j - i) :=
      congrArg (· + (j - i)) h_in
    have h_lhs : expSeq d (p' + 2 - 1) (i + (n - i) + (j - i))
               = expSeq d (p' + 2 - 1) (n + (j - i)) :=
      congrArg (expSeq d (p' + 2 - 1)) h_in_T
    have h_rhs : expSeq d (p' + 2 - 1) (i + (n - i))
               = expSeq d (p' + 2 - 1) n :=
      congrArg (expSeq d (p' + 2 - 1)) h_in
    exact h_lhs.symm.trans (hpro.trans h_rhs)

/-! ## §5 Lift to configCountD

Given the FLT hypothesis `d^(p-1) % p = 1 % p`, the configCount
layer mirrors the exponent layer via `configCountD_mod_pure`. -/

/-- ★★★★★ **Universal eventual periodicity** for
    `configCountD d · % p` at FLT-satisfying `(d, p)` with `p ≥ 2`:

      ∃ T ≥ 1, n₀ ≤ p - 1, ∀ n ≥ n₀,
        configCountD d (n + T) % p = configCountD d n % p.

    PURE.  Forward-only pigeonhole on the exponent layer +
    `configCountD_mod_pure` bridge.  Applies to every coprime
    pair, including eventually-constant cases where the
    exponent sequence collapses to a fixed point (e.g. when
    `gcd(d, p - 1) > 1`). -/
theorem configCountD_eventually_periodic
    (d p' : Nat)
    (h_flt : d ^ (p' + 2 - 1) % (p' + 2) = 1 % (p' + 2)) :
    ∃ T n₀, 1 ≤ T ∧ n₀ ≤ p' + 2 - 1 ∧
      ∀ n, n₀ ≤ n →
        configCountD d (n + T) % (p' + 2) = configCountD d n % (p' + 2) := by
  obtain ⟨T, n₀, hT, hn₀, h_exp⟩ := expSeq_eventually_periodic d p'
  refine ⟨T, n₀, hT, hn₀, ?_⟩
  intro n hn
  have h_lhs : configCountD d (n + T) % (p' + 2)
             = d ^ (d ^ (n + T) % (p' + 2 - 1)) % (p' + 2) :=
    configCountD_mod_pure d (p' + 2) h_flt (n + T)
  have h_rhs : configCountD d n % (p' + 2)
             = d ^ (d ^ n % (p' + 2 - 1)) % (p' + 2) :=
    configCountD_mod_pure d (p' + 2) h_flt n
  have h_exp_eq : d ^ (n + T) % (p' + 2 - 1) = d ^ n % (p' + 2 - 1) :=
    h_exp n hn
  have h_step : d ^ (d ^ (n + T) % (p' + 2 - 1)) % (p' + 2)
              = d ^ (d ^ n % (p' + 2 - 1)) % (p' + 2) :=
    congrArg (fun x => d ^ x % (p' + 2)) h_exp_eq
  exact h_lhs.trans (h_step.trans h_rhs.symm)

/-! ## §6 Smoke tests at FLT-instantiated primes

Instantiates at every prime where `UniversalFLT.universal_flt_main`
produces the FLT hypothesis. -/

/-- Smoke at `(d, p) = (5, 7)`: eventual periodicity. -/
theorem configCountD_5_eventually_periodic_mod_7 :
    ∃ T n₀, 1 ≤ T ∧ n₀ ≤ 6 ∧
      ∀ n, n₀ ≤ n → configCountD 5 (n + T) % 7 = configCountD 5 n % 7 :=
  configCountD_eventually_periodic 5 5
    E213.Lib.Math.Cohomology.Fractal.ConfigCountModular.flt_5_7

/-- Smoke at `(d, p) = (5, 11)`: eventual periodicity in the
    `gcd(d, p - 1) ≠ 1` regime (sister readout to the
    eventually-constant sharper closure in `ConfigCountModular §I`). -/
theorem configCountD_5_eventually_periodic_mod_11 :
    ∃ T n₀, 1 ≤ T ∧ n₀ ≤ 10 ∧
      ∀ n, n₀ ≤ n → configCountD 5 (n + T) % 11 = configCountD 5 n % 11 :=
  configCountD_eventually_periodic 5 9
    E213.Lib.Math.Cohomology.Fractal.ConfigCountModular.flt_5_11

/-- Smoke at `(d, p) = (5, 13)`: eventual periodicity (period 2 in
    fact via `configCountD_5_mod_13_period_2`). -/
theorem configCountD_5_eventually_periodic_mod_13 :
    ∃ T n₀, 1 ≤ T ∧ n₀ ≤ 12 ∧
      ∀ n, n₀ ≤ n → configCountD 5 (n + T) % 13 = configCountD 5 n % 13 :=
  configCountD_eventually_periodic 5 11
    E213.Lib.Math.Cohomology.Fractal.ConfigCountModular.flt_5_13

end E213.Lib.Math.Cohomology.Fractal.EventualPeriodicity
