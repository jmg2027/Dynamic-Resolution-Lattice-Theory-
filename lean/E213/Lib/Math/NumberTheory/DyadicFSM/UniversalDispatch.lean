import E213.Lib.Math.NumberTheory.DyadicFSM.UniversalInert
import E213.Lib.Math.NumberTheory.DyadicFSM.UniversalSplit
import E213.Lib.Math.NumberTheory.DyadicFSM.Pisano.Predictor
import E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrixAction
/-!
# Universal Phase 4 — Legendre dispatch (final campaign target)

Combines the three Phase 3 cases (ramified, split, inert) via Legendre
symbol dispatch into a single universal theorem for the Pisano period
of the Pell-5 matrix.

The Pisano predictor `pisano_predict p hp` returns:
  · `2 * p`       when `legendre213 5 p hp = 0` (ramified, p = 5)
  · `(p - 1) / 2` when `legendre213 5 p hp = 1` (split, 5 QR mod p)
  · `p + 1`       when `legendre213 5 p hp = 2` (inert, 5 NQR mod p)

The dispatch theorem `universal_dispatch_pellCoeff` takes one
case-specific hypothesis per Legendre value (each decidable per
prime via the corresponding `universal_phase_3_X` or `decide`),
and produces:

  `pellCoeff p hp (pisano_predict p hp) = pellCoeff p hp 0`

i.e., `M_pell^(pisano_predict p) = I` in 𝔽_p, universal.

Lifted to FSM bit-period via `pellCoeff_period_implies_pellFSMmod_bits_period`:

  `(pellFSMmod p hp).bits (k + pisano_predict p hp)
   = (pellFSMmod p hp).bits k`

This is **G119's terminal universal closure**.  All declarations PURE.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.UniversalDispatch

open E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrix (pellCoeff)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (pellFSMmod)
open E213.Lib.Math.NumberTheory.DyadicFSM.Legendre.V213 (legendre213)
open E213.Lib.Math.NumberTheory.DyadicFSM.Pisano.Predictor (pisano_predict)
open E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrixAction
  (pellCoeff_period_implies_pellFSMmod_bits_period)

/-- Helper: Fin 3 has exactly three possible values.  PURE. -/
private theorem fin3_cases (x : Fin 3) :
    x.val = 0 ∨ x.val = 1 ∨ x.val = 2 :=
  match x with
  | ⟨0, _⟩ => Or.inl rfl
  | ⟨1, _⟩ => Or.inr (Or.inl rfl)
  | ⟨2, _⟩ => Or.inr (Or.inr rfl)
  | ⟨n+3, hv⟩ => absurd hv (Nat.not_lt_of_le (Nat.le_add_left 3 n))

/-- ★★★★★★★★ **Universal Phase 4 dispatch — pellCoeff form**.

    Combines the three Phase 3 cases via Legendre symbol.  Each
    case-specific hypothesis is decidable per prime (via
    `universal_phase_3_X` or `decide`).

    Conclusion: `pellCoeff p hp (pisano_predict p hp) = pellCoeff p hp 0`,
    i.e., `M_pell^(pisano_predict p) = I` in 𝔽_p.

    PURE. -/
theorem universal_dispatch_pellCoeff
    (p : Nat) (hp : 1 < p)
    (h_ramified : (legendre213 5 p hp).val = 0 →
                  pellCoeff p hp (2 * p) = pellCoeff p hp 0)
    (h_split : (legendre213 5 p hp).val = 1 →
               pellCoeff p hp ((p - 1) / 2) = pellCoeff p hp 0)
    (h_inert : (legendre213 5 p hp).val = 2 →
               pellCoeff p hp (p + 1) = pellCoeff p hp 0) :
    pellCoeff p hp (pisano_predict p hp) = pellCoeff p hp 0 := by
  show pellCoeff p hp
       (let leg := (legendre213 5 p hp).val
        if leg = 0 then 2 * p
        else if leg = 1 then (p - 1) / 2
        else p + 1) = pellCoeff p hp 0
  rcases fin3_cases (legendre213 5 p hp) with h0 | h1 | h2
  · -- legendre = 0 (ramified)
    show pellCoeff p hp
         (if (legendre213 5 p hp).val = 0 then 2 * p
          else if (legendre213 5 p hp).val = 1 then (p - 1) / 2
          else p + 1) = pellCoeff p hp 0
    rw [if_pos h0]
    exact h_ramified h0
  · -- legendre = 1 (split)
    show pellCoeff p hp
         (if (legendre213 5 p hp).val = 0 then 2 * p
          else if (legendre213 5 p hp).val = 1 then (p - 1) / 2
          else p + 1) = pellCoeff p hp 0
    have h_ne_0 : (legendre213 5 p hp).val ≠ 0 := by rw [h1]; decide
    rw [if_neg h_ne_0, if_pos h1]
    exact h_split h1
  · -- legendre = 2 (inert)
    show pellCoeff p hp
         (if (legendre213 5 p hp).val = 0 then 2 * p
          else if (legendre213 5 p hp).val = 1 then (p - 1) / 2
          else p + 1) = pellCoeff p hp 0
    have h_ne_0 : (legendre213 5 p hp).val ≠ 0 := by rw [h2]; decide
    have h_ne_1 : (legendre213 5 p hp).val ≠ 1 := by rw [h2]; decide
    rw [if_neg h_ne_0, if_neg h_ne_1]
    exact h_inert h2

/-- ★★★★★★★★★ **Universal Phase 4 dispatch — FSM bit-period form**.

    Lifts the matrix-order claim to bit-periodicity of the Pell FSM
    via the bridge `pellCoeff_period_implies_pellFSMmod_bits_period`.

    Conclusion: `(pellFSMmod p hp).bits (k + pisano_predict p hp)
                 = (pellFSMmod p hp).bits k`.

    **This is the G119 campaign's terminal universal closure.**  PURE. -/
theorem universal_dispatch_FSM
    (p : Nat) (hp : 1 < p)
    (h_ramified : (legendre213 5 p hp).val = 0 →
                  pellCoeff p hp (2 * p) = pellCoeff p hp 0)
    (h_split : (legendre213 5 p hp).val = 1 →
               pellCoeff p hp ((p - 1) / 2) = pellCoeff p hp 0)
    (h_inert : (legendre213 5 p hp).val = 2 →
               pellCoeff p hp (p + 1) = pellCoeff p hp 0) :
    ∀ k, (pellFSMmod p hp).bits (k + pisano_predict p hp)
         = (pellFSMmod p hp).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period p hp
    (pisano_predict p hp)
    (universal_dispatch_pellCoeff p hp h_ramified h_split h_inert)

/-! ## Per-prime instantiations of `universal_dispatch_FSM` -/

/-- Phase 4 at p = 3 (inert): all three cases via `decide`. -/
theorem universal_dispatch_at_3 :
    ∀ k, (pellFSMmod 3 (by decide)).bits (k + pisano_predict 3 (by decide))
         = (pellFSMmod 3 (by decide)).bits k :=
  universal_dispatch_FSM 3 (by decide)
    (fun h => by exact absurd h (by decide))
    (fun h => by exact absurd h (by decide))
    (fun _ => by decide)

/-- Phase 4 at p = 5 (ramified): legendre = 0. -/
theorem universal_dispatch_at_5 :
    ∀ k, (pellFSMmod 5 (by decide)).bits (k + pisano_predict 5 (by decide))
         = (pellFSMmod 5 (by decide)).bits k :=
  universal_dispatch_FSM 5 (by decide)
    (fun _ => by decide)
    (fun h => by exact absurd h (by decide))
    (fun h => by exact absurd h (by decide))

/-- Phase 4 at p = 7 (inert). -/
theorem universal_dispatch_at_7 :
    ∀ k, (pellFSMmod 7 (by decide)).bits (k + pisano_predict 7 (by decide))
         = (pellFSMmod 7 (by decide)).bits k :=
  universal_dispatch_FSM 7 (by decide)
    (fun h => by exact absurd h (by decide))
    (fun h => by exact absurd h (by decide))
    (fun _ => by decide)

/-- Phase 4 at p = 11 (split). -/
theorem universal_dispatch_at_11 :
    ∀ k, (pellFSMmod 11 (by decide)).bits (k + pisano_predict 11 (by decide))
         = (pellFSMmod 11 (by decide)).bits k :=
  universal_dispatch_FSM 11 (by decide)
    (fun h => by exact absurd h (by decide))
    (fun _ => by decide)
    (fun h => by exact absurd h (by decide))

end E213.Lib.Math.NumberTheory.DyadicFSM.UniversalDispatch
