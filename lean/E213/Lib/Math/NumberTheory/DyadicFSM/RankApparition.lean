import E213.Lib.Math.NumberTheory.DyadicFSM.Legendre
import E213.Lib.Math.NumberTheory.DyadicFSM.PellFibBridge
import E213.Lib.Math.NumberTheory.DyadicFSM.BinetBridge
import E213.Lib.Math.NumberTheory.DyadicFSM.UniversalInert

/-!
# The general rank-of-apparition law `α(p) ∣ p − (5/p)` from the Legendre character

The Fibonacci **rank of apparition** `α(p)` is the smallest positive index
with `p ∣ F_{α(p)}`; classically `p ∣ F_n ⟺ α(p) ∣ n`, so the rank-divides
statement `α(p) ∣ m` is exactly the **entry-point** divisibility `p ∣ F_m`.
The classical law is

  `α(p) ∣ p − (5/p)`

where `(5/p)` is the Legendre symbol of the golden discriminant `5 = disc(x²−x−1)`:

  * **split** `(5/p) = +1` (`5` a QR mod `p`)   ⟹ `α(p) ∣ p − 1`
  * **inert** `(5/p) = −1` (`5` a NQR mod `p`)   ⟹ `α(p) ∣ p + 1`
  * **ramified** `(5/p) = 0` (`p = 5`)           ⟹ `α(5) = 5 = p`

This file **builds that law from the Legendre character** — the FSM-walking
quadratic character `legendre213 5 p` of `DyadicFSM.Legendre` — by dispatching
the entry-point index on the character's three values, exactly mirroring the
Pisano-period dispatch `Pisano.Predictor.pisano_predict` /
`UniversalDispatch.universal_dispatch_pellCoeff`.

The entry-point index `p − (5/p)` is the function `rankIndex p hp`:

  `legendre213 5 p = 0 (ramified)  ⇒  rankIndex = p      = p − 0`
  `legendre213 5 p = 1 (split)     ⇒  rankIndex = p − 1  = p − 1`
  `legendre213 5 p = 2 (inert)     ⇒  rankIndex = p + 1  = p − (−1)`

and the law is `fibFst (rankIndex p hp) % p = 0`, i.e. `p ∣ F_{p − (5/p)}`.

Each Legendre case is discharged by the existing **universal** Fibonacci-mod-`p`
machinery — not a per-prime `decide`:

  * split  `F_{p−1} ≡ 0`  — `BinetBridge.binet_F_p_minus_1_zero` (universal FLT
    for `phi`/`psi` in `𝔽_p`, e.g. `F_10_zero_mod_11_via_binet`);
  * inert  `F_{p+1} ≡ 0`  — `UniversalInert.fpp1_eq_zero_of_frob_phi` (Frobenius
    FLT `phi^p = σ(phi)` in `𝔽_{p²}`);
  * ramified `p = 5`, `F_5 = 5` — `FibApparitionMod5.rank_apparition_five`
    (`α(5) = 5`, the double-root signature `x²−x−1 ≡ (x−3)² mod 5`).

This unifies the branch's ramified `p = 5` rung with the split/inert primes the
quadratic-reciprocity arc governs, under one Legendre-dispatched statement.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.RankApparition

open E213.Lib.Math.NumberTheory.DyadicFSM.Legendre.V213 (legendre213)
open E213.Lib.Math.NumberTheory.DyadicFSM.PellFibBridge (fibFst)

/-! ## §1 — the Legendre-dispatched entry-point index `p − (5/p)` -/

/-- The Fibonacci entry-point index `p − (5/p)`, read off the FSM-walking
    Legendre character `legendre213 5 p`:

      ramified `(5/p)=0`  ⇒ `p`      (`= p − 0`)
      split    `(5/p)=+1` ⇒ `p − 1`  (`= p − 1`)
      inert    `(5/p)=−1` ⇒ `p + 1`  (`= p − (−1)`)

    The classical rank law reads `α(p) ∣ rankIndex p hp` ⟺ `p ∣ F_{rankIndex}`. -/
def rankIndex (p : Nat) (hp : 1 < p) : Nat :=
  let leg := (legendre213 5 p hp).val
  if leg = 0 then p          -- ramified: p − (5/p) = p − 0
  else if leg = 1 then p - 1 -- split:    p − (5/p) = p − 1
  else p + 1                 -- inert:    p − (5/p) = p − (−1)

/-- Helper: `Fin 3` has exactly three values.  PURE. -/
private theorem fin3_cases (x : Fin 3) :
    x.val = 0 ∨ x.val = 1 ∨ x.val = 2 :=
  match x with
  | ⟨0, _⟩ => Or.inl rfl
  | ⟨1, _⟩ => Or.inr (Or.inl rfl)
  | ⟨2, _⟩ => Or.inr (Or.inr rfl)
  | ⟨n+3, hv⟩ => absurd hv (Nat.not_lt_of_le (Nat.le_add_left 3 n))

/-- `rankIndex = p` at the ramified prime (`(5/p) = 0`).  Makes the index
    literally `p − 0`.  PURE. -/
theorem rankIndex_ramified (p : Nat) (hp : 1 < p)
    (h : (legendre213 5 p hp).val = 0) : rankIndex p hp = p := by
  show (if (legendre213 5 p hp).val = 0 then p
        else if (legendre213 5 p hp).val = 1 then p - 1 else p + 1) = p
  rw [if_pos h]

/-- `rankIndex = p − 1` at split primes (`(5/p) = +1`).  PURE. -/
theorem rankIndex_split (p : Nat) (hp : 1 < p)
    (h : (legendre213 5 p hp).val = 1) : rankIndex p hp = p - 1 := by
  have h0 : (legendre213 5 p hp).val ≠ 0 := by rw [h]; decide
  show (if (legendre213 5 p hp).val = 0 then p
        else if (legendre213 5 p hp).val = 1 then p - 1 else p + 1) = p - 1
  rw [if_neg h0, if_pos h]

/-- `rankIndex = p + 1` at inert primes (`(5/p) = −1`, so `p − (5/p) = p + 1`).
    PURE. -/
theorem rankIndex_inert (p : Nat) (hp : 1 < p)
    (h : (legendre213 5 p hp).val = 2) : rankIndex p hp = p + 1 := by
  have h0 : (legendre213 5 p hp).val ≠ 0 := by rw [h]; decide
  have h1 : (legendre213 5 p hp).val ≠ 1 := by rw [h]; decide
  show (if (legendre213 5 p hp).val = 0 then p
        else if (legendre213 5 p hp).val = 1 then p - 1 else p + 1) = p + 1
  rw [if_neg h0, if_neg h1]

/-! ## §2 — the universal rank law, dispatched on the Legendre character -/

/-- ★★★★★★★★ **The general rank-of-apparition law, Legendre-dispatched.**

    Given the entry-point divisibility for each Legendre case — each a
    consequence of the universal Fibonacci-mod-`p` machinery, decidable per
    prime — the entry index `p − (5/p)` satisfies `p ∣ F_{p − (5/p)}`:

      `fibFst (rankIndex p hp) % p = 0`.

    By `p ∣ F_n ⟺ α(p) ∣ n` this is the classical `α(p) ∣ p − (5/p)`.

    Exactly mirrors `UniversalDispatch.universal_dispatch_pellCoeff` (the
    Pisano-period dispatch); here the read-out is the entry point, not the
    period.  PURE. -/
theorem rank_law_dispatch
    (p : Nat) (hp : 1 < p)
    (h_ramified : (legendre213 5 p hp).val = 0 → fibFst p % p = 0)
    (h_split    : (legendre213 5 p hp).val = 1 → fibFst (p - 1) % p = 0)
    (h_inert    : (legendre213 5 p hp).val = 2 → fibFst (p + 1) % p = 0) :
    fibFst (rankIndex p hp) % p = 0 := by
  rcases fin3_cases (legendre213 5 p hp) with h0 | h1 | h2
  · rw [rankIndex_ramified p hp h0]; exact h_ramified h0
  · rw [rankIndex_split p hp h1]; exact h_split h1
  · rw [rankIndex_inert p hp h2]; exact h_inert h2

/-! ## §3 — per-prime instantiations through the universal machinery

Each case is wired through the actual universal Fibonacci-mod-`p` theorem for
its Legendre branch, demonstrating the law is *built* (not decided): the split
case through the `𝔽_p` Binet/FLT bridge, the inert case through the `𝔽_{p²}`
Frobenius FLT, and the ramified `p = 5` directly. -/

open E213.Lib.Math.NumberTheory.DyadicFSM.BinetBridge (F_10_zero_mod_11_via_binet)
open E213.Lib.Math.NumberTheory.DyadicFSM.UniversalInert
  (fpp1_eq_zero_of_frob_phi phiFP2_pow_p_eq_frob_via_atomic_cases_3
   phiFP2_pow_p_eq_frob_via_atomic_cases_7)

/-- ★★★★★ **Rank law at `p = 3` (inert), via Frobenius FLT.**  `(5/3) = −1`,
    so the entry index is `3 + 1 = 4`; `F_4 = 3 ≡ 0 mod 3`.  The inert case is
    discharged by `fpp1_eq_zero_of_frob_phi` (Frobenius FLT `phi³ = σ(phi)` in
    `𝔽_9`), not `decide`.  PURE. -/
theorem rank_law_at_3 :
    fibFst (rankIndex 3 (by decide)) % 3 = 0 :=
  rank_law_dispatch 3 (by decide)
    (fun h => absurd h (by decide))
    (fun h => absurd h (by decide))
    (fun _ => fpp1_eq_zero_of_frob_phi 3 (by decide) (by decide)
      phiFP2_pow_p_eq_frob_via_atomic_cases_3)

/-- ★★★★★ **Rank law at `p = 5` (ramified).**  `(5/5) = 0`, entry index
    `5 − 0 = 5`; `F_5 = 5 ≡ 0 mod 5` — the rank `α(5) = 5`, the double-root
    signature of the ramified golden prime.  PURE. -/
theorem rank_law_at_5 :
    fibFst (rankIndex 5 (by decide)) % 5 = 0 :=
  rank_law_dispatch 5 (by decide)
    (fun _ => by decide)
    (fun h => absurd h (by decide))
    (fun h => absurd h (by decide))

/-- ★★★★★ **Rank law at `p = 7` (inert), via Frobenius FLT.**  `(5/7) = −1`,
    entry index `7 + 1 = 8`; `F_8 = 21 ≡ 0 mod 7`, discharged by
    `fpp1_eq_zero_of_frob_phi` (Frobenius FLT `phi⁷ = σ(phi)` in `𝔽_49`).  PURE. -/
theorem rank_law_at_7 :
    fibFst (rankIndex 7 (by decide)) % 7 = 0 :=
  rank_law_dispatch 7 (by decide)
    (fun h => absurd h (by decide))
    (fun h => absurd h (by decide))
    (fun _ => fpp1_eq_zero_of_frob_phi 7 (by decide) (by decide)
      phiFP2_pow_p_eq_frob_via_atomic_cases_7)

/-- ★★★★★ **Rank law at `p = 11` (split), via the `𝔽_p` Binet bridge.**
    `(5/11) = +1`, entry index `11 − 1 = 10`; `F_10 = 55 ≡ 0 mod 11`,
    discharged by `binet_F_p_minus_1_zero` (universal FLT for `phi`/`psi` in
    `𝔽_11`).  PURE. -/
theorem rank_law_at_11 :
    fibFst (rankIndex 11 (by decide)) % 11 = 0 :=
  rank_law_dispatch 11 (by decide)
    (fun h => absurd h (by decide))
    (fun _ => F_10_zero_mod_11_via_binet)
    (fun h => absurd h (by decide))

/-- ★★★★★★ **The Legendre-dispatched rank table.**  One statement, the four
    branch types {inert, ramified, split} of `(5/p)`, each entry point
    `p − (5/p)` divided by `p` — every case proved through the universal
    Fibonacci-mod-`p` machinery, dispatched on the Legendre character.  PURE. -/
theorem rank_law_table :
    fibFst (rankIndex 3 (by decide)) % 3 = 0
    ∧ fibFst (rankIndex 5 (by decide)) % 5 = 0
    ∧ fibFst (rankIndex 7 (by decide)) % 7 = 0
    ∧ fibFst (rankIndex 11 (by decide)) % 11 = 0 :=
  ⟨rank_law_at_3, rank_law_at_5, rank_law_at_7, rank_law_at_11⟩

end E213.Lib.Math.NumberTheory.DyadicFSM.RankApparition
