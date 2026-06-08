import E213.Lib.Math.NumberTheory.ModArith.GaussLemma
import E213.Lib.Math.Algebra.Linalg213.PermGroup
import E213.Lib.Math.Algebra.Linalg213.PermSign
import E213.Meta.Nat.MulMod213

/-!
# ZolotarevSign — the multiplication permutation `×a mod p` and its sign

The value-list `mulPermMod a p = [0, a, 2a, …, (p−1)a]` (each reduced mod `p`) is the
permutation `σ_a : x ↦ a·x mod p` of `{0,…,p−1}`.  For a unit `a` (prime `p ∤ a`) it is a
genuine permutation (`mulPermMod_mem_perms`), and the map `a ↦ σ_a` is a homomorphism of the
unit group into the symmetric group: `σ_a ∘ σ_b = σ_{ab}` (`mulPermMod_comp`).  Composing
with the inversion sign gives a homomorphism to `{±1}`:

  `psign σ_{ab} = psign σ_a · psign σ_b`     (`psign_mulPermMod`).

This is the structural backbone of **Zolotarev's lemma** (`psign σ_a = (a/p)`, the Legendre
symbol): both `a ↦ psign σ_a` and the Legendre symbol are characters `(ℤ/p)^× → {±1}`.  One
direction is closed here — **quadratic residues map to even permutations**:

  `QR(a) ⟹ psign σ_a = 1`     (`psign_mulPermMod_qr`),

because `a ≡ z²` gives `σ_a = σ_z ∘ σ_z`, an even permutation (`altSign_self`).  Via
`GaussLemma.gauss_qr` (`QR(a) ⟺ ∏ₓ sgFn(a·x) = 1 = (a/p)`) this is the residue side of
Zolotarev: the sign character agrees with the Legendre symbol on the quadratic-residue
subgroup.

The **converse** (non-residue ⟹ odd permutation, i.e. the sign character is nontrivial) is
now **fully closed for every odd prime** in `ModArith/ZolotarevMuBridge.lean`
(`zolotarev_mu`: `psign σ_a = 1 ⟺ a` is a QR).  Because `σ_a(p−x) = p − σ_a(x)`, `σ_a` is in
block form `0 :: (fh ++ (revL fh).map (p−·))`, so `psign σ_a = altSign (diagCount p fh)`
reduces to a symmetric cross-count whose parity is Gauss's `μ` — no primitive root needed.
The `−1`-axis / `p ≡ 3 (mod 4)` partial result (`ZolotarevConverse.zolotarev_pmod4_three`)
is subsumed.  Closure record: `research-notes/frontiers/permutation_three_readouts.md`.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.ZolotarevSign

open E213.Lib.Math.Algebra.Linalg213.Permutation (iota perms psign inversions LPerm)
open E213.Lib.Math.Algebra.Linalg213.PermGroup
  (composeList composeList_getD composeList_length getD_iota)
open E213.Lib.Math.Algebra.Linalg213.PermSign (psign_mul altSign_self)
open E213.Lib.Math.Algebra.Linalg213.PermClosure (lt_of_mem_iota length_iota permsOf_complete)
open E213.Lib.Math.Algebra.Linalg213.Laplace (lperm_of_nodup_mem_iff mem_iota_of_lt)
open E213.Lib.Math.NumberTheory.ModArith.GaussLemma
  (mem_of_card_le cntNodup_of_listNodup listNodup_iota)
open E213.Tactic.List213
  (nodup_map_of_inj exists_of_mem_map getD_map_ib getD_ge list_ext_getD length_map)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure)
open E213.Meta.Nat.Gcd213 (mod_eq_dvd_sub)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Tactic.NatHelper (mul_sub mul_assoc)

/-! ## §1 — unit non-divisibility + residue-cancellation -/

/-- A unit residue `1 ≤ z < p` is coprime to a prime `p` (`p ∤ z`). -/
private theorem unit_not_dvd (p z : Nat) (hz1 : 1 ≤ z) (hzp : z < p) : ¬ p ∣ z :=
  fun h => absurd (le_of_dvd_pos p z (Nat.lt_of_lt_of_le Nat.zero_lt_one hz1) h) (Nat.not_le.mpr hzp)

/-- Residue cancellation (`y ≤ x` form): `a·x ≡ a·y (mod p)` with `x < p`, `p ∤ a` ⟹ `x = y`. -/
private theorem res_cancel_le (a p x y : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hnpa : ¬ p ∣ a) (hxp : x < p) (hyx : y ≤ x) (heq : (a * x) % p = (a * y) % p) : x = y := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hle : a * y ≤ a * x := Nat.mul_le_mul_left a hyx
  have hdvd : p ∣ (a * x - a * y) := mod_eq_dvd_sub (a * x) (a * y) p hppos hle heq
  rw [(mul_sub a x y).symm] at hdvd
  have hdxy : p ∣ (x - y) :=
    (nat_prime_dvd_mul p hp hpr a (x - y) hdvd).elim (fun h => absurd h hnpa) id
  have hxylt : x - y < p := Nat.lt_of_le_of_lt (Nat.sub_le x y) hxp
  have hxy0 : x - y = 0 := by
    rcases Nat.eq_zero_or_pos (x - y) with h0 | hpos
    · exact h0
    · exact absurd (Nat.lt_of_le_of_lt (le_of_dvd_pos p (x - y) hpos hdxy) hxylt) (Nat.lt_irrefl p)
  exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hxy0) hyx

/-- `x ↦ (a·x) % p` is injective on `[0, p)` for a unit `a`. -/
private theorem res_inj (a p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hnpa : ¬ p ∣ a) : ∀ x y, x < p → y < p → (a * x) % p = (a * y) % p → x = y := by
  intro x y hxp hyp heq
  rcases Nat.le_total y x with hyx | hxy
  · exact res_cancel_le a p x y hp hpr hnpa hxp hyx heq
  · exact (res_cancel_le a p y x hp hpr hnpa hyp hxy heq.symm).symm

/-! ## §2 — the multiplication permutation `σ_a` -/

/-- The value-list of `σ_a : x ↦ a·x mod p` over `{0,…,p−1}`. -/
def mulPermMod (a p : Nat) : List Nat := (iota p).map (fun x => (a * x) % p)

theorem mulPermMod_length (a p : Nat) : (mulPermMod a p).length = p := by
  rw [mulPermMod, length_map, length_iota]

/-- In-range readout: position `i < p` holds `(a·i) % p`. -/
theorem mulPermMod_getD (a p i : Nat) (hi : i < p) : (mulPermMod a p).getD i 0 = (a * i) % p := by
  rw [mulPermMod,
      getD_map_ib (fun x => (a * x) % p) 0 0 (iota p) i (by rw [length_iota]; exact hi),
      getD_iota p i hi]

/-- ★★ **`σ_a` is a permutation** of `{0,…,p−1}` for a unit `a` (`p ∤ a`): it is `Nodup`
    (residue-injective) and lands in `iota p`, hence by cardinality hits every residue. -/
theorem mulPermMod_mem_perms (a p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hnpa : ¬ p ∣ a) : mulPermMod a p ∈ perms p := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hinj : ∀ x, x ∈ iota p → ∀ y, y ∈ iota p → (a * x) % p = (a * y) % p → x = y :=
    fun x hx y hy h => res_inj a p hp hpr hnpa x y (lt_of_mem_iota hx) (lt_of_mem_iota hy) h
  have hfnd : (mulPermMod a p).Nodup := by
    rw [mulPermMod]; exact nodup_map_of_inj hinj (listNodup_iota p)
  have hsub : ∀ q, q ∈ mulPermMod a p → q ∈ iota p := by
    intro q hq
    obtain ⟨x, _, hxq⟩ := exists_of_mem_map (l := iota p) (by rw [mulPermMod] at hq; exact hq)
    rw [← hxq]; exact mem_iota_of_lt (Nat.mod_lt _ hppos)
  have hlen : (iota p).length ≤ (mulPermMod a p).length :=
    Nat.le_of_eq (by rw [length_iota, mulPermMod_length])
  have hmem : ∀ q, q ∈ mulPermMod a p ↔ q ∈ iota p :=
    fun q => ⟨hsub q, fun hq => mem_of_card_le hfnd hsub hlen q hq⟩
  exact permsOf_complete (iota p) (mulPermMod a p)
    (lperm_of_nodup_mem_iff (cntNodup_of_listNodup hfnd)
      (cntNodup_of_listNodup (listNodup_iota p)) hmem)

/-! ## §3 — the homomorphism `σ_a ∘ σ_b = σ_{ab}` -/

/-- ★★ **Composition law**: `σ_a ∘ σ_b = σ_{ab}` as value-lists.  At position `i`,
    `a·((b·i) mod p) ≡ (ab)·i (mod p)` (`mul_mod_right_pure` + associativity). -/
theorem mulPermMod_comp (a b p : Nat) (hp : 1 < p) :
    composeList (mulPermMod a p) (mulPermMod b p) = mulPermMod (a * b) p := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  refine list_ext_getD 0 ?_ ?_
  · rw [composeList_length, mulPermMod_length b p, mulPermMod_length (a * b) p]
  · intro i
    rcases Nat.lt_or_ge i p with hi | hi
    · rw [composeList_getD (mulPermMod a p) (mulPermMod b p) i
            (by rw [mulPermMod_length]; exact hi),
          mulPermMod_getD b p i hi,
          mulPermMod_getD a p ((b * i) % p) (Nat.mod_lt _ hppos),
          mulPermMod_getD (a * b) p i hi,
          ← mul_mod_right_pure a (b * i) p, ← mul_assoc a b i]
    · rw [getD_ge 0 (by rw [composeList_length, mulPermMod_length b p]; exact hi),
          getD_ge 0 (by rw [mulPermMod_length (a * b) p]; exact hi)]

/-- ★★★ **Sign-multiplicativity** (the character homomorphism):
    `psign σ_{ab} = psign σ_a · psign σ_b` for units `a, b`. -/
theorem psign_mulPermMod (a b p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hnpa : ¬ p ∣ a) (hnpb : ¬ p ∣ b) :
    psign (mulPermMod (a * b) p) = psign (mulPermMod a p) * psign (mulPermMod b p) := by
  have key := psign_mul p (mulPermMod a p) (mulPermMod b p)
    (mulPermMod_mem_perms a p hp hpr hnpa) (mulPermMod_mem_perms b p hp hpr hnpb)
  rw [mulPermMod_comp a b p hp] at key
  exact key

/-! ## §4 — quadratic residues map to even permutations -/

/-- A square multiplier reduces mod `p` without changing the permutation: `σ_{z²%p} = σ_{z·z}`. -/
private theorem mulPermMod_sq (z p a : Nat) (hsq : z ^ 2 % p = a) :
    mulPermMod a p = mulPermMod (z * z) p := by
  have hz2 : z ^ 2 = z * z := by rw [Nat.pow_succ, Nat.pow_one]
  refine list_ext_getD 0 (by rw [mulPermMod_length, mulPermMod_length]) (fun i => ?_)
  rcases Nat.lt_or_ge i p with hi | hi
  · rw [mulPermMod_getD a p i hi, mulPermMod_getD (z * z) p i hi, ← hsq,
        ← mul_mod_left_pure (z ^ 2) i p, hz2]
  · rw [getD_ge 0 (by rw [mulPermMod_length]; exact hi),
        getD_ge 0 (by rw [mulPermMod_length]; exact hi)]

/-- ★★★ **Quadratic residues are even permutations**: if `a` is a quadratic residue mod the
    prime `p` (`∃ z, 1 ≤ z < p, z² ≡ a`), then `psign σ_a = 1`.  `σ_a = σ_z ∘ σ_z` is the square
    of `σ_z`, so its sign is `(±1)² = 1` (`altSign_self`).

    With `GaussLemma.gauss_qr` (`QR(a) ⟺ ∏ₓ sgFn(a·x) = 1 = (a/p)`) this is the residue side of
    **Zolotarev's lemma**: the sign character `a ↦ psign σ_a` agrees with the Legendre symbol on
    the quadratic-residue subgroup. -/
theorem psign_mulPermMod_qr (a p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hqr : ∃ z, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = a) : psign (mulPermMod a p) = 1 := by
  obtain ⟨z, hz1, hzp, hsq⟩ := hqr
  have hnpz : ¬ p ∣ z := unit_not_dvd p z hz1 hzp
  rw [mulPermMod_sq z p a hsq, psign_mulPermMod z z p hp hpr hnpz hnpz]
  exact altSign_self (inversions (mulPermMod z p))

end E213.Lib.Math.NumberTheory.ModArith.ZolotarevSign
