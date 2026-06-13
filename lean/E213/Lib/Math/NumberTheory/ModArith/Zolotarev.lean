import E213.Lib.Math.Algebra.Linalg213.DetMul
import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.PolyNatMTactic

/-!
# Zolotarev — the multiplication-by-`a` permutation and its sign as a Legendre character

The permutation `mulPerm a p = [a·0, a·1, …, a·(p−1) mod p]` of `iota p` (a bijection because `a`
is a unit mod `p`).  Its sign `psign (mulPerm a p)` is the Legendre character `(a/p)` — Zolotarev's
lemma.  This file builds the **homomorphism half**: `psign ∘ mulPerm` is a `{±1}`-valued group
homomorphism on the residues, vanishing on squares.

The engine: `mulPerm` turns multiplication into permutation **composition** —
`composeList (mulPerm a) (mulPerm b) = mulPerm ((a·b) % p)` (both `getD i = (a·b·i) % p`).  With
`PermSign.psign_mul` this gives `psign (mulPerm (a·b)) = psign (mulPerm a) · psign (mulPerm b)`,
and a quadratic residue `a = z²` factors `mulPerm a = mulPerm z ∘ mulPerm z`, so
`psign (mulPerm a) = psign (mulPerm z)² = 1`.

  * ★★ `mulPerm_mem_perms` — `mulPerm a p ∈ perms p` (it is a permutation).
  * ★★ `mulPerm_comp` — multiplication ↦ composition.
  * ★★★ `psign_mulPerm_hom` — the sign is multiplicative.
  * ★★★ `psign_mulPerm_qr` — a quadratic residue's mul-permutation is **even** (`psign = 1`).

All ∅-axiom.  The converse — a non-residue's permutation is odd — is closed in `ZolotarevCycle`
(`psign_mulPerm_primitive`, the primitive-root `(p−1)`-cycle witness) and assembled into the full
identity `psign (mulPerm a p) = 1 ⟺ a` QR by `ZolotarevReduction.zolotarev_iff`.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.Zolotarev

open E213.Lib.Math.Algebra.Linalg213.Permutation (iota perms psign inversions)
open E213.Lib.Math.Algebra.Linalg213.PermGroup (composeList getD_iota)
open E213.Lib.Math.Algebra.Linalg213.PermSign (psign_mul altSign_self)
open E213.Lib.Math.Algebra.Linalg213.PermClosure (lt_of_mem_iota length_iota nodup_iota)
open E213.Lib.Math.Algebra.Linalg213.DetMul (funcs nodup_imp_perm mem_tuples)
open E213.Lib.Math.Algebra.Linalg213.DetTranspose (nodup_map_restrict)
open E213.Lib.Math.Algebra.Linalg213.Laplace (mem_iota_of_lt)
open E213.Tactic.List213 (getD_ge getD_map_ib list_ext_getD exists_of_mem_map length_map)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)
open E213.Meta.Nat.Gcd213 (mod_eq_dvd_sub)
open E213.Tactic.NatHelper (mul_sub)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure)

/-- The multiplication-by-`a` value-list mod `p`: `[a·0 % p, …, a·(p−1) % p]`. -/
def mulPerm (a p : Nat) : List Nat := (iota p).map (fun x => (a * x) % p)

theorem mulPerm_length (a p : Nat) : (mulPerm a p).length = p := by
  show ((iota p).map (fun x => (a * x) % p)).length = p
  rw [length_map, length_iota]

/-- `getD` of `mulPerm` in range: `(mulPerm a p).getD i 0 = (a·i) % p` for `i < p`. -/
theorem mulPerm_getD (a p i : Nat) (hi : i < p) : (mulPerm a p).getD i 0 = (a * i) % p := by
  show ((iota p).map (fun x => (a * x) % p)).getD i 0 = (a * i) % p
  rw [getD_map_ib (fun x => (a * x) % p) 0 0 (iota p) i (by rw [length_iota]; exact hi),
      getD_iota p i hi]

/-! ## §1 — `mulPerm` is a permutation -/

/-- Modular cancellation: `a·x ≡ a·y (mod p)` with `y ≤ x < p`, `p ∤ a` ⟹ `x = y`. -/
theorem res_cancel (a p x y : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hnpa : ¬ p ∣ a) (hxp : x < p) (hyx : y ≤ x) (heq : (a * x) % p = (a * y) % p) : x = y := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hle : a * y ≤ a * x := Nat.mul_le_mul_left a hyx
  have hdvd : p ∣ (a * x - a * y) := mod_eq_dvd_sub (a * x) (a * y) p hppos hle heq
  rw [← mul_sub a x y] at hdvd
  have hdxy : p ∣ (x - y) :=
    (nat_prime_dvd_mul p hp hpr a (x - y) hdvd).elim (fun h => absurd h hnpa) id
  have hxylt : x - y < p := Nat.lt_of_le_of_lt (Nat.sub_le x y) hxp
  have hxy0 : x - y = 0 := by
    rcases Nat.eq_zero_or_pos (x - y) with h0 | hpos
    · exact h0
    · exact absurd (le_of_dvd_pos p (x - y) hpos hdxy) (Nat.not_le.mpr hxylt)
  exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hxy0) hyx

/-- The mul-map is injective on the entries of `iota p`. -/
theorem mul_inj (a p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) (hnpa : ¬ p ∣ a) :
    ∀ x, x ∈ iota p → ∀ y, y ∈ iota p → (a * x) % p = (a * y) % p → x = y := by
  intro x hx y hy heq
  rcases Nat.le_total y x with hyx | hxy
  · exact res_cancel a p x y hp hpr hnpa (lt_of_mem_iota hx) hyx heq
  · exact (res_cancel a p y x hp hpr hnpa (lt_of_mem_iota hy) hxy heq.symm).symm

theorem mulPerm_nodup (a p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hnpa : ¬ p ∣ a) : E213.Lib.Math.Algebra.Linalg213.PermClosure.Nodup (mulPerm a p) :=
  nodup_map_restrict (mul_inj a p hp hpr hnpa) (nodup_iota p)

/-- ★★ **`mulPerm a p ∈ perms p`** — multiplication by a unit is a permutation of the residues. -/
theorem mulPerm_mem_perms (a p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hnpa : ¬ p ∣ a) : mulPerm a p ∈ perms p := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hfuncs : mulPerm a p ∈ funcs p := by
    have h := mem_tuples (iota p) (mulPerm a p)
      (fun v hv => by
        obtain ⟨y, _, hvy⟩ := exists_of_mem_map hv
        rw [← hvy]; exact mem_iota_of_lt (Nat.mod_lt _ hppos))
    rwa [mulPerm_length a p] at h
  exact nodup_imp_perm p (mulPerm a p) hfuncs (mulPerm_nodup a p hp hpr hnpa)

/-! ## §2 — multiplication ↦ composition -/

/-- ★★ **Multiplication becomes composition**: `composeList (mulPerm a) (mulPerm b) =
    mulPerm ((a·b) % p)` — both `getD i = (a·b·i) % p` (with `0` out of range). -/
theorem mulPerm_comp (a b p : Nat) :
    composeList (mulPerm a p) (mulPerm b p) = mulPerm ((a * b) % p) p := by
  apply list_ext_getD 0
  · show ((mulPerm b p).map (fun t => (mulPerm a p).getD t 0)).length
       = (mulPerm ((a * b) % p) p).length
    rw [length_map, mulPerm_length, mulPerm_length]
  · intro i
    rcases Nat.lt_or_ge i p with hi | hi
    · show ((mulPerm b p).map (fun t => (mulPerm a p).getD t 0)).getD i 0
         = (mulPerm ((a * b) % p) p).getD i 0
      have hbi : (b * i) % p < p := Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)
      rw [getD_map_ib (fun t => (mulPerm a p).getD t 0) 0 0 (mulPerm b p) i
            (by rw [mulPerm_length]; exact hi),
          mulPerm_getD b p i hi, mulPerm_getD a p ((b * i) % p) hbi,
          mulPerm_getD ((a * b) % p) p i hi,
          ← mul_mod_right_pure a (b * i) p, ← mul_mod_left_pure (a * b) i p,
          show a * (b * i) = a * b * i from by ring_nat]
    · show ((mulPerm b p).map (fun t => (mulPerm a p).getD t 0)).getD i 0
         = (mulPerm ((a * b) % p) p).getD i 0
      rw [getD_ge 0 (by rw [length_map, mulPerm_length]; exact hi),
          getD_ge 0 (by rw [mulPerm_length]; exact hi)]

/-! ## §3 — the sign homomorphism + the residue direction -/

/-- ★★★ **The sign is multiplicative**: `psign (mulPerm ((a·b) % p)) = psign (mulPerm a) ·
    psign (mulPerm b)` — `mulPerm` is a homomorphism (residues → permutations) and `psign` is one
    (permutations → `{±1}`). -/
theorem psign_mulPerm_hom (a b p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hna : ¬ p ∣ a) (hnb : ¬ p ∣ b) :
    psign (mulPerm ((a * b) % p) p) = psign (mulPerm a p) * psign (mulPerm b p) := by
  rw [← mulPerm_comp a b p,
      psign_mul p (mulPerm a p) (mulPerm b p)
        (mulPerm_mem_perms a p hp hpr hna) (mulPerm_mem_perms b p hp hpr hnb)]

/-- ★★★ **A square's multiplication-permutation is even** (`psign = 1`): `mulPerm ((z·z) % p) =
    mulPerm z ∘ mulPerm z`, so `psign = psign (mulPerm z)² = 1`. -/
theorem psign_mulPerm_qr (z p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hnz : ¬ p ∣ z) : psign (mulPerm ((z * z) % p) p) = 1 := by
  rw [← mulPerm_comp z z p,
      psign_mul p (mulPerm z p) (mulPerm z p)
        (mulPerm_mem_perms z p hp hpr hnz) (mulPerm_mem_perms z p hp hpr hnz)]
  exact altSign_self (inversions (mulPerm z p))

/-- ★★★ **Zolotarev, residue direction (QR-predicate form).**  If `a` is a quadratic residue mod
    `p` (`∃ z, 1 ≤ z < p, z² ≡ a`), its multiplication-permutation is even: `psign (mulPerm a p)
    = 1`.  (The Legendre symbol `(a/p) = +1` realised as the permutation's sign.) -/
theorem psign_mulPerm_qr_pred (a p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hqr : ∃ z, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = a) : psign (mulPerm a p) = 1 := by
  obtain ⟨z, hz1, hzp, hza⟩ := hqr
  have hnz : ¬ p ∣ z := fun h =>
    absurd (le_of_dvd_pos p z (Nat.lt_of_lt_of_le Nat.zero_lt_one hz1) h) (Nat.not_le.mpr hzp)
  have hsq : z ^ 2 = z * z := by rw [Nat.pow_succ, Nat.pow_one]
  rw [← hza, hsq]
  exact psign_mulPerm_qr z p hp hpr hnz

end E213.Lib.Math.NumberTheory.ModArith.Zolotarev
