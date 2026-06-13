import E213.Lib.Math.NumberTheory.ModArith.ZolotarevCycle
import E213.Lib.Math.NumberTheory.ModArith.ZolotarevMuBridge

/-!
# DiscreteLogParity — the quadratic character IS the discrete-log parity

Euler's criterion, read on the powers of a primitive root, dissolves the
quadratic character into one bit: the parity of the discrete logarithm.  For a
primitive root `g` mod a prime `p` (`ordModP g p = p − 1`, `2m = p − 1`):

  * ★★★★★ `qr_pow_iff_even_exp` — `QR(g^k % p) ⟺ 2 ∣ k`.  A power `g^k` is a
    quadratic residue **exactly when its exponent is even**.

A square sits at an even position in the single orbit `⟨g⟩`; a non-residue at an
odd one.  So the Legendre symbol `(a/p)` is `(−1)^{dlog_g a}` — the count-Lens
parity of the discrete logarithm (`seed/AXIOM/06_lens_readings.md` §6.7), not an
external residue/non-residue predicate stapled onto the units.

Because the primitive root generates, the discrete log is defined on *every*
unit (`dlog_exists`: the discrete-log list `tau` is a permutation of the
residues), giving the per-unit and fully-internal forms:

  * ★★★★★ `qr_iff_even_dlog` — for a unit `a`, `∃ k, a = g^k % p ∧ (QR(a) ⟺ 2 ∣ k)`.
  * `qr_iff_even_dlog_exists` — the same with the primitive root produced by
    `exists_primitive_root`, so the statement quantifies only over the unit `a`.

This makes "the quadratic character is a discrete-log parity"
(`theory/essays/synthesis/the_quadratic_character_is_a_discrete_log_parity.md`)
a theorem rather than a reading, tying `exists_primitive_root` to Euler's
criterion `qr_iff_pow_one`.  `2 ∣ k` is the count-Lens of the orbit position read
`mod 2` — the `(−1)^k` of the essay.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.DiscreteLogParity

open E213.Lib.Math.NumberTheory.ModArith.MulOrder (ordModP ord_dvd pow_ord)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (pow_mul_loc)
open E213.Lib.Math.NumberTheory.ModArith.OrderPow (not_dvd_pow)
open E213.Lib.Math.NumberTheory.ModArith.PrimitiveRoot (exists_primitive_root)
open E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative (qr_iff_pow_one)
open E213.Lib.Math.NumberTheory.ModArith.ZolotarevCycle
  (tau tauFun tau_mem_perms tauFun_zero tauFun_succ not_dvd_g)
open E213.Lib.Math.Algebra.Linalg213
open E213.Lib.Math.Algebra.Linalg213.Permutation (iota perms)
open E213.Lib.Math.Algebra.Linalg213.PermClosure (permsOf_sound mem_map')
open E213.Lib.Math.Algebra.Linalg213.Laplace (mem_iota_of_lt)
open E213.Lib.Math.NumberTheory.ModArith.ZolotarevMuBridge (zolotarev_mu)
open E213.Lib.Math.NumberTheory.ModArith.ZolotarevSign (mulPermMod)
open E213.Lib.Math.Algebra.Linalg213.Permutation (psign)
open E213.Meta.Nat.ModPow213 (pow_mod_base)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)

/-! ## §0 — `g^j ≡ 1` is exactly `ord g ∣ j`, and the half-order divisibility -/

/-- Converse of `ord_dvd`: `ord g ∣ j ⟹ g^j ≡ 1 (mod p)`.  `j = ord·c`, so
    `g^j = (g^ord)^c ≡ 1^c = 1`. -/
theorem pow_dvd_one (g p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hg0 : 0 < g) (hglt : g < p) (j : Nat) (hj : ordModP g p ∣ j) : g ^ j % p = 1 := by
  obtain ⟨c, rfl⟩ := hj
  rw [pow_mul_loc g (ordModP g p) c, pow_mod_base (g ^ ordModP g p) p c,
      pow_ord g p hp hpr hg0 hglt, Nat.one_pow]
  exact Nat.mod_eq_of_lt hp

/-- `g^j ≡ 1 (mod p) ⟺ ord g ∣ j` — the fixing exponents are exactly the
    multiples of the order. -/
theorem pow_one_iff_ord_dvd (g p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hg0 : 0 < g) (hglt : g < p) (j : Nat) : g ^ j % p = 1 ↔ ordModP g p ∣ j :=
  ⟨ord_dvd g p hp hpr hg0 hglt j, pow_dvd_one g p hp hpr hg0 hglt j⟩

/-- `2m ∣ km ⟺ 2 ∣ k` (cancel the positive `m`) — the half-order divisibility
    collapses to a parity of the exponent. -/
theorem two_mul_dvd_iff (m k : Nat) (hm : 0 < m) : 2 * m ∣ k * m ↔ 2 ∣ k := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := h
    have e : m * k = m * (2 * d) := by rw [Nat.mul_comm m k, hd]; ring_nat
    exact ⟨d, Nat.eq_of_mul_eq_mul_left hm e⟩
  · intro h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [hc]; ring_nat⟩

/-! ## §1 — the parity core: `QR(g^k) ⟺ 2 ∣ k` -/

/-- ★★★★★ **The quadratic character is the discrete-log parity.**  For a prime `p`
    (`2m = p − 1`) and a primitive root `g` (`ordModP g p = p − 1`):

      `g^k` is a quadratic residue mod `p`  ⟺  `2 ∣ k`.

    Euler's criterion (`qr_iff_pow_one`) reads `QR(g^k)` as `(g^k)^m ≡ 1`; with
    `(g^k)^m = g^{km}` and `g^{km} ≡ 1 ⟺ ord g ∣ km ⟺ (2m) ∣ km ⟺ 2 ∣ k`, the
    quadratic character collapses to the mod-2 readout of the exponent — even
    positions in the orbit `⟨g⟩` are the squares. -/
theorem qr_pow_iff_even_exp (p m g : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (hg1 : 1 ≤ g) (hgle : g ≤ p - 1)
    (hord : ordModP g p = p - 1) (k : Nat) :
    (∃ x : Nat, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = g ^ k % p) ↔ 2 ∣ k := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hglt : g < p := Nat.lt_of_le_of_lt hgle (Nat.sub_lt hppos Nat.zero_lt_one)
  have hnpg : ¬ p ∣ g := not_dvd_g g p hg1 hglt
  have hnpgk : ¬ p ∣ g ^ k := not_dvd_pow g p k hp hpr hnpg
  have ha1 : 1 ≤ g ^ k % p := Nat.pos_of_ne_zero (fun h0 => hnpgk (dvd_of_mod_eq_zero h0))
  have halt : g ^ k % p < p := Nat.mod_lt _ hppos
  -- `(g^k % p)^m % p = g^{km} % p` (pure Eq, propext-free)
  have hval : (g ^ k % p) ^ m % p = g ^ (k * m) % p := by
    rw [← pow_mod_base (g ^ k) p m, ← pow_mul_loc g k m]
  -- chain of Iffs (no `rw`-with-Iff, to stay propext-clean)
  calc (∃ x : Nat, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = g ^ k % p)
      ↔ (g ^ k % p) ^ m % p = 1 := qr_iff_pow_one p m (g ^ k % p) hp hpr h2m hm1 ha1 halt
    _ ↔ g ^ (k * m) % p = 1 := by rw [hval]
    _ ↔ ordModP g p ∣ (k * m) := pow_one_iff_ord_dvd g p hp hpr hg1 hglt (k * m)
    _ ↔ (p - 1) ∣ (k * m) := by rw [hord]
    _ ↔ 2 * m ∣ (k * m) := by rw [← h2m]
    _ ↔ 2 ∣ k := two_mul_dvd_iff m k hm1

/-! ## §2 — the discrete log is defined on every unit -/

/-- **The discrete log exists.**  A primitive root generates: every unit
    `1 ≤ a < p` is `g^k % p` for some `k`.  The discrete-log list `tau g p` is a
    permutation of the residues (`tau_mem_perms`), so `a`, lying in the residues,
    is one of its values `tauFun g p i = g^(p−1−i) % p`. -/
theorem dlog_exists (p g a : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hg0 : 0 < g) (hglt : g < p) (hord : ordModP g p = p - 1)
    (ha1 : 1 ≤ a) (halt : a < p) : ∃ k, g ^ k % p = a := by
  have htau : tau g p ∈ perms p := tau_mem_perms g p hp hpr hg0 hglt hord
  have hlp : Permutation.LPerm (iota p) (tau g p) :=
    Permutation.LPerm.symm (permsOf_sound (iota p) (tau g p) htau)
  have hain : a ∈ iota p := mem_iota_of_lt halt
  have hatau : a ∈ tau g p := PermClosure.LPerm.mem hlp hain
  have hatau2 : a ∈ (iota p).map (tauFun g p) := hatau
  obtain ⟨i, _, hival⟩ := mem_map' (tauFun g p) hatau2
  cases i with
  | zero =>
    rw [tauFun_zero] at hival
    exact absurd hival.symm (Nat.not_eq_zero_of_lt ha1)
  | succ i' =>
    rw [tauFun_succ] at hival
    exact ⟨p - 1 - (i' + 1), hival⟩

/-! ## §3 — the per-unit and fully-internal forms -/

/-- ★★★★★ **`(a/p) = (−1)^{dlog_g a}`, per unit.**  For a unit `a` and a primitive
    root `g`, there is a discrete log `k` (`a = g^k % p`) whose parity is the
    quadratic character: `a` is a QR ⟺ `2 ∣ k`. -/
theorem qr_iff_even_dlog (p m g a : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (hg1 : 1 ≤ g) (hgle : g ≤ p - 1)
    (hord : ordModP g p = p - 1) (ha1 : 1 ≤ a) (halt : a < p) :
    ∃ k, a = g ^ k % p ∧
      ((∃ x : Nat, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = a) ↔ 2 ∣ k) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hglt : g < p := Nat.lt_of_le_of_lt hgle (Nat.sub_lt hppos Nat.zero_lt_one)
  obtain ⟨k, hk⟩ := dlog_exists p g a hp hpr hg1 hglt hord ha1 halt
  refine ⟨k, hk.symm, ?_⟩
  rw [← hk]
  exact qr_pow_iff_even_exp p m g hp hpr h2m hm1 hg1 hgle hord k

/-- **Fully internal form.**  For every unit `a`, a primitive root `g`
    (`exists_primitive_root`) and a discrete log `k` exist with `a = g^k % p` and
    `a` a QR ⟺ `2 ∣ k` — the quadratic character is the orbit-position parity,
    with no residue/non-residue predicate imported from outside the units. -/
theorem qr_iff_even_dlog_exists (p m a : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (ha1 : 1 ≤ a) (halt : a < p) :
    ∃ g k, (1 ≤ g ∧ g ≤ p - 1 ∧ ordModP g p = p - 1) ∧ a = g ^ k % p ∧
      ((∃ x : Nat, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = a) ↔ 2 ∣ k) := by
  obtain ⟨g, hg1, hgle, hord⟩ := exists_primitive_root p hp hpr
  obtain ⟨k, hak, hiff⟩ := qr_iff_even_dlog p m g a hp hpr h2m hm1 hg1 hgle hord ha1 halt
  exact ⟨g, k, ⟨hg1, hgle, hord⟩, hak, hiff⟩

/-! ## §4 — the permutation-sign face: `psign σ_a = (−1)^{dlog}`

`zolotarev_mu` pins the multiply-by-`a` permutation sign to the quadratic
character for *every* odd prime (`psign σ_a = 1 ⟺ QR(a)`).  Composing it with the
discrete-log parity above gives the sign as the exponent parity directly — the
permutation-sign readout of `the_quadratic_character_is_a_discrete_log_parity.md`
made a theorem alongside the Euler readout. -/

/-- ★★★★★ **Permutation sign = discrete-log parity.**  For a primitive root `g`,
    the sign of multiply-by-`g^k` is `+1` exactly when the exponent is even:
    `psign σ_{g^k} = 1 ⟺ 2 ∣ k`.  (`zolotarev_mu` ∘ `qr_pow_iff_even_exp`.) -/
theorem psign_pow_iff_even_exp (p m g : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (hg1 : 1 ≤ g) (hgle : g ≤ p - 1)
    (hord : ordModP g p = p - 1) (k : Nat) :
    psign (mulPermMod (g ^ k % p) p) = 1 ↔ 2 ∣ k := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hglt : g < p := Nat.lt_of_le_of_lt hgle (Nat.sub_lt hppos Nat.zero_lt_one)
  have hnpgk : ¬ p ∣ g ^ k := not_dvd_pow g p k hp hpr (not_dvd_g g p hg1 hglt)
  have ha1 : 1 ≤ g ^ k % p := Nat.pos_of_ne_zero (fun h0 => hnpgk (dvd_of_mod_eq_zero h0))
  have halt : g ^ k % p < p := Nat.mod_lt _ hppos
  exact (zolotarev_mu (g ^ k % p) p m hp hpr h2m hm1 ha1 halt).trans
    (qr_pow_iff_even_exp p m g hp hpr h2m hm1 hg1 hgle hord k)

/-- **Permutation-sign face, per unit.**  For every unit `a`, a primitive root `g`
    and discrete log `k` (`a = g^k % p`) exist with `psign σ_a = 1 ⟺ 2 ∣ k` —
    the `psign`/Euler/discrete-log readouts of one bit `k mod 2`, all theorems. -/
theorem psign_iff_even_dlog_exists (p m a : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (ha1 : 1 ≤ a) (halt : a < p) :
    ∃ g k, (1 ≤ g ∧ g ≤ p - 1 ∧ ordModP g p = p - 1) ∧ a = g ^ k % p ∧
      (psign (mulPermMod a p) = 1 ↔ 2 ∣ k) := by
  obtain ⟨g, hg1, hgle, hord⟩ := exists_primitive_root p hp hpr
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hglt : g < p := Nat.lt_of_le_of_lt hgle (Nat.sub_lt hppos Nat.zero_lt_one)
  obtain ⟨k, hak⟩ := dlog_exists p g a hp hpr hg1 hglt hord ha1 halt
  refine ⟨g, k, ⟨hg1, hgle, hord⟩, hak.symm, ?_⟩
  rw [← hak]
  exact psign_pow_iff_even_exp p m g hp hpr h2m hm1 hg1 hgle hord k

end E213.Lib.Math.NumberTheory.ModArith.DiscreteLogParity
