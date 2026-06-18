import E213.Lib.Math.NumberTheory.WilsonGeneralization

/-!
# Wilson `−1` value direction (∅-axiom scratch)

`∏(units of ℤ/n) ≡ −1 (mod n)` when the only square roots of `1` are `±1`.
-/

namespace E213.Lib.Math.NumberTheory.WilsonValue

open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.NumberTheory.EulerTheorem
  (totativeList totativeList_coprime totativeList_pos totativeList_le nodup_totativeList
   mem_totListUpto totative_lt_n prodMod_lt)
open E213.Lib.Math.NumberTheory.ModArith.WilsonTheorem
  (prodMod prodMod_cons eraseV memV noDupV beqN beqN_refl eq_of_beqN beqN_of_eq
   orB_elim orB_inl orB_inr andB_elim memV_cons memV_cons_self memV_of_cons_ne
   prodMod_eraseV length_eraseV_lt memV_of_memV_eraseV memV_eraseV_of_ne
   noDupV_eraseV bnotin_eraseV_self)
open E213.Lib.Math.NumberTheory.WilsonGeneralization
  (selfInverse selfInvB selfInvB_iff selfFilter selfFilter_cons_true selfFilter_cons_false
   units_prod_eq_selfinv_prod unitInv mem_of_memV memV_of_mem noDupV_of_nodup)

/-! ## §1 — `1` and `n−1` are self-inverse units `< n` -/

/-- `1` is a self-inverse unit `< n` (for `1 < n`). -/
theorem one_self_inverse {n : Nat} (hn : 1 < n) :
    gcd213 1 n = 1 ∧ 0 < 1 ∧ (1 : Nat) < n ∧ selfInverse n 1 := by
  refine ⟨E213.Meta.Nat.Gcd213.gcd213_one_left n, by decide, hn, ?_⟩
  show (1 * 1) % n = 1 % n
  rw [Nat.one_mul]

/-- `n − 1` is a self-inverse unit `< n` (for `1 < n`).  Stated with `n = m + 2`
    so `n − 1 = m + 1` is subtraction-free. -/
theorem pred_self_inverse {m : Nat} :
    gcd213 (m + 1) (m + 2) = 1 ∧ 0 < (m + 1) ∧ (m + 1) < (m + 2)
      ∧ selfInverse (m + 2) (m + 1) := by
  refine ⟨?_, Nat.succ_pos m, Nat.lt_succ_self _, ?_⟩
  · -- gcd (m+1) (m+2) = 1 via gcd_succ_self + comm
    have h := E213.Meta.Nat.Gcd213.gcd213_succ_self (m + 1)  -- gcd (m+2) (m+1) = 1
    exact (E213.Meta.Nat.Gcd213.gcd213_comm (m + 1) (m + 2)).trans h
  · -- ((m+1)*(m+1)) % (m+2) = 1 % (m+2)
    show ((m + 1) * (m + 1)) % (m + 2) = 1 % (m + 2)
    -- key identity: (m+1)*(m+1) + (m+2) = 1 + (m+1)*(m+2)
    have hid : (m + 1) * (m + 1) + (m + 2) = 1 + (m + 1) * (m + 2) := by ring_nat
    -- ((m+1)*(m+1)) % (m+2) = ((m+1)*(m+1) + 1*(m+2)) % (m+2)
    have h1 : ((m + 1) * (m + 1) + 1 * (m + 2)) % (m + 2) = ((m + 1) * (m + 1)) % (m + 2) :=
      E213.Tactic.NatHelper.add_mul_mod_self_pure ((m + 1) * (m + 1)) (m + 2) 1
    have h1' : (m + 1) * (m + 1) + 1 * (m + 2) = (m + 1) * (m + 1) + (m + 2) := by
      rw [Nat.one_mul]
    rw [h1'] at h1
    -- (1 + (m+1)*(m+2)) % (m+2) = 1 % (m+2)
    have h2 : (1 + (m + 1) * (m + 2)) % (m + 2) = 1 % (m + 2) :=
      E213.Tactic.NatHelper.add_mul_mod_self_pure 1 (m + 2) (m + 1)
    rw [← h1, hid, h2]

/-! ## §2 — `selfFilter` membership characterization -/

/-- A member of `selfFilter n l` is a member of `l`. -/
theorem mem_of_mem_selfFilter {n x : Nat} :
    ∀ {l : List Nat}, x ∈ selfFilter n l → x ∈ l
  | [], h => by exact absurd h (by intro hh; nomatch hh)
  | a :: l, h => by
    cases hsa : selfInvB n a with
    | true =>
      rw [selfFilter_cons_true hsa] at h
      cases h with
      | head => exact List.Mem.head _
      | tail _ h' => exact List.Mem.tail _ (mem_of_mem_selfFilter h')
    | false =>
      rw [selfFilter_cons_false hsa] at h
      exact List.Mem.tail _ (mem_of_mem_selfFilter h)

/-- A member of `selfFilter n l` is self-inverse. -/
theorem selfInv_of_mem_selfFilter {n x : Nat} :
    ∀ {l : List Nat}, x ∈ selfFilter n l → selfInverse n x
  | [], h => by exact absurd h (by intro hh; nomatch hh)
  | a :: l, h => by
    cases hsa : selfInvB n a with
    | true =>
      rw [selfFilter_cons_true hsa] at h
      cases h with
      | head => exact eq_of_beqN hsa
      | tail _ h' => exact selfInv_of_mem_selfFilter h'
    | false =>
      rw [selfFilter_cons_false hsa] at h
      exact selfInv_of_mem_selfFilter h

/-- A self-inverse member of `l` is a member of `selfFilter n l`. -/
theorem mem_selfFilter_of_selfInv {n x : Nat} (hs : selfInvB n x = true) :
    ∀ {l : List Nat}, x ∈ l → x ∈ selfFilter n l
  | a :: l, h => by
    cases hsa : selfInvB n a with
    | true =>
      rw [selfFilter_cons_true hsa]
      cases h with
      | head => exact List.Mem.head _
      | tail _ h' => exact List.Mem.tail _ (mem_selfFilter_of_selfInv hs h')
    | false =>
      cases h with
      | head =>
        rw [hs] at hsa; exact absurd hsa (by decide)
      | tail _ h' =>
        rw [selfFilter_cons_false hsa]
        exact mem_selfFilter_of_selfInv hs h'

/-! ## §3 — a NoDup list whose members are exactly `{1, n−1}` has `prodMod ≡ n−1` -/

/-- A list with no boolean members is `nil`. -/
theorem nil_of_no_memV : ∀ {l : List Nat}, (∀ x, memV x l = false) → l = []
  | [], _ => rfl
  | a :: l, h => by
    have hh : memV a (a :: l) = false := h a
    rw [memV_cons, beqN_refl a, Bool.true_or] at hh
    exact absurd hh (by decide)

/-- `selfFilter` preserves boolean NoDup (it only drops elements). -/
theorem noDupV_selfFilter {n : Nat} :
    ∀ {l : List Nat}, noDupV l = true → noDupV (selfFilter n l) = true
  | [], h => h
  | a :: l, h => by
    have hpair := andB_elim h
    have ha_notin : memV a l = false := by
      have hnm : (!memV a l) = true := hpair.1
      cases hcase : memV a l with
      | false => rfl
      | true => rw [hcase] at hnm; exact absurd hnm (by decide)
    have hndl : noDupV l = true := hpair.2
    cases hsa : selfInvB n a with
    | true =>
      rw [selfFilter_cons_true hsa]
      show ((!memV a (selfFilter n l)) && noDupV (selfFilter n l)) = true
      have ha_sf : memV a (selfFilter n l) = false := by
        cases hcase : memV a (selfFilter n l) with
        | false => rfl
        | true =>
          have hin : a ∈ l := mem_of_mem_selfFilter (mem_of_memV hcase)
          have : memV a l = true := memV_of_mem hin
          rw [this] at ha_notin; exact absurd ha_notin (by decide)
      rw [ha_sf]
      show (true && noDupV (selfFilter n l)) = true
      rw [noDupV_selfFilter hndl]; rfl
    | false =>
      rw [selfFilter_cons_false hsa]
      exact noDupV_selfFilter hndl

/-- ★ **Two-membered prodMod.**  For `1 < n`, a NoDup list `p` whose members are
    exactly `{1, n−1}` (with `1 ≠ n−1`) has `prodMod n p = (n−1) % n`. -/
theorem prodMod_two_membered {n : Nat} {p : List Nat} (hn : 1 < n)
    (hL : noDupV p = true)
    (hone : memV 1 p = true)
    (hpred : memV (n - 1) p = true)
    (hne : beqN 1 (n - 1) = false)
    (hall : ∀ x, memV x p = true → x = 1 ∨ x = n - 1) :
    prodMod n p = (n - 1) % n := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hn)
  have hstep1 : prodMod n p = (1 * prodMod n (eraseV 1 p)) % n := prodMod_eraseV hone
  have hpred_ne : beqN (n - 1) 1 = false := by
    cases hcase : beqN (n - 1) 1 with
    | false => rfl
    | true =>
      have hh : (1 : Nat) = n - 1 := (eq_of_beqN hcase).symm
      rw [beqN_of_eq hh] at hne; exact absurd hne (by decide)
  have hpred1 : memV (n - 1) (eraseV 1 p) = true :=
    memV_eraseV_of_ne hL hpred hpred_ne
  have hnd1 : noDupV (eraseV 1 p) = true := noDupV_eraseV hL
  have hstep2 : prodMod n (eraseV 1 p)
      = ((n - 1) * prodMod n (eraseV (n - 1) (eraseV 1 p))) % n :=
    prodMod_eraseV hpred1
  have hnil : eraseV (n - 1) (eraseV 1 p) = [] := by
    apply nil_of_no_memV
    intro x
    cases hx : memV x (eraseV (n - 1) (eraseV 1 p)) with
    | false => rfl
    | true =>
      exfalso
      have hx1 : memV x (eraseV 1 p) = true := memV_of_memV_eraseV hx
      have hxp : memV x p = true := memV_of_memV_eraseV hx1
      rcases hall x hxp with h1 | hpr
      · rw [h1] at hx1
        exact bnotin_eraseV_self hL hone hx1
      · rw [hpr] at hx
        exact bnotin_eraseV_self hnd1 hpred1 hx
  rw [hnil] at hstep2
  have hprodnil : prodMod n ([] : List Nat) = 1 % n := rfl
  rw [hprodnil] at hstep2
  rw [hstep1, hstep2]
  rw [Nat.one_mul]
  have h1n : (1 : Nat) % n = 1 := Nat.mod_eq_of_lt hn
  rw [h1n, Nat.mul_one]
  rw [E213.Meta.Nat.AddMod213.mod_mod]

/-! ## §4 — ★★★ the `−1` value theorem under square-root-triviality -/

/-- ★★★ **Wilson `−1` under trivial square roots of `1`.**  For `2 < n`, if the
    only solutions of `u² ≡ 1 (mod n)` among units `u < n` are `1` and `n−1`,
    then `∏(units of ℤ/n) ≡ n−1 ≡ −1 (mod n)`. -/
theorem wilson_neg_one_of_sqrt_trivial (n : Nat) (hn : 2 < n)
    (htriv : ∀ u, u < n → 0 < u → (u * u) % n = 1 % n → u = 1 ∨ u = n - 1) :
    prodMod n (totativeList n) % n = (n - 1) % n := by
  have hn1 : 1 < n := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hn)
  have hred : prodMod n (totativeList n) = prodMod n (selfFilter n (totativeList n)) :=
    units_prod_eq_selfinv_prod hn1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, (E213.Tactic.NatHelper.sub_add_cancel hn).symm⟩
  have hn1eq : (m + 3) - 1 = m + 2 := rfl
  have hpred := pred_self_inverse (m := m + 1)
  have hpred_co : gcd213 (m + 2) (m + 3) = 1 := hpred.1
  have hpred_self : selfInverse (m + 3) (m + 2) := hpred.2.2.2
  have hone := one_self_inverse (n := m + 3) hn1
  have hone_tot : 1 ∈ totativeList (m + 3) :=
    mem_totListUpto.mpr ⟨Nat.le_refl 1, Nat.succ_le_succ (Nat.zero_le _), hone.1⟩
  have hpred_tot : (m + 2) ∈ totativeList (m + 3) :=
    mem_totListUpto.mpr
      ⟨Nat.succ_pos (m + 1), Nat.le_of_lt (Nat.lt_succ_self _), hpred_co⟩
  have hone_b : selfInvB (m + 3) 1 = true := beqN_of_eq hone.2.2.2
  have hpred_b : selfInvB (m + 3) (m + 2) = true := beqN_of_eq hpred_self
  have hone_sf : memV 1 (selfFilter (m + 3) (totativeList (m + 3))) = true :=
    memV_of_mem (mem_selfFilter_of_selfInv hone_b hone_tot)
  have hpred_sf : memV (m + 2) (selfFilter (m + 3) (totativeList (m + 3))) = true :=
    memV_of_mem (mem_selfFilter_of_selfInv hpred_b hpred_tot)
  have hsf_nd : noDupV (selfFilter (m + 3) (totativeList (m + 3))) = true :=
    noDupV_selfFilter (noDupV_of_nodup (nodup_totativeList (m + 3)))
  have hne : beqN 1 ((m + 3) - 1) = false := by rw [hn1eq]; rfl
  have hall : ∀ x, memV x (selfFilter (m + 3) (totativeList (m + 3))) = true →
      x = 1 ∨ x = (m + 3) - 1 := by
    intro x hx
    have hxm : x ∈ selfFilter (m + 3) (totativeList (m + 3)) := mem_of_memV hx
    have hx_tot : x ∈ totativeList (m + 3) := mem_of_mem_selfFilter hxm
    have hx_self : selfInverse (m + 3) x := selfInv_of_mem_selfFilter hxm
    have hx_co : gcd213 x (m + 3) = 1 := totativeList_coprime hx_tot
    have hx_pos : 0 < x := totativeList_pos hx_tot
    have hx_lt : x < m + 3 :=
      totative_lt_n hn1 hx_co (totativeList_pos hx_tot) (totativeList_le hx_tot)
    exact htriv x hx_lt hx_pos hx_self
  have hcompute : prodMod (m + 3) (selfFilter (m + 3) (totativeList (m + 3)))
      = ((m + 3) - 1) % (m + 3) := by
    have hpred_sf' : memV ((m + 3) - 1) (selfFilter (m + 3) (totativeList (m + 3))) = true := by
      rw [hn1eq]; exact hpred_sf
    exact prodMod_two_membered hn1 hsf_nd hone_sf hpred_sf' hne hall
  rw [hred, hcompute]
  rw [E213.Meta.Nat.AddMod213.mod_mod]

/-! ## §5 — prime recovery: a prime modulus satisfies the trivial-square-root hypothesis -/

open E213.Meta.Nat.VpMul (IsPrime213)
open E213.Lib.Math.NumberTheory.ModArith.WilsonInverse (self_inverse)

/-- A prime `p` satisfies `htriv`: every unit `u < p` with `u² ≡ 1` is `1` or `p−1`. -/
theorem prime_sqrt_trivial {p : Nat} (hp : IsPrime213 p) :
    ∀ u, u < p → 0 < u → (u * u) % p = 1 % p → u = 1 ∨ u = p - 1 := by
  intro u hult hupos hself
  rcases self_inverse hp hupos hult hself with h1 | hpred
  · exact Or.inl h1
  · right
    have hh : p - 1 = u := by
      rw [← hpred]; show (u + 1) - 1 = u; rfl
    exact hh.symm

/-- ★ **Wilson for a prime (the `−1` value).**  For prime `p` with `2 < p`,
    `∏(units of ℤ/p) ≡ p − 1 ≡ −1 (mod p)`. -/
theorem wilson_prime_neg_one {p : Nat} (hp : IsPrime213 p) (hp2 : 2 < p) :
    prodMod p (totativeList p) % p = (p - 1) % p :=
  wilson_neg_one_of_sqrt_trivial p hp2 (prime_sqrt_trivial hp)

/-! ## §6 — smokes -/

/-- **n = 4**: units `{3, 1}`, both self-inverse (`3² = 9 ≡ 1 mod 4`); product
    `3 ≡ −1 (mod 4)`.  Direct computation (`htriv` holds: roots of `1` are `{1,3}`). -/
theorem neg_one_smoke_4 :
    prodMod 4 (totativeList 4) % 4 = (4 - 1) % 4 ∧
    totativeList 4 = [3, 1] ∧
    prodMod 4 (totativeList 4) = 3 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **n = 8** (non-example): units `{7,5,3,1}` are **all** self-inverse, so `htriv`
    FAILS (`3² ≡ 1` yet `3 ∉ {1,7}`).  The theorem correctly does not apply:
    `∏ units = 105 ≡ 1 (mod 8) ≠ −1`. -/
theorem neg_one_nonexample_8 :
    prodMod 8 (totativeList 8) = 1 ∧
    (3 * 3) % 8 = 1 % 8 ∧ (3 : Nat) ≠ 1 ∧ (3 : Nat) ≠ 8 - 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end E213.Lib.Math.NumberTheory.WilsonValue
