import E213.Lib.Math.NumberTheory.WilsonGeneralization
import E213.Lib.Math.NumberTheory.WilsonValue

/-!
# Wilson `+1` direction (∅-axiom scratch)

If there is a square root of `1` other than `±1`, then `∏(units of ℤ/n) ≡ +1 (mod n)`.

Proof via the **pairing-accumulation** lemma `prodMod_pair_accum`:
`prodMod n L ≡ t^(|L|/2)` for any nontrivial `t ∈ S`, applied to `L = S` (the
self-inverse units = square roots of `1`).  Then a parity argument on `k = |S|/2`
using two distinct nontrivial roots `n-1` and `x` forces `k` even, so `t^k ≡ 1`.

No group theory — explicit `% n` bookkeeping mirroring
`WilsonGeneralization.prodMod_pairing_selfinv_fuel`.
-/

namespace E213.Lib.Math.NumberTheory.WilsonPlusOne

open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.NumberTheory.EulerTheorem
  (totativeList totativeList_coprime totativeList_pos totativeList_le nodup_totativeList
   mem_totListUpto totative_lt_n prodMod_lt cancel_unit)
open E213.Lib.Math.NumberTheory.ModArith.WilsonTheorem
  (prodMod prodMod_cons eraseV memV noDupV beqN beqN_refl eq_of_beqN beqN_of_eq
   orB_elim orB_inl orB_inr andB_elim memV_cons memV_cons_self memV_of_cons_ne
   prodMod_eraseV length_eraseV_lt memV_of_memV_eraseV memV_eraseV_of_ne
   noDupV_eraseV bnotin_eraseV_self)
open E213.Lib.Math.NumberTheory.WilsonGeneralization
  (selfInverse selfInvB selfInvB_iff selfFilter selfFilter_cons_true selfFilter_cons_false
   units_prod_eq_selfinv_prod unitInv mem_of_memV memV_of_mem noDupV_of_nodup)
open E213.Lib.Math.NumberTheory.WilsonValue
  (one_self_inverse pred_self_inverse mem_of_mem_selfFilter selfInv_of_mem_selfFilter
   mem_selfFilter_of_selfInv noDupV_selfFilter)

/-! ## §0 — small list/arithmetic helpers -/

/-- Exact length after erasing a present element: `(eraseV x l).length + 1 = l.length`. -/
theorem length_eraseV_eq {x : Nat} :
    ∀ {l : List Nat}, memV x l = true → (eraseV x l).length + 1 = l.length
  | [], h => by exact absurd h Bool.false_ne_true
  | a :: l, h => by
    show (match beqN a x with | true => l | false => a :: eraseV x l).length + 1 = l.length + 1
    cases hb : beqN a x with
    | true =>
      show l.length + 1 = l.length + 1
      rfl
    | false =>
      show (a :: eraseV x l).length + 1 = l.length + 1
      show ((eraseV x l).length + 1) + 1 = l.length + 1
      have hmem : memV x l = true := by
        rcases orB_elim h with h1 | h2
        · rw [hb] at h1; exact absurd h1 Bool.false_ne_true
        · exact h2
      rw [length_eraseV_eq hmem]

/-! ## §0b — the σ_t map is an involution on `[0,n)` and t-cancellative -/

/-- σ_t is an involution on residues `< n`: `(((s*t)%n)*t)%n = s` when `(t*t)%n = 1%n`
    and `s < n`. -/
theorem sigt_invol {n s t : Nat} (hn : 1 < n) (ht : (t * t) % n = 1 % n) (hslt : s < n) :
    (((s * t) % n) * t) % n = s := by
  -- (((s*t)%n)*t)%n = ((s*t)*t)%n = (s*(t*t))%n = (s*(1%n))%n = (s*1)%n = s%n = s
  rw [← E213.Meta.Nat.MulMod213.mul_mod_left_pure (s * t) t n,
      E213.Tactic.NatHelper.mul_assoc s t t,
      E213.Meta.Nat.MulMod213.mul_mod_right_pure s (t * t) n, ht,
      ← E213.Meta.Nat.MulMod213.mul_mod_right_pure s 1 n, Nat.mul_one,
      Nat.mod_eq_of_lt hslt]

/-- σ_t is injective on `[0,n)`: `(x*t)%n = (y*t)%n ⟹ x = y` for a unit `t`,
    `x,y < n`. -/
theorem sigt_inj {n t x y : Nat} (hn : 1 < n) (ht : gcd213 t n = 1)
    (heq : (x * t) % n = (y * t) % n) (hxlt : x < n) (hylt : y < n) : x = y := by
  -- commute to (t*x)%n = (t*y)%n, cancel t
  have heq' : (t * x) % n = (t * y) % n := by
    rw [Nat.mul_comm t x, Nat.mul_comm t y]; exact heq
  have hx : x % n = y := cancel_unit hn ht heq' hylt
  rw [Nat.mod_eq_of_lt hxlt] at hx; exact hx

/-! ## §1 — the pair contribution: `(s * (s*t)%n) % n = t % n` for a self-inverse `s` -/

/-- For a self-inverse `s` (`(s*s)%n = 1%n`), the pair product
    `(s · (s·t mod n)) mod n = t mod n`. -/
theorem pair_contribution {n s t : Nat} (hs : (s * s) % n = 1 % n) :
    (s * ((s * t) % n)) % n = t % n := by
  -- (s * ((s*t)%n)) % n = (s*(s*t)) % n = ((s*s)*t) % n = ((1%n)*t) % n = t % n
  rw [← E213.Meta.Nat.MulMod213.mul_mod_right_pure s (s * t) n,
      ← E213.Tactic.NatHelper.mul_assoc s s t,
      E213.Meta.Nat.MulMod213.mul_mod_left_pure (s * s) t n, hs,
      ← E213.Meta.Nat.MulMod213.mul_mod_left_pure 1 t n, Nat.one_mul]

/-! ## §2 — ★★ the pairing-accumulation crux -/

/-- ★★ **Pairing-accumulation (fuel-bounded).**  For a fixed nontrivial self-inverse
    unit `t` (`t < n`, `gcd t n = 1`, `t ≠ 1`, `(t*t)%n = 1%n`) and a list `L` that is
    NoDup, all self-inverse units `< n`, and **closed under `σ_t : s ↦ (s*t)%n`**,
    `prodMod n L % n = (t ^ (L.length / 2)) % n`.

    `σ_t` partitions `L` into fixed-point-free pairs `{s, (s*t)%n}` (distinct since
    `s = (s*t)%n ⟹ t ≡ 1`); each pair contributes a factor `t` (`pair_contribution`,
    using `s` self-inverse).  Fuel recursion mirroring
    `WilsonGeneralization.prodMod_pairing_selfinv_fuel`, accumulating `t` per pair. -/
theorem prodMod_pair_accum {n t : Nat} (hn : 1 < n)
    (htlt : t < n) (htco : gcd213 t n = 1) (htne : t ≠ 1) (htself : (t * t) % n = 1 % n) :
    ∀ (fuel : Nat) (L : List Nat), L.length ≤ fuel →
      noDupV L = true →
      (∀ x, memV x L = true → gcd213 x n = 1 ∧ x < n ∧ (x * x) % n = 1 % n) →
      (∀ x, memV x L = true → memV ((x * t) % n) L = true) →
      prodMod n L % n = (t ^ (L.length / 2)) % n
  | _, [], _, _, _, _ => by
      show prodMod n ([] : List Nat) % n = (t ^ (0 / 2)) % n
      show (1 % n) % n = (t ^ 0) % n
      rw [E213.Meta.Nat.AddMod213.mod_mod]; rfl
  | 0, a :: l, hlen, _, _, _ => by
      exact absurd hlen (Nat.not_succ_le_zero l.length)
  | fuel + 1, a :: l, hlen, hnd, hunit, hclosed => by
    have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hn)
    have hamem : memV a (a :: l) = true := memV_cons_self a l
    obtain ⟨ha_co, ha_lt, ha_self⟩ := hunit a hamem
    have hndl : noDupV l = true := (andB_elim hnd).2
    have hlen_l : l.length ≤ fuel := Nat.le_of_succ_le_succ hlen
    have ha_notin_l : memV a l = false := by
      have hnm : (!memV a l) = true := (andB_elim hnd).1
      cases hcase : memV a l with
      | false => rfl
      | true => rw [hcase] at hnm; exact absurd hnm (by decide)
    -- partner b := (a*t)%n ∈ l, b ≠ a
    have hbmem_all : memV ((a * t) % n) (a :: l) = true := hclosed a hamem
    have hba_ne : beqN a ((a * t) % n) = false := by
      cases hcase : beqN a ((a * t) % n) with
      | false => rfl
      | true =>
        exfalso
        have hab : a = (a * t) % n := eq_of_beqN hcase
        have he1 : (a * 1) % n = (a * t) % n := by
          rw [Nat.mul_one, Nat.mod_eq_of_lt ha_lt]; exact hab
        have ht1 : (1 : Nat) % n = t := cancel_unit hn ha_co he1 htlt
        rw [Nat.mod_eq_of_lt hn] at ht1
        exact htne ht1.symm
    have hbmem_l : memV ((a * t) % n) l = true := memV_of_cons_ne hbmem_all hba_ne
    -- peel a, then b from l
    have hfact : prodMod n l = ((a * t) % n * prodMod n (eraseV ((a * t) % n) l)) % n :=
      prodMod_eraseV hbmem_l
    have hpair : (a * ((a * t) % n)) % n = t % n := pair_contribution ha_self
    have hstep : prodMod n (a :: l) % n
        = (t * prodMod n (eraseV ((a * t) % n) l)) % n := by
      rw [prodMod_cons, E213.Meta.Nat.AddMod213.mod_mod, hfact,
          ← E213.Meta.Nat.MulMod213.mul_mod_right_pure a
            ((a * t) % n * prodMod n (eraseV ((a * t) % n) l)) n,
          ← E213.Tactic.NatHelper.mul_assoc a ((a * t) % n)
            (prodMod n (eraseV ((a * t) % n) l)),
          E213.Meta.Nat.MulMod213.mul_mod_left_pure (a * ((a * t) % n))
            (prodMod n (eraseV ((a * t) % n) l)) n, hpair,
          ← E213.Meta.Nat.MulMod213.mul_mod_left_pure t
            (prodMod n (eraseV ((a * t) % n) l)) n]
    -- recurse on L' := eraseV b l
    have hnd_rest : noDupV (eraseV ((a * t) % n) l) = true := noDupV_eraseV hndl
    have hlen_rest : (eraseV ((a * t) % n) l).length ≤ fuel :=
      Nat.le_of_lt (Nat.lt_of_lt_of_le (length_eraseV_lt hbmem_l) hlen_l)
    have hunit_rest : ∀ x, memV x (eraseV ((a * t) % n) l) = true →
        gcd213 x n = 1 ∧ x < n ∧ (x * x) % n = 1 % n := by
      intro x hx
      exact hunit x (by rw [memV_cons]; exact orB_inr (memV_of_memV_eraseV hx))
    have hclosed_rest : ∀ x, memV x (eraseV ((a * t) % n) l) = true →
        memV ((x * t) % n) (eraseV ((a * t) % n) l) = true := by
      intro x hx
      have hxl : memV x l = true := memV_of_memV_eraseV hx
      have hxal : memV x (a :: l) = true := by rw [memV_cons]; exact orB_inr hxl
      obtain ⟨hx_co, hx_lt, _⟩ := hunit x hxal
      have hsx_al : memV ((x * t) % n) (a :: l) = true := hclosed x hxal
      -- σ_t(x) ≠ a : else x = σ_t(σ_t x) = σ_t(a) = b, but x ∈ eraseV b l ⟹ x ≠ b
      have hsx_ne_a : beqN a ((x * t) % n) = false := by
        cases hcase : beqN a ((x * t) % n) with
        | false => rfl
        | true =>
          exfalso
          have hax : a = (x * t) % n := eq_of_beqN hcase
          have hbx : (a * t) % n = x := by rw [hax]; exact sigt_invol hn htself hx_lt
          rw [hbx] at hx
          exact bnotin_eraseV_self hndl hxl hx
      have hsx_l : memV ((x * t) % n) l = true := memV_of_cons_ne hsx_al hsx_ne_a
      -- σ_t(x) ≠ b : else x = a (σ_t inj), but a ∉ l, x ∈ l
      have hsx_ne_b : beqN ((x * t) % n) ((a * t) % n) = false := by
        cases hcase : beqN ((x * t) % n) ((a * t) % n) with
        | false => rfl
        | true =>
          exfalso
          have heq : (x * t) % n = (a * t) % n := eq_of_beqN hcase
          have hxa : x = a := sigt_inj hn htco heq hx_lt ha_lt
          have : memV a l = true := hxa ▸ hxl
          rw [this] at ha_notin_l; exact absurd ha_notin_l (by decide)
      exact memV_eraseV_of_ne hndl hsx_l hsx_ne_b
    have hrec : prodMod n (eraseV ((a * t) % n) l) % n
        = (t ^ ((eraseV ((a * t) % n) l).length / 2)) % n :=
      prodMod_pair_accum hn htlt htco htne htself fuel (eraseV ((a * t) % n) l)
        hlen_rest hnd_rest hunit_rest hclosed_rest
    -- prodMod (a::l) % n = (t * R) % n = (t * t^(|L'|/2)) % n = t^(|L'|/2 + 1) % n
    rw [hstep, E213.Meta.Nat.MulMod213.mul_mod_right_pure t
          (prodMod n (eraseV ((a * t) % n) l)) n, hrec,
        ← E213.Meta.Nat.MulMod213.mul_mod_right_pure t
          (t ^ ((eraseV ((a * t) % n) l).length / 2)) n]
    have hpow : t * t ^ ((eraseV ((a * t) % n) l).length / 2)
        = t ^ ((eraseV ((a * t) % n) l).length / 2 + 1) := by
      rw [E213.Meta.Nat.PureNat.pow_add t ((eraseV ((a * t) % n) l).length / 2) 1,
          Nat.pow_one, Nat.mul_comm]
    rw [hpow]
    -- length: (a::l).length / 2 = (eraseV b l).length / 2 + 1
    have hlen_eq : (eraseV ((a * t) % n) l).length + 1 = l.length :=
      length_eraseV_eq hbmem_l
    have hdiv : (a :: l).length / 2 = (eraseV ((a * t) % n) l).length / 2 + 1 := by
      show (l.length + 1) / 2 = (eraseV ((a * t) % n) l).length / 2 + 1
      rw [← hlen_eq]
      show ((eraseV ((a * t) % n) l).length + 1 + 1) / 2
         = (eraseV ((a * t) % n) l).length / 2 + 1
      exact E213.Meta.Nat.NatDiv213.add_div_right_pos (n := 2) (by decide)
        (eraseV ((a * t) % n) l).length
    rw [hdiv]

/-! ## §3 — self-inverse powers split by parity -/

/-- For self-inverse `t` (`(t*t)%n = 1%n`), an **even** power is `≡ 1`:
    `(t ^ (2*j)) % n = 1 % n`. -/
theorem self_inv_pow_even {n t : Nat} (ht : (t * t) % n = 1 % n) :
    ∀ j, (t ^ (2 * j)) % n = 1 % n
  | 0 => by show (t ^ 0) % n = 1 % n; rw [Nat.pow_zero]
  | j + 1 => by
    have ih := self_inv_pow_even ht j
    -- t^(2*(j+1)) = t^(2*j + 2) = t^(2*j) * (t*t)
    rw [Nat.mul_succ,
        E213.Meta.Nat.PureNat.pow_add t (2 * j) 2]
    show (t ^ (2 * j) * t ^ 2) % n = 1 % n
    have hsq : t ^ 2 = t * t := by rw [Nat.pow_succ, Nat.pow_one]
    rw [hsq, E213.Meta.Nat.MulMod213.mul_mod_pure (t ^ (2 * j)) (t * t) n, ih, ht,
        ← E213.Meta.Nat.MulMod213.mul_mod_pure 1 1 n, Nat.one_mul]

/-- For self-inverse `t`, an **odd** power is `≡ t`:  `(t ^ (2*j+1)) % n = t % n`. -/
theorem self_inv_pow_odd {n t : Nat} (ht : (t * t) % n = 1 % n) (j : Nat) :
    (t ^ (2 * j + 1)) % n = t % n := by
  rw [E213.Meta.Nat.PureNat.pow_add t (2 * j) 1, Nat.pow_one,
      E213.Meta.Nat.MulMod213.mul_mod_left_pure (t ^ (2 * j)) t n,
      self_inv_pow_even ht j,
      ← E213.Meta.Nat.MulMod213.mul_mod_left_pure 1 t n, Nat.one_mul]

/-! ## §4 — `S = selfFilter (totativeList)` is `σ_t`-closed -/

open E213.Meta.Nat.PureNat (mul_mul_mul_comm)

/-- The product (mod `n`) of two self-inverse residues is self-inverse:
    `((s*t)%n)² ≡ 1` from `s² ≡ 1`, `t² ≡ 1`. -/
theorem mul_selfInverse {n s t : Nat}
    (hs : (s * s) % n = 1 % n) (ht : (t * t) % n = 1 % n) :
    (((s * t) % n) * ((s * t) % n)) % n = 1 % n := by
  rw [← E213.Meta.Nat.MulMod213.mul_mod_pure (s * t) (s * t) n,
      mul_mul_mul_comm s t s t,
      E213.Meta.Nat.MulMod213.mul_mod_pure (s * s) (t * t) n, hs, ht,
      ← E213.Meta.Nat.MulMod213.mul_mod_pure 1 1 n, Nat.one_mul]

/-- A self-inverse unit `v` with `0 < v < n` lies in `S = selfFilter n (totativeList n)`. -/
theorem mem_S_of_selfinv_unit {n v : Nat} (hn : 1 < n)
    (hpos : 0 < v) (hlt : v < n) (hco : gcd213 v n = 1) (hself : (v * v) % n = 1 % n) :
    memV v (selfFilter n (totativeList n)) = true := by
  have hvtot : v ∈ totativeList n :=
    mem_totListUpto.mpr ⟨hpos, Nat.le_of_lt hlt, hco⟩
  have hvb : selfInvB n v = true := beqN_of_eq hself
  exact memV_of_mem (mem_selfFilter_of_selfInv hvb hvtot)

/-- `(v * t) % n > 0` for units `v, t` (a unit is nonzero, and `gcd 0 n = n ≠ 1`). -/
theorem image_pos {n v t : Nat} (hn : 1 < n)
    (hco : gcd213 ((v * t) % n) n = 1) : 0 < (v * t) % n := by
  rcases Nat.eq_zero_or_pos ((v * t) % n) with h0 | hpos
  · exfalso
    rw [h0, E213.Meta.Nat.Gcd213.gcd213_zero_left] at hco
    rw [hco] at hn; exact absurd hn (by decide)
  · exact hpos

/-- ★ **`S` is `σ_t`-closed.**  For a self-inverse unit `t` and any self-inverse unit
    `v ∈ S` (members of `selfFilter n (totativeList n)`), `(v*t)%n ∈ S`. -/
theorem S_sigt_closed {n t : Nat} (hn : 1 < n)
    (htco : gcd213 t n = 1) (htself : (t * t) % n = 1 % n) :
    ∀ x, memV x (selfFilter n (totativeList n)) = true →
      memV ((x * t) % n) (selfFilter n (totativeList n)) = true := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hn)
  intro x hx
  have hxm : x ∈ selfFilter n (totativeList n) := mem_of_memV hx
  have hx_tot : x ∈ totativeList n := mem_of_mem_selfFilter hxm
  have hx_self : selfInverse n x := selfInv_of_mem_selfFilter hxm
  have hx_co : gcd213 x n = 1 := totativeList_coprime hx_tot
  -- (x*t)%n: unit, self-inverse, 0 < · < n
  have hco : gcd213 ((x * t) % n) n = 1 :=
    E213.Lib.Math.NumberTheory.EulerTheorem.image_coprime hnpos hx_co htco
  have hself : (((x * t) % n) * ((x * t) % n)) % n = 1 % n := mul_selfInverse hx_self htself
  have hpos : 0 < (x * t) % n := image_pos hn hco
  have hlt : (x * t) % n < n := Nat.mod_lt _ hnpos
  exact mem_S_of_selfinv_unit hn hpos hlt hco hself

/-! ## §5 — `P ≡ t^(|S|/2)` for every nontrivial `t ∈ S` -/

/-- Members of `S = selfFilter n (totativeList n)` are self-inverse units `< n`. -/
theorem S_members {n : Nat} (hn : 1 < n) :
    ∀ x, memV x (selfFilter n (totativeList n)) = true →
      gcd213 x n = 1 ∧ x < n ∧ (x * x) % n = 1 % n := by
  intro x hx
  have hxm : x ∈ selfFilter n (totativeList n) := mem_of_memV hx
  have hx_tot : x ∈ totativeList n := mem_of_mem_selfFilter hxm
  have hx_co : gcd213 x n = 1 := totativeList_coprime hx_tot
  have hx_lt : x < n :=
    totative_lt_n hn hx_co (totativeList_pos hx_tot) (totativeList_le hx_tot)
  have hx_self : selfInverse n x := selfInv_of_mem_selfFilter hxm
  exact ⟨hx_co, hx_lt, hx_self⟩

/-- ★ **`P ≡ t^(|S|/2)`** for every nontrivial self-inverse unit `t < n`.  Here
    `P = prodMod n S` with `S = selfFilter n (totativeList n)`. -/
theorem P_eq_pow {n t : Nat} (hn : 1 < n)
    (htlt : t < n) (htco : gcd213 t n = 1) (htne : t ≠ 1) (htself : (t * t) % n = 1 % n) :
    prodMod n (selfFilter n (totativeList n)) % n
      = (t ^ ((selfFilter n (totativeList n)).length / 2)) % n :=
  prodMod_pair_accum hn htlt htco htne htself
    (selfFilter n (totativeList n)).length (selfFilter n (totativeList n))
    (Nat.le_refl _)
    (noDupV_selfFilter (noDupV_of_nodup (nodup_totativeList n)))
    (S_members hn)
    (S_sigt_closed hn htco htself)

/-! ## §6 — ★★★ the Wilson `+1` headline -/

/-- ★★★ **Wilson `+1` under a nontrivial square root of `1`.**  For `1 < n`, if there
    is a unit `x < n` with `x² ≡ 1 (mod n)` and `x ∉ {1, n−1}`, then
    `∏(units of ℤ/n) ≡ +1 (mod n)`.

    Dual of `WilsonValue.wilson_neg_one_of_sqrt_trivial`: with two distinct nontrivial
    square roots of `1` (here `n−1` and `x`), the common value `P ≡ t^(|S|/2)` forces
    `k = |S|/2` even (odd would give `n−1 ≡ x`), so `P ≡ (n−1)^k ≡ 1`. -/
theorem wilson_plus_one_of_nontrivial_sqrt (n : Nat) (hn : 1 < n)
    (hx : ∃ x, x < n ∧ gcd213 x n = 1 ∧ (x * x) % n = 1 % n ∧ x ≠ 1 ∧ x ≠ n - 1) :
    prodMod n (totativeList n) % n = 1 % n := by
  obtain ⟨x, hx_lt, hx_co, hx_self, hx_ne1, hx_nepred⟩ := hx
  -- 2 < n: else n = 2, where the only unit < 2 is 1, contradicting x ≠ 1
  have hn2 : 2 < n := by
    rcases Nat.lt_or_ge 2 n with h | h
    · exact h
    · exfalso
      -- n ≤ 2 and 1 < n ⟹ n = 2
      have hne2 : n = 2 := Nat.le_antisymm h hn
      subst hne2
      -- x < 2, gcd x 2 = 1 ⟹ x = 1 (x=0 gives gcd 0 2 = 2)
      have hxle1 : x ≤ 1 := Nat.le_of_lt_succ hx_lt
      rcases Nat.eq_zero_or_pos x with hx0 | hxpos
      · rw [hx0, E213.Meta.Nat.Gcd213.gcd213_zero_left] at hx_co
        exact absurd hx_co (by decide)
      · exact hx_ne1 (Nat.le_antisymm hxle1 hxpos)
  -- write n = m + 3
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, (E213.Tactic.NatHelper.sub_add_cancel hn2).symm⟩
  have hpred := pred_self_inverse (m := m + 1)
  have hpred_co : gcd213 (m + 2) (m + 3) = 1 := hpred.1
  have hpred_lt : (m + 2) < (m + 3) := Nat.lt_succ_self _
  have hpred_self : ((m + 2) * (m + 2)) % (m + 3) = 1 % (m + 3) := hpred.2.2.2
  have hpredval : (m + 3) - 1 = m + 2 := rfl
  -- t₁ = m+2 = n-1 is a nontrivial self-inverse unit
  have ht1_ne1 : (m + 2) ≠ 1 := by
    intro h
    have h12 : 1 < m + 2 := Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 2 m)
    rw [h] at h12
    exact Nat.lt_irrefl 1 h12
  -- t₂ = x is a nontrivial self-inverse unit (hx).  k := |S| / 2.
  have hP1 : prodMod (m + 3) (selfFilter (m + 3) (totativeList (m + 3))) % (m + 3)
      = ((m + 2) ^ ((selfFilter (m + 3) (totativeList (m + 3))).length / 2)) % (m + 3) :=
    P_eq_pow hn hpred_lt hpred_co ht1_ne1 hpred_self
  have hP2 : prodMod (m + 3) (selfFilter (m + 3) (totativeList (m + 3))) % (m + 3)
      = (x ^ ((selfFilter (m + 3) (totativeList (m + 3))).length / 2)) % (m + 3) :=
    P_eq_pow hn hx_lt hx_co hx_ne1 hx_self
  -- reduce the headline product to P
  have hred : prodMod (m + 3) (totativeList (m + 3)) % (m + 3)
      = prodMod (m + 3) (selfFilter (m + 3) (totativeList (m + 3))) % (m + 3) := by
    rw [units_prod_eq_selfinv_prod hn]
  -- parity of k
  rcases E213.Meta.Nat.PureNat.nat_dichotomy
      ((selfFilter (m + 3) (totativeList (m + 3))).length / 2) with ⟨j, hj⟩ | ⟨j, hj⟩
  · -- k even: P ≡ (m+2)^k ≡ 1
    rw [hred, hP1, hj, self_inv_pow_even hpred_self j]
  · -- k odd: P ≡ (m+2) and P ≡ x, so m+2 = x, contra x ≠ n-1
    exfalso
    have h1 : prodMod (m + 3) (selfFilter (m + 3) (totativeList (m + 3))) % (m + 3)
        = (m + 2) % (m + 3) := by rw [hP1, hj, self_inv_pow_odd hpred_self j]
    have h2 : prodMod (m + 3) (selfFilter (m + 3) (totativeList (m + 3))) % (m + 3)
        = x % (m + 3) := by rw [hP2, hj, self_inv_pow_odd hx_self j]
    have heq : (m + 2) % (m + 3) = x % (m + 3) := h1.symm.trans h2
    rw [Nat.mod_eq_of_lt hpred_lt, Nat.mod_eq_of_lt hx_lt] at heq
    rw [hpredval] at hx_nepred
    exact hx_nepred heq.symm

/-! ## §7 — smokes -/

/-- **n = 8**: nontrivial sqrt `3` (`3² = 9 ≡ 1 mod 8`, `3 ∉ {1,7}`), so
    `∏(units of ℤ/8) ≡ 1 (mod 8)`. -/
theorem plus_one_smoke_8 :
    prodMod 8 (totativeList 8) % 8 = 1 % 8 :=
  wilson_plus_one_of_nontrivial_sqrt 8 (by decide)
    ⟨3, by decide, by decide, by decide, by decide, by decide⟩

/-- **n = 15**: nontrivial sqrt `4` (`4² = 16 ≡ 1 mod 15`, `4 ∉ {1,14}`), so
    `∏(units of ℤ/15) ≡ 1 (mod 15)`. -/
theorem plus_one_smoke_15 :
    prodMod 15 (totativeList 15) % 15 = 1 % 15 :=
  wilson_plus_one_of_nontrivial_sqrt 15 (by decide)
    ⟨4, by decide, by decide, by decide, by decide, by decide⟩

/-- **n = 12**: nontrivial sqrt `5` (`5² = 25 ≡ 1 mod 12`, `5 ∉ {1,11}`), so
    `∏(units of ℤ/12) ≡ 1 (mod 12)`. -/
theorem plus_one_smoke_12 :
    prodMod 12 (totativeList 12) % 12 = 1 % 12 :=
  wilson_plus_one_of_nontrivial_sqrt 12 (by decide)
    ⟨5, by decide, by decide, by decide, by decide, by decide⟩

end E213.Lib.Math.NumberTheory.WilsonPlusOne
