import E213.Lib.Math.NumberTheory.EulerTheorem
import E213.Lib.Math.NumberTheory.ModArith.WilsonTheorem
import E213.Lib.Math.NumberTheory.ModArith.WilsonInverse
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.Gcd213
import E213.Meta.Tactic.NatHelper

/-!
# Generalized Wilson: the inverse-pairing core (∅-axiom)

**The forcing.**  Classically `∏(units of ℤ/n) ≡ ±1 (mod n)` is read off the
*abelian group structure* of `(ℤ/n)^×` — a quotient-group identity (pair each
element with its inverse in the quotient group).  ∅-axiom over `Nat` has no
quotient group: the pairing is an **explicit involution on the coprime-residue
set** `u ↦ unitInv n u = (modBezout u n).2 % n`, the cancellation a `% n`
computation (`u · unitInv u ≡ 1`), the survivors the *computed* square-roots of
`1` — the **fixed points** of the inverse-involution.

This file proves the *core*: the product over the units equals the product over
the **self-inverse** units (the inverse-involution cancels every non-self-inverse
unit in a `{u, u⁻¹}` pair).  Wilson's `±1` is then this self-inverse product —
a computed fixed-point set, not a group identity.

Reuse:
* `EulerTheorem`: `totativeList`, `aInv`, `aInv_spec`, `aInv_coprime`,
  `inv_mul_image`, `image_inj`, `totative_lt_n`, `prodMod_coprime`, `cancel_unit`.
* `WilsonTheorem`: `prodMod`, `eraseV`, `memV`, `noDupV`, `prodMod_cons`,
  `prodMod_eraseV`, `length_eraseV_lt`, `beqN`, `eq_of_beqN`, `beqN_of_eq`,
  `memV_of_cons_ne`, `memV_of_memV_eraseV`, `memV_eraseV_of_ne`, `noDupV_eraseV`,
  `bnotin_eraseV_self`, `memV_cons_self`, `memV_cons`, `andB_elim`, `orB_*`.
* `UnitsOfZn`: `isUnit`.
-/

namespace E213.Lib.Math.NumberTheory.WilsonGeneralization

open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.NumberTheory.EulerTheorem
  (totativeList totativeList_coprime totativeList_pos totativeList_le nodup_totativeList
   mem_totListUpto totative_lt_n aInv aInv_spec aInv_coprime inv_mul_image
   prodMod_coprime prodMod_lt cancel_unit)
open E213.Lib.Math.NumberTheory.ModArith.WilsonTheorem
  (prodMod prodMod_cons eraseV memV noDupV beqN beqN_refl eq_of_beqN beqN_of_eq
   orB_elim orB_inl orB_inr andB_elim memV_cons memV_cons_self memV_of_cons_ne
   prodMod_eraseV length_eraseV_lt memV_of_memV_eraseV memV_eraseV_of_ne
   noDupV_eraseV bnotin_eraseV_self)
open E213.Lib.Math.NumberTheory.ModArith.ModBezout (modBezout)

/-! ## §1 — the unit inverse and self-inverse predicate -/

/-- The reduced modular inverse of `u` mod `n`: `unitInv n u = (modBezout u n).2 % n`.
    (Same reduced Bezout inverse `EulerTheorem` uses, but with the `% n` folded in,
    matching `WilsonTheorem.invF`'s reduced form so it lands in `[0, n)`.) -/
def unitInv (n u : Nat) : Nat := aInv u n % n

/-- `u` is **self-inverse** mod `n`: `u² ≡ 1 (mod n)`. -/
def selfInverse (n u : Nat) : Prop := (u * u) % n = 1 % n

/-- `unitInv n u` inverts `u`:  `(u · unitInv n u) % n = 1 % n` for a unit `u`. -/
theorem unitInv_mul {n u : Nat} (hn : 0 < n) (hu : gcd213 u n = 1) :
    (u * unitInv n u) % n = 1 % n := by
  show (u * (aInv u n % n)) % n = 1 % n
  rw [E213.Meta.Nat.MulMod213.mul_mod_right_pure u (aInv u n % n) n,
      E213.Meta.Nat.AddMod213.mod_mod,
      ← E213.Meta.Nat.MulMod213.mul_mod_right_pure u (aInv u n) n]
  exact aInv_spec hn hu

/-- `unitInv n u` is itself a unit. -/
theorem unitInv_coprime {n u : Nat} (hn : 1 < n) (hu : gcd213 u n = 1) :
    gcd213 (unitInv n u) n = 1 := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hn)
  show gcd213 (aInv u n % n) n = 1
  rw [E213.Lib.Math.NumberTheory.EulerTheorem.gcd_mod_left (aInv u n) n hnpos]
  exact aInv_coprime hn hu

/-- `unitInv n u < n` (it is a `% n` value). -/
theorem unitInv_lt {n u : Nat} (hn : 0 < n) : unitInv n u < n :=
  Nat.mod_lt _ hn

/-- `unitInv n u > 0` for a unit `u` (its product with `u` is `1`, so it is nonzero). -/
theorem unitInv_pos {n u : Nat} (hn : 1 < n) (hu : gcd213 u n = 1) : 0 < unitInv n u := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hn)
  rcases Nat.eq_zero_or_pos (unitInv n u) with h0 | hpos
  · exfalso
    have hmul : (u * unitInv n u) % n = 1 % n := unitInv_mul hnpos hu
    rw [h0, Nat.mul_zero, Nat.mod_eq_of_lt hnpos] at hmul
    rw [Nat.mod_eq_of_lt hn] at hmul
    exact absurd hmul (by decide)
  · exact hpos

/-! ## §2 — ★ item 1: the inverse is `u` itself ⟺ `u² ≡ 1` -/

/-- ★ **The Bezout inverse equals `u` (reduced) iff `u` is self-inverse.**
    For a unit `u < n` (`1 < n`):  `unitInv n u = u  ↔  selfInverse n u`.

    Forward: `unitInv n u = u`, and `(u · unitInv n u) % n = 1 % n`, so substituting
    gives `(u·u) % n = 1 % n`.
    Backward: `(u·u) % n = 1 % n = (u · unitInv n u) % n`; both `u` and `unitInv n u`
    are inverses of `u` in `[0,n)`, so by inverse-cancellation `u = unitInv n u`. -/
theorem unitInv_eq_self_iff {n u : Nat} (hn : 1 < n) (hu : gcd213 u n = 1) (hult : u < n) :
    unitInv n u = u ↔ selfInverse n u := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hn)
  constructor
  · intro hself
    show (u * u) % n = 1 % n
    have hmul : (u * unitInv n u) % n = 1 % n := unitInv_mul hnpos hu
    rw [hself] at hmul; exact hmul
  · intro hsq
    -- (u · unitInv n u) % n = 1 % n = (u · u) % n
    have hmul : (u * unitInv n u) % n = 1 % n := unitInv_mul hnpos hu
    have heq : (u * unitInv n u) % n = (u * u) % n := hmul.trans hsq.symm
    -- cancel u (unit):  unitInv n u % n = u, with unitInv n u < n and u < n
    have hcancel : unitInv n u % n = u :=
      cancel_unit hn hu heq hult
    rw [Nat.mod_eq_of_lt (unitInv_lt hnpos)] at hcancel
    exact hcancel

/-- `unitInv` is an **involution** on units `< n`:  `unitInv n (unitInv n u) = u`. -/
theorem unitInv_invol {n u : Nat} (hn : 1 < n) (hu : gcd213 u n = 1) (hult : u < n) :
    unitInv n (unitInv n u) = u := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hn)
  -- v := unitInv n u is a unit, v < n.  (u·v)%n = 1, (v·(unitInv v))%n = 1.
  -- u and unitInv n v are both inverses of v; cancel v.
  have hv_co : gcd213 (unitInv n u) n = 1 := unitInv_coprime hn hu
  have hv_lt : unitInv n u < n := unitInv_lt hnpos
  -- (v · u) % n = 1 % n  (from (u·v)%n = 1%n, commute)
  have huv : (u * unitInv n u) % n = 1 % n := unitInv_mul hnpos hu
  have hvu : (unitInv n u * u) % n = 1 % n := by
    rw [Nat.mul_comm (unitInv n u) u]; exact huv
  -- (v · unitInv n v) % n = 1 % n
  have hvw : (unitInv n u * unitInv n (unitInv n u)) % n = 1 % n := unitInv_mul hnpos hv_co
  -- so (v · unitInv n v) % n = (v · u) % n;  cancel v:  unitInv n v % n = u
  have heq : (unitInv n u * unitInv n (unitInv n u)) % n = (unitInv n u * u) % n :=
    hvw.trans hvu.symm
  have hcancel : unitInv n (unitInv n u) % n = u := cancel_unit hn hv_co heq hult
  rw [Nat.mod_eq_of_lt (unitInv_lt hnpos)] at hcancel
  exact hcancel

/-! ## §3 — boolean self-inverse predicate + self-inverse filter -/

/-- Boolean self-inverse test: `selfInvB n u = (u·u mod n =? 1 mod n)`. -/
def selfInvB (n u : Nat) : Bool := beqN ((u * u) % n) (1 % n)

theorem selfInvB_iff {n u : Nat} : selfInvB n u = true ↔ selfInverse n u := by
  constructor
  · intro h; exact eq_of_beqN h
  · intro h; exact beqN_of_eq h

/-- `selfFilter n l` keeps the self-inverse elements of `l`. -/
def selfFilter (n : Nat) : List Nat → List Nat
  | []     => []
  | a :: l =>
    match selfInvB n a with
    | true  => a :: selfFilter n l
    | false => selfFilter n l

theorem selfFilter_cons_true {n a : Nat} {l : List Nat} (h : selfInvB n a = true) :
    selfFilter n (a :: l) = a :: selfFilter n l := by
  show (match selfInvB n a with | true => a :: selfFilter n l | false => selfFilter n l)
     = a :: selfFilter n l
  rw [h]

theorem selfFilter_cons_false {n a : Nat} {l : List Nat} (h : selfInvB n a = false) :
    selfFilter n (a :: l) = selfFilter n l := by
  show (match selfInvB n a with | true => a :: selfFilter n l | false => selfFilter n l)
     = selfFilter n l
  rw [h]

/-! ## §4 — the involution preserves non-self-inverseness -/

/-- If `a` is **not** self-inverse, neither is its inverse `b = unitInv n a`.
    (Self-inverseness is symmetric under the involution: `b² ≡ 1 ⟺ a² ≡ 1`.) -/
theorem unitInv_not_selfInv {n a : Nat} (hn : 1 < n) (ha : gcd213 a n = 1) (halt : a < n)
    (hns : selfInvB n a = false) : selfInvB n (unitInv n a) = false := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hn)
  cases hcase : selfInvB n (unitInv n a) with
  | false => rfl
  | true =>
    exfalso
    -- unitInv n (unitInv n a) = unitInv n a  (b self-inverse ⟹ b's inverse is b)
    have hb_self : selfInverse n (unitInv n a) := eq_of_beqN hcase
    have hb_co : gcd213 (unitInv n a) n = 1 := unitInv_coprime hn ha
    have hb_lt : unitInv n a < n := unitInv_lt hnpos
    have hbb : unitInv n (unitInv n a) = unitInv n a :=
      (unitInv_eq_self_iff hn hb_co hb_lt).mpr hb_self
    -- but unitInv n (unitInv n a) = a (involution), so a = unitInv n a, so a self-inverse
    have hinvol : unitInv n (unitInv n a) = a := unitInv_invol hn ha halt
    have ha_eq : a = unitInv n a := hinvol.symm.trans hbb
    -- a = unitInv n a ⟹ a self-inverse (item 1 forward needs unitInv n a = a)
    have ha_self : selfInverse n a := (unitInv_eq_self_iff hn ha halt).mp ha_eq.symm
    have : selfInvB n a = true := beqN_of_eq ha_self
    rw [this] at hns; exact absurd hns (by decide)

/-- A self-inverse unit is its own inverse: `unitInv n a = a` (for `a` self-inverse, `a < n`). -/
theorem unitInv_self_of_selfInv {n a : Nat} (hn : 1 < n) (ha : gcd213 a n = 1) (halt : a < n)
    (hs : selfInvB n a = true) : unitInv n a = a :=
  (unitInv_eq_self_iff hn ha halt).mpr (eq_of_beqN hs)

/-! ## §5 — `selfFilter` commutes with erasing a non-self-inverse element -/

/-- Erasing a **non-self-inverse** value `b` leaves `selfFilter` unchanged.
    (The filter drops `b` anyway; erasing its first occurrence makes no difference.) -/
theorem selfFilter_eraseV {n b : Nat} (hns : selfInvB n b = false) :
    ∀ {l : List Nat}, selfFilter n (eraseV b l) = selfFilter n l
  | [] => rfl
  | a :: l => by
    cases hab : beqN a b with
    | true =>
      -- eraseV b (a::l) = l ; a = b non-self ⟹ selfFilter drops a too
      have hax : a = b := eq_of_beqN hab
      have heq : eraseV b (a :: l) = l := by
        show (match beqN a b with | true => l | false => a :: eraseV b l) = l
        rw [hab]
      have hns_a : selfInvB n a = false := by rw [hax]; exact hns
      rw [heq, selfFilter_cons_false hns_a]
    | false =>
      have heq : eraseV b (a :: l) = a :: eraseV b l := by
        show (match beqN a b with | true => l | false => a :: eraseV b l) = a :: eraseV b l
        rw [hab]
      rw [heq]
      cases hsa : selfInvB n a with
      | true =>
        rw [selfFilter_cons_true hsa, selfFilter_cons_true hsa, selfFilter_eraseV hns]
      | false =>
        rw [selfFilter_cons_false hsa, selfFilter_cons_false hsa, selfFilter_eraseV hns]

/-! ## §5b — bridge: boolean `memV`/`noDupV` ↔ `List.Mem`/`List.Nodup` -/

/-- `memV x l = true → x ∈ l`. -/
theorem mem_of_memV {x : Nat} : ∀ {l : List Nat}, memV x l = true → x ∈ l
  | [], h => by exact absurd h Bool.false_ne_true
  | a :: l, h => by
    rw [memV_cons] at h
    rcases orB_elim h with h1 | h2
    · exact (eq_of_beqN h1) ▸ List.Mem.head _
    · exact List.Mem.tail _ (mem_of_memV h2)

/-- `x ∈ l → memV x l = true`. -/
theorem memV_of_mem {x : Nat} : ∀ {l : List Nat}, x ∈ l → memV x l = true
  | b :: l, h => by
    rw [memV_cons]
    cases h with
    | head as => exact orB_inl (beqN_refl x)
    | tail _ h' => exact orB_inr (memV_of_mem h')

/-- `l.Nodup → noDupV l = true`. -/
theorem noDupV_of_nodup : ∀ {l : List Nat}, l.Nodup → noDupV l = true
  | [], _ => rfl
  | a :: l, h => by
    cases h with
    | cons hh ht =>
      show ((!memV a l) && noDupV l) = true
      have ha_notin : memV a l = false := by
        cases hcase : memV a l with
        | false => rfl
        | true => exact absurd (hh a (mem_of_memV hcase)) (fun h => h rfl)
      rw [ha_notin]
      show (true && noDupV l) = true
      rw [noDupV_of_nodup ht]; rfl

/-! ## §6 — ★ the pairing fold: `prodMod l ≡ prodMod (selfFilter l)` -/

/-- ★★ **The inverse-pairing core (fuel-bounded).**  For a NoDup, all-unit, all-`< n`,
    inverse-closed list `l` over modulus `n` (`1 < n`):
    `prodMod n l = prodMod n (selfFilter n l)`.

    The non-self-inverse units cancel in `{a, unitInv n a}` pairs (`a·a⁻¹ ≡ 1`);
    the survivors are exactly the self-inverse units.  Strong recursion on length:
    a self-inverse head is kept; a non-self-inverse head `a` is paired with its
    distinct inverse `b = unitInv n a ∈ l`, both erased (the product picks up
    `a·b ≡ 1`), inverse-closure passing to `eraseV b l`. -/
theorem prodMod_pairing_selfinv_fuel {n : Nat} (hn : 1 < n) :
    ∀ (fuel : Nat) (l : List Nat), l.length ≤ fuel →
      noDupV l = true →
      (∀ x, memV x l = true → gcd213 x n = 1 ∧ x < n) →
      (∀ x, memV x l = true → memV (unitInv n x) l = true) →
      prodMod n l = prodMod n (selfFilter n l)
  | _, [], _, _, _, _ => rfl
  | 0, a :: l, hlen, _, _, _ => by
      exact absurd hlen (Nat.not_succ_le_zero l.length)
  | fuel + 1, a :: l, hlen, hnd, hunit, hclosed => by
    have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hn)
    have hamem : memV a (a :: l) = true := memV_cons_self a l
    obtain ⟨ha_co, ha_lt⟩ := hunit a hamem
    -- tail facts shared by both branches
    have hndl : noDupV l = true := (andB_elim hnd).2
    have hlen_l : l.length ≤ fuel := Nat.le_of_succ_le_succ hlen
    cases hsa : selfInvB n a with
    | true =>
      -- a is kept.  recurse on l (sublist: unit, <n, NoDup, inverse-closed).
      rw [selfFilter_cons_true hsa, prodMod_cons, prodMod_cons]
      -- need prodMod n l = prodMod n (selfFilter n l).  But closure on l alone may fail:
      -- inv of an element of l could be a.  Handle: a is self-inverse, so inv a = a ∉ l (NoDup),
      -- so any element of l whose inverse is a would force that element = inv a = a ∉ l.  Hence
      -- closure restricts to l.
      have ha_notin_l : memV a l = false := by
        have hnm : (!memV a l) = true := (andB_elim hnd).1
        cases hcase : memV a l with
        | false => rfl
        | true => rw [hcase] at hnm; exact absurd hnm (by decide)
      have hinva : unitInv n a = a := unitInv_self_of_selfInv hn ha_co ha_lt hsa
      have hclosed_l : ∀ x, memV x l = true → memV (unitInv n x) l = true := by
        intro x hx
        have hxal : memV x (a :: l) = true := by rw [memV_cons]; exact orB_inr hx
        obtain ⟨hx_co, hx_lt⟩ := hunit x hxal
        have hinvx_al : memV (unitInv n x) (a :: l) = true := hclosed x hxal
        -- unitInv n x ≠ a:  else x = unitInv n (unitInv n x) = unitInv n a = a, but a ∉ l, x ∈ l
        have hinvx_ne_a : beqN a (unitInv n x) = false := by
          cases hcase : beqN a (unitInv n x) with
          | false => rfl
          | true =>
            exfalso
            have haix : a = unitInv n x := eq_of_beqN hcase
            have hxa : x = a := by
              have : unitInv n (unitInv n x) = x := unitInv_invol hn hx_co hx_lt
              rw [← haix] at this; rw [hinva] at this; exact this.symm
            have : memV a l = true := hxa ▸ hx
            rw [this] at ha_notin_l; exact absurd ha_notin_l (by decide)
        exact memV_of_cons_ne hinvx_al hinvx_ne_a
      have hrec : prodMod n l = prodMod n (selfFilter n l) :=
        prodMod_pairing_selfinv_fuel hn fuel l hlen_l hndl
          (fun x hx => hunit x (by rw [memV_cons]; exact orB_inr hx)) hclosed_l
      rw [hrec]
    | false =>
      -- a is dropped; pair a with b := unitInv n a.
      rw [selfFilter_cons_false hsa]
      have hbmem_all : memV (unitInv n a) (a :: l) = true := hclosed a hamem
      -- b ≠ a (a not self-inverse ⟹ unitInv n a ≠ a)
      have hba_ne : beqN a (unitInv n a) = false := by
        cases hcase : beqN a (unitInv n a) with
        | false => rfl
        | true =>
          exfalso
          have hself_eq : unitInv n a = a := (eq_of_beqN hcase).symm
          have : selfInverse n a := (unitInv_eq_self_iff hn ha_co ha_lt).mp hself_eq
          have : selfInvB n a = true := beqN_of_eq this
          rw [this] at hsa; exact absurd hsa (by decide)
      have hbmem_l : memV (unitInv n a) l = true := memV_of_cons_ne hbmem_all hba_ne
      -- b not self-inverse
      have hb_ns : selfInvB n (unitInv n a) = false := unitInv_not_selfInv hn ha_co ha_lt hsa
      -- prodMod (a::l) = (a·b·R)%n = R%n where R = prodMod (eraseV b l)
      have hfact : prodMod n l = (unitInv n a * prodMod n (eraseV (unitInv n a) l)) % n :=
        prodMod_eraseV hbmem_l
      have hab1 : (a * unitInv n a) % n = 1 % n := unitInv_mul hnpos ha_co
      have hab1' : (a * unitInv n a) % n = 1 := by
        rw [hab1, Nat.mod_eq_of_lt hn]
      have hstep : prodMod n (a :: l) = prodMod n (eraseV (unitInv n a) l) % n := by
        rw [prodMod_cons, hfact]
        rw [← E213.Meta.Nat.MulMod213.mul_mod_right_pure a
              (unitInv n a * prodMod n (eraseV (unitInv n a) l)) n]
        rw [← E213.Tactic.NatHelper.mul_assoc a (unitInv n a)
              (prodMod n (eraseV (unitInv n a) l))]
        rw [E213.Meta.Nat.MulMod213.mul_mod_left_pure (a * unitInv n a)
              (prodMod n (eraseV (unitInv n a) l)) n, hab1', Nat.one_mul]
      -- recurse on eraseV b l : NoDup, unit, <n, inverse-closed
      have hnd_rest : noDupV (eraseV (unitInv n a) l) = true := noDupV_eraseV hndl
      have hlen_rest : (eraseV (unitInv n a) l).length ≤ fuel :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le (length_eraseV_lt hbmem_l) hlen_l)
      have hunit_rest : ∀ x, memV x (eraseV (unitInv n a) l) = true → gcd213 x n = 1 ∧ x < n := by
        intro x hx
        have hxl : memV x l = true := memV_of_memV_eraseV hx
        exact hunit x (by rw [memV_cons]; exact orB_inr hxl)
      -- a ∉ l (NoDup head)
      have ha_notin_l : memV a l = false := by
        have hnm : (!memV a l) = true := (andB_elim hnd).1
        cases hcase : memV a l with
        | false => rfl
        | true => rw [hcase] at hnm; exact absurd hnm (by decide)
      have hclosed_rest : ∀ x, memV x (eraseV (unitInv n a) l) = true →
          memV (unitInv n x) (eraseV (unitInv n a) l) = true := by
        intro x hx
        have hxl : memV x l = true := memV_of_memV_eraseV hx
        have hxal : memV x (a :: l) = true := by rw [memV_cons]; exact orB_inr hxl
        obtain ⟨hx_co, hx_lt⟩ := hunit x hxal
        have hinvx_al : memV (unitInv n x) (a :: l) = true := hclosed x hxal
        -- x ≠ b : x ∈ eraseV b l with NoDup ⟹ x ≠ b
        have hxb_ne : beqN x (unitInv n a) = false := by
          cases hcase : beqN x (unitInv n a) with
          | false => rfl
          | true =>
            exfalso
            have hxb : x = unitInv n a := eq_of_beqN hcase
            rw [hxb] at hx
            exact bnotin_eraseV_self hndl hbmem_l hx
        -- unitInv n x ≠ a : else x = unitInv n (unitInv n x) = unitInv n a = b, contra x ≠ b
        have hinvx_ne_a : beqN a (unitInv n x) = false := by
          cases hcase : beqN a (unitInv n x) with
          | false => rfl
          | true =>
            exfalso
            have haix : a = unitInv n x := eq_of_beqN hcase
            have hbx : unitInv n a = x := by
              rw [haix]; exact unitInv_invol hn hx_co hx_lt
            have : beqN x (unitInv n a) = true := beqN_of_eq hbx.symm
            rw [this] at hxb_ne; exact absurd hxb_ne (by decide)
        have hinvx_l : memV (unitInv n x) l = true := memV_of_cons_ne hinvx_al hinvx_ne_a
        -- unitInv n x ≠ b : else x = a (involution injective), but a ∉ l, x ∈ l
        have hxa_ne : beqN (unitInv n x) (unitInv n a) = false := by
          cases hcase : beqN (unitInv n x) (unitInv n a) with
          | false => rfl
          | true =>
            exfalso
            have heqinv : unitInv n x = unitInv n a := eq_of_beqN hcase
            have hxa : x = a := by
              have h1 : unitInv n (unitInv n x) = unitInv n (unitInv n a) := by rw [heqinv]
              rw [unitInv_invol hn hx_co hx_lt, unitInv_invol hn ha_co ha_lt] at h1
              exact h1
            have : memV a l = true := hxa ▸ hxl
            rw [this] at ha_notin_l; exact absurd ha_notin_l (by decide)
        exact memV_eraseV_of_ne hndl hinvx_l hxa_ne
      have hrec : prodMod n (eraseV (unitInv n a) l)
                = prodMod n (selfFilter n (eraseV (unitInv n a) l)) :=
        prodMod_pairing_selfinv_fuel hn fuel (eraseV (unitInv n a) l) hlen_rest hnd_rest
          hunit_rest hclosed_rest
      -- selfFilter (eraseV b l) = selfFilter l  (b not self-inverse)
      have hsf : selfFilter n (eraseV (unitInv n a) l) = selfFilter n l :=
        selfFilter_eraseV hb_ns
      rw [hsf] at hrec
      -- assemble: prodMod (a::l) = R%n = (prodMod (selfFilter l))%n = prodMod (selfFilter l)
      rw [hstep, hrec]
      -- prodMod n (selfFilter n l) < n, so %n is identity
      have hsflt : prodMod n (selfFilter n l) < n := prodMod_lt hnpos (selfFilter n l)
      exact Nat.mod_eq_of_lt hsflt

/-! ## §7 — ★★★ the core, on the totative list -/

/-- `unitInv n u` is a totative when `u` is (closure of the unit set under the inverse). -/
theorem unitInv_mem_totativeList {n u : Nat} (hn : 1 < n) (hu : u ∈ totativeList n) :
    unitInv n u ∈ totativeList n := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hn)
  have hu_co : gcd213 u n = 1 := totativeList_coprime hu
  have hco : gcd213 (unitInv n u) n = 1 := unitInv_coprime hn hu_co
  have hpos : 0 < unitInv n u := unitInv_pos hn hu_co
  have hlt : unitInv n u < n := unitInv_lt hnpos
  exact mem_totListUpto.mpr ⟨hpos, Nat.le_of_lt hlt, hco⟩

/-- ★★★ **The Wilson inverse-pairing core.**  For `1 < n`,
    `∏_{u unit, u<n} u ≡ ∏_{u unit, selfInverse, u<n} u (mod n)` — the product over
    the units of `ℤ/n` (on representatives = `totativeList n`) equals the product
    over the **self-inverse** units (`selfFilter n (totativeList n)`).

    The inverse-involution `u ↦ unitInv n u` cancels every non-self-inverse unit
    against its distinct inverse partner (`u·u⁻¹ ≡ 1`); the survivors are exactly
    the computed square-roots of `1`.  No quotient group: an explicit `% n`
    pairing on the coprime-residue set. -/
theorem units_prod_eq_selfinv_prod {n : Nat} (hn : 1 < n) :
    prodMod n (totativeList n)
      = prodMod n (selfFilter n (totativeList n)) := by
  refine prodMod_pairing_selfinv_fuel hn (totativeList n).length (totativeList n)
    (Nat.le_refl _) (noDupV_of_nodup (nodup_totativeList n)) ?_ ?_
  · intro x hx
    have hxm : x ∈ totativeList n := mem_of_memV hx
    refine ⟨totativeList_coprime hxm, ?_⟩
    exact totative_lt_n hn (totativeList_coprime hxm) (totativeList_pos hxm) (totativeList_le hxm)
  · intro x hx
    have hxm : x ∈ totativeList n := mem_of_memV hx
    exact memV_of_mem (unitInv_mem_totativeList hn hxm)

/-! ## §8 — smokes -/

/-- **n = 8**: units `{7,5,3,1}` (`totativeList 8`), **all self-inverse**
    (`x² ≡ 1 mod 8` for every unit), so `selfFilter` keeps all of them and the
    product is `≡ 1 (mod 8)`.  (Gauss `−1` does *not* occur: more than one
    nontrivial self-inverse unit.) -/
theorem selfinv_smoke_8 :
    prodMod 8 (totativeList 8) = prodMod 8 (selfFilter 8 (totativeList 8)) ∧
    totativeList 8 = [7, 5, 3, 1] ∧
    selfFilter 8 (totativeList 8) = [7, 5, 3, 1] ∧
    prodMod 8 (totativeList 8) = 1 := by
  refine ⟨units_prod_eq_selfinv_prod (by decide), ?_, ?_, ?_⟩ <;> decide

/-- **n = 5** (prime): units `{4,3,2,1}`; the involution pairs `2 ↔ 3`
    (`2·3 = 6 ≡ 1`) leaving the **self-inverse** survivors `{4,1}`.  The full
    product `24 ≡ 4 ≡ −1 (mod 5)` equals the self-inverse product `4·1 = 4`
    — Wilson `(5−1)! ≡ −1`. -/
theorem selfinv_smoke_5 :
    prodMod 5 (totativeList 5) = prodMod 5 (selfFilter 5 (totativeList 5)) ∧
    totativeList 5 = [4, 3, 2, 1] ∧
    selfFilter 5 (totativeList 5) = [4, 1] ∧
    prodMod 5 (totativeList 5) = 4 ∧
    prodMod 5 (selfFilter 5 (totativeList 5)) = 4 := by
  refine ⟨units_prod_eq_selfinv_prod (by decide), ?_, ?_, ?_, ?_⟩ <;> decide

/-- **n = 7** (prime): involution pairs `2↔4`, `3↔5` (`2·4=8≡1`, `3·5=15≡1`),
    self-inverse survivors `{6,1}`, product `6·1 = 6 ≡ −1 (mod 7)` = Wilson. -/
theorem selfinv_smoke_7 :
    prodMod 7 (totativeList 7) = prodMod 7 (selfFilter 7 (totativeList 7)) ∧
    selfFilter 7 (totativeList 7) = [6, 1] ∧
    prodMod 7 (totativeList 7) = 6 := by
  refine ⟨units_prod_eq_selfinv_prod (by decide), ?_, ?_⟩ <;> decide

/-- **n = 12** (composite, three nontrivial self-inverse units): units
    `{11,7,5,1}`, **all self-inverse** (`5²=25≡1`, `7²=49≡1`, `11²≡1 mod 12`),
    product `≡ 1 (mod 12)` (Gauss `+1`). -/
theorem selfinv_smoke_12 :
    prodMod 12 (totativeList 12) = prodMod 12 (selfFilter 12 (totativeList 12)) ∧
    selfFilter 12 (totativeList 12) = [11, 7, 5, 1] ∧
    prodMod 12 (totativeList 12) = 1 := by
  refine ⟨units_prod_eq_selfinv_prod (by decide), ?_, ?_⟩ <;> decide

/-- **n = 10** (composite, Gauss `−1` case): units `{9,7,3,1}`, involution pairs
    `3↔7` (`3·7=21≡1`), self-inverse survivors `{9,1}`, product `9·1 = 9 ≡ −1 (mod 10)`. -/
theorem selfinv_smoke_10 :
    prodMod 10 (totativeList 10) = prodMod 10 (selfFilter 10 (totativeList 10)) ∧
    selfFilter 10 (totativeList 10) = [9, 1] ∧
    prodMod 10 (totativeList 10) = 9 := by
  refine ⟨units_prod_eq_selfinv_prod (by decide), ?_, ?_⟩ <;> decide

/-! ## §9 — item 3: prime recovery (self-inverse units of a prime are `{1, p−1}`) -/

open E213.Meta.Nat.VpMul (IsPrime213)
open E213.Lib.Math.NumberTheory.ModArith.WilsonInverse (self_inverse)

/-- ★ **For prime `p`, the only self-inverse units are `1` and `p−1`.**  Every
    survivor of the inverse-involution on `totativeList p` is `1` or `p−1`
    (`WilsonInverse.self_inverse`: `x² ≡ 1 mod p ⟹ x = 1 ∨ x = p−1`).  Hence
    `selfFilter p (totativeList p)` is (a permutation of) `[p−1, 1]`, whose
    product is `p−1 ≡ −1`: the general Gauss/Wilson value for a prime modulus,
    read off the *computed fixed-point set* of the involution — not a group law. -/
theorem prime_selfinv_is_one_or_pred {p x : Nat} (hp : IsPrime213 p)
    (hx : x ∈ selfFilter p (totativeList p)) : x = 1 ∨ x + 1 = p := by
  -- selfFilter ⊆ totativeList, and a survivor is self-inverse
  have hmem_tot : x ∈ totativeList p := by
    -- selfFilter only removes elements
    have : ∀ {l : List Nat}, x ∈ selfFilter p l → x ∈ l := by
      intro l
      induction l with
      | nil => intro h; exact absurd h (by intro hh; nomatch hh)
      | cons a l ih =>
        intro h
        cases hsa : selfInvB p a with
        | true =>
          rw [selfFilter_cons_true hsa] at h
          cases h with
          | head => exact List.Mem.head _
          | tail _ h' => exact List.Mem.tail _ (ih h')
        | false =>
          rw [selfFilter_cons_false hsa] at h
          exact List.Mem.tail _ (ih h)
    exact this hx
  -- survivor ⟹ selfInvB p x = true
  have hself_b : selfInvB p x = true := by
    have : ∀ {l : List Nat}, x ∈ selfFilter p l → selfInvB p x = true := by
      intro l
      induction l with
      | nil => intro h; exact absurd h (by intro hh; nomatch hh)
      | cons a l ih =>
        intro h
        cases hsa : selfInvB p a with
        | true =>
          rw [selfFilter_cons_true hsa] at h
          cases h with
          | head => exact hsa
          | tail _ h' => exact ih h'
        | false =>
          rw [selfFilter_cons_false hsa] at h
          exact ih h
    exact this hx
  have hself : selfInverse p x := eq_of_beqN hself_b
  have hp1 : 1 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  have hx0 : 0 < x := totativeList_pos hmem_tot
  have hxlt : x < p :=
    totative_lt_n hp1 (totativeList_coprime hmem_tot) (totativeList_pos hmem_tot)
      (totativeList_le hmem_tot)
  exact self_inverse hp hx0 hxlt hself

/-- Concrete prime recovery (`decide`): at `p = 11`, the involution leaves
    self-inverse survivors `{10, 1}`, product `10 ≡ −1 (mod 11)` = Wilson. -/
theorem wilson_prime_recovers_11 :
    prodMod 11 (totativeList 11) = prodMod 11 (selfFilter 11 (totativeList 11)) ∧
    selfFilter 11 (totativeList 11) = [10, 1] ∧
    prodMod 11 (totativeList 11) = 10 := by
  refine ⟨units_prod_eq_selfinv_prod (by decide), ?_, ?_⟩ <;> decide

end E213.Lib.Math.NumberTheory.WilsonGeneralization
