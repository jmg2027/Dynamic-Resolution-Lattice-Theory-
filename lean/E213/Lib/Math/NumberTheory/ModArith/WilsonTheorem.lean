import E213.Lib.Math.NumberTheory.ModArith.WilsonInverse
import E213.Lib.Math.Combinatorics.Permutations
import E213.Meta.Nat.MulMod213
import E213.Meta.Tactic.BoolHelper
import E213.Meta.Nat.Beq213

/-!
# Wilson's theorem `(p−1)! ≡ −1 (mod p)` (∅-axiom)

★★★ `wilson : IsPrime213 p → (fact (p−1)) % p = p − 1` — for every prime `p`,
general (not a table).  Closes the W3 obstruction left open by `WilsonInverse.lean`
(which supplied W1 `self_inverse` `x²≡1 → x=1 ∨ x=p−1` and W2
`inverse_exists`/`inverse_unique`).

Proof: `fact (p−1) % p = prodMod p [p−1,…,1]` (factorial as a folded list-product
mod p); the multiplicative inverse `invF p x = (modBezout x p).2 % p` is an
involution on `[1,p−1]` (W2) with no fixed point in the middle band `[2,p−2]` (W1).
The crux `prodMod_pairing_fuel` is a fuel-bounded strong recursion: any NoDup,
middle-band, inverse-closed list has `prodMod ≡ 1` (pair the head with its distinct
inverse `a·inv(a)≡1`, erase both via the `eraseV` toolkit preserving closure under
the involution, recurse).  The final assembly peels `p−1` as head and `1` as the
trailing identity factor, leaving the band `≡ 1` in the middle and `(p−1)·1 ≡ p−1`.
All ∅-axiom (WF via explicit `Nat` fuel; `Bool` `match` not `if`/`ite`).
-/

namespace E213.Lib.Math.NumberTheory.ModArith.WilsonTheorem

open E213.Lib.Math.Combinatorics.Permutations (fact)
open E213.Meta.Nat.VpMul (IsPrime213)
open E213.Tactic.NatHelper (gcd213)

/-! ## T2 — Wilson table (decide) -/

theorem wilson_2  : (fact (2  - 1)) % 2  = 2  - 1 := by decide
theorem wilson_3  : (fact (3  - 1)) % 3  = 3  - 1 := by decide
theorem wilson_5  : (fact (5  - 1)) % 5  = 5  - 1 := by decide
theorem wilson_7  : (fact (7  - 1)) % 7  = 7  - 1 := by decide
theorem wilson_11 : (fact (11 - 1)) % 11 = 11 - 1 := by decide
theorem wilson_13 : (fact (13 - 1)) % 13 = 13 - 1 := by decide

/-! ## §A — product mod p over a list -/

/-- `prodMod p l = (∏ x∈l, x) % p`, folded with reduction at each step. -/
def prodMod (p : Nat) : List Nat → Nat
  | []      => 1 % p
  | a :: l  => (a * prodMod p l) % p

/-- `prodMod` of a single-element list. -/
theorem prodMod_cons (p a : Nat) (l : List Nat) :
    prodMod p (a :: l) = (a * prodMod p l) % p := rfl

/-- `[n, n-1, ..., 1]` — the descending residue list (length `n`, entries `1..n`). -/
def downFrom : Nat → List Nat
  | 0     => []
  | n + 1 => (n + 1) :: downFrom n

/-- `prodMod p (downFrom n) = fact n % p`: the factorial as a folded list product. -/
theorem prodMod_downFrom (p : Nat) : ∀ n, prodMod p (downFrom n) = fact n % p
  | 0     => rfl
  | n + 1 => by
    show ((n + 1) * prodMod p (downFrom n)) % p = fact (n + 1) % p
    rw [prodMod_downFrom p n]
    show ((n + 1) * (fact n % p)) % p = ((n + 1) * fact n) % p
    rw [← E213.Meta.Nat.MulMod213.mul_mod_right_pure]

/-! ## §B — pairing toolkit: erase-by-value -/

open E213.Lib.Math.NumberTheory.ModArith.WilsonInverse
  (self_inverse inverse_exists inverse_unique)

/-- Boolean equality on `Nat` (∅-axiom: `Nat.beq`, structural). -/
def beqN (a b : Nat) : Bool := Nat.beq a b

theorem beqN_refl : ∀ a : Nat, beqN a a = true
  | 0     => rfl
  | n + 1 => beqN_refl n

theorem eq_of_beqN {a b : Nat} (h : beqN a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem beqN_of_eq {a b : Nat} (h : a = b) : beqN a b = true := by
  rw [h]; exact beqN_refl b

/-- PURE `||`-destructuring (`Bool.or_eq_true` is propext-dirty). -/
theorem orB_elim {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a with
  | true  => exact Or.inl rfl
  | false => exact Or.inr h

/-- PURE `||`-intro from the left. -/
theorem orB_inl {a b : Bool} (h : a = true) : (a || b) = true := by rw [h]; rfl

/-- PURE `||`-intro from the right. -/
theorem orB_inr {a b : Bool} (h : b = true) : (a || b) = true := by
  cases a with
  | true  => rfl
  | false => exact h

/-- PURE `&&`-destructuring (`Bool.and_eq_true` is propext-dirty). -/
theorem andB_elim {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true :=
  E213.Tactic.BoolHelper.and_eq_true_pair h

/-- Erase the first occurrence of `x` (by value). -/
def eraseV (x : Nat) : List Nat → List Nat
  | []     => []
  | a :: l =>
    match beqN a x with
    | true  => l
    | false => a :: eraseV x l

/-- Boolean membership by value. -/
def memV (x : Nat) : List Nat → Bool
  | []     => false
  | a :: l => beqN a x || memV x l

theorem memV_cons (x a : Nat) (l : List Nat) :
    memV x (a :: l) = (beqN a x || memV x l) := rfl

/-- `length (eraseV x l) < length l` when `x ∈ l`. -/
theorem length_eraseV_lt {x : Nat} :
    ∀ {l : List Nat}, memV x l = true → (eraseV x l).length < l.length
  | [], h => by exact absurd h Bool.false_ne_true
  | a :: l, h => by
    show (match beqN a x with | true => l | false => a :: eraseV x l).length < (l.length + 1)
    cases hb : beqN a x with
    | true =>
      show l.length < l.length + 1
      exact Nat.lt_succ_self _
    | false =>
      show (a :: eraseV x l).length < l.length + 1
      show (eraseV x l).length + 1 < l.length + 1
      have hmem : memV x l = true := by
        have := orB_elim h
        rcases this with h1 | h2
        · rw [hb] at h1; exact absurd h1 Bool.false_ne_true
        · exact h2
      exact Nat.succ_lt_succ (length_eraseV_lt hmem)

/-- `prodMod` factors out an element present in the list (peeling its first occurrence). -/
theorem prodMod_eraseV {p x : Nat} :
    ∀ {l : List Nat}, memV x l = true →
      prodMod p l = (x * prodMod p (eraseV x l)) % p
  | [], h => by exact absurd h (Bool.false_ne_true)
  | a :: l, h => by
    cases hb : beqN a x with
    | true =>
      have hax : a = x := eq_of_beqN hb
      show (a * prodMod p l) % p = (x * prodMod p (eraseV x (a :: l))) % p
      have heq : eraseV x (a :: l) = l := by
        show (match beqN a x with | true => l | false => a :: eraseV x l) = l
        rw [hb]
      rw [heq, hax]
    | false =>
      have hmem : memV x l = true := by
        have := orB_elim h
        rcases this with h1 | h2
        · rw [hb] at h1; exact absurd h1 Bool.false_ne_true
        · exact h2
      have heq : eraseV x (a :: l) = a :: eraseV x l := by
        show (match beqN a x with | true => l | false => a :: eraseV x l) = a :: eraseV x l
        rw [hb]
      show (a * prodMod p l) % p = (x * prodMod p (eraseV x (a :: l))) % p
      rw [heq]
      -- rewrite inner: prodMod p l = (x * prodMod p (eraseV x l)) % p
      rw [prodMod_eraseV hmem]
      show (a * ((x * prodMod p (eraseV x l)) % p)) % p
         = (x * ((a * prodMod p (eraseV x l)) % p)) % p
      -- both sides equal (a*x*rest) % p
      rw [← E213.Meta.Nat.MulMod213.mul_mod_right_pure a (x * prodMod p (eraseV x l)) p,
          ← E213.Meta.Nat.MulMod213.mul_mod_right_pure x (a * prodMod p (eraseV x l)) p]
      have hcomm : a * (x * prodMod p (eraseV x l)) = x * (a * prodMod p (eraseV x l)) :=
        E213.Tactic.NatHelper.mul_left_comm a x (prodMod p (eraseV x l))
      rw [hcomm]

/-! ## §C — the inverse function and its core properties -/

open E213.Lib.Math.NumberTheory.ModArith.ModBezout (modBezout)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (inverse_of_coprime)
open E213.Lib.Math.NumberTheory.ModArith.WilsonInverse (coprime_of_lt)

/-- The reduced modular inverse of `x` in `[1, p-1]` (for prime `p`, `0 < x < p`). -/
def invF (p x : Nat) : Nat := (modBezout x p).2 % p

/-- `invF` lands in `[1, p-1]` and inverts `x`. -/
theorem invF_spec {p x : Nat} (hp : IsPrime213 p) (hx0 : 0 < x) (hxlt : x < p) :
    0 < invF p x ∧ invF p x < p ∧ (x * invF p x) % p = 1 := by
  obtain ⟨b, hb0, hblt, hbinv⟩ := inverse_exists hp hx0 hxlt
  -- show invF p x = b by uniqueness; but invF is defined directly. Re-derive directly.
  have hp1 : 1 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  have hco : gcd213 x p = 1 := coprime_of_lt hp hx0 hxlt
  have hraw : (x * (modBezout x p).2) % p = 1 % p :=
    inverse_of_coprime x p hppos hco
  have h1mod : (1 : Nat) % p = 1 := Nat.mod_eq_of_lt hp1
  rw [h1mod] at hraw
  have hinvmod : (x * invF p x) % p = 1 := by
    show (x * ((modBezout x p).2 % p)) % p = 1
    rw [E213.Meta.Nat.MulMod213.mul_mod_right_pure x ((modBezout x p).2 % p) p,
        E213.Meta.Nat.AddMod213.mod_mod,
        ← E213.Meta.Nat.MulMod213.mul_mod_right_pure x (modBezout x p).2 p]
    exact hraw
  have hpos : 0 < invF p x := by
    rcases Nat.eq_zero_or_pos (invF p x) with h0 | hpos
    · exfalso
      rw [h0, Nat.mul_zero, Nat.mod_eq_of_lt hppos] at hinvmod
      exact absurd hinvmod (by decide)
    · exact hpos
  exact ⟨hpos, Nat.mod_lt _ hppos, hinvmod⟩

open E213.Lib.Math.NumberTheory.ModArith.WilsonInverse (inverse_unique self_inverse)

/-- `invF` is an involution. -/
theorem invF_invol {p x : Nat} (hp : IsPrime213 p) (hx0 : 0 < x) (hxlt : x < p) :
    invF p (invF p x) = x := by
  obtain ⟨hy0, hylt, hxy⟩ := invF_spec hp hx0 hxlt
  obtain ⟨hz0, hzlt, hyz⟩ := invF_spec hp hy0 hylt
  -- invF p x =: y;  invF p y =: z, with (y*z)%p=1.  Also (x*y)%p=1 ⟹ (y*x)%p=1.
  have hyx : (invF p x * x) % p = 1 := by
    rw [Nat.mul_comm (invF p x) x]; exact hxy
  -- z and x are both inverses of y; uniqueness ⟹ z = x
  exact inverse_unique hp hy0 hylt hzlt hxlt hyz hyx

/-- `x · invF p x ≡ 1`, and so does the symmetric product. -/
theorem invF_mul {p x : Nat} (hp : IsPrime213 p) (hx0 : 0 < x) (hxlt : x < p) :
    (x * invF p x) % p = 1 := (invF_spec hp hx0 hxlt).2.2

/-- The only self-inverse residues are `1` and `p-1`: if `x` in `[2, p-2]`
    (i.e. `2 ≤ x` and `x + 2 ≤ p`), then `invF p x ≠ x`. -/
theorem invF_ne_self {p x : Nat} (hp : IsPrime213 p)
    (hx2 : 2 ≤ x) (hxp2 : x + 2 ≤ p) (hself : invF p x = x) : False := by
  have hx0 : 0 < x := Nat.lt_of_lt_of_le (by decide) hx2
  have hxlt : x < p :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self x) (Nat.succ_le_succ (Nat.le_succ x))) hxp2
  have hmul : (x * x) % p = 1 := by
    have := invF_mul hp hx0 hxlt
    rw [hself] at this; exact this
  have hp1 : 1 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  have h1mod : (1 : Nat) % p = 1 := Nat.mod_eq_of_lt hp1
  have hself' : (x * x) % p = 1 % p := by rw [hmul, h1mod]
  rcases self_inverse hp hx0 hxlt hself' with h1 | h2
  · -- x = 1 contradicts 2 ≤ x
    rw [h1] at hx2; exact absurd hx2 (by decide)
  · -- x + 1 = p contradicts x + 2 ≤ p
    have hle : x + 2 ≤ x + 1 := h2 ▸ hxp2
    have : x + 1 + 1 ≤ x + 1 := hle
    exact absurd this (Nat.not_succ_le_self (x + 1))

/-- `invF p 1 = 1` (1 is its own inverse). -/
theorem invF_one {p : Nat} (hp : IsPrime213 p) : invF p 1 = 1 := by
  have hp1 : 1 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  obtain ⟨hy0, hylt, hmul⟩ := invF_spec hp (by decide) hp1
  have h1mul : (1 * invF p 1) % p = invF p 1 := by
    rw [Nat.one_mul, Nat.mod_eq_of_lt hylt]
  rw [h1mul] at hmul; exact hmul

/-- `invF p (p-1) = p-1` (`p-1 ≡ -1` is its own inverse). -/
theorem invF_pred {p : Nat} (hp : IsPrime213 p) : invF p (p - 1) = p - 1 := by
  have hp1 : 1 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
  have hpm0 : 0 < p - 1 := E213.Tactic.NatHelper.sub_pos_of_lt hp1
  have hpmlt : p - 1 < p := Nat.sub_lt hppos (by decide)
  obtain ⟨hy0, hylt, hmul⟩ := invF_spec hp hpm0 hpmlt
  have hsq : ((p - 1) * (p - 1)) % p = 1 := by
    have hid : (p - 1) * (p - 1) = 1 + (p - 2) * p := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, (E213.Tactic.NatHelper.sub_add_cancel hp.two_le).symm⟩
      show (q + 2 - 1) * (q + 2 - 1) = 1 + (q + 2 - 2) * (q + 2)
      have e1 : q + 2 - 1 = q + 1 := rfl
      have e2 : q + 2 - 2 = q := rfl
      rw [e1, e2]; ring_nat
    rw [hid, E213.Tactic.NatHelper.add_mul_mod_self_pure 1 p (p - 2)]
    exact Nat.mod_eq_of_lt hp1
  exact inverse_unique hp hpm0 hpmlt hylt hpmlt hmul hsq

/-- `invF` maps the middle band `[2, p-2]` into itself. -/
theorem invF_mid {p x : Nat} (hp : IsPrime213 p)
    (hx2 : 2 ≤ x) (hxp2 : x + 2 ≤ p) :
    2 ≤ invF p x ∧ invF p x + 2 ≤ p := by
  have hx0 : 0 < x := Nat.lt_of_lt_of_le (by decide) hx2
  have hxlt : x < p :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self x) (Nat.succ_le_succ (Nat.le_succ x))) hxp2
  obtain ⟨hy0, hylt, _⟩ := invF_spec hp hx0 hxlt
  have hinvol : invF p (invF p x) = x := invF_invol hp hx0 hxlt
  refine ⟨?_, ?_⟩
  · -- 2 ≤ invF p x.  Else invF p x = 1 (since > 0), then x = invF 1 = 1, contra.
    rcases Nat.lt_or_ge (invF p x) 2 with hlt | hge
    · exfalso
      have h1 : invF p x = 1 :=
        Nat.le_antisymm (Nat.le_of_lt_succ hlt) hy0
      have hxeq : x = 1 := by
        rw [h1] at hinvol; rw [invF_one hp] at hinvol; exact hinvol.symm
      rw [hxeq] at hx2; exact absurd hx2 (by decide)
    · exact hge
  · -- invF p x + 2 ≤ p.  Else invF p x = p-1 (since < p), then x = invF (p-1) = p-1, contra.
    rcases Nat.lt_or_ge (invF p x + 2) (p + 1) with hlt | hge
    · exact Nat.le_of_lt_succ hlt
    · exfalso
      have hpm1 : invF p x + 1 = p :=
        Nat.le_antisymm (Nat.succ_le_of_lt hylt) (Nat.le_of_succ_le_succ hge)
      have hival : invF p x = p - 1 := by
        have : p - 1 = invF p x + 1 - 1 := by rw [hpm1]
        rw [this, E213.Tactic.NatHelper.add_sub_cancel_right]
      have hxeq : x = p - 1 := by
        rw [hival] at hinvol; rw [invF_pred hp] at hinvol; exact hinvol.symm
      rw [hxeq] at hxp2
      have hpe : p - 1 + 2 = p + 1 := by
        have hsc : p - 1 + 1 = p := E213.Tactic.NatHelper.sub_add_cancel (Nat.le_of_lt
          (Nat.lt_of_lt_of_le (by decide) hp.two_le))
        show p - 1 + 2 = p + 1
        rw [show p - 1 + 2 = (p - 1 + 1) + 1 from rfl, hsc]
      rw [hpe] at hxp2
      exact absurd hxp2 (Nat.not_succ_le_self p)

/-! ## §D — membership and NoDup lemmas for the pairing fold -/

/-- Boolean NoDup: head not in tail, recursively. -/
def noDupV : List Nat → Bool
  | []     => true
  | a :: l => (!memV a l) && noDupV l

theorem memV_cons_self (a : Nat) (l : List Nat) : memV a (a :: l) = true := by
  rw [memV_cons]
  have : beqN a a = true := beqN_refl a
  rw [this]; rfl

/-- If `memV y (a :: l)` and `y ≠ a` (as values), then `memV y l`. -/
theorem memV_of_cons_ne {y a : Nat} {l : List Nat}
    (h : memV y (a :: l) = true) (hne : beqN a y = false) : memV y l = true := by
  rw [memV_cons, hne] at h
  rcases orB_elim h with h1 | h2
  · exact absurd h1 Bool.false_ne_true
  · exact h2

/-- Membership in `eraseV x l` implies membership in `l` (erasing only removes). -/
theorem memV_of_memV_eraseV {x y : Nat} :
    ∀ {l : List Nat}, memV y (eraseV x l) = true → memV y l = true
  | [], h => by exact absurd h Bool.false_ne_true
  | a :: l, h => by
    cases hb : beqN a x with
    | true =>
      -- eraseV x (a::l) = l
      have heq : eraseV x (a :: l) = l := by
        show (match beqN a x with | true => l | false => a :: eraseV x l) = l
        rw [hb]
      rw [heq] at h
      rw [memV_cons]; exact orB_inr (h)
    | false =>
      have heq : eraseV x (a :: l) = a :: eraseV x l := by
        show (match beqN a x with | true => l | false => a :: eraseV x l) = a :: eraseV x l
        rw [hb]
      rw [heq, memV_cons] at h
      rw [memV_cons]
      rcases orB_elim h with h1 | h2
      · exact orB_inl (h1)
      · exact orB_inr ((memV_of_memV_eraseV h2))

/-- For a NoDup list, membership in `eraseV x l` ⟺ member of `l` and `≠ x`. -/
theorem memV_eraseV_of_ne {x y : Nat} :
    ∀ {l : List Nat}, noDupV l = true → memV y l = true → beqN y x = false →
      memV y (eraseV x l) = true
  | [], _, h, _ => by exact absurd h Bool.false_ne_true
  | a :: l, hnd, h, hyx => by
    cases hb : beqN a x with
    | true =>
      -- a = x.  Then since y ≠ x, y ≠ a, so y ∈ l; and eraseV x (a::l) = l.
      have hax : a = x := eq_of_beqN hb
      have hay : beqN a y = false := by
        -- a = x, y ≠ x (beqN y x = false); so beqN a y = false
        cases hcase : beqN a y with
        | false => rfl
        | true =>
          have hay2 : a = y := eq_of_beqN hcase
          have hyx2 : beqN y x = true := by rw [← hay2, hb]
          rw [hyx2] at hyx; exact absurd hyx (by decide)
      have hyl : memV y l = true := memV_of_cons_ne h hay
      have heq : eraseV x (a :: l) = l := by
        show (match beqN a x with | true => l | false => a :: eraseV x l) = l
        rw [hb]
      rw [heq]; exact hyl
    | false =>
      have heq : eraseV x (a :: l) = a :: eraseV x l := by
        show (match beqN a x with | true => l | false => a :: eraseV x l) = a :: eraseV x l
        rw [hb]
      have hndl : noDupV l = true := by
        have := andB_elim hnd; exact this.2
      rw [heq, memV_cons]
      cases hcase : beqN a y with
      | true =>
        exact orB_inl (rfl)
      | false =>
        have hyl : memV y l = true := memV_of_cons_ne h hcase
        exact orB_inr ((memV_eraseV_of_ne hndl hyl hyx))

/-- Erasing preserves NoDup. -/
theorem noDupV_eraseV {x : Nat} :
    ∀ {l : List Nat}, noDupV l = true → noDupV (eraseV x l) = true
  | [], h => h
  | a :: l, h => by
    cases hb : beqN a x with
    | true =>
      have heq : eraseV x (a :: l) = l := by
        show (match beqN a x with | true => l | false => a :: eraseV x l) = l
        rw [hb]
      rw [heq]; exact (andB_elim h).2
    | false =>
      have heq : eraseV x (a :: l) = a :: eraseV x l := by
        show (match beqN a x with | true => l | false => a :: eraseV x l) = a :: eraseV x l
        rw [hb]
      have hpair := andB_elim h
      have hanil : memV a l = false := by
        have hnm : (!memV a l) = true := hpair.1
        cases hcase : memV a l with
        | false => rfl
        | true => rw [hcase] at hnm; exact absurd hnm (by decide)
      have hndl : noDupV l = true := hpair.2
      rw [heq]
      show ((!memV a (eraseV x l)) && noDupV (eraseV x l)) = true
      have ha_notin : memV a (eraseV x l) = false := by
        cases hcase : memV a (eraseV x l) with
        | false => rfl
        | true =>
          have : memV a l = true := memV_of_memV_eraseV hcase
          rw [this] at hanil; exact absurd hanil (by decide)
      rw [ha_notin]
      show (true && noDupV (eraseV x l)) = true
      have hrec := noDupV_eraseV (x := x) hndl
      rw [hrec]; rfl

/-- For NoDup `l`, erasing `b` removes it entirely. -/
theorem bnotin_eraseV_self {b : Nat} :
    ∀ {l : List Nat}, noDupV l = true → memV b l = true →
      memV b (eraseV b l) = true → False
  | [], _, h, _ => absurd h Bool.false_ne_true
  | a :: l, hnd, _, herase => by
    cases hb : beqN a b with
    | true =>
      -- eraseV b (a::l) = l; and a = b not in l (NoDup)
      have hab : a = b := eq_of_beqN hb
      have heq : eraseV b (a :: l) = l := by
        show (match beqN a b with | true => l | false => a :: eraseV b l) = l
        rw [hb]
      rw [heq] at herase
      -- herase : memV b l = true, but a = b ∉ l (NoDup head)
      have ha_notin : memV a l = false := by
        have hnm : (!memV a l) = true := (andB_elim hnd).1
        cases hcase : memV a l with
        | false => rfl
        | true => rw [hcase] at hnm; exact absurd hnm (by decide)
      rw [hab] at ha_notin
      rw [herase] at ha_notin; exact absurd ha_notin (by decide)
    | false =>
      -- eraseV b (a::l) = a :: eraseV b l; herase : memV b (a :: eraseV b l)
      have heq : eraseV b (a :: l) = a :: eraseV b l := by
        show (match beqN a b with | true => l | false => a :: eraseV b l) = a :: eraseV b l
        rw [hb]
      rw [heq, memV_cons, hb] at herase
      have hb_in_rest : memV b (eraseV b l) = true := by
        rcases orB_elim herase with h1 | h2
        · exact absurd h1 Bool.false_ne_true
        · exact h2
      have hndl : noDupV l = true := (andB_elim hnd).2
      have hb_in_l : memV b l = true := memV_of_memV_eraseV hb_in_rest
      exact bnotin_eraseV_self hndl hb_in_l hb_in_rest

/-! ## §E — the pairing fold: middle product ≡ 1 -/

/-- The inverse-pairing key step:  for a NoDup, middle-band, inverse-closed list,
    `prodMod p l = 1 % p`.  Fuel-bounded strong recursion on `l.length`. -/
theorem prodMod_pairing_fuel {p : Nat} (hp : IsPrime213 p) :
    ∀ (n : Nat) (l : List Nat), l.length ≤ n →
      noDupV l = true →
      (∀ x, memV x l = true → 2 ≤ x ∧ x + 2 ≤ p) →
      (∀ x, memV x l = true → memV (invF p x) l = true) →
      prodMod p l = 1 % p
  | _, [], _, _, _, _ => rfl
  | 0, a :: l, hlen, _, _, _ => by
      exact absurd hlen (Nat.not_succ_le_zero l.length ∘ (fun h => h))
  | n + 1, a :: l, hlen, hnd, hband, hclosed => by
    -- a is head; b := invF p a; b ≠ a; b ∈ l (since b ∈ a::l and b ≠ a).
    have hamem : memV a (a :: l) = true := memV_cons_self a l
    obtain ⟨ha2, hap2⟩ := hband a hamem
    have ha0 : 0 < a := Nat.lt_of_lt_of_le (by decide) ha2
    have halt : a < p := Nat.lt_of_lt_of_le
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self a) (Nat.succ_le_succ (Nat.le_succ a))) hap2
    -- b = invF p a
    have hbmem_all : memV (invF p a) (a :: l) = true := hclosed a hamem
    -- b ≠ a  (no self-inverse in the band)
    have hba_ne : beqN a (invF p a) = false := by
      cases hcase : beqN a (invF p a) with
      | false => rfl
      | true =>
        exfalso
        have : a = invF p a := eq_of_beqN hcase
        exact invF_ne_self hp ha2 hap2 this.symm
    -- b ∈ l (tail): from b ∈ a::l and beqN a b = false
    have hbmem_l : memV (invF p a) l = true := memV_of_cons_ne hbmem_all hba_ne
    -- prodMod p (a::l) = (a * prodMod p l) % p
    -- factor out b from l:  prodMod p l = (b * prodMod p (eraseV b l)) % p
    have hfact : prodMod p l = (invF p a * prodMod p (eraseV (invF p a) l)) % p :=
      prodMod_eraseV hbmem_l
    -- so prodMod p (a::l) = (a * ((b * R) % p)) % p = ((a*b) * R) % p = R % p (a*b ≡ 1)
    have hab1 : (a * invF p a) % p = 1 := invF_mul hp ha0 halt
    -- Let R := prodMod p (eraseV (invF p a) l)
    have hstep : prodMod p (a :: l)
        = prodMod p (eraseV (invF p a) l) % p := by
      rw [prodMod_cons, hfact]
      rw [← E213.Meta.Nat.MulMod213.mul_mod_right_pure a
            (invF p a * prodMod p (eraseV (invF p a) l)) p]
      rw [← E213.Tactic.NatHelper.mul_assoc a (invF p a)
            (prodMod p (eraseV (invF p a) l))]
      rw [E213.Meta.Nat.MulMod213.mul_mod_left_pure (a * invF p a)
            (prodMod p (eraseV (invF p a) l)) p, hab1, Nat.one_mul]
    -- Now show R = 1 % p by recursion on the erased list, which is NoDup, band, closed.
    -- rest = eraseV b l.  Its length ≤ n.
    have hlen_l : l.length ≤ n := Nat.le_of_succ_le_succ hlen
    have hndl : noDupV l = true := (andB_elim hnd).2
    -- eraseV b l has length < l.length ≤ n, so ≤ n
    have hlen_rest : (eraseV (invF p a) l).length ≤ n :=
      Nat.le_of_lt (Nat.lt_of_lt_of_le (length_eraseV_lt hbmem_l) hlen_l)
    -- NoDup preserved
    have hnd_rest : noDupV (eraseV (invF p a) l) = true := noDupV_eraseV hndl
    -- band preserved (subset of l)
    have hband_rest : ∀ x, memV x (eraseV (invF p a) l) = true → 2 ≤ x ∧ x + 2 ≤ p := by
      intro x hx
      have hxl : memV x l = true := memV_of_memV_eraseV hx
      have hxal : memV x (a :: l) = true := by
        rw [memV_cons]; exact orB_inr (hxl)
      exact hband x hxal
    -- closure preserved: the subtle step
    have hclosed_rest : ∀ x, memV x (eraseV (invF p a) l) = true →
        memV (invF p x) (eraseV (invF p a) l) = true := by
      intro x hx
      -- x ∈ rest ⟹ x ∈ l, x ≠ b.  inv x ∈ a::l (closure on full).  Show inv x ∈ rest.
      have hxl : memV x l = true := memV_of_memV_eraseV hx
      have hxal : memV x (a :: l) = true := by
        rw [memV_cons]; exact orB_inr (hxl)
      -- band facts for x
      obtain ⟨hx2, hxp2⟩ := hband x hxal
      have hx0 : 0 < x := Nat.lt_of_lt_of_le (by decide) hx2
      have hxlt : x < p := Nat.lt_of_lt_of_le
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self x) (Nat.succ_le_succ (Nat.le_succ x))) hxp2
      -- inv x ∈ a::l
      have hinvx_al : memV (invF p x) (a :: l) = true := hclosed x hxal
      -- inv x ≠ a:  else x = inv a = b, but x ∈ rest means x ≠ b.  Need x ≠ b.
      -- x ≠ b (= invF p a):  x ∈ eraseV b l with NoDup ⟹ x ≠ b.
      -- Prove beqN x (invF p a) = false from: x ∈ rest, and if x = b then b ∈ rest contradicts NoDup-erase.
      have hxb_ne : beqN x (invF p a) = false := by
        cases hcase : beqN x (invF p a) with
        | false => rfl
        | true =>
          exfalso
          have hxb : x = invF p a := eq_of_beqN hcase
          -- then memV b (eraseV b l) = true, but erasing b from NoDup l removes it
          rw [hxb] at hx
          -- b ∈ eraseV b l, but for NoDup l, b occurs once, erased ⟹ not present
          exact bnotin_eraseV_self hndl hbmem_l hx
      -- inv x ≠ a:  if inv x = a then x = inv(inv x) = inv a = b, contra x ≠ b
      have hinvx_ne_a : beqN a (invF p x) = false := by
        cases hcase : beqN a (invF p x) with
        | false => rfl
        | true =>
          exfalso
          have haix : a = invF p x := eq_of_beqN hcase
          -- apply invF to both sides:  invF a = invF (invF x) = x
          have hbx : invF p a = x := by
            rw [haix]; exact invF_invol hp hx0 hxlt
          -- so beqN x (invF p a) should be true, contradicting hxb_ne
          have : beqN x (invF p a) = true := beqN_of_eq hbx.symm
          rw [this] at hxb_ne; exact absurd hxb_ne (by decide)
      -- inv x ∈ l (tail), and inv x ≠ b ⟹ inv x ∈ rest
      have hinvx_l : memV (invF p x) l = true := memV_of_cons_ne hinvx_al hinvx_ne_a
      -- inv x ≠ b:  if inv x = b = inv a then x = a (inv injective), but a ∉ rest's source... need x ≠ a.
      -- x ≠ a:  x ∈ l, NoDup (a::l) ⟹ a ∉ l ⟹ x ≠ a.
      have ha_notin_l : memV a l = false := by
        have hnm : (!memV a l) = true := (andB_elim hnd).1
        cases hcase : memV a l with
        | false => rfl
        | true => rw [hcase] at hnm; exact absurd hnm (by decide)
      have hxa_ne : beqN (invF p x) (invF p a) = false := by
        cases hcase : beqN (invF p x) (invF p a) with
        | false => rfl
        | true =>
          exfalso
          have heqinv : invF p x = invF p a := eq_of_beqN hcase
          -- apply invF: x = a
          have : invF p (invF p x) = invF p (invF p a) := by rw [heqinv]
          rw [invF_invol hp hx0 hxlt, invF_invol hp ha0 halt] at this
          -- this : x = a;  but x ∈ l, a ∉ l
          have : memV a l = true := this ▸ hxl
          rw [this] at ha_notin_l; exact absurd ha_notin_l (by decide)
      exact memV_eraseV_of_ne hndl hinvx_l hxa_ne
    -- recurse
    have hRval : prodMod p (eraseV (invF p a) l) = 1 % p :=
      prodMod_pairing_fuel hp n (eraseV (invF p a) l) hlen_rest hnd_rest hband_rest hclosed_rest
    rw [hstep, hRval]
    exact E213.Meta.Nat.AddMod213.mod_mod 1 p

/-! ## §F — assembling Wilson -/

/-- Every element of `downFrom n` is `≤ n`. -/
theorem memV_downFrom_le : ∀ (n y : Nat), memV y (downFrom n) = true → y ≤ n
  | 0,     _, h => by exact absurd h Bool.false_ne_true
  | n + 1, y, h => by
    have h2 : memV y ((n + 1) :: downFrom n) = true := h
    rw [memV_cons] at h2
    rcases orB_elim h2 with h1 | hr
    · exact Nat.le_of_eq (eq_of_beqN h1).symm
    · exact Nat.le_succ_of_le (memV_downFrom_le n y hr)

/-- Every element of `downFrom n` is `≥ 1`. -/
theorem memV_downFrom_pos : ∀ (n y : Nat), memV y (downFrom n) = true → 1 ≤ y
  | 0,     _, h => by exact absurd h Bool.false_ne_true
  | n + 1, y, h => by
    have h2 : memV y ((n + 1) :: downFrom n) = true := h
    rw [memV_cons] at h2
    rcases orB_elim h2 with h1 | hr
    · exact (eq_of_beqN h1) ▸ Nat.succ_le_succ (Nat.zero_le n)
    · exact memV_downFrom_pos n y hr

/-- `downFrom n` is NoDup. -/
theorem noDupV_downFrom : ∀ n, noDupV (downFrom n) = true
  | 0     => rfl
  | n + 1 => by
    show ((!memV (n + 1) (downFrom n)) && noDupV (downFrom n)) = true
    have hmem : memV (n + 1) (downFrom n) = false := by
      cases hcase : memV (n + 1) (downFrom n) with
      | false => rfl
      | true => exact absurd (memV_downFrom_le n (n + 1) hcase) (Nat.not_succ_le_self n)
    rw [hmem]
    show (true && noDupV (downFrom n)) = true
    rw [noDupV_downFrom n]; rfl

/-- `band k = [k, k-1, ..., 2]` — the residues `2..k` in descending order (empty if `k < 2`). -/
def band : Nat → List Nat
  | 0          => []
  | 1          => []
  | (k + 2)    => (k + 2) :: band (k + 1)

/-- `downFrom (k+1) = band (k+1) ++ [1]` — split off the trailing `1`. -/
theorem downFrom_eq_band_app : ∀ k, downFrom (k + 1) = band (k + 1) ++ [1]
  | 0     => rfl
  | k + 1 => by
    show (k + 2) :: downFrom (k + 1) = band (k + 2) ++ [1]
    show (k + 2) :: downFrom (k + 1) = ((k + 2) :: band (k + 1)) ++ [1]
    show (k + 2) :: downFrom (k + 1) = (k + 2) :: (band (k + 1) ++ [1])
    rw [downFrom_eq_band_app k]

/-- `prodMod` over `band ++ [1]` equals `prodMod` over `band` (trailing `1` is identity). -/
theorem prodMod_band_app_one (p : Nat) (hp1 : 1 < p) :
    ∀ l : List Nat, prodMod p (l ++ [1]) = prodMod p l
  | []      => by
    show prodMod p [1] = 1 % p
    show (1 * (1 % p)) % p = 1 % p
    rw [Nat.one_mul, E213.Meta.Nat.AddMod213.mod_mod]
  | a :: l  => by
    show prodMod p (a :: (l ++ [1])) = prodMod p (a :: l)
    rw [prodMod_cons, prodMod_cons, prodMod_band_app_one p hp1 l]

/-- Every element of `band k` is in `[2, k]`. -/
theorem memV_band_bound : ∀ (k y : Nat), memV y (band k) = true → 2 ≤ y ∧ y ≤ k
  | 0,     _, h => by exact absurd h Bool.false_ne_true
  | 1,     _, h => by exact absurd h Bool.false_ne_true
  | k + 2, y, h => by
    have h2 : memV y ((k + 2) :: band (k + 1)) = true := h
    rw [memV_cons] at h2
    rcases orB_elim h2 with h1 | hr
    · have hy : y = k + 2 := (eq_of_beqN h1).symm
      exact ⟨hy ▸ Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k)), Nat.le_of_eq hy⟩
    · obtain ⟨hlo, hhi⟩ := memV_band_bound (k + 1) y hr
      exact ⟨hlo, Nat.le_succ_of_le hhi⟩

/-- Membership completeness: every `y ∈ [2, k]` is in `band k`. -/
theorem memV_band_complete : ∀ (k y : Nat), 2 ≤ y → y ≤ k → memV y (band k) = true
  | 0,     y, h2, hk => by exact absurd (Nat.le_trans h2 hk) (by decide)
  | 1,     y, h2, hk => by exact absurd (Nat.le_trans h2 hk) (by decide)
  | k + 2, y, h2, hk => by
    show memV y ((k + 2) :: band (k + 1)) = true
    rw [memV_cons]
    -- y ≤ k+2.  Either y = k+2 or y ≤ k+1.
    rcases Nat.lt_or_ge y (k + 2) with hlt | hge
    · -- y ≤ k+1
      have hyk1 : y ≤ k + 1 := Nat.le_of_lt_succ hlt
      exact orB_inr ((memV_band_complete (k + 1) y h2 hyk1))
    · -- y = k+2
      have hy : y = k + 2 := Nat.le_antisymm hk hge
      exact orB_inl ((beqN_of_eq hy.symm))

/-- `band k` is NoDup. -/
theorem noDupV_band : ∀ k, noDupV (band k) = true
  | 0     => rfl
  | 1     => rfl
  | k + 2 => by
    show ((!memV (k + 2) (band (k + 1))) && noDupV (band (k + 1))) = true
    have hmem : memV (k + 2) (band (k + 1)) = false := by
      cases hcase : memV (k + 2) (band (k + 1)) with
      | false => rfl
      | true =>
        have := (memV_band_bound (k + 1) (k + 2) hcase).2
        exact absurd this (Nat.not_succ_le_self (k + 1))
    rw [hmem]
    show (true && noDupV (band (k + 1))) = true
    rw [noDupV_band (k + 1)]; rfl

/-! ## §G — band product ≡ 1, and Wilson -/

/-- For prime `p`, the band product `[p-2, ..., 2]` is `≡ 1 (mod p)`. -/
theorem band_product_one {p : Nat} (hp : IsPrime213 p) :
    prodMod p (band (p - 2)) = 1 % p := by
  have hp2 : 2 ≤ p := hp.two_le
  -- helper: y ≤ p-2 ↔ y+2 ≤ p
  have hle_iff : ∀ y : Nat, y ≤ p - 2 → y + 2 ≤ p := by
    intro y hy
    have : y + 2 ≤ (p - 2) + 2 := Nat.add_le_add_right hy 2
    rw [E213.Tactic.NatHelper.sub_add_cancel hp2] at this; exact this
  have hband : ∀ x, memV x (band (p - 2)) = true → 2 ≤ x ∧ x + 2 ≤ p := by
    intro x hx
    obtain ⟨hlo, hhi⟩ := memV_band_bound (p - 2) x hx
    exact ⟨hlo, hle_iff x hhi⟩
  have hclosed : ∀ x, memV x (band (p - 2)) = true → memV (invF p x) (band (p - 2)) = true := by
    intro x hx
    obtain ⟨hx2, hxp2⟩ := hband x hx
    obtain ⟨hi2, hip2⟩ := invF_mid hp hx2 hxp2
    -- invF p x ≤ p-2 from invF p x + 2 ≤ p
    have hi_le : invF p x ≤ p - 2 := by
      have : invF p x + 2 - 2 ≤ p - 2 := Nat.sub_le_sub_right hip2 2
      rw [E213.Tactic.NatHelper.add_sub_cancel_right] at this; exact this
    exact memV_band_complete (p - 2) (invF p x) hi2 hi_le
  exact prodMod_pairing_fuel hp (band (p - 2)).length (band (p - 2))
    (Nat.le_refl _) (noDupV_band (p - 2)) hband hclosed

/-- ★★★ **Wilson's theorem.**  For prime `p`, `(p-1)! ≡ -1 (mod p)`, i.e.
    `(fact (p-1)) % p = p - 1`. -/
theorem wilson {p : Nat} (hp : IsPrime213 p) : (fact (p - 1)) % p = p - 1 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : 1 < p := Nat.lt_of_lt_of_le (by decide) hp2
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp2
  -- p - 1 = (p - 2) + 1
  obtain ⟨k, hk⟩ : ∃ k, p = k + 2 := ⟨p - 2, (E213.Tactic.NatHelper.sub_add_cancel hp2).symm⟩
  -- fact (p-1) % p = prodMod p (downFrom (p-1))
  rw [← prodMod_downFrom p (p - 1)]
  -- p - 1 = k + 1
  have hpm1 : p - 1 = k + 1 := by rw [hk]; rfl
  have hpm2 : p - 2 = k := by rw [hk]; rfl
  rw [hpm1]
  -- downFrom (k+1) = (k+1) :: downFrom k  (definitional)
  show prodMod p ((k + 1) :: downFrom k) = (k + 2) - 1
  rw [prodMod_cons]
  -- prodMod p (downFrom k) = 1 % p:
  --   downFrom k = band k ++ [1] when k ≥ 1; for k = 0, downFrom 0 = [], prodMod = 1 % p too.
  have hdk : prodMod p (downFrom k) = 1 % p := by
    cases k with
    | zero => rfl
    | succ k' =>
      rw [downFrom_eq_band_app k', prodMod_band_app_one p hp1 (band (k' + 1))]
      have := band_product_one hp; rw [hpm2] at this; exact this
  rw [hdk]
  have h1mod : (1 : Nat) % p = 1 := Nat.mod_eq_of_lt hp1
  rw [h1mod, Nat.mul_one]
  have hk1lt : k + 1 < p := by rw [hk]; exact Nat.lt_succ_self (k + 1)
  rw [Nat.mod_eq_of_lt hk1lt]
  show k + 1 = (k + 2) - 1
  rfl






end E213.Lib.Math.NumberTheory.ModArith.WilsonTheorem
