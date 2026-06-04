import E213.Meta.Int213.Core
import E213.Meta.Int213.PolyIntMTactic

/-!
# PolyZ — integer-coefficient polynomials (∅-axiom)

A polynomial over `ℤ` is a coefficient list `[a₀, a₁, …]` (low-to-high), evaluated by
Horner.  This is the **entry ring** for the characteristic-polynomial determinant
`det (xI − M)` used in the integer Cayley–Hamilton theorem (`Linalg213.CayleyHamilton`,
toward the C-finite Hadamard product `cfiniteZ_mul`).

The companion `Polynomial213` is over `ℕ`; the characteristic polynomial needs **signed**
coefficients (`xI − M`), so this module rebuilds the layer over `ℤ`.

All operations come with an `eval` **soundness** lemma (each op commutes with evaluation),
making `PolyZ` a commutative-ring reflection of `Int`.  All ∅-axiom (over `Int213`).
-/

namespace E213.Lib.Math.Algebra.PolyZ

/-- An integer polynomial: coefficient list, low-to-high (`[a₀, a₁, a₂] = a₀ + a₁x + a₂x²`). -/
abbrev PolyZ := List Int

/-- Horner evaluation `p(x)`. -/
def eval : PolyZ → Int → Int
  | [],     _ => 0
  | a :: p, x => a + x * eval p x

/-- The constant polynomial `c`. -/
def C (c : Int) : PolyZ := [c]

/-- The polynomial `X`. -/
def Xp : PolyZ := [0, 1]

/-- Coefficient-wise addition. -/
def addP : PolyZ → PolyZ → PolyZ
  | [],     q      => q
  | a :: p, []     => a :: p
  | a :: p, b :: q => (a + b) :: addP p q

/-- Coefficient-wise negation. -/
def negP (p : PolyZ) : PolyZ := p.map (fun a => - a)

/-- Scalar multiple. -/
def scaleP (k : Int) (p : PolyZ) : PolyZ := p.map (fun a => k * a)

/-- Multiply by `X` (shift up by one degree). -/
def shiftP (p : PolyZ) : PolyZ := 0 :: p

/-- Polynomial multiplication. -/
def mulP : PolyZ → PolyZ → PolyZ
  | [],     _ => []
  | a :: p, q => addP (scaleP a q) (shiftP (mulP p q))

/-- The `k`-th coefficient (`0` past the end). -/
def coeff : PolyZ → Nat → Int
  | [],     _     => 0
  | a :: _, 0     => a
  | _ :: p, k + 1 => coeff p k

/-! ## ℤ helpers (`Int213` lacks `add_zero` / `mul_zero` / `one_mul`) -/

/-- `a + 0 = a`. -/
theorem add_zero' (a : Int) : a + 0 = a := by
  rw [E213.Meta.Int213.add_comm, E213.Meta.Int213.zero_add]

/-- `a * 0 = 0`. -/
theorem mul_zero' (a : Int) : a * 0 = 0 := by
  rw [E213.Meta.Int213.mul_comm, E213.Meta.Int213.zero_mul]

/-- `1 * a = a`. -/
theorem one_mul' (a : Int) : 1 * a = a := by
  rw [E213.Meta.Int213.mul_comm, E213.Meta.Int213.mul_one]

/-- `-0 = 0`. -/
theorem neg_zero' : -(0 : Int) = 0 :=
  (E213.Meta.Int213.zero_add (-0)).symm.trans (E213.Meta.Int213.add_neg_cancel 0)

/-! ## Evaluation soundness — each operation commutes with `eval` -/

/-- `eval` of a constant. -/
theorem eval_C (c : Int) (x : Int) : eval (C c) x = c := by
  show c + x * eval [] x = c
  rw [show eval [] x = 0 from rfl, mul_zero', add_zero']

/-- `eval` of `X`. -/
theorem eval_Xp (x : Int) : eval Xp x = x := by
  show (0 : Int) + x * (1 + x * eval [] x) = x
  rw [show eval [] x = 0 from rfl, mul_zero', add_zero', E213.Meta.Int213.mul_one,
      E213.Meta.Int213.zero_add]

/-- ★ `eval` is additive. -/
theorem eval_addP : ∀ (p q : PolyZ) (x : Int), eval (addP p q) x = eval p x + eval q x
  | [],     q,      x => by
    show eval q x = 0 + eval q x
    rw [E213.Meta.Int213.zero_add]
  | a :: p, [],     x => by
    show a + x * eval p x = (a + x * eval p x) + 0
    rw [add_zero']
  | a :: p, b :: q, x => by
    show (a + b) + x * eval (addP p q) x = (a + x * eval p x) + (b + x * eval q x)
    rw [eval_addP p q x, E213.Meta.Int213.mul_add]
    -- (a+b) + (x*ep + x*eq) = (a + x*ep) + (b + x*eq)
    rw [E213.Meta.Int213.add_assoc, E213.Meta.Int213.add_assoc,
        ← E213.Meta.Int213.add_assoc b (x * eval p x), ← E213.Meta.Int213.add_assoc (x * eval p x) b,
        E213.Meta.Int213.add_comm (x * eval p x) b]

/-- ★ `eval` of a scalar multiple. -/
theorem eval_scaleP (k : Int) : ∀ (p : PolyZ) (x : Int), eval (scaleP k p) x = k * eval p x
  | [],     x => (mul_zero' k).symm
  | a :: p, x => by
    show k * a + x * eval (scaleP k p) x = k * (a + x * eval p x)
    rw [eval_scaleP k p x, E213.Meta.Int213.mul_add]
    -- k*a + x*(k*ep) = k*a + k*(x*ep)
    rw [← E213.Meta.Int213.mul_assoc x k, E213.Meta.Int213.mul_comm x k,
        E213.Meta.Int213.mul_assoc k x]

/-- `eval` of `X · p` (shift). -/
theorem eval_shiftP (p : PolyZ) (x : Int) : eval (shiftP p) x = x * eval p x := by
  show (0 : Int) + x * eval p x = x * eval p x
  rw [E213.Meta.Int213.zero_add]

/-- ★ `eval` is negation-compatible. -/
theorem eval_negP : ∀ (p : PolyZ) (x : Int), eval (negP p) x = - eval p x
  | [],     x => by
    show (0 : Int) = -0
    rw [show -(0:Int) = 0 from (E213.Meta.Int213.zero_add (-0)).symm.trans
        (E213.Meta.Int213.add_neg_cancel 0)]
  | a :: p, x => by
    show (- a) + x * eval (negP p) x = -(a + x * eval p x)
    rw [eval_negP p x, E213.Meta.Int213.mul_neg, E213.Meta.Int213.neg_add]

/-- ★★ `eval` is multiplicative. -/
theorem eval_mulP : ∀ (p q : PolyZ) (x : Int), eval (mulP p q) x = eval p x * eval q x
  | [],     q, x => by
    show (0 : Int) = 0 * eval q x
    rw [E213.Meta.Int213.zero_mul]
  | a :: p, q, x => by
    show eval (addP (scaleP a q) (shiftP (mulP p q))) x = (a + x * eval p x) * eval q x
    rw [eval_addP, eval_scaleP, eval_shiftP, eval_mulP p q x,
        E213.Meta.Int213.add_mul, E213.Meta.Int213.mul_assoc]

/-! ## Coefficient soundness for `addP` / `negP` -/

/-- `coeff` of a sum. -/
theorem coeff_addP : ∀ (p q : PolyZ) (k : Nat), coeff (addP p q) k = coeff p k + coeff q k
  | [],      q,      k     => by show coeff q k = 0 + coeff q k; rw [E213.Meta.Int213.zero_add]
  | a :: p', [],     k     => by show coeff (a :: p') k = coeff (a :: p') k + 0; rw [add_zero']
  | _ :: _,  _ :: _, 0     => rfl
  | _ :: p', _ :: q', k + 1 => coeff_addP p' q' k

/-- `coeff` of a negation. -/
theorem coeff_negP : ∀ (p : PolyZ) (k : Nat), coeff (negP p) k = - coeff p k
  | [],      _     => neg_zero'.symm
  | _ :: _,  0     => rfl
  | _ :: p', k + 1 => coeff_negP p' k

/-- `coeff` of the zero polynomial. -/
theorem coeff_nil (k : Nat) : coeff ([] : PolyZ) k = 0 := rfl

/-- `coeff` of a scalar multiple. -/
theorem coeff_scaleP : ∀ (c : Int) (p : PolyZ) (k : Nat), coeff (scaleP c p) k = c * coeff p k
  | c, [],      _     => (mul_zero' c).symm
  | _, _ :: _,  0     => rfl
  | c, _ :: p', k + 1 => coeff_scaleP c p' k

/-- `coeff` of `X·p` at `0`. -/
theorem coeff_shiftP_zero (p : PolyZ) : coeff (shiftP p) 0 = 0 := rfl

/-- `coeff` of `X·p` at `k+1`. -/
theorem coeff_shiftP_succ (p : PolyZ) (k : Nat) : coeff (shiftP p) (k + 1) = coeff p k := rfl

/-- The constant `[0]` has all coefficients `0`. -/
theorem coeff_c_zero : ∀ (k : Nat), coeff ([0] : PolyZ) k = 0
  | 0     => rfl
  | _ + 1 => rfl

/-- `coeff` of a product by a degree-`0` polynomial `[c]`. -/
theorem coeff_mulP_single (c : Int) (q : PolyZ) (k : Nat) :
    coeff (mulP [c] q) k = c * coeff q k := by
  show coeff (addP (scaleP c q) (shiftP (mulP ([] : PolyZ) q))) k = c * coeff q k
  rw [coeff_addP, coeff_scaleP, show shiftP (mulP ([] : PolyZ) q) = ([0] : PolyZ) from rfl,
      coeff_c_zero, add_zero']

/-- `coeff` of a product by a degree-`≤1` polynomial `[c, d]` at `0`. -/
theorem coeff_mulP_pair_zero (c d : Int) (q : PolyZ) :
    coeff (mulP [c, d] q) 0 = c * coeff q 0 := by
  show coeff (addP (scaleP c q) (shiftP (mulP [d] q))) 0 = c * coeff q 0
  rw [coeff_addP, coeff_scaleP, coeff_shiftP_zero, add_zero']

/-- `coeff` of a product by a degree-`≤1` polynomial `[c, d]` at `k+1`. -/
theorem coeff_mulP_pair_succ (c d : Int) (q : PolyZ) (k : Nat) :
    coeff (mulP [c, d] q) (k + 1) = c * coeff q (k + 1) + d * coeff q k := by
  show coeff (addP (scaleP c q) (shiftP (mulP [d] q))) (k + 1) = c * coeff q (k + 1) + d * coeff q k
  rw [coeff_addP, coeff_scaleP, coeff_shiftP_succ, coeff_mulP_single]

/-! ## Degree bound — `degLe p d` (`deg p ≤ d`) and its closure laws -/

/-- `p` has degree `≤ d`: all coefficients above index `d` vanish. -/
def degLe (p : PolyZ) (d : Nat) : Prop := ∀ m, d < m → coeff p m = 0

/-- The zero polynomial: all coefficients vanish. -/
def IsZeroP (p : PolyZ) : Prop := ∀ m, coeff p m = 0

theorem degLe_nil (d : Nat) : degLe [] d := fun _ _ => rfl

/-- A larger degree bound is weaker. -/
theorem degLe_mono {p : PolyZ} {d e : Nat} (h : degLe p d) (hde : d ≤ e) : degLe p e :=
  fun m hm => h m (Nat.lt_of_le_of_lt hde hm)

theorem degLe_addP {p q : PolyZ} {d : Nat} (hp : degLe p d) (hq : degLe q d) :
    degLe (addP p q) d :=
  fun m hm => by rw [coeff_addP, hp m hm, hq m hm, add_zero']

theorem degLe_scaleP {p : PolyZ} {d : Nat} (c : Int) (hp : degLe p d) : degLe (scaleP c p) d :=
  fun m hm => by rw [coeff_scaleP, hp m hm, mul_zero']

theorem degLe_shiftP {p : PolyZ} {d : Nat} (hp : degLe p d) : degLe (shiftP p) (d + 1) := by
  intro m hm
  cases m with
  | zero => exact absurd hm (Nat.not_lt_zero _)
  | succ m' => rw [coeff_shiftP_succ]; exact hp m' (Nat.lt_of_succ_lt_succ hm)

/-- Drop the head: `deg (a :: p') ≤ d+1 ⟹ deg p' ≤ d`. -/
theorem degLe_tail {a : Int} {p' : PolyZ} {d : Nat} (h : degLe (a :: p') (d + 1)) : degLe p' d :=
  fun m hm => h (m + 1) (Nat.succ_lt_succ hm)

/-- A degree-`0` cons has a zero tail. -/
theorem isZeroP_tail_of_degLe_zero {a : Int} {p' : PolyZ} (h : degLe (a :: p') 0) : IsZeroP p' :=
  fun m => h (m + 1) (Nat.succ_pos m)

theorem isZeroP_shiftP {p : PolyZ} (h : IsZeroP p) : IsZeroP (shiftP p) := by
  intro m
  cases m with
  | zero   => rfl
  | succ k => exact h k

/-- `0 · q = 0` (the zero polynomial absorbs on the left). -/
theorem mulP_isZeroP_left : ∀ (p : PolyZ), IsZeroP p → ∀ (q : PolyZ), IsZeroP (mulP p q)
  | [],      _, _ => fun _ => rfl
  | a :: p', h, q => fun m => by
    have ha : a = 0 := h 0
    have hmul : IsZeroP (mulP p' q) := mulP_isZeroP_left p' (fun k => h (k + 1)) q
    show coeff (addP (scaleP a q) (shiftP (mulP p' q))) m = 0
    rw [coeff_addP, coeff_scaleP, ha, E213.Meta.Int213.zero_mul,
        isZeroP_shiftP hmul m, E213.Meta.Int213.zero_add]

/-- ★ **Degree of a product** is `≤` the sum of degrees. -/
theorem degLe_mulP : ∀ (p : PolyZ) (dp : Nat) (q : PolyZ) (dq : Nat),
    degLe p dp → degLe q dq → degLe (mulP p q) (dp + dq)
  | [],      _,  _, _,  _,  _  => fun m _ => rfl
  | a :: p', dp, q, dq, hp, hq => by
    show degLe (addP (scaleP a q) (shiftP (mulP p' q))) (dp + dq)
    apply degLe_addP
    · exact degLe_mono (degLe_scaleP a hq) (Nat.le_add_left dq dp)
    · cases dp with
      | zero =>
        have hz : IsZeroP (mulP p' q) := mulP_isZeroP_left p' (isZeroP_tail_of_degLe_zero hp) q
        exact fun m _ => isZeroP_shiftP hz m
      | succ d' =>
        have hp' : degLe p' d' := degLe_tail hp
        rw [Nat.succ_add]
        exact degLe_shiftP (degLe_mulP p' d' q dq hp' hq)

/-- Coefficients above the degree bound vanish (the usable form). -/
theorem coeff_eq_zero_of_degLe {p : PolyZ} {d : Nat} (h : degLe p d) {m : Nat} (hm : d < m) :
    coeff p m = 0 := h m hm

/-! ## Uniqueness — synthetic division, root bound, coefficient identity -/

/-- `a - b = 0 → a = b` over `ℤ`. -/
theorem sub_eq_zero_imp {a b : Int} (h : a - b = 0) : a = b := by
  rw [← E213.Meta.Int213.sub_add_cancel_int a b, h, E213.Meta.Int213.zero_add]

/-- `a + -b = 0 → a = b` over `ℤ`. -/
theorem eq_of_add_neg {a b : Int} (h : a + -b = 0) : a = b := by
  have hb : (a + -b) + b = 0 + b := by rw [h]
  rwa [E213.Meta.Int213.add_assoc, E213.Meta.Int213.add_left_neg, add_zero',
       E213.Meta.Int213.zero_add] at hb

/-- Synthetic-division quotient of `p` by `(X − r)` (low-to-high, no trailing zero). -/
def synth : PolyZ → Int → PolyZ
  | [],          _ => []
  | [_],         _ => []
  | a :: p',     r => eval p' r :: synth p' r

/-- **Factor theorem**: `p(x) = p(r) + (x − r)·q(x)` where `q = synth p r`. -/
theorem eval_synth : ∀ (p : PolyZ) (r x : Int),
    eval p x = eval p r + (x - r) * eval (synth p r) x
  | [],              r, x => by
    show (0 : Int) = 0 + (x - r) * 0
    rw [mul_zero', E213.Meta.Int213.zero_add]
  | [a],             r, x => by
    show a + x * eval ([] : PolyZ) x = (a + r * eval ([] : PolyZ) r) + (x - r) * eval ([] : PolyZ) x
    rw [show eval ([] : PolyZ) x = 0 from rfl, show eval ([] : PolyZ) r = 0 from rfl]
    ring_intZ
  | a :: b :: rest, r, x => by
    show a + x * eval (b :: rest) x
       = (a + r * eval (b :: rest) r)
         + (x - r) * (eval (b :: rest) r + x * eval (synth (b :: rest) r) x)
    rw [eval_synth (b :: rest) r x]
    ring_intZ

/-- `synth` drops exactly one degree (length decreases by one). -/
theorem length_synth_cons (a : Int) (p' : PolyZ) (r : Int) :
    (synth (a :: p') r).length + 1 = (a :: p').length := by
  induction p' generalizing a with
  | nil => rfl
  | cons b rest ih =>
    show ((eval (b :: rest) r :: synth (b :: rest) r).length) + 1 = (a :: b :: rest).length
    show (synth (b :: rest) r).length + 1 + 1 = (b :: rest).length + 1
    rw [ih b]

/-- ★ **Root bound**: a polynomial of length `≤ L` with `L` distinct roots is the zero function. -/
theorem roots_bound (r : Nat → Int) (hinj : ∀ i j, r i = r j → i = j) :
    ∀ (L : Nat) (p : PolyZ), p.length ≤ L → (∀ i, i < L → eval p (r i) = 0) →
      ∀ x, eval p x = 0
  | 0,     [],       _,    _,      _ => rfl
  | 0,     a :: _,   hlen, _,      _ => absurd hlen (Nat.not_succ_le_zero _)
  | L + 1, [],       _,    _,      _ => rfl
  | L + 1, a :: p',  hlen, hroots, x => by
    have hrL : eval (a :: p') (r L) = 0 := hroots L (Nat.lt_succ_self L)
    have hlenq : (synth (a :: p') (r L)).length ≤ L := by
      have hl := length_synth_cons a p' (r L)
      rw [← hl] at hlen
      exact Nat.le_of_succ_le_succ hlen
    have hqroots : ∀ i, i < L → eval (synth (a :: p') (r L)) (r i) = 0 := by
      intro i hi
      have hfac := eval_synth (a :: p') (r L) (r i)
      rw [hrL, hroots i (Nat.lt_succ_of_lt hi), E213.Meta.Int213.zero_add] at hfac
      have hne : r i - r L ≠ 0 := fun he =>
        Nat.ne_of_lt hi (hinj i L (sub_eq_zero_imp he))
      rcases E213.Meta.Int213.mul_eq_zero hfac.symm with h0 | h0
      · exact absurd h0 hne
      · exact h0
    have hq : ∀ y, eval (synth (a :: p') (r L)) y = 0 :=
      roots_bound r hinj L (synth (a :: p') (r L)) hlenq hqroots
    have hfacx := eval_synth (a :: p') (r L) x
    rw [hrL, E213.Meta.Int213.zero_add, hq x, mul_zero'] at hfacx
    exact hfacx

/-- ★ **Coefficient identity**: a polynomial that vanishes everywhere has all coefficients `0`. -/
theorem coeff_zero_of_eval_zero : ∀ (p : PolyZ), (∀ x, eval p x = 0) → ∀ k, coeff p k = 0
  | [],      _ => fun _ => rfl
  | a :: p', h => by
    have ha : a = 0 := by
      have h0 := h 0
      rw [show eval (a :: p') 0 = a + 0 * eval p' 0 from rfl, E213.Meta.Int213.zero_mul,
          add_zero'] at h0
      exact h0
    have hmul : ∀ x, x * eval p' x = 0 := by
      intro x
      have hx := h x
      rw [show eval (a :: p') x = a + x * eval p' x from rfl, ha, E213.Meta.Int213.zero_add] at hx
      exact hx
    have hp' : ∀ x, eval p' x = 0 :=
      roots_bound (fun i => Int.ofNat (i + 1))
        (fun i j he => Nat.succ.inj (Int.ofNat.inj he)) p'.length p' (Nat.le_refl _)
        (fun i _ => by
          rcases E213.Meta.Int213.mul_eq_zero (hmul (Int.ofNat (i + 1))) with h0 | h0
          · exact absurd h0 (fun he => Nat.noConfusion (Int.ofNat.inj he))
          · exact h0)
    intro k
    cases k with
    | zero => exact ha
    | succ k' => exact coeff_zero_of_eval_zero p' hp' k'

/-- ★★ **Uniqueness**: two polynomials agreeing at every integer have equal coefficients. -/
theorem coeff_unique (p q : PolyZ) (h : ∀ x, eval p x = eval q x) :
    ∀ k, coeff p k = coeff q k := by
  have hd : ∀ x, eval (addP p (negP q)) x = 0 := by
    intro x
    rw [eval_addP, eval_negP, h x, E213.Meta.Int213.add_neg_cancel]
  have hc := coeff_zero_of_eval_zero (addP p (negP q)) hd
  intro k
  have hk := hc k
  rw [coeff_addP, coeff_negP] at hk
  exact eq_of_add_neg hk

end E213.Lib.Math.Algebra.PolyZ
