import E213.Lens.Number.Nat213.EuclidUnique

/-!
# Lens.Number.Nat213.FTA — the Fundamental Theorem of Arithmetic over the Raw-generated ℕ₊ (∅-axiom)

The **descent leg**, M4 — the *capstone* (`research-notes/frontiers/the_descent_leg.md`).  The FTA,
**generated** over `Nat213` (the distinguishing's own counting object), not re-derived over Lean `Nat`:

  * **existence** — every `n` is a product of irreducibles (`Factorization.exists_factorization`);
  * **uniqueness** — any two irreducible factorizations of `n` are permutations of each other
    (`factorization_unique`), via `EuclidUnique.prime_dvd_prod` + native cancellation
    (`Order.mul_left_cancel`).

Everything stays `Nat213`-native and ∅-axiom: a **native, `propext`-free `Perm`** (the core
`List.Perm` lemmas import `propext`), a native `erase` with its `prod`/membership laws, and the
decidable equality split (`by_cases`, structural `DecidableEq`, no `Classical`).

`fta` bundles both halves — the moment "mathematics is the distinguishing's unfolding" stops being
asserted and becomes a single machine-checked theorem about a discipline *computed on the
Raw-generated carrier*.
-/

namespace E213.Lens.Number.Nat213.FTA

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213 (mul one mul_left_comm)
open E213.Lens.Number.Nat213.Order (mul_left_cancel)
open E213.Lens.Number.Nat213.Divisibility (Dvd dvd_mul_right mul_eq_one)
open E213.Lens.Number.Nat213.Irreducible (Irreducible)
open E213.Lens.Number.Nat213.Factorization (prod not_mem_nil exists_factorization)
open E213.Lens.Number.Nat213.EuclidUnique (prime_dvd_prod)

/-! ## A native, propext-free list permutation -/

/-- Multiset equality as a native inductive permutation (the core `List.Perm` lemmas carry
    `propext`; this one is ∅-axiom). -/
inductive Perm : List Nat213 → List Nat213 → Prop
  | nil : Perm [] []
  | cons (x : Nat213) {l1 l2 : List Nat213} : Perm l1 l2 → Perm (x :: l1) (x :: l2)
  | swap (x y : Nat213) (l : List Nat213) : Perm (x :: y :: l) (y :: x :: l)
  | trans {l1 l2 l3 : List Nat213} : Perm l1 l2 → Perm l2 l3 → Perm l1 l3

theorem perm_refl : ∀ (L : List Nat213), Perm L L
  | [] => Perm.nil
  | a :: l => Perm.cons a (perm_refl l)

theorem perm_symm {L1 L2 : List Nat213} (h : Perm L1 L2) : Perm L2 L1 := by
  induction h with
  | nil => exact Perm.nil
  | cons x _ ih => exact Perm.cons x ih
  | swap x y l => exact Perm.swap y x l
  | trans _ _ ih1 ih2 => exact Perm.trans ih2 ih1

/-! ## Native `erase` and its laws -/

/-- Remove the first occurrence of `b` (native, via `DecidableEq Nat213`). -/
def erase : List Nat213 → Nat213 → List Nat213
  | [], _ => []
  | a :: l, b => if a = b then l else a :: erase l b

theorem erase_cons_pos {a b : Nat213} {l : List Nat213} (h : a = b) :
    erase (a :: l) b = l := by
  show (if a = b then l else a :: erase l b) = l
  rw [if_pos h]

theorem erase_cons_neg {a b : Nat213} {l : List Nat213} (h : a ≠ b) :
    erase (a :: l) b = a :: erase l b := by
  show (if a = b then l else a :: erase l b) = a :: erase l b
  rw [if_neg h]

/-- `prod L = p · prod (erase L p)` when `p ∈ L` — erasing one factor divides the product out. -/
theorem prod_erase : ∀ (L : List Nat213) (p : Nat213), p ∈ L → prod L = mul p (prod (erase L p))
  | [], _, hmem => absurd hmem not_mem_nil
  | a :: l, p, hmem => by
      by_cases h : a = p
      · rw [erase_cons_pos h]
        show mul a (prod l) = mul p (prod l)
        rw [h]
      · have hpl : p ∈ l := by
          cases hmem with
          | head => exact absurd rfl h
          | tail _ hx => exact hx
        rw [erase_cons_neg h]
        show mul a (prod l) = mul p (mul a (prod (erase l p)))
        rw [prod_erase l p hpl, mul_left_comm]

theorem mem_of_mem_erase : ∀ {L : List Nat213} {p x : Nat213}, x ∈ erase L p → x ∈ L
  | [], p, x, hx => absurd hx not_mem_nil
  | a :: l, p, x, hx => by
      by_cases h : a = p
      · rw [erase_cons_pos h] at hx
        exact List.Mem.tail _ hx
      · rw [erase_cons_neg h] at hx
        cases hx with
        | head => exact List.Mem.head _
        | tail _ hx' => exact List.Mem.tail _ (mem_of_mem_erase hx')

/-- `L` is a permutation of `p :: erase L p` when `p ∈ L` (the cons-erase law). -/
theorem cons_erase_perm : ∀ (L : List Nat213) (p : Nat213), p ∈ L → Perm L (p :: erase L p)
  | [], _, hmem => absurd hmem not_mem_nil
  | a :: l, p, hmem => by
      by_cases h : a = p
      · rw [erase_cons_pos h, h]
        exact perm_refl (p :: l)
      · have hpl : p ∈ l := by
          cases hmem with
          | head => exact absurd rfl h
          | tail _ hx => exact hx
        rw [erase_cons_neg h]
        exact Perm.trans (Perm.cons a (cons_erase_perm l p hpl)) (Perm.swap a p (erase l p))

/-! ## Uniqueness, and the capstone -/

/-- A product of irreducibles is never `one` unless the list is empty. -/
theorem prod_eq_nil_of_prod_one :
    ∀ (L : List Nat213), (∀ p, p ∈ L → Irreducible p) → prod L = one → L = []
  | [], _, _ => rfl
  | q :: l, hq, hprod => absurd (mul_eq_one hprod).1 (hq q (List.Mem.head _)).1

/-- ★★★ **Uniqueness of factorization over the Raw-generated ℕ₊**: two irreducible factorizations of
    the same `Nat213` are permutations of each other.  Structural induction on the first list,
    `prime_dvd_prod` to locate the head in the second, native cancellation to descend. ∅-axiom. -/
theorem factorization_unique :
    ∀ (L1 L2 : List Nat213),
      (∀ p, p ∈ L1 → Irreducible p) → (∀ p, p ∈ L2 → Irreducible p) →
      prod L1 = prod L2 → Perm L1 L2
  | [], L2, _, h2, hprod => by
      have hone : prod L2 = one := hprod.symm
      rw [prod_eq_nil_of_prod_one L2 h2 hone]
      exact Perm.nil
  | p :: L1', L2, h1, h2, hprod => by
      have hpirr : Irreducible p := h1 p (List.Mem.head _)
      have hpdvd : Dvd p (prod L2) := by
        rw [← hprod]; exact dvd_mul_right p (prod L1')
      have hpin : p ∈ L2 := prime_dvd_prod hpirr L2 h2 hpdvd
      have hpe : prod L2 = mul p (prod (erase L2 p)) := prod_erase L2 p hpin
      have hcancel : prod L1' = prod (erase L2 p) := by
        apply mul_left_cancel (a := p)
        rw [← hpe]; exact hprod
      have hIH : Perm L1' (erase L2 p) :=
        factorization_unique L1' (erase L2 p)
          (fun x hx => h1 x (List.Mem.tail _ hx))
          (fun x hx => h2 x (mem_of_mem_erase hx))
          hcancel
      exact Perm.trans (Perm.cons p hIH) (perm_symm (cons_erase_perm L2 p hpin))

/-- ★★★ **The Fundamental Theorem of Arithmetic, generated over the Raw-generated ℕ₊** — existence
    (`exists_factorization`) and uniqueness-up-to-permutation (`factorization_unique`), both computed
    entirely over `Nat213`, the distinguishing's own counting object.  ∅-axiom.  This is the descent
    leg's capstone: a classical discipline *generated* on the Raw-derived carrier, not re-derived over
    Lean `Nat` and bridged. -/
theorem fta (n : Nat213) :
    (∃ L, (∀ p, p ∈ L → Irreducible p) ∧ prod L = n) ∧
    (∀ L1 L2, (∀ p, p ∈ L1 → Irreducible p) → (∀ p, p ∈ L2 → Irreducible p) →
      prod L1 = n → prod L2 = n → Perm L1 L2) :=
  ⟨exists_factorization n,
   fun L1 L2 h1 h2 e1 e2 => factorization_unique L1 L2 h1 h2 (e1.trans e2.symm)⟩

end E213.Lens.Number.Nat213.FTA
