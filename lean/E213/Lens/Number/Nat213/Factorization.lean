import E213.Lens.Number.Nat213.Irreducible

/-!
# Lens.Number.Nat213.Factorization — every `Nat213` is a product of irreducibles (∅-axiom)

The **descent leg**, M2 (the `the_descent_leg` frontier).  Rung 2 of the
Fundamental-Theorem-of-Arithmetic capstone, over the Raw-generated ℕ₊: **factorization existence** —
`∀ n, ∃ l, (∀ p ∈ l, Irreducible p) ∧ prod l = n`, computed entirely over `Nat213` with no Lean
`Nat`.

The two pins the descent-leg scouting flagged are both honoured here, **constructively** (no
`Classical.em`, which is forbidden):

  * **native well-foundedness** — `acc_lt : ∀ n, Acc lt n` by structural recursion on `Nat213`
    (`one` is `lt`-minimal; `succ n` reduces to the accessibility of `n`), so `wf_lt : WellFounded lt`
    is ∅-axiom with no `Nat` measure;
  * **a constructive bounded divisor search** — `decBoundedExists` decides `∃ c ≤ k, P c` for any
    decidable `P` by structural recursion on the bound `k`; from it, `Dvd` is decidable
    (cofactor `≤ b`), and the irreducible/composite dichotomy `irreducible_or_properDiv` is a
    *decision*, not a `by_cases (Irreducible n)` (which would need the forbidden `em`).

Every membership/append fact is re-proved natively (`mem_append_pure`) to avoid core `List` lemmas
that import `propext`.  ∅-axiom throughout.
-/

namespace E213.Lens.Number.Nat213.Factorization

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213
  (mul add one succ two mul_one one_mul mul_comm mul_assoc mul_succ_right
   add_comm add_one_right add_succ_right add_assoc succ_ne_one)
open E213.Lens.Number.Nat213.Order
  (lt lt_irrefl lt_ne succ_lt_succ_of_lt lt_trichotomy mul_left_cancel)
open E213.Lens.Number.Nat213.Divisibility (Dvd dvd_imp_eq_or_lt)
open E213.Lens.Number.Nat213.Irreducible
  (not_lt_one lt_one_of_ne_one lt_succ_iff lt_left_mul lt_right_mul cofactor_lt
   Irreducible irreducible_of_only_trivial_divisors)

/-! ## Order: transitivity, the successor step both ways, decidability -/

theorem lt_trans {a b c : Nat213} (h1 : lt a b) (h2 : lt b c) : lt a c := by
  obtain ⟨x, hx⟩ := h1; obtain ⟨y, hy⟩ := h2
  exact ⟨add x y, by rw [← add_assoc, hx, hy]⟩

theorem lt_succ_self (a : Nat213) : lt a (succ a) := ⟨one, add_one_right a⟩

theorem lt_of_succ_lt_succ {a b : Nat213} (h : lt (succ a) (succ b)) : lt a b := by
  rcases lt_trichotomy a b with h1 | h1 | h1
  · exact h1
  · exact absurd (h1 ▸ h) (lt_irrefl (succ b))
  · exact absurd (lt_trans h (succ_lt_succ_of_lt h1)) (lt_irrefl (succ a))

/-- Decidable strict order — structural double recursion, no `Nat` order (which is propext-dirty). -/
def decLt : (a b : Nat213) → Decidable (lt a b)
  | a, one => isFalse (not_lt_one a)
  | one, succ b => isTrue ⟨b, by rw [add_comm]; exact add_one_right b⟩
  | succ a, succ b =>
      match decLt a b with
      | isTrue h => isTrue (succ_lt_succ_of_lt h)
      | isFalse h => isFalse (fun hlt => h (lt_of_succ_lt_succ hlt))

instance (a b : Nat213) : Decidable (lt a b) := decLt a b

/-! ## `le` and the constructive bounded existential -/

/-- Non-strict order. -/
def le (a b : Nat213) : Prop := a = b ∨ lt a b

theorem le_refl (a : Nat213) : le a a := Or.inl rfl

theorem le_succ_of_le {a b : Nat213} (h : le a b) : le a (succ b) := by
  rcases h with rfl | h
  · exact Or.inr (lt_succ_self a)
  · exact Or.inr (lt_trans h (lt_succ_self b))

/-- ★ **Constructive bounded search**: `∃ c ≤ k, P c` is decidable for any decidable `P`, by
    structural recursion on the bound `k`.  This is the engine that replaces `Classical.em` —
    every "does there exist…" the factorization needs is *decided*, not assumed. -/
def decBoundedExists (P : Nat213 → Prop) (dp : ∀ a, Decidable (P a)) :
    (k : Nat213) → Decidable (∃ c, le c k ∧ P c)
  | one =>
      match dp one with
      | isTrue h => isTrue ⟨one, le_refl one, h⟩
      | isFalse h => isFalse (by
          rintro ⟨c, hc, hpc⟩
          rcases hc with rfl | hlt
          · exact h hpc
          · exact absurd hlt (not_lt_one c))
  | succ k =>
      match dp (succ k), decBoundedExists P dp k with
      | isTrue h, _ => isTrue ⟨succ k, le_refl (succ k), h⟩
      | _, isTrue h => isTrue (by obtain ⟨c, hc, hpc⟩ := h; exact ⟨c, le_succ_of_le hc, hpc⟩)
      | isFalse h1, isFalse h2 => isFalse (by
          rintro ⟨c, hc, hpc⟩
          rcases hc with rfl | hlt
          · exact h1 hpc
          · rcases lt_succ_iff.mp hlt with heq | hlt'
            · exact h2 ⟨c, Or.inl heq, hpc⟩
            · exact h2 ⟨c, Or.inr hlt', hpc⟩)

/-! ## Decidable divisibility (cofactor is `≤` the dividend) -/

/-- A factor's cofactor is `≤` the dividend: `c ≤ a·c` (positivity, no zero). -/
theorem le_mul_left (a c : Nat213) : le c (mul a c) := by
  by_cases h : a = one
  · subst h; exact Or.inl (one_mul c).symm
  · exact Or.inr (lt_right_mul (lt_one_of_ne_one h))

theorem dvd_iff_bounded {a b : Nat213} : Dvd a b ↔ ∃ c, le c b ∧ mul a c = b := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc]; exact le_mul_left a c, hc.symm⟩
  · rintro ⟨c, _, hcb⟩
    exact ⟨c, hcb.symm⟩

instance decDvd (a b : Nat213) : Decidable (Dvd a b) :=
  let _ : Decidable (∃ c, le c b ∧ mul a c = b) :=
    decBoundedExists (fun c => mul a c = b) (fun _ => inferInstance) b
  decidable_of_iff _ dvd_iff_bounded.symm

/-! ## The irreducible / composite dichotomy (decided, not assumed) -/

/-- ★ For `n ≠ 1`, either `n` is irreducible or it has a proper divisor — **decided** by the bounded
    search, with no `Classical.em` on the (∀-quantified, not obviously decidable) `Irreducible n`. -/
theorem irreducible_or_properDiv (n : Nat213) (hn : n ≠ one) :
    Irreducible n ∨ ∃ a, lt one a ∧ lt a n ∧ Dvd a n := by
  cases decBoundedExists (fun a => lt one a ∧ lt a n ∧ Dvd a n) (fun _ => inferInstance) n with
  | isTrue hp =>
      obtain ⟨a, _, ha⟩ := hp
      exact Or.inr ⟨a, ha⟩
  | isFalse h =>
      refine Or.inl (irreducible_of_only_trivial_divisors hn ?_)
      intro d hd
      rcases dvd_imp_eq_or_lt hd with heq | hlt
      · exact Or.inr heq
      · by_cases hd1 : d = one
        · exact Or.inl hd1
        · exact absurd ⟨d, Or.inr hlt, lt_one_of_ne_one hd1, hlt, hd⟩ h

/-! ## Native well-foundedness -/

/-- ★ **`Acc lt`** by structural recursion on `Nat213` — no `Nat` measure, ∅-axiom.  `one` is
    `lt`-minimal (`not_lt_one`); the accessibility of `succ n` reduces to that of `n` via
    `lt_succ_iff`. -/
theorem acc_lt : ∀ n : Nat213, Acc lt n
  | one => Acc.intro one (fun y h => absurd h (not_lt_one y))
  | succ n => Acc.intro (succ n) (fun y h => by
      rcases lt_succ_iff.mp h with heq | hlt
      · exact heq ▸ acc_lt n
      · cases acc_lt n with
        | intro _ g => exact g y hlt)

/-- The native strict order is well-founded — the descent recursion's foundation, ∅-axiom. -/
theorem wf_lt : WellFounded lt := ⟨acc_lt⟩

/-! ## Product over a factor list, native append -/

/-- Product of a list of `Nat213` (empty product `= one`). -/
def prod : List Nat213 → Nat213
  | [] => one
  | p :: l => mul p (prod l)

theorem prod_append : ∀ (l1 l2 : List Nat213), prod (l1 ++ l2) = mul (prod l1) (prod l2)
  | [], l2 => by show prod l2 = mul one (prod l2); rw [one_mul]
  | p :: l1, l2 => by
      show mul p (prod (l1 ++ l2)) = mul (mul p (prod l1)) (prod l2)
      rw [prod_append l1 l2, mul_assoc]

/-- Nothing is a member of the empty list (native, propext-free). -/
theorem not_mem_nil {p : Nat213} : ¬ p ∈ ([] : List Nat213) := nofun

/-- Native membership-append split (avoids the propext-carrying core `List.mem_append`). -/
theorem mem_append_pure {p : Nat213} :
    ∀ {l1 l2 : List Nat213}, p ∈ l1 ++ l2 → p ∈ l1 ∨ p ∈ l2
  | [], _, h => Or.inr h
  | q :: l1, l2, h => by
      cases h with
      | head => exact Or.inl (List.Mem.head _)
      | tail _ h' =>
          rcases mem_append_pure h' with h'' | h''
          · exact Or.inl (List.Mem.tail _ h'')
          · exact Or.inr h''

/-! ## Factorization existence -/

/-- ★★★ **Every `Nat213` is a product of irreducibles** — factorization existence over the
    Raw-generated ℕ₊, by well-founded recursion on the native `lt` and the decided dichotomy.
    `n = 1` → empty product; `n` irreducible → `[n]`; `n` composite → split at a proper divisor
    `a` (with cofactor `c`, both `< n`) and append the recursive factorizations.  ∅-axiom. -/
theorem exists_factorization (n : Nat213) :
    ∃ l : List Nat213, (∀ p, p ∈ l → Irreducible p) ∧ prod l = n := by
  refine wf_lt.induction
    (C := fun n => ∃ l : List Nat213, (∀ p, p ∈ l → Irreducible p) ∧ prod l = n) n
    (fun n ih => ?_)
  by_cases hn : n = one
  · exact ⟨[], fun p hp => absurd hp not_mem_nil, by subst hn; rfl⟩
  · rcases irreducible_or_properDiv n hn with hirr | ⟨a, ha1, han, hdvd⟩
    · refine ⟨[n], ?_, ?_⟩
      · intro p hp
        cases hp with
        | head => exact hirr
        | tail _ h => exact absurd h not_mem_nil
      · show mul n one = n; exact mul_one n
    · obtain ⟨c, hc⟩ := hdvd
      have hcn : lt c n := cofactor_lt (fun he => lt_ne ha1 he.symm) hc
      obtain ⟨la, hla, hpa⟩ := ih a han
      obtain ⟨lc, hlc, hpc⟩ := ih c hcn
      refine ⟨la ++ lc, ?_, ?_⟩
      · intro p hp
        rcases mem_append_pure hp with h | h
        · exact hla p h
        · exact hlc p h
      · rw [prod_append, hpa, hpc, ← hc]

end E213.Lens.Number.Nat213.Factorization
