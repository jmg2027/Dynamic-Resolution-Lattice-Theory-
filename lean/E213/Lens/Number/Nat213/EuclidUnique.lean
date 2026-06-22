import E213.Lens.Number.Nat213.Factorization

/-!
# Lens.Number.Nat213.EuclidUnique — Euclid's lemma over the Raw-generated ℕ₊ (∅-axiom)

The **descent leg**, M3 (`research-notes/frontiers/the_descent_leg.md`).  Rung 3 of the
Fundamental-Theorem-of-Arithmetic capstone, the **primality** content: an irreducible over `Nat213`
is *prime* — `p ∣ a·b → p ∣ a ∨ p ∣ b` (`euclid`), hence `p ∣ ∏ L → p ∈ L` (`prime_dvd_prod`).

The no-zero / no-subtraction shape of `Nat213` blocks the textbook routes (Bézout needs `ℤ`;
division-with-remainder needs a zero remainder).  The **internal handle** (per
`seed/AXIOM/05_no_exterior.md` §5.4: look for it before declaring a wall) is the **subtractive
Euclidean gcd**, which needs no zero — every step subtracts the smaller from the larger, and the
difference is the `lt`-witness (`a < b ⟺ ∃ k, a + k = b`), so it lives in ℕ₊.  gcd existence *and* the
multiplicative law `gcd(c·a, c·b) = c·gcd(a,b)` (the Bézout substitute Euclid needs) are proved in
**one** well-founded induction on `a + b` (`gcd_exists_mul`), the spec quantified over the scaling `c`.

∅-axiom throughout — decidable `Dvd` (`Factorization`) powers the `p ∣ a?` split with no `Classical`.
-/

namespace E213.Lens.Number.Nat213.EuclidUnique

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213
  (mul add one mul_add mul_comm add_comm one_mul mul_one add_left_cancel)
open E213.Lens.Number.Nat213.Order (lt lt_irrefl lt_trichotomy lt_mul_left)
open E213.Lens.Number.Nat213.Divisibility (Dvd dvd_refl dvd_mul_left mul_eq_one)
open E213.Lens.Number.Nat213.Irreducible (Irreducible irreducible_divisors)
open E213.Lens.Number.Nat213.Factorization (lt_trans wf_lt prod)

/-! ## Multiplicative cancellation in the order, and divisibility of sums/complements -/

/-- `c·a < c·b ⟹ a < b` (the reverse of `Order.lt_mul_left`), via trichotomy. -/
theorem lt_of_mul_lt_mul_left {a b c : Nat213} (h : lt (mul a b) (mul a c)) : lt b c := by
  rcases lt_trichotomy b c with h1 | h1 | h1
  · exact h1
  · exact absurd (h1 ▸ h) (lt_irrefl _)
  · exact absurd (lt_trans h (lt_mul_left h1)) (lt_irrefl _)

/-- If `x + y = z` and `d ∣ x`, `d ∣ y`, then `d ∣ z` (witness `p + q`). -/
theorem dvd_add_w {d x y z : Nat213} (h : add x y = z) (hx : Dvd d x) (hy : Dvd d y) : Dvd d z := by
  obtain ⟨p, hp⟩ := hx
  obtain ⟨q, hq⟩ := hy
  exact ⟨add p q, by rw [← h, hp, hq, mul_add]⟩

/-- If `x + y = z` and `d ∣ x`, `d ∣ z`, then `d ∣ y` (the complement — `lt x z` gives the witness
    via multiplicative cancellation, no subtraction operator). -/
theorem dvd_sub_w {d x y z : Nat213} (h : add x y = z) (hx : Dvd d x) (hz : Dvd d z) : Dvd d y := by
  obtain ⟨p, hp⟩ := hx
  obtain ⟨r, hr⟩ := hz
  have hxz : lt x z := ⟨y, h⟩
  rw [hp, hr] at hxz
  obtain ⟨w, hw⟩ := lt_of_mul_lt_mul_left hxz
  refine ⟨w, ?_⟩
  have key : add x y = add x (mul d w) := by rw [h, hr, ← hw, mul_add, ← hp]
  exact add_left_cancel key

/-! ## gcd existence + the multiplicative law, in one well-founded induction -/

/-- The scaled greatest-common-divisor spec: `d` is, *for every scaling `c`*, a common divisor of
    `c·a`, `c·b` that every common divisor of `c·a`, `c·b` divides.  `c = 1` is plain gcd; the `c`
    quantifier is the multiplicative law `gcd(c·a,c·b) = c·gcd(a,b)` that Euclid needs. -/
def GcdMulSpec (a b d : Nat213) : Prop :=
  ∀ c : Nat213,
    Dvd (mul c d) (mul c a) ∧ Dvd (mul c d) (mul c b) ∧
    (∀ e, Dvd e (mul c a) → Dvd e (mul c b) → Dvd e (mul c d))

/-- ★★★ **Subtractive gcd exists over the Raw-generated ℕ₊**, with the scaled (multiplicative) spec —
    one well-founded induction on `a + b`, no zero, no subtraction operator (differences are
    `lt`-witnesses).  This is the Bézout substitute that powers Euclid's lemma. ∅-axiom. -/
theorem gcd_exists_mul (a₀ b₀ : Nat213) : ∃ d, GcdMulSpec a₀ b₀ d := by
  have H : ∀ n : Nat213, ∀ a b : Nat213, add a b = n → ∃ d, GcdMulSpec a b d := by
    intro n
    refine wf_lt.induction
      (C := fun n => ∀ a b : Nat213, add a b = n → ∃ d, GcdMulSpec a b d) n ?_
    intro m ih a b hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · -- a < b: reduce to (a, k) where a + k = b
      obtain ⟨k, hk⟩ := hlt
      obtain ⟨d, hd⟩ := ih b ⟨a, by rw [add_comm]; exact hab⟩ a k hk
      refine ⟨d, fun c => ⟨(hd c).1, ?_, ?_⟩⟩
      · have e : mul c b = add (mul c a) (mul c k) := by rw [← hk, mul_add]
        exact dvd_add_w e.symm (hd c).1 (hd c).2.1
      · intro e he1 he2
        have ee : add (mul c a) (mul c k) = mul c b := by rw [← mul_add, hk]
        exact (hd c).2.2 e he1 (dvd_sub_w ee he1 he2)
    · -- a = b: gcd is a
      refine ⟨a, fun c => ⟨dvd_refl _, ?_, ?_⟩⟩
      · rw [heq]; exact dvd_refl _
      · intro e he1 _; exact he1
    · -- b < a: reduce to (k, b) where b + k = a
      obtain ⟨k, hk⟩ := hgt
      obtain ⟨d, hd⟩ := ih a ⟨b, hab⟩ k b (by rw [add_comm]; exact hk)
      refine ⟨d, fun c => ⟨?_, (hd c).2.1, ?_⟩⟩
      · have e : mul c a = add (mul c b) (mul c k) := by rw [← hk, mul_add]
        exact dvd_add_w e.symm (hd c).2.1 (hd c).1
      · intro e he1 he2
        have ee : add (mul c b) (mul c k) = mul c a := by rw [← mul_add, hk]
        exact (hd c).2.2 e (dvd_sub_w ee he2 he1) he2
  exact H (add a₀ b₀) a₀ b₀ rfl

/-! ## Euclid's lemma — an irreducible over `Nat213` is prime -/

/-- ★★★ **Euclid's lemma over the Raw-generated ℕ₊**: `p` irreducible, `p ∣ a·b ⟹ p ∣ a ∨ p ∣ b`.
    If `p ∤ a` then `gcd(p,a) = 1` (a divisor of the irreducible `p`, and `≠ p` since `p ∤ a`), so the
    scaled spec at `c = b` gives `p ∣ gcd(b·p, b·a) = b·gcd(p,a) = b`.  ∅-axiom (the `p ∣ a?` split is
    `Factorization`'s decidable `Dvd`, no `Classical`). -/
theorem euclid {p a b : Nat213} (hp : Irreducible p) (h : Dvd p (mul a b)) :
    Dvd p a ∨ Dvd p b := by
  by_cases hpa : Dvd p a
  · exact Or.inl hpa
  · refine Or.inr ?_
    obtain ⟨d, hd⟩ := gcd_exists_mul p a
    have hdp : Dvd d p := by have := (hd one).1; rwa [one_mul, one_mul] at this
    have hda : Dvd d a := by have := (hd one).2.1; rwa [one_mul, one_mul] at this
    have hd_one : d = one := by
      rcases irreducible_divisors hp hdp with h1 | hpe
      · exact h1
      · exact absurd (hpe ▸ hda) hpa
    have hpbp : Dvd p (mul b p) := dvd_mul_left b p
    have hpba : Dvd p (mul b a) := by rw [mul_comm b a]; exact h
    have hpbd : Dvd p (mul b d) := (hd b).2.2 p hpbp hpba
    rwa [hd_one, mul_one] at hpbd

/-- ★★ **An irreducible dividing a product of factors is one of them** — `p ∣ ∏ L ⟹ p ∈ L`
    (Euclid iterated).  This is the primality of irreducibles over `Nat213`; with cancellation
    (`mul_left_cancel`) it yields the uniqueness half of the FTA. -/
theorem prime_dvd_prod {p : Nat213} (hp : Irreducible p) :
    ∀ (L : List Nat213), (∀ q, q ∈ L → Irreducible q) → Dvd p (prod L) → p ∈ L
  | [], _, hdvd => by
      obtain ⟨c, hc⟩ := hdvd
      exact absurd (mul_eq_one hc.symm).1 hp.1
  | q :: L', hq, hdvd => by
      have hdvd' : Dvd p (mul q (prod L')) := hdvd
      rcases euclid hp hdvd' with hpq | hpL
      · rcases irreducible_divisors (hq q (List.Mem.head _)) hpq with h1 | hpe
        · exact absurd h1 hp.1
        · rw [hpe]; exact List.Mem.head _
      · exact List.Mem.tail _
          (prime_dvd_prod hp L' (fun x hx => hq x (List.Mem.tail _ hx)) hpL)

end E213.Lens.Number.Nat213.EuclidUnique
