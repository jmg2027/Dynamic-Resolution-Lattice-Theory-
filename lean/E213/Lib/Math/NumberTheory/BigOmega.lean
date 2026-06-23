import E213.Lib.Math.NumberTheory.PrimeFactorization
import E213.Lib.Math.NumberTheory.FTAUniqueness
import E213.Meta.Tactic.List213

/-!
# `Ω` — the multiplicative leaf-count (the `×`-dual of `Raw.leaves`)

The genesis-seam frontier (`research-notes/frontiers/the_genesis_seam.md`) located the
boundary of "generation, not re-derivation" at the **multiplicative descent**: the
additive monoid is generated on Raw's additive `slash`-peel
(`Raw.leaves_slash : leaves (slash x y) = leaves x + leaves y`), but unique factorization
(FTA) completes on the borrowed `Nat.strongRecOn` because the multiplicative peel
`n ↦ n / minFac n` is non-structural over `Nat`.  Round 3's standing claim was that the
multiplicative descent is *"a genuinely second structure, not reducible to Raw's additive
peel."*

This file refines that claim.  The **total prime-factor count** `Ω n` (big-Omega: the
length of `n`'s factorization, multiplicity counted) is the **multiplicative leaf-count** —
the `×`-dual of `Raw.leaves`:

  * `Omega_mul : Ω (m · n) = Ω m + Ω n` — the exact dual of `Raw.leaves_slash`.  The
    leaf-count splits a `slash` *additively*; the multiplicative leaf-count splits a
    *product* additively.  `Ω` is to `·` what `leaves` is to `slash`.
  * `Omega_descent : Ω (n / minFac n) + 1 = Ω n` — the multiplicative peel drops the
    count by exactly **one**, the dual of the unit depth-drop `part_depth_succ_le`.
  * `no_infinite_mul_descent` — there is no infinite chain of multiplicative peels,
    because `Ω` is a finite count dropping by 1 each step.  The exact mirror of
    `Raw.no_infinite_descent` (via `omega_chain_drops`, mirroring `descent_chain_drops`).

So the multiplicative descent's well-foundedness **is** the additive `×`-atom count peel:
the *Lens* is second (distinguishable primes → an exponent vector, not one merged count),
but the *descent engine* is the same additive count peel that generates the additive
monoid — now reading distinguishable `×`-atoms instead of indistinguishable `+`-atoms.
"Counting (+) is generated; factoring (×) terminates on the same count, applied to
distinguishable atoms."

Built only on `factorize`/`minFac` (`PrimeFactorization`), `factorization_unique`
(`FTAUniqueness`, valuation-count invariance), and `length_append` (`List213`).  ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.BigOmega

open E213.Lib.Math.NumberTheory.PrimeFactorization
  (prodL prodL_cons factorize factorizeF minFac minFac_spec minFac_div minFac_prime
   factorize_prod factorizeF_all_prime)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Lib.Math.NumberTheory.FTAUniqueness (countOcc countOcc_cons factorization_unique)
open E213.Tactic.List213 (length_append mem_append_iff)
open E213.Meta.Nat.NatRing213 (nat_mul_assoc nat_add_right_cancel)

/-! ## §0 — the two defeq prime predicates, bridged

`PrimeFactorization` produces `Prime213`; `factorization_unique` consumes
`VpMul.IsPrime213`.  Both unfold to `2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p`, so they are
definitionally equal and the bridge is the identity. -/

theorem isPrime_of_prime213 {p : Nat} (h : Prime213 p) : E213.Meta.Nat.VpMul.IsPrime213 p := h
theorem prime213_of_isPrime {p : Nat} (h : E213.Meta.Nat.VpMul.IsPrime213 p) : Prime213 p := h

/-! ## §1 — fuel irrelevance and the factorization cons-unfolding -/

/-- `factorizeF` returns `[]` for `n < 2` at any fuel. -/
theorem factorizeF_lt_two : ∀ (f n : Nat), n < 2 → factorizeF f n = [] := by
  intro f n hlt
  cases f with
  | zero => rfl
  | succ g =>
    show (if h : 2 ≤ n then minFac n :: factorizeF g (n / minFac n) else []) = []
    exact dif_neg (Nat.not_le_of_lt hlt)

/-- **Fuel irrelevance**: the factorization does not depend on the fuel, provided the
    fuel is at least `n`.  By strong induction on `n` along the multiplicative peel. -/
theorem factorizeF_fuel_irrel : ∀ (n f1 f2 : Nat), n ≤ f1 → n ≤ f2 →
    factorizeF f1 n = factorizeF f2 n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f1 f2 h1 h2
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · rw [factorizeF_lt_two f1 n hlt, factorizeF_lt_two f2 n hlt]
    · -- n ≥ 2 ⇒ f1, f2 ≥ 2 ⇒ both succ
      have hn1 : 1 ≤ n := Nat.le_trans (by decide) hge
      obtain ⟨g1, rfl⟩ : ∃ g1, f1 = g1 + 1 :=
        ⟨f1 - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le hn1 h1)).symm⟩
      obtain ⟨g2, rfl⟩ : ∃ g2, f2 = g2 + 1 :=
        ⟨f2 - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le hn1 h2)).symm⟩
      obtain ⟨_hprod, hqlt⟩ := minFac_div hge
      have hq1 : n / minFac n ≤ g1 := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hqlt h1)
      have hq2 : n / minFac n ≤ g2 := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hqlt h2)
      show (if h : 2 ≤ n then minFac n :: factorizeF g1 (n / minFac n) else [])
         = (if h : 2 ≤ n then minFac n :: factorizeF g2 (n / minFac n) else [])
      rw [dif_pos hge, dif_pos hge,
          ih (n / minFac n) hqlt g1 g2 hq1 hq2]

/-- **The factorization cons-unfolding**: for `n ≥ 2`,
    `factorize n = minFac n :: factorize (n / minFac n)`. -/
theorem factorize_cons {n : Nat} (hn : 2 ≤ n) :
    factorize n = minFac n :: factorize (n / minFac n) := by
  have hn1 : 1 ≤ n := Nat.le_trans (by decide) hn
  obtain ⟨g, rfl⟩ : ∃ g, n = g + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos hn1).symm⟩
  obtain ⟨_hprod, hqlt⟩ := minFac_div hn
  have hqg : (g + 1) / minFac (g + 1) ≤ g := Nat.le_of_lt_succ hqlt
  -- one peel of `factorizeF (g+1) (g+1)`
  have hstep : factorizeF (g + 1) (g + 1)
      = minFac (g + 1) :: factorizeF g ((g + 1) / minFac (g + 1)) := by
    show (if h : 2 ≤ g + 1 then minFac (g + 1) :: factorizeF g ((g + 1) / minFac (g + 1))
          else []) = _
    exact dif_pos hn
  show factorizeF (g + 1) (g + 1) = minFac (g + 1) :: factorize ((g + 1) / minFac (g + 1))
  rw [hstep]
  congr 1
  exact factorizeF_fuel_irrel ((g + 1) / minFac (g + 1)) g ((g + 1) / minFac (g + 1))
    hqg (Nat.le_refl _)

/-! ## §2 — `Ω`, the multiplicative leaf-count -/

/-- **Big-Omega**: the total number of prime factors of `n`, multiplicity counted —
    the length of `n`'s factorization.  The `×`-dual of `Raw.leaves`. -/
def Omega (n : Nat) : Nat := (factorize n).length

@[simp] theorem Omega_def (n : Nat) : Omega n = (factorize n).length := rfl

/-- `Ω 1 = 0` — the multiplicative unit has no `×`-atoms (the floor). -/
theorem Omega_one : Omega 1 = 0 := by decide

/-- **The multiplicative peel drops the count by one** — the `×`-dual of the unit
    depth-drop `Raw.part_depth_succ_le`.  For `n ≥ 2`,
    `Ω (n / minFac n) + 1 = Ω n`. -/
theorem Omega_descent {n : Nat} (hn : 2 ≤ n) :
    Omega (n / minFac n) + 1 = Omega n := by
  show (factorize (n / minFac n)).length + 1 = (factorize n).length
  rw [factorize_cons hn]
  rfl

/-- The minimal factor of a prime is itself. -/
theorem minFac_eq_self_of_prime {p : Nat} (hp : Prime213 p) : minFac p = p := by
  obtain ⟨hge, hdvd, _hle, _hmin⟩ := minFac_spec hp.1
  rcases hp.2 (minFac p) hdvd with h1 | hpp
  · exact absurd (h1 ▸ hge) (by decide)
  · exact hpp

/-- `Ω p = 1` for a prime `p` — one `×`-atom. -/
theorem Omega_prime {p : Nat} (hp : Prime213 p) : Omega p = 1 := by
  have hpp : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  have hself : minFac p = p := minFac_eq_self_of_prime hp
  have hdiv : p / minFac p = 1 := by
    rw [hself]
    have : p * 1 = p := Nat.mul_one p
    calc p / p = (p * 1) / p :=
          by rw [Nat.mul_one]
      _ = 1 := E213.Meta.Nat.NatDiv213.mul_div_cancel_left_pure p 1 hpp
  have hd := Omega_descent hp.1
  rw [hdiv, Omega_one] at hd
  -- hd : 0 + 1 = Omega p, and 0 + 1 reduces to 1
  exact hd.symm

/-! ## §3 — occurrence-erase: from valuation-count invariance to length -/

/-- Remove the first occurrence of `a` from a list. -/
def eraseFirst (a : Nat) : List Nat → List Nat
  | []      => []
  | x :: xs => if x = a then xs else x :: eraseFirst a xs

theorem mem_of_countOcc_pos {a : Nat} :
    ∀ l : List Nat, 0 < countOcc a l → a ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (Nat.lt_irrefl 0)
  | cons x xs ih =>
    intro h
    rw [countOcc_cons] at h
    by_cases hx : x = a
    · exact hx ▸ List.Mem.head xs
    · rw [if_neg hx, Nat.zero_add] at h
      exact List.Mem.tail x (ih h)

theorem mem_of_mem_eraseFirst {a : Nat} :
    ∀ {l : List Nat} {x : Nat}, x ∈ eraseFirst a l → x ∈ l := by
  intro l
  induction l with
  | nil => intro x h; exact h
  | cons y ys ih =>
    intro x h
    by_cases hy : y = a
    · -- eraseFirst a (y::ys) = ys
      have : eraseFirst a (y :: ys) = ys := by show (if y = a then ys else _) = ys; rw [if_pos hy]
      rw [this] at h
      exact List.Mem.tail y h
    · have he : eraseFirst a (y :: ys) = y :: eraseFirst a ys := by
        show (if y = a then ys else y :: eraseFirst a ys) = _; rw [if_neg hy]
      rw [he] at h
      cases h with
      | head _ => exact List.Mem.head ys
      | tail _ ht => exact List.Mem.tail y (ih ht)

theorem length_eraseFirst_of_mem {a : Nat} :
    ∀ {l : List Nat}, a ∈ l → (eraseFirst a l).length + 1 = l.length := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (List.not_mem_nil a)
  | cons x xs ih =>
    intro h
    by_cases hx : x = a
    · show (if x = a then xs else x :: eraseFirst a xs).length + 1 = xs.length + 1
      rw [if_pos hx]
    · have hmem : a ∈ xs := by
        cases h with
        | head _ => exact absurd rfl hx
        | tail _ ht => exact ht
      show (if x = a then xs else x :: eraseFirst a xs).length + 1 = xs.length + 1
      rw [if_neg hx]
      show (eraseFirst a xs).length + 1 + 1 = xs.length + 1
      rw [ih hmem]

theorem countOcc_eraseFirst_self {a : Nat} :
    ∀ {l : List Nat}, a ∈ l → countOcc a (eraseFirst a l) + 1 = countOcc a l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (List.not_mem_nil a)
  | cons x xs ih =>
    intro h
    by_cases hx : x = a
    · show countOcc a (if x = a then xs else _) + 1 = countOcc a (x :: xs)
      rw [if_pos hx, countOcc_cons, hx, if_pos rfl, Nat.add_comm]
    · have hmem : a ∈ xs := by
        cases h with
        | head _ => exact absurd rfl hx
        | tail _ ht => exact ht
      show countOcc a (if x = a then xs else x :: eraseFirst a xs) + 1 = countOcc a (x :: xs)
      rw [if_neg hx, countOcc_cons, countOcc_cons, if_neg hx, Nat.zero_add, Nat.zero_add,
          ih hmem]

theorem countOcc_eraseFirst_other {a b : Nat} (hba : b ≠ a) :
    ∀ (l : List Nat), countOcc b (eraseFirst a l) = countOcc b l := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x = a
    · show countOcc b (if x = a then xs else _) = countOcc b (x :: xs)
      rw [if_pos hx, countOcc_cons, hx, if_neg (fun e => hba e.symm), Nat.zero_add]
    · show countOcc b (if x = a then xs else x :: eraseFirst a xs) = countOcc b (x :: xs)
      rw [if_neg hx, countOcc_cons, countOcc_cons, ih]

/-- **Equal prime-occurrence counts ⇒ equal length.**  Two prime lists whose `countOcc`
    agrees at every prime have the same length (the multiset is the same).  Proved by
    erasing one shared prime per step. -/
theorem length_eq_of_countOcc_eq :
    ∀ (l1 l2 : List Nat),
      (∀ x, x ∈ l1 → Prime213 x) → (∀ x, x ∈ l2 → Prime213 x) →
      (∀ q, Prime213 q → countOcc q l1 = countOcc q l2) →
      l1.length = l2.length := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 _ h2 hc
    cases l2 with
    | nil => rfl
    | cons y ys =>
      exfalso
      have hy : Prime213 y := h2 y (List.Mem.head ys)
      have hpos : 0 < countOcc y (y :: ys) := by
        rw [countOcc_cons, if_pos rfl]; exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
      have hcy : (0 : Nat) = countOcc y (y :: ys) := hc y hy
      exact absurd (hcy ▸ hpos) (Nat.lt_irrefl _)
  | cons p ps ih =>
    intro l2 h1 h2 hc
    have hp : Prime213 p := h1 p (List.Mem.head ps)
    have hps : ∀ x, x ∈ ps → Prime213 x := fun x hx => h1 x (List.Mem.tail p hx)
    -- p occurs in l2
    have hposp : 0 < countOcc p (p :: ps) := by
      rw [countOcc_cons, if_pos rfl]; exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
    have hpl2 : 0 < countOcc p l2 := (hc p hp) ▸ hposp
    have hmem : p ∈ l2 := mem_of_countOcc_pos l2 hpl2
    -- the erased tail is still all-prime
    have h2' : ∀ x, x ∈ eraseFirst p l2 → Prime213 x :=
      fun x hx => h2 x (mem_of_mem_eraseFirst hx)
    -- counts agree on (ps, eraseFirst p l2) at every prime
    have hc' : ∀ q, Prime213 q → countOcc q ps = countOcc q (eraseFirst p l2) := by
      intro q hq
      by_cases hqp : q = p
      · -- self axis: cancel the +1 both sides
        subst hqp
        have e1 : countOcc q (q :: ps) = countOcc q ps + 1 := by
          rw [countOcc_cons, if_pos rfl, Nat.add_comm]
        have e2 : countOcc q l2 = countOcc q (eraseFirst q l2) + 1 :=
          (countOcc_eraseFirst_self hmem).symm
        have key : countOcc q ps + 1 = countOcc q (eraseFirst q l2) + 1 := by
          rw [← e1, hc q hq, e2]
        exact nat_add_right_cancel key
      · -- other axis: counts pass through unchanged
        have e1 : countOcc q (p :: ps) = countOcc q ps := by
          rw [countOcc_cons, if_neg (fun e => hqp e.symm), Nat.zero_add]
        have e2 : countOcc q (eraseFirst p l2) = countOcc q l2 :=
          countOcc_eraseFirst_other hqp l2
        rw [← e1, hc q hq, e2]
    have hlen : ps.length = (eraseFirst p l2).length := ih (eraseFirst p l2) hps h2' hc'
    show ps.length + 1 = l2.length
    rw [hlen]
    exact length_eraseFirst_of_mem hmem

/-! ## §4 — `Ω` is additive over `×` (the `×`-dual of `Raw.leaves_slash`) -/

/-- Product of an appended list, for `PrimeFactorization.prodL`
    (`prodL (l ++ m) = prodL l * prodL m`). -/
theorem prodL_append : ∀ (l m : List Nat), prodL (l ++ m) = prodL l * prodL m
  | [],      m => (Nat.one_mul (prodL m)).symm
  | p :: l,  m => by
    show p * prodL (l ++ m) = (p * prodL l) * prodL m
    rw [prodL_append l m, nat_mul_assoc]

/-- Every entry of `factorize n` is prime (any `n`; vacuous for `n < 2`). -/
theorem factorize_all_prime' (n : Nat) : ∀ p, p ∈ factorize n → Prime213 p :=
  factorizeF_all_prime n n (Nat.le_refl n)

/-- ★★★ **`Ω` is additive over `×`** — the exact `×`-dual of
    `Raw.leaves_slash : leaves (slash x y) = leaves x + leaves y`.  The multiplicative
    leaf-count splits a product additively, just as the additive leaf-count splits a
    slash additively. -/
theorem Omega_mul {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    Omega (m * n) = Omega m + Omega n := by
  -- two prime-factorizations of m*n: `factorize (m*n)` and `factorize m ++ factorize n`
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  have hL1prime : ∀ x, x ∈ factorize (m * n) → Prime213 x := factorize_all_prime' (m * n)
  have hL2prime : ∀ x, x ∈ factorize m ++ factorize n → Prime213 x := by
    intro x hx
    rcases mem_append_iff hx with h | h
    · exact factorize_all_prime' m x h
    · exact factorize_all_prime' n x h
  -- both have product m*n
  have hprod1 : prodL (factorize (m * n)) = m * n := factorize_prod (m * n) hmn
  have hprod2 : prodL (factorize m ++ factorize n) = m * n := by
    rw [prodL_append, factorize_prod m hm, factorize_prod n hn]
  have heq : prodL (factorize (m * n)) = prodL (factorize m ++ factorize n) := by
    rw [hprod1, hprod2]
  -- valuation-count invariance ⇒ equal occurrence counts at every prime
  have hcount : ∀ q, Prime213 q →
      countOcc q (factorize (m * n)) = countOcc q (factorize m ++ factorize n) := by
    intro q hq
    exact factorization_unique
      (fun x hx => isPrime_of_prime213 (hL1prime x hx))
      (fun x hx => isPrime_of_prime213 (hL2prime x hx))
      heq q (isPrime_of_prime213 hq)
  -- ⇒ equal length ⇒ Ω additive
  have hlen : (factorize (m * n)).length = (factorize m ++ factorize n).length :=
    length_eq_of_countOcc_eq _ _ hL1prime hL2prime hcount
  show (factorize (m * n)).length = (factorize m).length + (factorize n).length
  rw [hlen, length_append]

/-! ## §5 — no infinite multiplicative descent (the `×`-dual of `Raw.no_infinite_descent`)

A multiplicative descent chain peels `minFac` at each step.  `Ω` drops by exactly one
per peel (`Omega_descent`), so after `k` peels it has dropped by at least `k` — and a
chain of length `Ω (chain 0) + 1` would force `Ω (chain 0) + 1 ≤ Ω (chain 0)`.  This is
the exact mirror of `descent_chain_drops` / `no_infinite_descent` for Raw's additive peel,
now on the additive `×`-atom count. -/

/-- A step of the multiplicative descent: `c` is `p` with its least prime peeled off. -/
def IsMulPeel (c p : Nat) : Prop := 2 ≤ p ∧ c = p / minFac p

/-- **The `×`-descent drops `Ω` — the explicit bound.**  Mirrors `descent_chain_drops`. -/
theorem omega_chain_drops (chain : Nat → Nat)
    (hstep : ∀ k, IsMulPeel (chain (k + 1)) (chain k)) :
    ∀ k, Omega (chain (k + 1)) + (k + 1) ≤ Omega (chain 0) := by
  intro k
  induction k with
  | zero =>
    obtain ⟨hge, heq⟩ := hstep 0
    have : Omega (chain 1) + 1 = Omega (chain 0) := by
      rw [heq]; exact Omega_descent hge
    exact Nat.le_of_eq this
  | succ k ih =>
    obtain ⟨hge, heq⟩ := hstep (k + 1)
    have hdrop : Omega (chain (k + 2)) + 1 = Omega (chain (k + 1)) := by
      rw [heq]; exact Omega_descent hge
    calc Omega (chain (k + 2)) + (k + 2)
        = (Omega (chain (k + 2)) + 1) + (k + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 (k+1)]
      _ = Omega (chain (k + 1)) + (k + 1) := by rw [hdrop]
      _ ≤ Omega (chain 0) := ih

/-- ★★★ **No infinite multiplicative descent** — the `×`-dual of
    `Raw.no_infinite_descent`.  There is no total `chain : Nat → Nat` peeling its least
    prime at every step: the additive `×`-atom count `Ω` would have to drop forever, but
    it is a finite count dropping by one per peel.  The multiplicative descent terminates
    on the same additive-count well-foundedness that grounds Raw's additive peel. -/
theorem no_infinite_mul_descent (chain : Nat → Nat)
    (hstep : ∀ k, IsMulPeel (chain (k + 1)) (chain k)) : False := by
  have hb := omega_chain_drops chain hstep (Omega (chain 0))
  have : Omega (chain 0) + 1 ≤ Omega (chain 0) :=
    Nat.le_trans (Nat.le_add_left _ _) hb
  exact Nat.not_succ_le_self _ this

/-! ## §6 — concrete smokes -/

example : Omega 12 = 3 := by decide      -- 12 = 2·2·3
example : Omega 30 = 3 := by decide      -- 30 = 2·3·5
example : Omega 17 = 1 := by decide      -- prime
example : Omega 1 = 0 := by decide       -- the floor
example : Omega 16 = 4 := by decide      -- 2^4

end E213.Lib.Math.NumberTheory.BigOmega
