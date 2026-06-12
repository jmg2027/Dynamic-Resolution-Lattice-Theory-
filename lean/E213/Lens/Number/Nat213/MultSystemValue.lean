import E213.Lens.Number.Nat213.MultSystem
import E213.Meta.Nat.FoldCriterion

/-!
# Lens.Number.Nat213.MultSystemValue — the prime-valued instance (case A)

`MultSystem` counts the *abstract* monomials: degree-`≤N` exponent vectors over
`k` bases number `C(N+k, k)` (`MultSystem.totalCount_closed`).  This file pins the
other half — when the bases are **primes**, those monomials are
`C(N+k, k)` **distinct natural numbers**, by unique factorization.

`expVal pr e` is the natural value of an exponent list `e` under a prime indexing
`pr` (position `i` ↦ prime `pr i`); the tail shifts `pr` by one, so
`expVal pr [a₀,a₁,…] = (pr 0)^{a₀} · (pr 1)^{a₁} · ⋯`.  The keystone is
`expVal_inj`: for any pairwise-distinct prime basis, `expVal pr` is **injective**
on equal-length exponent lists.  Proof = recover each exponent by the
`pr 0`-adic valuation (`vp_expVal_head`, using `vp_mul`/`vp_pow`/`vp_self_pow`
and that distinct primes have valuation `0`, `vp_expVal_zero`), then cancel and
recurse.  This is `vp_separation` (unique factorization, proven & ∅-axiom in
`Meta/Nat/VpSeparation`) cast onto the multiplicative count.

So: `#{degree-≤N monomials over k primes}` (a `C(N+k,k)` from `MultSystem`) is a
count of *distinct naturals* — the free combinatorial count IS a count of
genuine numbers.  (The bridge to the value-ordered naturals `1..N`, which brings
in `π(N)`, is case B, deliberately not here.)

∅-axiom; built on `MultSystem` + `FoldCriterion`/`VpSeparation`.
-/

namespace E213.Lens.Number.Nat213.MultSystemValue

open E213.Meta.Nat.VpMul (IsPrime213 vp_mul vp_pow vp_self_pow euclid_lemma)
open E213.Meta.Nat.Valuation (vp pow_vp_dvd mod_zero_of_dvd)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Meta.Nat.VpSeparation (vp_eq_zero_of_not_dvd exists_prime_factor)
open E213.Meta.Nat.FoldCriterion (prime_not_dvd_prime)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Lens.Number.Nat213.MultSystem (totalCount binom totalCount_closed)

/-- `p ≥ 2` divides no unit (pure; avoids `Nat.le_of_dvd`'s `propext`). -/
theorem not_dvd_one {p : Nat} (hp : 2 ≤ p) : ¬ p ∣ 1 := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  cases c with
  | zero => rw [Nat.mul_zero] at hc; exact Nat.noConfusion hc
  | succ c' =>
      rw [Nat.mul_succ] at hc
      have h2 : 2 ≤ p * c' + p := Nat.le_trans hp (Nat.le_add_left p (p * c'))
      rw [← hc] at h2
      exact absurd h2 (by decide)

/-- Natural value of an exponent list under prime indexing `pr`:
    `expVal pr [a₀,a₁,…] = (pr 0)^{a₀} · (pr 1)^{a₁} · ⋯` (tail shifts `pr`). -/
def expVal (pr : Nat → Nat) : List Nat → Nat
  | []      => 1
  | a :: as => (pr 0) ^ a * expVal (fun i => pr (i + 1)) as

/-- A prime-valued monomial is positive. -/
theorem expVal_pos (pr : Nat → Nat) (hpr : ∀ i, IsPrime213 (pr i)) :
    ∀ e, 0 < expVal pr e
  | []      => Nat.one_pos
  | a :: as => by
      have h0 : 0 < pr 0 := Nat.lt_of_lt_of_le (by decide) (hpr 0).two_le
      exact Nat.mul_pos (Nat.pow_pos h0)
        (expVal_pos (fun i => pr (i + 1)) (fun i => hpr (i + 1)) as)

/-- A prime `p` not in the basis has valuation `0` on the whole product. -/
theorem vp_expVal_zero (p : Nat) (hp : IsPrime213 p) (pr : Nat → Nat)
    (hpr : ∀ i, IsPrime213 (pr i)) (hne : ∀ i, p ≠ pr i) :
    ∀ e, vp p (expVal pr e) = 0
  | []      => by
      show vp p 1 = 0
      exact vp_eq_zero_of_not_dvd hp Nat.one_pos (not_dvd_one hp.two_le)
  | a :: as => by
      have h0 : 0 < pr 0 := Nat.lt_of_lt_of_le (by decide) (hpr 0).two_le
      show vp p ((pr 0) ^ a * expVal (fun i => pr (i + 1)) as) = 0
      rw [vp_mul hp (Nat.pow_pos h0)
            (expVal_pos (fun i => pr (i + 1)) (fun i => hpr (i + 1)) as),
          vp_pow hp h0 a,
          vp_eq_zero_of_not_dvd hp h0 (prime_not_dvd_prime hp (hpr 0) (hne 0)),
          Nat.mul_zero,
          vp_expVal_zero p hp (fun i => pr (i + 1)) (fun i => hpr (i + 1))
            (fun i => hne (i + 1)) as]

/-- The `pr 0`-adic valuation recovers the head exponent. -/
theorem vp_expVal_head (pr : Nat → Nat) (hpr : ∀ i, IsPrime213 (pr i))
    (hinj : ∀ i j, pr i = pr j → i = j) (a : Nat) (as : List Nat) :
    vp (pr 0) (expVal pr (a :: as)) = a := by
  have h0 : 0 < pr 0 := Nat.lt_of_lt_of_le (by decide) (hpr 0).two_le
  have hself : vp (pr 0) (pr 0) = 1 := by
    have := vp_self_pow (hpr 0) 1; rwa [Nat.pow_one] at this
  have htail : vp (pr 0) (expVal (fun i => pr (i + 1)) as) = 0 :=
    vp_expVal_zero (pr 0) (hpr 0) (fun i => pr (i + 1)) (fun i => hpr (i + 1))
      (fun i e => Nat.noConfusion (hinj 0 (i + 1) e)) as
  show vp (pr 0) ((pr 0) ^ a * expVal (fun i => pr (i + 1)) as) = a
  rw [vp_mul (hpr 0) (Nat.pow_pos h0)
        (expVal_pos (fun i => pr (i + 1)) (fun i => hpr (i + 1)) as),
      vp_pow (hpr 0) h0 a, hself, Nat.mul_one, htail, Nat.add_zero]

/-- **Case A — distinct naturals (unique factorization).**  For any pairwise
    distinct prime basis `pr`, the value map `expVal pr` is **injective** on
    equal-length exponent lists.  So the `C(N+k,k)` degree-`≤N` monomials over
    `k` primes are `C(N+k,k)` distinct naturals. -/
theorem expVal_inj (pr : Nat → Nat) (hpr : ∀ i, IsPrime213 (pr i))
    (hinj : ∀ i j, pr i = pr j → i = j) :
    ∀ e1 e2 : List Nat, e1.length = e2.length → expVal pr e1 = expVal pr e2 → e1 = e2
  | [],      [],      _, _  => rfl
  | [],      _ :: _,  h, _  => Nat.noConfusion h
  | _ :: _,  [],      h, _  => Nat.noConfusion h
  | a :: as, b :: bs, h, he => by
      have h0 : 0 < pr 0 := Nat.lt_of_lt_of_le (by decide) (hpr 0).two_le
      have hab : a = b := by
        have hc := congrArg (vp (pr 0)) he
        rwa [vp_expVal_head pr hpr hinj a as, vp_expVal_head pr hpr hinj b bs] at hc
      subst hab
      have hcancel : expVal (fun i => pr (i + 1)) as = expVal (fun i => pr (i + 1)) bs :=
        Nat.eq_of_mul_eq_mul_left (Nat.pow_pos h0) he
      rw [expVal_inj (fun i => pr (i + 1)) (fun i => hpr (i + 1))
            (fun i j e => Nat.succ.inj (hinj (i + 1) (j + 1) e))
            as bs (Nat.succ.inj h) hcancel]

/-! ## Case A — closed -/

/-- **Case A (closed).**  For a pairwise-distinct prime basis: the abstract
    degree-`≤N` monomial count `C(N+k,k)` (`totalCount_closed`) together with
    value-map injectivity (`expVal_inj`) say the `C(N+k,k)` degree-`≤N` monomials
    over `k` primes are `C(N+k,k)` **distinct natural numbers** (the free
    combinatorial count is a count of genuine numbers). -/
theorem caseA_distinct_naturals (pr : Nat → Nat) (hpr : ∀ i, IsPrime213 (pr i))
    (hinj : ∀ i j, pr i = pr j → i = j) (k N : Nat) :
    totalCount k N = binom (N + k) k
    ∧ (∀ e1 e2 : List Nat, e1.length = e2.length →
        expVal pr e1 = expVal pr e2 → e1 = e2) :=
  ⟨totalCount_closed k N, expVal_inj pr hpr hinj⟩

/-! ## The exp/log bridge — value is the exponential of the depth

Where `ln` comes from on the prime-number-theorem path, as a *finite ∅-axiom*
fact (no transcendental: `exp` here is `Nat.pow` = iterated `×`). -/

/-- **exp/log bridge.**  `p^(vp p n) ≤ n` for `n > 0`: the factor-depth `vp p n`
    (the `p`-axis exponent) sits *under the logarithm* of the value,
    `vp p n ≤ log_p n`.  The value `n` is the *exponential* of the depth, so the
    depth is *logarithmic* in the value — the structural reason `ln` appears in
    `π(N)`.  (Per-axis; the total `Ω(n) ≤ log₂ n` is `omega_le_log` below.) -/
theorem vp_pow_le_self (p n : Nat) (hn : 0 < n) : p ^ (vp p n) ≤ n :=
  le_of_dvd_pos _ n hn (pow_vp_dvd p n)

/-! ## Factorization reconstruction ⇒ the total `Ω(n) ≤ log₂ n`

The per-axis bridge summed: every `n > 0` is a product of primes (`fromVec`, the
inverse of `toVec`), so the total factor count `Ω(n) = #primes` satisfies
`2^{Ω(n)} ≤ n`, i.e. `Ω(n) ≤ log₂ n`. -/

/-- Product of a list of naturals (∅-axiom local; avoids `List.prod`'s imports). -/
def listProd : List Nat → Nat
  | []      => 1
  | x :: xs => x * listProd xs

/-- **Factorization reconstruction (`fromVec`).**  Every `n > 0` is the product
    of a list of primes — the existence half of unique factorization (the
    uniqueness half is `vp_separation`).  Peels one prime factor at a time. -/
theorem factorization_exists : ∀ (fuel n : Nat), n ≤ fuel → 0 < n →
    ∃ ps : List Nat, (∀ p, p ∈ ps → IsPrime213 p) ∧ listProd ps = n := by
  intro fuel
  induction fuel with
  | zero => intro n hn hpos; exact absurd (Nat.lt_of_lt_of_le hpos hn) (Nat.lt_irrefl 0)
  | succ f ih =>
      intro n hn hpos
      rcases Nat.lt_or_ge n 2 with h1 | h2
      · have hn1 : n = 1 := Nat.le_antisymm (Nat.le_of_lt_succ h1) hpos
        refine ⟨[], ?_, ?_⟩
        · intro p hp; nomatch hp
        · exact hn1.symm
      · obtain ⟨q, hq, hqn⟩ := exists_prime_factor n n (Nat.le_refl n) h2
        obtain ⟨c, hc⟩ := hqn
        have hcpos : 0 < c := by
          rcases Nat.eq_zero_or_pos c with h0 | hp
          · rw [h0, Nat.mul_zero] at hc; rw [hc] at hpos; exact absurd hpos (Nat.lt_irrefl 0)
          · exact hp
        have hcc : c < c + c := by
          have := Nat.add_lt_add_left hcpos c; rwa [Nat.add_zero] at this
        have hclt : c < n := by
          rw [hc]
          have h2c : c + c ≤ q * c := by
            rw [← Nat.two_mul]; exact Nat.mul_le_mul hq.two_le (Nat.le_refl c)
          exact Nat.lt_of_lt_of_le hcc h2c
        obtain ⟨ps, hps, hprod⟩ :=
          ih c (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hclt hn)) hcpos
        refine ⟨q :: ps, ?_, ?_⟩
        · intro p hp
          cases hp with
          | head => exact hq
          | tail _ h => exact hps p h
        · show q * listProd ps = n
          rw [hprod, ← hc]

/-- Each prime factor is `≥ 2`, so `2^{#factors} ≤ product`. -/
theorem two_pow_length_le_prod : ∀ ps : List Nat, (∀ p, p ∈ ps → 2 ≤ p) →
    2 ^ ps.length ≤ listProd ps
  | [],      _ => Nat.le_refl 1
  | p :: ps, h => by
      have hp : 2 ≤ p := h p (List.Mem.head ps)
      have ih := two_pow_length_le_prod ps (fun q hq => h q (List.Mem.tail p hq))
      show 2 ^ (ps.length + 1) ≤ p * listProd ps
      calc 2 ^ (ps.length + 1) = 2 * 2 ^ ps.length := by rw [Nat.pow_succ, Nat.mul_comm]
        _ ≤ p * listProd ps := Nat.mul_le_mul hp ih

/-- **The total exp/log bridge: `Ω(n) ≤ log₂ n`.**  Every `n > 0` factors into
    `ps` primes with `2^{Ω(n)} ≤ n` (`Ω(n) = ps.length` = factor count) — the
    aggregate of `vp_pow_le_self` over all axes.  This is the finite ∅-axiom
    skeleton under the `ln` of the prime number theorem. -/
theorem omega_le_log (n : Nat) (hn : 0 < n) :
    ∃ ps : List Nat, (∀ p, p ∈ ps → IsPrime213 p) ∧ listProd ps = n
      ∧ 2 ^ ps.length ≤ n := by
  obtain ⟨ps, hps, hprod⟩ := factorization_exists n n (Nat.le_refl n) hn
  refine ⟨ps, hps, hprod, ?_⟩
  have hb := two_pow_length_le_prod ps (fun p hp => (hps p hp).two_le)
  rwa [hprod] at hb

/-! ## B-entry — `π(N)` bound: naturals `≤ N` use only primes `≤ N`

The prime bases needed to build every natural `≤ N` are exactly the `π(N)`
primes `≤ N` — so the relevant base count is `k = π(N)`.  (Defining `π(N)` as a
counting function needs a decidable primality test, recorded as a frontier.) -/

/-- A list member divides the list product. -/
theorem dvd_listProd (ps : List Nat) (p : Nat) : p ∈ ps → p ∣ listProd ps := by
  induction ps with
  | nil => intro hp; nomatch hp
  | cons x xs ih =>
      intro hp
      cases hp with
      | head => exact ⟨listProd xs, rfl⟩
      | tail _ h =>
          obtain ⟨c, hc⟩ := ih h
          refine ⟨x * c, ?_⟩
          show x * listProd xs = p * (x * c)
          rw [hc]
          exact E213.Tactic.NatHelper.mul_left_comm x p c

/-- **`π(N)` bound.**  Every `n > 0` factors into primes that are all `≤ n`: to
    build the naturals up to `n` you only need primes `≤ n`, so `k = π(n)` bases
    suffice (a prime factor divides `n`, hence is `≤ n`). -/
theorem factorization_bounded (n : Nat) (hn : 0 < n) :
    ∃ ps : List Nat, (∀ p, p ∈ ps → IsPrime213 p) ∧ listProd ps = n
      ∧ (∀ p, p ∈ ps → p ≤ n) := by
  obtain ⟨ps, hps, hprod⟩ := factorization_exists n n (Nat.le_refl n) hn
  exact ⟨ps, hps, hprod, fun p hp => le_of_dvd_pos p n hn (hprod ▸ dvd_listProd ps p hp)⟩

/-- **Pure decidable divisibility.**  `Decidable (k ∣ n)` for `k > 0`, ∅-axiom via
    `n % k` (Lean-core `Nat.decidable_dvd` carries `propext`).  This is the
    propext-free divisibility decision the `π(N)` prime counter needs — the
    blocker that the bounded-search route hit (`Nat.decidable_dvd`, `Bool`
    reflection lemmas are all propext-tainted). -/
def decDvd (k n : Nat) (hk : 0 < k) : Decidable (k ∣ n) :=
  match h : n % k with
  | 0     => isTrue (dvd_of_mod_eq_zero h)
  | _ + 1 => isFalse (fun hd => Nat.noConfusion ((mod_zero_of_dvd hk hd).symm.trans h))

/-- Decidable "no nontrivial divisor below `b`" (recursion on the bound `b`,
    using `decDvd` at each `d`). -/
def decNoFactor (n : Nat) : (b : Nat) → Decidable (∀ d, 2 ≤ d → d < b → ¬ d ∣ n)
  | 0     => isTrue (fun d _ hlt => absurd hlt (Nat.not_lt_zero d))
  | b + 1 =>
      match decNoFactor n b with
      | isFalse hf =>
          isFalse (fun hall => hf (fun d h2 hlt => hall d h2 (Nat.lt_succ_of_lt hlt)))
      | isTrue ht =>
          if hb2 : 2 ≤ b then
            match decDvd b n (Nat.lt_of_lt_of_le (by decide) hb2) with
            | isTrue hbn => isFalse (fun hall => hall b hb2 (Nat.lt_succ_self b) hbn)
            | isFalse hbn => isTrue (fun d h2 hlt => by
                rcases Nat.lt_or_ge d b with hdb | hdb
                · exact ht d h2 hdb
                · have hde : d = b := Nat.le_antisymm (Nat.le_of_lt_succ hlt) hdb
                  rw [hde]; exact hbn)
          else
            isTrue (fun d h2 hlt => by
              rcases Nat.lt_or_ge d b with hdb | hdb
              · exact ht d h2 hdb
              · have hde : d = b := Nat.le_antisymm (Nat.le_of_lt_succ hlt) hdb
                rw [hde] at h2; exact absurd h2 hb2)

/-- Primality as `2 ≤ n` plus a *bounded* no-divisor check (divisor dichotomy). -/
theorem isPrime_iff (n : Nat) :
    IsPrime213 n ↔ (2 ≤ n ∧ ∀ d, 2 ≤ d → d < n → ¬ d ∣ n) := by
  constructor
  · intro hp
    refine ⟨hp.1, fun d h2 hlt hdvd => ?_⟩
    rcases hp.2 d hdvd with h1 | he
    · rw [h1] at h2; exact absurd h2 (by decide)
    · rw [he] at hlt; exact Nat.lt_irrefl n hlt
  · intro h
    obtain ⟨h2n, hnf⟩ := h
    refine ⟨h2n, fun d hdvd => ?_⟩
    have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) h2n
    have hdle : d ≤ n := le_of_dvd_pos d n hnpos hdvd
    cases d with
    | zero =>
        obtain ⟨c, hc⟩ := hdvd; rw [Nat.zero_mul] at hc
        exact absurd (hc ▸ hnpos) (Nat.lt_irrefl 0)
    | succ d' =>
        cases d' with
        | zero => exact Or.inl rfl
        | succ d'' =>
            rcases Nat.lt_or_ge (Nat.succ (Nat.succ d'')) n with hdn | hdn
            · exact absurd hdvd (hnf _ (Nat.le_add_left 2 d'') hdn)
            · exact Or.inr (Nat.le_antisymm hdle hdn)

/-- **Decidable `IsPrime213`** (∅-axiom): `2 ≤ n` and the bounded no-divisor check
    (`decNoFactor n n`), transported by `isPrime_iff`.  No `Classical`, no
    propext (uses `decDvd`, not core `Nat.decidable_dvd`). -/
def decPrime (n : Nat) : Decidable (IsPrime213 n) :=
  match Nat.decLe 2 n, decNoFactor n n with
  | isTrue h2,  isTrue hnf  => isTrue ((isPrime_iff n).mpr ⟨h2, hnf⟩)
  | isFalse h2, _           => isFalse (fun hp => h2 ((isPrime_iff n).mp hp).1)
  | _,          isFalse hnf => isFalse (fun hp => hnf ((isPrime_iff n).mp hp).2)

/-- Prime indicator: `1` if `n` is prime, else `0`. -/
def primeIndicator (n : Nat) : Nat :=
  match decPrime n with
  | isTrue _  => 1
  | isFalse _ => 0

theorem primeIndicator_le_one (n : Nat) : primeIndicator n ≤ 1 := by
  unfold primeIndicator
  cases decPrime n with
  | isTrue _  => exact Nat.le_refl 1
  | isFalse _ => exact Nat.zero_le 1

theorem primeIndicator_eq_one_iff (n : Nat) : primeIndicator n = 1 ↔ IsPrime213 n := by
  unfold primeIndicator
  cases decPrime n with
  | isTrue h  => exact ⟨fun _ => h, fun _ => rfl⟩
  | isFalse h => exact ⟨fun he => Nat.noConfusion he, fun hp => absurd hp h⟩

/-- **`π(N)`** — the number of primes `≤ N` (= the base count needed to build
    every natural `≤ N`, by `factorization_bounded`). -/
def primePi : Nat → Nat
  | 0     => 0
  | n + 1 => primePi n + primeIndicator (n + 1)

/-- `π(N) ≤ N` (at most one prime per number). -/
theorem primePi_le_self : ∀ n, primePi n ≤ n
  | 0     => Nat.le_refl 0
  | n + 1 => Nat.add_le_add (primePi_le_self n) (primeIndicator_le_one (n + 1))

/-- `π` is monotone. -/
theorem primePi_monotone {m n : Nat} (h : m ≤ n) : primePi m ≤ primePi n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (Nat.le_add_right _ _)

/-! ## Infinitude of primes — the finite skeleton of `π(N) → ∞`

`π` is unbounded: for every `N` there is a prime `> N` (Euclid, via `N! + 1`).
This is the qualitative content under the PNT horizon — `π(N) → ∞` as a
*pointing* (each `N` exhibits a next prime), never a completed limit.  Uses a
local minimal factorial (`fact`); the repo's `factorial` sits in `Real213.ExpLog`,
a layer above this `Nat`-level file. -/

/-- Local minimal factorial (avoids importing `Real213.ExpLog`). -/
def fact : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : ∀ n, 0 < fact n
  | 0     => Nat.one_pos
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

/-- `k ∣ N!` for `0 < k ≤ N`. -/
theorem dvd_fact {k : Nat} (hk : 0 < k) : ∀ {n : Nat}, k ≤ n → k ∣ fact n
  | 0,     h => absurd (Nat.lt_of_lt_of_le hk h) (Nat.lt_irrefl 0)
  | n + 1, h => by
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · obtain ⟨c, hc⟩ := dvd_fact hk (Nat.le_of_lt_succ hlt)
        refine ⟨(n + 1) * c, ?_⟩
        show (n + 1) * fact n = k * ((n + 1) * c)
        rw [hc]; exact E213.Tactic.NatHelper.mul_left_comm (n + 1) k c
      · have heq : k = n + 1 := Nat.le_antisymm h hge
        exact ⟨fact n, by show (n + 1) * fact n = k * fact n; rw [heq]⟩

/-- **`p ∤ n!` for a prime `p > n`** (= `vp_p(n!) = 0`): no factor `1..n` is a
    multiple of `p`, and a prime dividing a product divides a factor (`euclid_lemma`).
    The denominator side of "every prime in `(n,2n]` divides `C(2n,n)`". -/
theorem prime_not_dvd_fact {p : Nat} (hp : IsPrime213 p) :
    ∀ {n : Nat}, n < p → ¬ p ∣ fact n
  | 0,     _,   h => not_dvd_one hp.two_le h
  | n + 1, hlt, h => by
      rcases euclid_lemma hp h with h1 | h2
      · exact Nat.lt_irrefl p
          (Nat.lt_of_le_of_lt (le_of_dvd_pos p (n + 1) (Nat.succ_pos n) h1) hlt)
      · exact prime_not_dvd_fact hp (Nat.lt_of_succ_lt hlt) h2

/-- **Infinitude of primes** (Euclid).  For every `N` there is a prime `> N`:
    a prime factor of `N! + 1` cannot be `≤ N` (it would divide both `N!` and
    `N! + 1`, hence `1`). -/
theorem exists_prime_gt (N : Nat) : ∃ p, IsPrime213 p ∧ N < p := by
  have hM2 : 2 ≤ fact N + 1 := Nat.succ_le_succ (fact_pos N)
  obtain ⟨q, hq, hqM⟩ := exists_prime_factor (fact N + 1) (fact N + 1) (Nat.le_refl _) hM2
  refine ⟨q, hq, ?_⟩
  rcases Nat.lt_or_ge N q with hlt | hle
  · exact hlt
  · exfalso
    have hqpos : 0 < q := Nat.lt_of_lt_of_le (by decide) hq.two_le
    obtain ⟨a, ha⟩ := dvd_fact hqpos hle
    obtain ⟨b, hb⟩ := hqM
    have hb' : q * b = q * a + 1 := by rw [← hb, ha]
    rcases Nat.lt_or_ge a b with hab | hab
    · have h1 : q * (a + 1) ≤ q * b := Nat.mul_le_mul (Nat.le_refl q) hab
      rw [hb', Nat.mul_succ] at h1
      exact absurd (Nat.le_trans hq.two_le
        (E213.Meta.Nat.NatDiv213.le_of_add_le_add_left_pure h1)) (by decide)
    · have h1 : q * b ≤ q * a := Nat.mul_le_mul (Nat.le_refl q) hab
      rw [hb'] at h1
      exact absurd h1 (Nat.not_succ_le_self (q * a))

/-- **Divergence certificate for `π`** (the 213-native ε-δ for `π(N) → ∞`):
    for every target `k` there is an explicit threshold `N` with `k ≤ primePi N`.
    Built from `exists_prime_gt` + monotonicity — each step a fresh prime above
    the previous threshold bumps the count.  This is the *modulus* witnessing the
    pointing `π → ∞` (cf. `AbCutSeq.toCauchy`'s `N`), the finite certificate the
    asymptotic horizon reduces to. -/
theorem primePi_unbounded : ∀ k, ∃ N, k ≤ primePi N
  | 0     => ⟨0, Nat.zero_le _⟩
  | k + 1 => by
      obtain ⟨N, hN⟩ := primePi_unbounded k
      obtain ⟨p, hp, hpN⟩ := exists_prime_gt N
      cases p with
      | zero => exact absurd hp.two_le (by decide)
      | succ q =>
          refine ⟨q + 1, ?_⟩
          have h1 : primeIndicator (q + 1) = 1 := (primeIndicator_eq_one_iff (q + 1)).mpr hp
          have h2 : primePi N ≤ primePi q := primePi_monotone (Nat.le_of_lt_succ hpN)
          show k + 1 ≤ primePi q + primeIndicator (q + 1)
          rw [h1]
          exact Nat.add_le_add (Nat.le_trans hN h2) (Nat.le_refl 1)

/-! ## The PNT cut — convergence to `0` as a 213 ε-δ certificate

The prime number theorem's content is a *convergence*: prime density
`π(N)/N → 0`.  213-natively (cf. `AbCutSeq.toCauchy`) the certificate IS a
**modulus** — for each resolution `k`, a threshold past which `π(N)/N < 1/k`,
written division-free as `π(N)·k < N`.  `RatTendsToZero` packages this ε-δ.  Its
soundness (`below`: eventually under *every* positive rational) is ∅-axiom; the
PNT certificate's *existence* (`PrimeDensityToZero`) is the open analytic core —
the single `hsep`-style hypothesis, exactly as transcendental cuts isolate their
modulus. -/

/-- ε-δ certificate that the rational sequence `a N / b N` converges to `0`:
    a modulus `M` with `a N · k < b N` (i.e. `a N / b N < 1/k`) for `N ≥ M k`. -/
structure RatTendsToZero (a b : Nat → Nat) where
  M : Nat → Nat
  cert : ∀ k, 1 ≤ k → ∀ N, M k ≤ N → a N * k < b N

/-- **Soundness**: the certificate forces `a N / b N` eventually below *every*
    positive rational `c/d` (`c ≥ 1`) — genuine convergence to `0`. -/
theorem RatTendsToZero.below {a b : Nat → Nat} (h : RatTendsToZero a b)
    (c d : Nat) (hc : 1 ≤ c) : ∃ Th, ∀ N, Th ≤ N → a N * d < c * b N := by
  refine ⟨h.M (d + 1), fun N hN => ?_⟩
  have key : a N * (d + 1) < b N :=
    h.cert (d + 1) (Nat.succ_le_succ (Nat.zero_le d)) N hN
  calc a N * d ≤ a N * (d + 1) := Nat.mul_le_mul (Nat.le_refl _) (Nat.le_succ d)
    _ < b N := key
    _ ≤ c * b N := by
        have h' := Nat.mul_le_mul hc (Nat.le_refl (b N)); rwa [Nat.one_mul] at h'

/-- **Framework validation**: `1/N → 0` carries an explicit certificate
    (`M k = k + 1`).  Confirms the ε-δ notion is inhabited and correct. -/
def oneOverN : RatTendsToZero (fun _ => 1) (fun N => N) where
  M := fun k => k + 1
  cert := fun k _ N hN => by
    show 1 * k < N
    rw [Nat.one_mul]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hN

/-- **The PNT density cut certificate.**  Prime density `π(N)/N → 0` as a 213
    ε-δ.  Its inhabitation is the open analytic core (Chebyshev/PNT-strength) —
    the one hypothesis isolated, with `RatTendsToZero.below` giving the usable
    consequence for free.  (`π(N) → ∞` is already certified, `primePi_unbounded`;
    this is the dual density side.) -/
abbrev PrimeDensityToZero : Type := RatTendsToZero primePi (fun N => N)

/-! ## Chebyshev start — `π(2n) ≤ n` (density `≤ 1/2`)

The first real density bound feeding the certificate: every even number `≥ 4`
has `2` as a nontrivial divisor, so only `2` is an even prime.  Hence each pair
`(2m+1, 2m+2)` holds at most one prime, giving `π(2n) ≤ n` — prime density
`≤ 1/2`.  (Not yet `→ 0`; that needs sharper Chebyshev work to inhabit
`PrimeDensityToZero`.) -/

/-- Even numbers `≥ 4` are not prime (`2` is a nontrivial divisor). -/
theorem not_prime_two_mul (k : Nat) : ¬ IsPrime213 (2 * (k + 2)) := by
  intro hp
  rcases hp.2 2 ⟨k + 2, rfl⟩ with h1 | h2
  · exact absurd h1 (by decide)
  · have h4 : (4 : Nat) ≤ 2 * (k + 2) := Nat.mul_le_mul (Nat.le_refl 2) (Nat.le_add_left 2 k)
    rw [← h2] at h4
    exact absurd h4 (by decide)

theorem primeIndicator_two_mul (k : Nat) : primeIndicator (2 * (k + 2)) = 0 := by
  unfold primeIndicator
  cases decPrime (2 * (k + 2)) with
  | isTrue hp => exact absurd hp (not_prime_two_mul k)
  | isFalse _ => rfl

/-- Each `(2m+1, 2m+2)` pair holds at most one prime. -/
theorem pair_bound : ∀ m, primeIndicator (2 * m + 1) + primeIndicator (2 * m + 2) ≤ 1
  | 0     => by decide
  | m + 1 => by
      have h0 : primeIndicator (2 * (m + 1) + 2) = 0 := primeIndicator_two_mul m
      rw [h0, Nat.add_zero]
      exact primeIndicator_le_one (2 * (m + 1) + 1)

/-- **Chebyshev start**: `π(2n) ≤ n` — prime density `≤ 1/2`. -/
theorem primePi_two_mul_le : ∀ n, primePi (2 * n) ≤ n
  | 0     => Nat.le_refl 0
  | m + 1 => by
      have ih : primePi (2 * m) ≤ m := primePi_two_mul_le m
      have e : 2 * (m + 1) = 2 * m + 1 + 1 := by rw [Nat.mul_succ]
      rw [e]
      show primePi (2 * m) + primeIndicator (2 * m + 1) + primeIndicator (2 * m + 1 + 1) ≤ m + 1
      rw [Nat.add_assoc]
      exact Nat.add_le_add ih (pair_bound m)

end E213.Lens.Number.Nat213.MultSystemValue
