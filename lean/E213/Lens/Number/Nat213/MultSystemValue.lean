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

open E213.Meta.Nat.VpMul (IsPrime213 vp_mul vp_pow vp_self_pow)
open E213.Meta.Nat.Valuation (vp pow_vp_dvd)
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

end E213.Lens.Number.Nat213.MultSystemValue
