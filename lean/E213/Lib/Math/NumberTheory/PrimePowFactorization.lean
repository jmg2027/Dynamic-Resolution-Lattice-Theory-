import E213.Lens.Number
import E213.Meta.Nat.VpSeparation
import E213.Meta.Nat.FoldCriterion

/-!
# Prime-power factorization — the explicit FTA product form (∅-axiom)

`factorization_exists` (MultSystemValue) gives every `n > 0` as `listProd ps` for
some *flat* prime list `ps` (with multiplicity, unordered).  `vp_separation`
(VpSeparation) gives uniqueness — a positive natural is determined by its full
`vp`-coordinate.  This file closes the **explicit product-of-prime-powers form**
of the fundamental theorem of arithmetic:

  `m = ∏_{p ≤ B, prime} p^{vₚ(m)}`     (`prod_prime_pow_eq`)

whenever every prime factor of `m` is `≤ B`.  This is the form the Erdős proof of
Bertrand's postulate needs to **upper-bound** `C(2n,n)`: write it as a product of
prime powers grouped by the size of `p`, then bound each range.  The flat-list
`factorization_exists` cannot do this (no exponents, no fixed index set); the
divisibility lemmas (`listProd_dvd`, `window_prod_dvd_central_binom`) bound
*sub-products from below*, the wrong direction.

The product is taken over the fixed index list `primesIn 0 B` (so the exponents
live on a definite set), built with a direct recursion `primePowProd` rather than
`listProd ∘ List.map` to keep every step propext-free.

Proof route: `vp_separation`.  Two targeted lemmas compute `vₚ` of the product on
a `Nodup` prime list — `e q` at a member `q`, `0` off the list — and the size
hypothesis forces `vₚ(m) = 0` for the primes `> B` that the index set omits.

All ∅-axiom (built on `MultSystemValue` + `VpSeparation` + `VpMul`).
-/

namespace E213.Lib.Math.NumberTheory.PrimePowFactorization

open E213.Lens.Number.Nat213.MultSystemValue
  (listProd primesIn primesIn_cons primesIn_skip
   mem_primesIn_le mem_primesIn_prime primesIn_nodup not_dvd_one decPrime)
open E213.Meta.Nat.VpMul (IsPrime213 vp_mul vp_pow vp_self_pow)
open E213.Meta.Nat.Valuation (vp)
open E213.Meta.Nat.VpSeparation (vp_separation vp_eq_zero_of_not_dvd)
open E213.Meta.Nat.FoldCriterion (prime_not_dvd_prime)

/-! ## §0 — positivity helper -/

/-- `0 < p → 0 < pᵏ` (pure; `pᵏ⁺¹ = pᵏ·p` definitionally). -/
private theorem pow_pos_nat {p : Nat} (hp : 0 < p) : ∀ k, 0 < p ^ k
  | 0     => Nat.one_pos
  | k + 1 => Nat.mul_pos (pow_pos_nat hp k) hp

/-! ## §1 — the prime-power product over an index list -/

/-- `∏_{p ∈ ps} p^{e p}`, by direct recursion (no `List.map`). -/
def primePowProd (e : Nat → Nat) : List Nat → Nat
  | []      => 1
  | p :: ps => p ^ (e p) * primePowProd e ps

/-- A prime-power product over a list of primes is positive. -/
theorem primePowProd_pos (e : Nat → Nat) :
    ∀ {ps : List Nat}, (∀ p, p ∈ ps → IsPrime213 p) → 0 < primePowProd e ps := by
  intro ps
  induction ps with
  | nil => intro _; exact Nat.one_pos
  | cons p rest ih =>
      intro hps
      have hp : IsPrime213 p := hps p (List.Mem.head rest)
      have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
      show 0 < p ^ (e p) * primePowProd e rest
      exact Nat.mul_pos (pow_pos_nat hppos (e p))
        (ih (fun q hq => hps q (List.Mem.tail p hq)))

/-- The product splits over list concatenation (the index-range split lemma:
    `∏_{xs ++ ys} = ∏_{xs} · ∏_{ys}`).  Drives the size-range partition of the
    Bertrand upper bound. -/
theorem primePowProd_append (e : Nat → Nat) :
    ∀ xs ys : List Nat,
      primePowProd e (xs ++ ys) = primePowProd e xs * primePowProd e ys := by
  intro xs ys
  induction xs with
  | nil => show primePowProd e ys = 1 * primePowProd e ys; rw [Nat.one_mul]
  | cons p rest ih =>
      show p ^ (e p) * primePowProd e (rest ++ ys)
          = (p ^ (e p) * primePowProd e rest) * primePowProd e ys
      rw [ih, Nat.mul_assoc]

/-! ## §2 — `vₚ` of the product: `0` off the list, `e q` at a member -/

/-- **Off the list ⟹ valuation 0.**  A prime `q` not among the (prime) bases
    divides no factor `p^{e p}`, so `vₚ(∏) = 0`. -/
theorem vp_primePowProd_not_mem {q : Nat} (hq : IsPrime213 q) (e : Nat → Nat) :
    ∀ {ps : List Nat}, (∀ p, p ∈ ps → IsPrime213 p) → q ∉ ps →
      vp q (primePowProd e ps) = 0 := by
  intro ps
  induction ps with
  | nil =>
      intro _ _
      show vp q 1 = 0
      exact vp_eq_zero_of_not_dvd hq Nat.one_pos (not_dvd_one hq.two_le)
  | cons p rest ih =>
      intro hps hnmem
      have hp : IsPrime213 p := hps p (List.Mem.head rest)
      have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
      have hrestprime : ∀ r, r ∈ rest → IsPrime213 r := fun r hr => hps r (List.Mem.tail p hr)
      have hqp : q ≠ p := fun he => hnmem (he ▸ List.Mem.head rest)
      have hpowpos : 0 < p ^ (e p) := pow_pos_nat hppos (e p)
      have hrestpos : 0 < primePowProd e rest := primePowProd_pos e hrestprime
      have hnrest : q ∉ rest := fun hm => hnmem (List.Mem.tail p hm)
      show vp q (p ^ (e p) * primePowProd e rest) = 0
      rw [vp_mul hq hpowpos hrestpos]
      have h0 : vp q (p ^ (e p)) = 0 := by
        rw [vp_pow hq hppos (e p),
            vp_eq_zero_of_not_dvd hq hppos (prime_not_dvd_prime hq hp hqp),
            Nat.mul_zero]
      rw [h0, ih hrestprime hnrest]

/-- **At a member ⟹ valuation `e q`.**  For a `Nodup` list of primes containing
    `q`, only the `q`-factor contributes: `vₚ(∏) = e q`. -/
theorem vp_primePowProd_mem {q : Nat} (hq : IsPrime213 q) (e : Nat → Nat) :
    ∀ {ps : List Nat}, (∀ p, p ∈ ps → IsPrime213 p) → ps.Nodup → q ∈ ps →
      vp q (primePowProd e ps) = e q := by
  intro ps
  induction ps with
  | nil => intro _ _ hmem; nomatch hmem
  | cons p rest ih =>
      intro hps hnd hmem
      have hp : IsPrime213 p := hps p (List.Mem.head rest)
      have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
      have hrestprime : ∀ r, r ∈ rest → IsPrime213 r := fun r hr => hps r (List.Mem.tail p hr)
      have hpowpos : 0 < p ^ (e p) := pow_pos_nat hppos (e p)
      have hrestpos : 0 < primePowProd e rest := primePowProd_pos e hrestprime
      cases hnd with
      | cons hhead htail =>
          show vp q (p ^ (e p) * primePowProd e rest) = e q
          rw [vp_mul hq hpowpos hrestpos]
          cases hmem with
          | head =>
              rw [vp_self_pow hp (e q),
                  vp_primePowProd_not_mem hp e hrestprime (fun hm => hhead q hm rfl),
                  Nat.add_zero]
          | tail _ hmem' =>
              have hpq : p ≠ q := hhead q hmem'
              have h0 : vp q (p ^ (e p)) = 0 := by
                rw [vp_pow hq hppos (e p),
                    vp_eq_zero_of_not_dvd hq hppos
                      (prime_not_dvd_prime hq hp (fun he => hpq he.symm)),
                    Nat.mul_zero]
              rw [h0, ih hrestprime htail hmem', Nat.zero_add]

/-! ## §3 — converse membership for `primesIn` -/

/-- **Converse membership.**  A prime `p` in the open-closed window `(lo, hi]` is a
    member of `primesIn lo hi` (the companion of `mem_primesIn_le`/`_prime`/`_gt`). -/
theorem mem_primesIn {lo : Nat} : ∀ {hi p : Nat},
    IsPrime213 p → lo < p → p ≤ hi → p ∈ primesIn lo hi := by
  intro hi
  induction hi with
  | zero => intro p hp _ hle; exact absurd (Nat.le_trans hp.two_le hle) (by decide)
  | succ k ih =>
      intro p hp hlo hle
      rcases Nat.lt_or_ge p (k + 1) with hlt | hge
      · have hpk : p ≤ k := Nat.le_of_lt_succ hlt
        have hlo1 : lo < k + 1 := Nat.lt_of_lt_of_le hlo (Nat.le_succ_of_le hpk)
        have hmem_k : p ∈ primesIn lo k := ih hp hlo hpk
        cases decPrime (k + 1) with
        | isTrue hpk1 => rw [primesIn_cons hlo1 hpk1]; exact List.Mem.tail _ hmem_k
        | isFalse hpk1 => rw [primesIn_skip hlo1 hpk1]; exact hmem_k
      · have heq : p = k + 1 := Nat.le_antisymm hle hge
        rw [heq, primesIn_cons (heq ▸ hlo) (heq ▸ hp)]
        exact List.Mem.head _

/-! ## §4 — the explicit FTA product form -/

/-- ★★★ **Prime-power factorization (explicit FTA product form).**  If every prime
    factor of `m > 0` is `≤ B`, then

      `m = ∏_{p ≤ B, prime} p^{vₚ(m)}`   (`= primePowProd (vp · m) (primesIn 0 B)`).

    Proved by `vp_separation`: at each prime `q`, the right side has valuation `e q`
    if `q ≤ B` (member, `vp_primePowProd_mem`) and `0` if `q > B` (off the list,
    `vp_primePowProd_not_mem`) — and `q > B` forces `vₚ(m) = 0` because `q ∣ m`
    would put `q ≤ B`.  So the two `vp`-coordinates agree everywhere, hence `m`
    equals the product.  ∅-axiom. -/
theorem prod_prime_pow_eq {m B : Nat} (hm : 0 < m)
    (hB : ∀ q, IsPrime213 q → q ∣ m → q ≤ B) :
    m = primePowProd (fun p => vp p m) (primesIn 0 B) := by
  have hprime : ∀ p, p ∈ primesIn 0 B → IsPrime213 p := fun p hp => mem_primesIn_prime hp
  have hpos : 0 < primePowProd (fun p => vp p m) (primesIn 0 B) := primePowProd_pos _ hprime
  refine vp_separation hm hpos (fun q hq => ?_)
  by_cases hqB : q ≤ B
  · have h0q : 0 < q := Nat.lt_of_lt_of_le (by decide) hq.two_le
    have hmem : q ∈ primesIn 0 B := mem_primesIn hq h0q hqB
    rw [vp_primePowProd_mem hq (fun p => vp p m) hprime primesIn_nodup hmem]
  · have hqnm : ¬ q ∣ m := fun hd => hqB (hB q hq hd)
    have hvm : vp q m = 0 := vp_eq_zero_of_not_dvd hq hm hqnm
    have hnmem : q ∉ primesIn 0 B := fun hm' => hqB (mem_primesIn_le hm')
    rw [hvm, vp_primePowProd_not_mem hq (fun p => vp p m) hprime hnmem]

end E213.Lib.Math.NumberTheory.PrimePowFactorization
