import E213.Lib.Math.NumberTheory.DyadicFSM.Forward.ForwardClosure

import E213.Lib.Math.NumberTheory.DyadicFSM.Forward.ForwardPeriodicity
/-!
# Common-multiple closure — periodic streams combine multiplicatively

Pisano-style CRT structural lemma at the stream level:

If `bs` has period `p`, then `bs` has period `kp` for any `k`
(already proven in `bs_periodic_multiple`).  In particular, for
any common multiple `N` of `p` and `q`, both `bs1` and `bs2` are
periodic at `N` simultaneously.  Combining them via any function
yields a stream with period dividing `N`.

This was previously formulated using `Nat.lcm p q` as the canonical
common multiple, but `Nat.lcm` (and the cascade `Nat.gcd`) brings
`propext` from Lean-core well-founded termination proofs.  We now
take an *arbitrary* common multiple `N` and specialise to `p * q`
(the trivially-correct common multiple) in the API surface used by
downstream capstones — staying ∅-axiom while preserving content.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.Product.LCMClosure

open E213.Lib.Math.NumberTheory.DyadicFSM.Forward.ForwardPeriodicity (bs_periodic_multiple)

/-- ★★★ A purely-periodic stream is periodic at any multiple of its period.
    (Pure-periodic strengthening of bs_periodic_multiple.) -/
theorem bs_periodic_at_multiple (bs : Nat → Bool) (p : Nat) (hp : 0 < p)
    (h : ∀ k, bs (k + p) = bs k) : ∀ k m, bs (k + m * p) = bs k := by
  intro k m
  induction m with
  | zero => show bs (k + 0 * p) = bs k
            rw [_root_.Nat.zero_mul, _root_.Nat.add_zero]
  | succ m' ih =>
    show bs (k + (m' + 1) * p) = bs k
    rw [_root_.Nat.succ_mul, ← _root_.Nat.add_assoc, h (k + m' * p), ih]

/-- ★★★★ Periodic with period p, p ∣ q ⇒ periodic with period q. -/
theorem bs_periodic_of_dvd (bs : Nat → Bool) (p q : Nat) (hp : 0 < p)
    (hpq : p ∣ q) (h : ∀ k, bs (k + p) = bs k) :
    ∀ k, bs (k + q) = bs k := by
  intro k
  obtain ⟨m, rfl⟩ := hpq
  rw [_root_.Nat.mul_comm p m]
  exact bs_periodic_at_multiple bs p hp h k m

/-- ★★★★★ A stream periodic with period `p` is periodic at any `N`
    with `p ∣ N`.  General common-multiple form (∅-axiom). -/
theorem bs_periodic_at_common_multiple
    (bs : Nat → Bool) (p N : Nat) (hp : 0 < p) (hpN : p ∣ N)
    (h : ∀ k, bs (k + p) = bs k) :
    ∀ k, bs (k + N) = bs k :=
  bs_periodic_of_dvd bs p N hp hpN h

/-- ★★★★★★ CRT period multiplicativity (general form): two streams
    with periods `p`, `q` and *any* common multiple `N` of both
    combine via `g` to a stream periodic at `N`.  Specialise via
    `bs_combined_periodic_product` for `N := p * q`. -/
theorem bs_combined_periodic_at
    (bs1 bs2 : Nat → Bool) (p q N : Nat)
    (hp : 0 < p) (hq : 0 < q)
    (hpN : p ∣ N) (hqN : q ∣ N)
    (h1 : ∀ k, bs1 (k + p) = bs1 k) (h2 : ∀ k, bs2 (k + q) = bs2 k)
    (g : Bool → Bool → Bool) :
    ∀ k, g (bs1 (k + N)) (bs2 (k + N)) = g (bs1 k) (bs2 k) := by
  intro k
  have h1' : bs1 (k + N) = bs1 k :=
    bs_periodic_of_dvd bs1 p N hp hpN h1 k
  have h2' : bs2 (k + N) = bs2 k :=
    bs_periodic_of_dvd bs2 q N hq hqN h2 k
  rw [h1', h2']

/-- ★★★★★★ Trivial-common-multiple specialisation: `N := p * q`.
    Drop-in replacement for the previous `bs_combined_periodic_lcm`
    that avoids `Nat.lcm` and stays ∅-axiom. -/
theorem bs_combined_periodic_product
    (bs1 bs2 : Nat → Bool) (p q : Nat)
    (hp : 0 < p) (hq : 0 < q)
    (h1 : ∀ k, bs1 (k + p) = bs1 k) (h2 : ∀ k, bs2 (k + q) = bs2 k)
    (g : Bool → Bool → Bool) :
    ∀ k, g (bs1 (k + p * q)) (bs2 (k + p * q)) = g (bs1 k) (bs2 k) :=
  bs_combined_periodic_at bs1 bs2 p q (p * q) hp hq
    ⟨q, rfl⟩ ⟨p, _root_.Nat.mul_comm p q⟩ h1 h2 g

end E213.Lib.Math.NumberTheory.DyadicFSM.Product.LCMClosure
