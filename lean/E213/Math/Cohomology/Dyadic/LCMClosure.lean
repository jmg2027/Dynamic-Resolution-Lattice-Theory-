import E213.Math.Cohomology.Dyadic.ForwardClosure

/-!
# LCM closure — periodic streams combine multiplicatively

Pisano-style CRT structural lemma at the stream level:

If `bs` has period `p`, then `bs` has period `kp` for any `k`
(already proven in `bs_periodic_multiple`).  In particular, for
any `q`, `bs` has period `lcm(p, q)`.

Symmetrically, two streams with periods `p, q` *both* have period
`lcm(p, q)` simultaneously.  Combining them via any function
yields a stream with period dividing `lcm(p, q)` — the formal
content of CRT period multiplicativity.
-/

namespace E213.Math.Cohomology.Dyadic.LCMClosure

/-- Nat.lcm positivity. -/
theorem Nat.lcm_pos {p q : Nat} (hp : 0 < p) (hq : 0 < q) : 0 < Nat.lcm p q := by
  show 0 < p * q / _root_.Nat.gcd p q
  have h1 : 0 < p * q := _root_.Nat.mul_pos hp hq
  have h2 : 0 < _root_.Nat.gcd p q := _root_.Nat.gcd_pos_of_pos_left q hp
  have h3 : _root_.Nat.gcd p q ∣ p * q :=
    _root_.Nat.dvd_trans (_root_.Nat.gcd_dvd_left p q) (_root_.Nat.dvd_mul_right p q)
  have h4 : _root_.Nat.gcd p q ≤ p * q := _root_.Nat.le_of_dvd h1 h3
  have h5 : 1 ≤ p * q / _root_.Nat.gcd p q :=
    (_root_.Nat.le_div_iff_mul_le h2).mpr (by omega)
  omega

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

/-- ★★★★★ A stream periodic with two periods is periodic with their LCM. -/
theorem bs_periodic_lcm (bs : Nat → Bool) (p q : Nat)
    (hp : 0 < p) (hq : 0 < q)
    (h_p : ∀ k, bs (k + p) = bs k) (h_q : ∀ k, bs (k + q) = bs k) :
    ∀ k, bs (k + Nat.lcm p q) = bs k := by
  intro k
  exact bs_periodic_of_dvd bs p (Nat.lcm p q) hp (_root_.Nat.dvd_lcm_left p q) h_p k

/-- ★★★★★★ CRT period multiplicativity: two streams with periods p, q
    combined via any function g have period dividing lcm(p, q). -/
theorem bs_combined_periodic_lcm (bs1 bs2 : Nat → Bool) (p q : Nat)
    (hp : 0 < p) (hq : 0 < q)
    (h1 : ∀ k, bs1 (k + p) = bs1 k) (h2 : ∀ k, bs2 (k + q) = bs2 k)
    (g : Bool → Bool → Bool) :
    ∀ k, g (bs1 (k + Nat.lcm p q)) (bs2 (k + Nat.lcm p q))
        = g (bs1 k) (bs2 k) := by
  intro k
  have h1' : bs1 (k + Nat.lcm p q) = bs1 k :=
    bs_periodic_of_dvd bs1 p (Nat.lcm p q) hp (_root_.Nat.dvd_lcm_left p q) h1 k
  have h2' : bs2 (k + Nat.lcm p q) = bs2 k :=
    bs_periodic_of_dvd bs2 q (Nat.lcm p q) hq (_root_.Nat.dvd_lcm_right p q) h2 k
  rw [h1', h2']

end E213.Math.Cohomology.Dyadic.LCMClosure
