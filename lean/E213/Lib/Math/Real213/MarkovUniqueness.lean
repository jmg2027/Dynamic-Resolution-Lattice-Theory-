import E213.Lib.Math.Real213.MarkovTree
import E213.Meta.Nat.Gcd213

/-!
# MarkovUniqueness — the neighbor congruence `a²+b² ≡ 0 (mod c)` and the uniqueness machinery

`MarkovTree` built the Vieta tree of `x²+y²+z² = 3xyz`, its two spines, and the first fork.
This file develops the **arithmetic engine** behind the classical *Markov uniqueness conjecture*
(Frobenius 1913): every Markov number is the maximum of a unique ordered triple.

The headline ∅-axiom fact is the **neighbor congruence**: for any Markov triple `(a,b,c)`,
the largest entry `c` divides the sum of squares of the other two,

  `c ∣ a² + b²`,

with the explicit witness `a² + b² = c·(3ab − c)`.  This is the lever of every known partial
result: reducing `a²+b²+c² = 3abc` mod `c` gives `a²+b² ≡ 0 (mod c)`, i.e. `(a·b⁻¹)² ≡ −1`,
so `−1` is a quadratic residue mod `c`; the conjecture then follows whenever the square roots
of `−1` mod `c` are forced to be essentially unique (e.g. `c = pᵏ, 2pᵏ, 4pᵏ`, the
Baragar/Button/Zhang prime-power cases).

Everything here is pure `ℕ` arithmetic (no subtraction landmines, no `mod` `Iff`-rewrites):

  * `markov_self_le_triple` — every entry satisfies `e ≤ 3·(product of the other two)`
    (from `e² ≤ a²+b²+c² = 3abc`), giving the `c ≤ 3ab` needed for the witness;
  * `markov_neighbor_dvd` — `c ∣ a²+b²` with witness `3ab − c` (the neighbor congruence);
  * `markov_neighbor_dvd_all` — the three symmetric divisibilities;
  * `markov_neighbor_residue` — the residue form `(a²+b²) % c = 0`.
-/

namespace E213.Lib.Math.Real213.MarkovUniqueness

open E213.Lib.Math.Real213.MarkovTree (markovEq markov_symm)
open E213.Lib.Math.Real213.GoldenFormMarkov (add_left_cancel_pure)
open E213.Tactic.NatHelper (add_sub_cancel_right mul_sub_distrib mul_assoc mul_mul_mul_comm_213)
open E213.Meta.Nat.Gcd213 (dvd_sub_213 dvd_add_213)

/-- `c ∣ m → c ∣ k·m`.  ∅-axiom — explicit witness `k·t`. -/
theorem dvd_mul_left_213 (c k m : Nat) (h : c ∣ m) : c ∣ (k * m) := by
  obtain ⟨t, ht⟩ := h
  exact ⟨k * t, by rw [ht, ← mul_assoc k c t, Nat.mul_comm k c, mul_assoc c k t]⟩

/-! ## §1 — the self-bound `c ≤ 3ab` -/

/-- `c² ≤ 3·a·b·c` for a Markov triple: `c²` is one of the three summands of `a²+b²+c² = 3abc`. -/
theorem markov_sq_le (a b c : Nat) (h : markovEq a b c) : c * c ≤ 3 * a * b * c := by
  rw [← h]
  exact Nat.le_add_left (c * c) (a * a + b * b)

/-- ★★★ **The self-bound `c ≤ 3ab`.**  Every entry of a Markov triple is at most three times
    the product of the other two: from `c² ≤ a²+b²+c² = 3abc = (3ab)·c`, cancel one `c`.
    (Holds for each entry by symmetry; this is the `c`-form used by the neighbor witness.) -/
theorem markov_le_3mul (a b c : Nat) (hc : 0 < c) (h : markovEq a b c) : c ≤ 3 * a * b := by
  have hsq : c * c ≤ 3 * a * b * c := markov_sq_le a b c h
  rw [Nat.mul_comm (3 * a * b) c] at hsq
  exact Nat.le_of_mul_le_mul_left hsq hc

/-! ## §2 — the neighbor congruence `c ∣ a² + b²` -/

/-- ★★★★ **The neighbor congruence.**  For a Markov triple `(a,b,c)`, the entry `c` divides
    `a² + b²`, with the explicit witness `a² + b² = c·(3ab − c)`.

    This is `a²+b²+c² = 3abc` reduced mod `c`: `a²+b² = 3abc − c² = c·(3ab − c)`.  Pure `ℕ`
    (the witness multiplication `c·(3ab−c)` reconstructs the sum exactly, so no genuine
    subtraction obstruction).  It is the arithmetic lever of the uniqueness conjecture:
    `−1` is a quadratic residue mod every Markov number, via its neighbors. -/
theorem markov_neighbor_dvd (a b c : Nat) (h : markovEq a b c) : c ∣ (a * a + b * b) := by
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · -- c = 0 forces a² + b² = 0, divisible by anything
    subst hc0
    have h0 : a * a + b * b + 0 * 0 = 3 * a * b * 0 := h
    rw [Nat.mul_zero, Nat.mul_zero, Nat.add_zero] at h0
    exact ⟨0, by rw [h0, Nat.mul_zero]⟩
  · refine ⟨3 * a * b - c, ?_⟩
    have hle : c ≤ 3 * a * b := markov_le_3mul a b c hcpos h
    -- c·(3ab − c) = c·(3ab) − c·c
    rw [mul_sub_distrib hle]
    -- c·(3ab) = 3ab·c = a²+b²+c²
    have hcomm : c * (3 * a * b) = a * a + b * b + c * c := by
      rw [Nat.mul_comm c (3 * a * b)]; exact h.symm
    rw [hcomm, add_sub_cancel_right]

/-- The three symmetric neighbor congruences: each entry divides the sum of squares of the
    other two (`a ∣ b²+c²`, `b ∣ a²+c²`, `c ∣ a²+b²`).  By `markov_symm` permutations. -/
theorem markov_neighbor_dvd_all (a b c : Nat) (h : markovEq a b c) :
    c ∣ (a * a + b * b) ∧ b ∣ (a * a + c * c) ∧ a ∣ (b * b + c * c) := by
  refine ⟨markov_neighbor_dvd a b c h, ?_, ?_⟩
  · -- b ∣ a² + c²: permute (a,b,c) → (a,c,b) so b is the last slot
    have h' : markovEq a c b := markov_symm a b c h
    exact markov_neighbor_dvd a c b h'
  · -- a ∣ b² + c²: permute to put a last.  (a,b,c) → (b,a,c) → (b,c,a)
    have h1 : markovEq b a c := by
      show b * b + a * a + c * c = 3 * b * a * c
      have hmul : 3 * b * a * c = 3 * a * b * c := by
        rw [mul_assoc 3 b a, Nat.mul_comm b a, ← mul_assoc 3 a b]
      rw [Nat.add_comm (b * b) (a * a), hmul]; exact h
    have h2 : markovEq b c a := markov_symm b a c h1
    exact markov_neighbor_dvd b c a h2

/-- The residue form: `(a² + b²) % c = 0` for a Markov triple.  Equivalent to
    `markov_neighbor_dvd`; the explicit-residue statement.  Pure via the witness
    `a²+b² = c·k` and `NatHelper.mul_mod_right` (`c·k % c = 0`). -/
theorem markov_neighbor_residue (a b c : Nat) (h : markovEq a b c) :
    (a * a + b * b) % c = 0 := by
  obtain ⟨k, hk⟩ := markov_neighbor_dvd a b c h
  rw [hk]
  exact E213.Tactic.NatHelper.mul_mod_right c k

/-! ## §3 — the square-root-of-(−1) encoding (`u² ≡ −1 mod c`) -/

/-- ★★★★★ **The square-root-of-(−1) encoding.**  This is the form of the Markov uniqueness
    conjecture that every partial result (Frobenius → Baragar/Button/Zhang) exploits.

    If `b` is invertible mod `c` — concretely, `b·b' = 1 + c·j` for some inverse `b'` and `j`
    — then the neighbor congruence `c ∣ a²+b²` upgrades to: **`−1` is a quadratic residue mod
    `c`**, witnessed by `u = a·b'`:

      `c ∣ (a·b')² + 1`.

    Proof (subtraction-free except one `dvd_sub_213`): multiply `c ∣ a²+b²` by `b'²` to get
    `c ∣ (a b')² + (b b')²`; since `(b b')² = (1+cj)² = 1 + c·M` (`M = 2j + c·j²`), this reads
    `c ∣ ((a b')² + 1) + c·M`; subtract the multiple `c·M`.

    The classical reduction then runs: distinct ordered triples sharing max `c` give distinct
    `±u` roots of `x²≡−1`, so if `x²≡−1 (mod c)` has ≤ 2 solutions (e.g. `c = pᵏ, 2pᵏ, 4pᵏ`),
    the triple is unique.  Here the *encoding* is ∅-axiom; the root-count input is the open
    part. -/
theorem neg_one_qr_of_inverse (a b c b' j : Nat) (h : markovEq a b c)
    (hinv : b * b' = 1 + c * j) : c ∣ ((a * b') * (a * b') + 1) := by
  -- M with (b·b')² = 1 + c·M  (introduced abstractly via the explicit witness)
  obtain ⟨M, hsq⟩ : ∃ M, (b * b') * (b * b') = 1 + c * M := by
    refine ⟨2 * j + c * (j * j), ?_⟩
    rw [hinv]
    -- normalise LHS and RHS to the common form `1 + (cj + (cj + (cj)(cj)))`
    have hL : (1 + c * j) * (1 + c * j)
              = 1 + (c * j + (c * j + (c * j) * (c * j))) := by
      rw [E213.Tactic.NatHelper.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    have hR : 1 + c * (2 * j + c * (j * j))
              = 1 + (c * j + (c * j + (c * j) * (c * j))) := by
      rw [Nat.mul_add, Nat.two_mul, Nat.mul_add, ← mul_assoc c c (j * j),
          ← mul_mul_mul_comm_213 c j c j, Nat.add_assoc]
    exact hL.trans hR.symm
  -- b'²·(a²+b²) = (a b')² + (b b')²
  have hkey : (b' * b') * (a * a + b * b) = (a * b') * (a * b') + (b * b') * (b * b') := by
    have e1 : (b' * b') * (a * a) = (a * b') * (a * b') := by
      rw [Nat.mul_comm (b' * b') (a * a), ← mul_mul_mul_comm_213 a b' a b']
    have e2 : (b' * b') * (b * b) = (b * b') * (b * b') := by
      rw [Nat.mul_comm (b' * b') (b * b), ← mul_mul_mul_comm_213 b b' b b']
    rw [Nat.mul_add, e1, e2]
  -- c divides the b'²-multiple of (a²+b²)
  have hdvd : c ∣ ((a * b') * (a * b') + (b * b') * (b * b')) := by
    rw [← hkey]; exact dvd_mul_left_213 c (b' * b') _ (markov_neighbor_dvd a b c h)
  -- rewrite (b b')² = 1 + c·M and regroup to ((a b')² + 1) + c·M
  rw [hsq] at hdvd
  have hregroup : (a * b') * (a * b') + (1 + c * M) = ((a * b') * (a * b') + 1) + c * M := by
    rw [← Nat.add_assoc]
  rw [hregroup] at hdvd
  -- subtract the multiple c·M
  have hcM : c ∣ c * M := ⟨M, rfl⟩
  have hle : c * M ≤ ((a * b') * (a * b') + 1) + c * M := Nat.le_add_left _ _
  have hsub : c ∣ (((a * b') * (a * b') + 1) + c * M - c * M) :=
    dvd_sub_213 (c * M) (((a * b') * (a * b') + 1) + c * M) c hle hcM hdvd
  rwa [add_sub_cancel_right] at hsub

end E213.Lib.Math.Real213.MarkovUniqueness
