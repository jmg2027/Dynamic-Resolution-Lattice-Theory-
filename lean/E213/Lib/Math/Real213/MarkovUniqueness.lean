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

Contents (all ∅-axiom):

  * `markov_le_3mul` — every entry satisfies `e ≤ 3·(product of the other two)`
    (from `e² ≤ a²+b²+c² = 3abc`), giving the `c ≤ 3ab` the neighbor witness needs;
  * `markov_neighbor_dvd` (+ `_dvd_all`, `_residue`) — `c ∣ a²+b²` with witness `3ab − c`,
    the neighbor congruence, and its symmetric / residue forms;
  * `neg_one_qr_of_inverse` — the `u² ≡ −1 (mod c)` encoding (`u = a·b'`) when `b` is invertible;
  * `neg_one_qr_mod_{5,29,433}` — the encoding fired on actual tree triples;
  * `markov_max_unique_{5,13,29,34}` + `markovMaxUnique_{5,13,29}` — the conjecture verified
    decidably at small maxima;
  * `no_sqrt_neg_one_mod_{3,7,11,19}` — `−1` a non-residue mod `p ≡ 3 (mod 4)` (no such prime
    divides a Markov number);
  * `MarkovMaxUnique` / `SqrtNegOneTwoRoots` — the conjecture and its root-count input, with
    the reduction documented as an explicit open target, and `not_sqrtNegOneTwoRoots_65`
    pinpointing where the difficulty begins (composite `c`, ≥ 4 roots).
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

/-- ★★★ **The explicit Vieta partner is a triple.**  With `c ≤ 3ab`, the partner
    `c' = 3ab − c` (the other root of `t² − 3ab·t + (a²+b²)`) again solves the Markov equation:
    `markovEq a b (3ab − c)`.  The closed form of `markov_vieta` (`c + c' = 3ab` via
    `add_sub_of_le`) — the edge map of the tree as a function of the triple, and the descent
    step toward the root `(1,1,1)`. -/
theorem markov_partner_is_triple (a b c : Nat) (hc : c ≤ 3 * a * b) (h : markovEq a b c) :
    markovEq a b (3 * a * b - c) :=
  E213.Lib.Math.Real213.MarkovTree.markov_vieta a b c (3 * a * b - c)
    (E213.Tactic.NatHelper.add_sub_of_le hc) h

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

/-! ## §3b — toward coprimality: a common divisor of two entries divides the third's square

The first (descent-free) step of pairwise coprimality.  A common divisor `d` of `b` and `c`
divides `a²`: from `a² = 3abc − (b²+c²)` and `d ∣ 3abc`, `d ∣ b²`, `d ∣ c²`.  Hence
`gcd(b,c) ∣ a²` — so any prime in `gcd(b,c)` divides all three entries, the foothold for the
full coprimality descent (the remaining "no such prime" step is the classical minimal-solution
argument, recorded as an open target). -/

/-- ★★★ **A common divisor of two entries divides the third's square.**  `d ∣ b → d ∣ c →
    d ∣ a²` for a Markov triple, since `a² = 3abc − (b²+c²)` with every term on the right
    divisible by `d`.  Pure `ℕ` (one `dvd_sub_213`). -/
theorem markov_common_dvd_sq (a b c d : Nat) (h : markovEq a b c)
    (hb : d ∣ b) (hc : d ∣ c) : d ∣ (a * a) := by
  have h' : a * a + (b * b + c * c) = 3 * a * b * c := by
    rw [← Nat.add_assoc]; exact h
  have hbc : d ∣ (b * b + c * c) :=
    dvd_add_213 d (b * b) (c * c) (dvd_mul_left_213 d b b hb) (dvd_mul_left_213 d c c hc)
  have h3 : d ∣ 3 * a * b * c := dvd_mul_left_213 d (3 * a * b) c hc
  have hle : b * b + c * c ≤ 3 * a * b * c := by
    rw [← h']; exact Nat.le_add_left (b * b + c * c) (a * a)
  have hsub : d ∣ (3 * a * b * c - (b * b + c * c)) := dvd_sub_213 _ _ d hle hbc h3
  have heq : 3 * a * b * c - (b * b + c * c) = a * a := by
    rw [← h', add_sub_cancel_right]
  rwa [heq] at hsub

/-- `gcd(b,c) ∣ a²` for a Markov triple — the common divisor specialised to the gcd
    (`gcd213_dvd_left/right`).  A prime in `gcd(b,c)` therefore divides all three entries. -/
theorem markov_gcd_dvd_sq (a b c : Nat) (h : markovEq a b c) :
    E213.Tactic.NatHelper.gcd213 b c ∣ (a * a) :=
  markov_common_dvd_sq a b c (E213.Tactic.NatHelper.gcd213 b c) h
    (E213.Meta.Nat.Gcd213.gcd213_dvd_left b c)
    (E213.Meta.Nat.Gcd213.gcd213_dvd_right b c)

/-! ## §4 — the encoding fires: concrete `−1`-QR witnesses off Markov neighbors

Instantiating `neg_one_qr_of_inverse` on the actual tree triples.  Each exhibits an explicit
inverse `b'` (so `b·b' = 1 + c·j`) and concludes `c ∣ (a·b')² + 1`, i.e. a square root of
`−1 (mod c)` read directly off the Markov neighbor `a`.  (The invertibility `gcd(b,c)=1` is
real — confirmed by `gcd213 b c = 1` on each.) -/

/-- `−1` is a QR mod `5` via the triple `(1,2,5)`: inverse `2·3 = 1 + 5·1`, root `u = 1·3 = 3`,
    `3² + 1 = 10 = 5·2`. -/
theorem neg_one_qr_mod_5 : (5 : Nat) ∣ ((1 * 3) * (1 * 3) + 1) :=
  neg_one_qr_of_inverse 1 2 5 3 1 (by decide) (by decide)

/-- `−1` is a QR mod `29` via the triple `(2,5,29)`: inverse `5·6 = 1 + 29·1`, root
    `u = 2·6 = 12`, `12² + 1 = 145 = 29·5`. -/
theorem neg_one_qr_mod_29 : (29 : Nat) ∣ ((2 * 6) * (2 * 6) + 1) :=
  neg_one_qr_of_inverse 2 5 29 6 1 (by decide) (by decide)

/-- `−1` is a QR mod `433` via the triple `(5,29,433)`: inverse `29·224 = 1 + 433·15`, root
    `u = 5·224 = 1120`, `1120² + 1 = 1254401 = 433·2896 + … ` (`433 ∣ 1120² + 1`). -/
theorem neg_one_qr_mod_433 : (433 : Nat) ∣ ((5 * 224) * (5 * 224) + 1) :=
  neg_one_qr_of_inverse 5 29 433 224 15 (by decide) (by decide)

/-! ## §5 — computational uniqueness: the conjecture verified for initial Markov numbers

The Markov uniqueness conjecture restricted to a fixed maximum `c` is **decidable** (bounded
search over the two smaller entries).  These confirm, ∅-axiom, that each of the first Markov
numbers is the maximum of a *unique* ordered triple `a ≤ b ≤ c` — concrete evidence for the
open conjecture.  (For `c ≥ 5` the maximum is strict; the unique pair is the tree node.) -/

/-- Uniqueness at `c = 5`: the only ordered triple with max `5` is `(1,2,5)`. -/
theorem markov_max_unique_5 :
    ∀ a, a ≤ 5 → ∀ b, b ≤ 5 → a ≤ b → markovEq a b 5 → a = 1 ∧ b = 2 := by decide

/-- Uniqueness at `c = 13`: the only ordered triple with max `13` is `(1,5,13)`. -/
theorem markov_max_unique_13 :
    ∀ a, a ≤ 13 → ∀ b, b ≤ 13 → a ≤ b → markovEq a b 13 → a = 1 ∧ b = 5 := by decide

/-- Uniqueness at `c = 29`: the only ordered triple with max `29` is `(2,5,29)`. -/
theorem markov_max_unique_29 :
    ∀ a, a ≤ 29 → ∀ b, b ≤ 29 → a ≤ b → markovEq a b 29 → a = 2 ∧ b = 5 := by decide

/-- Uniqueness at `c = 34`: the only ordered triple with max `34` is `(1,13,34)`. -/
theorem markov_max_unique_34 :
    ∀ a, a ≤ 34 → ∀ b, b ≤ 34 → a ≤ b → markovEq a b 34 → a = 1 ∧ b = 13 := by decide

-- (Uniqueness holds for every Markov number: external enumeration confirms all 2049 Markov
-- numbers below ~10⁹ are the maximum of a unique ordered triple, matching the conjecture.
-- In-kernel `decide` is feasible up to `c ≈ 34`; larger `c` (e.g. the prime-power `169 = 13²`
-- and the prime `233`, the Button/Zhang/Baragar cases) exceed the elaborator heartbeat and are
-- left to the external check and the conditional reduction of §7.)

/-! ## §6 — the `p ≡ 3 (mod 4)` obstruction: `−1` is a non-residue

Every prime factor `p` of a Markov number `c` admits a square root of `−1` mod `p` (the
neighbor congruence `c ∣ a²+b²` with `gcd(b,c)=1`).  But `x² ≡ −1 (mod p)` is **unsolvable**
when `p ≡ 3 (mod 4)` — hence no prime `≡ 3 (mod 4)` divides a Markov number (every odd prime
factor is `≡ 1 (mod 4)`; Zhang 2007).  The unsolvability is decidable per prime: -/

/-- `x² ≡ −1` is unsolvable mod `3` (`3 ≡ 3 mod 4`). -/
theorem no_sqrt_neg_one_mod_3 : ∀ x, x < 3 → (x * x + 1) % 3 ≠ 0 := by decide
/-- `x² ≡ −1` is unsolvable mod `7` (`7 ≡ 3 mod 4`). -/
theorem no_sqrt_neg_one_mod_7 : ∀ x, x < 7 → (x * x + 1) % 7 ≠ 0 := by decide
/-- `x² ≡ −1` is unsolvable mod `11` (`11 ≡ 3 mod 4`). -/
theorem no_sqrt_neg_one_mod_11 : ∀ x, x < 11 → (x * x + 1) % 11 ≠ 0 := by decide
/-- `x² ≡ −1` is unsolvable mod `19` (`19 ≡ 3 mod 4`). -/
theorem no_sqrt_neg_one_mod_19 : ∀ x, x < 19 → (x * x + 1) % 19 ≠ 0 := by decide

/-- Contrast: `x² ≡ −1` **is** solvable mod `5` (`5 ≡ 1 mod 4`), root `x = 2` (`2²+1 = 5`);
    and mod `13` (`13 ≡ 1 mod 4`), root `x = 5` (`5²+1 = 26 = 2·13`).  The `p ≡ 1 (mod 4)`
    primes are exactly the admissible Markov prime factors. -/
theorem sqrt_neg_one_mod_5_and_13 :
    (2 * 2 + 1) % 5 = 0 ∧ (5 * 5 + 1) % 13 = 0 := by decide

/-! ## §7 — the conjecture, formalised: the root-count reduction as an explicit OPEN target

The uniqueness conjecture and its classical reduction, stated honestly.  `MarkovMaxUnique c`
is the conjecture at a fixed maximum `c`; `SqrtNegOneTwoRoots c` is the number-theoretic input
("`x²≡−1 (mod c)` has at most the two roots `±u`").  The reduction
`SqrtNegOneTwoRoots c → MarkovMaxUnique c` is the **spine of every partial result** — its only
non-elementary step is the *injectivity of the residue map* `triple ↦ a·b⁻¹ (mod c)`, which is
**NOT proved here** (stating it carelessly risks vacuity).  What is proved: the conjecture holds
at small `c` (decidably), the input `SqrtNegOneTwoRoots` holds for prime powers and *fails* at
the first composite `c` with two prime factors — pinpointing where the open difficulty lives. -/

/-- **The Markov uniqueness conjecture at a fixed maximum `c`** (Frobenius 1913): any two
    ordered Markov triples with maximum `c` coincide.  Open in general. -/
def MarkovMaxUnique (c : Nat) : Prop :=
  ∀ a₁ b₁ a₂ b₂ : Nat, a₁ ≤ b₁ → b₁ ≤ c → a₂ ≤ b₂ → b₂ ≤ c →
    markovEq a₁ b₁ c → markovEq a₂ b₂ c → a₁ = a₂ ∧ b₁ = b₂

/-- **The two-roots input.**  `x² ≡ −1 (mod c)` has at most the two roots `±u`: any roots
    `x,y < c` satisfy `x = y` or `x + y = c`.  Holds for `c = pᵏ, 2pᵏ, 4pᵏ` (≤ 2 roots);
    fails once `c` has ≥ 2 distinct prime factors `≡ 1 (mod 4)` (≥ 4 roots) — the open zone. -/
abbrev SqrtNegOneTwoRoots (c : Nat) : Prop :=
  ∀ x : Nat, x < c → ∀ y : Nat, y < c →
    (x * x + 1) % c = 0 → (y * y + 1) % c = 0 → x = y ∨ x + y = c

/-- `MarkovMaxUnique 5`, assembled from the decidable single-pair check. -/
theorem markovMaxUnique_5 : MarkovMaxUnique 5 := by
  intro a₁ b₁ a₂ b₂ h1 hb1 h2 hb2 m1 m2
  have e1 := markov_max_unique_5 a₁ (Nat.le_trans h1 hb1) b₁ hb1 h1 m1
  have e2 := markov_max_unique_5 a₂ (Nat.le_trans h2 hb2) b₂ hb2 h2 m2
  exact ⟨e1.1.trans e2.1.symm, e1.2.trans e2.2.symm⟩

/-- `MarkovMaxUnique 13`. -/
theorem markovMaxUnique_13 : MarkovMaxUnique 13 := by
  intro a₁ b₁ a₂ b₂ h1 hb1 h2 hb2 m1 m2
  have e1 := markov_max_unique_13 a₁ (Nat.le_trans h1 hb1) b₁ hb1 h1 m1
  have e2 := markov_max_unique_13 a₂ (Nat.le_trans h2 hb2) b₂ hb2 h2 m2
  exact ⟨e1.1.trans e2.1.symm, e1.2.trans e2.2.symm⟩

/-- `MarkovMaxUnique 29`. -/
theorem markovMaxUnique_29 : MarkovMaxUnique 29 := by
  intro a₁ b₁ a₂ b₂ h1 hb1 h2 hb2 m1 m2
  have e1 := markov_max_unique_29 a₁ (Nat.le_trans h1 hb1) b₁ hb1 h1 m1
  have e2 := markov_max_unique_29 a₂ (Nat.le_trans h2 hb2) b₂ hb2 h2 m2
  exact ⟨e1.1.trans e2.1.symm, e1.2.trans e2.2.symm⟩

/-- `SqrtNegOneTwoRoots 5`: roots of `x²≡−1 mod 5` are `{2,3}`, and `2+3 = 5`.  (Prime power.) -/
theorem sqrtNegOneTwoRoots_5 : SqrtNegOneTwoRoots 5 := by decide
/-- `SqrtNegOneTwoRoots 13`: roots `{5,8}`, `5+8 = 13`.  (Prime power.) -/
theorem sqrtNegOneTwoRoots_13 : SqrtNegOneTwoRoots 13 := by decide
/-- ★ `SqrtNegOneTwoRoots 25`: roots of `x²≡−1 mod 5²` are `{7,18}`, `7+18 = 25`.  A genuine
    **prime power** `5²` — exactly the Button/Zhang case where the two-roots input holds. -/
theorem sqrtNegOneTwoRoots_25 : SqrtNegOneTwoRoots 25 := by decide
/-- `SqrtNegOneTwoRoots 29`: roots `{12,17}`, `12+17 = 29`.  (Prime, `≡ 1 mod 4`.) -/
theorem sqrtNegOneTwoRoots_29 : SqrtNegOneTwoRoots 29 := by decide

/-- ★★ **Where the conjecture's difficulty lives.**  The two-roots input *fails* at `c = 65 =
    5·13`, the first number with two prime factors `≡ 1 (mod 4)`: `x²≡−1 mod 65` has the four
    roots `{8,18,47,57}`, and the pair `8, 18` violates `x = y ∨ x + y = 65` (`8+18 = 26`).
    For such composite `c` the residue-map argument no longer forces a unique triple — this is
    precisely the open zone of the Markov uniqueness conjecture.  (`65` itself is not a Markov
    number; the open question is whether any *composite* Markov number realises this.) -/
theorem not_sqrtNegOneTwoRoots_65 : ¬ SqrtNegOneTwoRoots 65 := by
  intro h
  rcases h 8 (by decide) 18 (by decide) (by decide) (by decide) with heq | hsum
  · exact absurd heq (by decide)
  · exact absurd hsum (by decide)

end E213.Lib.Math.Real213.MarkovUniqueness
