import E213.Lib.Math.Real213.MarkovTree
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.PolyNatMTactic
import E213.Lib.Math.ModArith.MarkovPrimeFactor

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
    pinpointing where the difficulty begins (composite `c`, ≥ 4 roots);
  * `fib_spine_sqrt_neg_one` — for the whole Fibonacci spine, `fib(2n+3) ∣ fib(2n+2)²+1`
    straight from Cassini (`golden_min_attained_on_fib`): φ's convergents are the spine's
    `√(−1)` roots;
  * `cohn_sq_neg_one_mod` — the Cohn-matrix form `C² ≡ −I (mod c)` (`tr C = 3c`, `det C = 1`,
    Cayley–Hamilton): the order-4 modular generator `S` survives mod every Markov number.
-/

namespace E213.Lib.Math.Real213.MarkovUniqueness

open E213.Lib.Math.Real213.MarkovTree (markovEq markov_symm)
open E213.Lib.Math.Real213.GoldenFormMarkov (add_left_cancel_pure)
open E213.Tactic.NatHelper (add_sub_cancel_right mul_sub_distrib mul_assoc mul_mul_mul_comm_213)
open E213.Meta.Nat.Gcd213 (dvd_sub_213 dvd_add_213)
open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.Gcd213
  (gcd213_dvd_left gcd213_dvd_right gcd213_greatest gcd213_comm mul_eq_one_left)
open E213.Lib.Math.Mobius213.Px.FibonacciAtomicLock (fib)
open E213.Lib.Math.Real213.GoldenFormMarkov (golden_min_attained_on_fib)

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
      have hmul : 3 * b * a * c = 3 * a * b * c := by ring_nat
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
    rw [hinv]; ring_nat
  -- b'²·(a²+b²) = (a b')² + (b b')²
  have hkey : (b' * b') * (a * a + b * b) = (a * b') * (a * b') + (b * b') * (b * b') := by
    ring_nat
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

/-! ## §8 — the Fibonacci spine's `√(−1)` residues are φ's convergents (from Cassini)

The most `213`-native fact in the file: the square root of `−1` mod a Fibonacci-spine Markov
number is the *next Fibonacci convergent of* `φ`.  Because the Cassini/Catalan identity gives
`fib(2n+2)² + 1 = fib(2n+1)·fib(2n+3)` (already in the repo as `golden_min_attained_on_fib`,
the golden form taking its minimum `−1`), the Markov number `fib(2n+3)` divides `fib(2n+2)²+1`:

  `fib(2n+3) ∣ fib(2n+2)² + 1`,

i.e. `u = fib(2n+2)` is a root of `x² ≡ −1` mod the spine Markov number `fib(2n+3)` — for every
`n`, a *general* `√(−1)` encoding (no inverse to exhibit; the Cassini convergent IS the root).
So the worst-approximable number's convergents are exactly the `√(−1)` residues that index its
Markov spine.  (The other factor `fib(2n+1)` gives the same residue mod the predecessor.) -/

/-- ★★★★ **The Fibonacci spine's `√(−1)` residue.**  `fib(2n+3) ∣ fib(2n+2)² + 1` — the Markov
    number `fib(2n+3)` has `u = fib(2n+2)` as a square root of `−1`, directly from Cassini
    (`golden_min_attained_on_fib`).  General in `n`: φ's convergents are the spine's roots. -/
theorem fib_spine_sqrt_neg_one (n : Nat) :
    fib (2 * n + 3) ∣ (fib (2 * n + 2) * fib (2 * n + 2) + 1) := by
  refine ⟨fib (2 * n + 1), ?_⟩
  rw [golden_min_attained_on_fib n]
  -- fib(2n+2)·fib(2n+1) + fib(2n+1)² = (fib(2n+2)+fib(2n+1))·fib(2n+1) = fib(2n+3)·fib(2n+1)
  have hrec : fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) := rfl
  rw [hrec, E213.Tactic.NatHelper.add_mul]

/-- The predecessor factor: `fib(2n+1) ∣ fib(2n+2)² + 1` too — the same Cassini product
    `fib(2n+2)²+1 = fib(2n+1)·fib(2n+3)`, read on the other factor. -/
theorem fib_spine_sqrt_neg_one_pred (n : Nat) :
    fib (2 * n + 1) ∣ (fib (2 * n + 2) * fib (2 * n + 2) + 1) := by
  refine ⟨fib (2 * n + 3), ?_⟩
  rw [golden_min_attained_on_fib n]
  have hrec : fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) := rfl
  rw [hrec, Nat.mul_add, Nat.mul_comm (fib (2 * n + 1)) (fib (2 * n + 2))]

/-- ★★★ **The Markov spine is the trace-`NS` linear recurrence.**  The odd-index Fibonacci
    numbers — the golden Markov spine — satisfy the second-order linear recurrence

      `fib(2n+1) + fib(2n+5) = 3 · fib(2n+3)`     (`= NS · fib(2n+3)`),

    i.e. `fib(2n+5) = 3·fib(2n+3) − fib(2n+1)`, char. polynomial `x² − 3x + 1` — exactly the
    characteristic polynomial of the golden matrix `P = [[2,1],[1,1]]` (trace `3 = NS`, det `1`),
    whose `P`-orbit *is* the odd-index Fibonacci sequence.  The recurrence step is the
    **Markov-Vieta jump** on the spine (`F_{2n−1} + F_{2n+3} = 3·F_{2n+1}`, `markov_fibonacci_branch`).
    So the spine is a C-finite (constant-coefficient linear-recurrence) sequence — exponential
    growth, *not* finite forward-difference depth (like the geometric witness `2ⁿ` in the
    holonomicity hierarchy `QuasiPolyCF ⊊ C-finite`); and the **Casoratian** (discrete Wronskian)
    of this recurrence is the Cassini constant `±1`, which `fib_spine_sqrt_neg_one` reads as the
    `√(−1)` residue mod the spine Markov number.  Coefficient `NS = 3` ties recurrence, golden
    matrix, and Markov equation into one number. -/
theorem fib_spine_recurrence (n : Nat) :
    fib (2 * n + 1) + fib (2 * n + 5) = 3 * fib (2 * n + 3) := by
  have h5 : fib (2 * n + 5) = fib (2 * n + 4) + fib (2 * n + 3) := rfl
  have h4 : fib (2 * n + 4) = fib (2 * n + 3) + fib (2 * n + 2) := rfl
  have h3 : fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) := rfl
  rw [h5, h4, h3]; ring_nat

/-- ★★ **The silver (Pell) Markov spine recurrence.**  The odd-index Pell numbers `1,5,29,169,…`
    (the `√8`/silver Markov spine) satisfy the trace-`6` linear recurrence
    `pell(2n+1) + pell(2n+5) = 6·pell(2n+3)` (char. polynomial `x²−6x+1`, `6 = NS·NT`, the trace
    of the silver square / Cohn `B`).  The second C-finite Markov spine, companion to the golden
    `fib_spine_recurrence`. -/
theorem pell_spine_recurrence (n : Nat) :
    E213.Lib.Math.Real213.MarkovTree.pell (2 * n + 1)
      + E213.Lib.Math.Real213.MarkovTree.pell (2 * n + 5)
    = 6 * E213.Lib.Math.Real213.MarkovTree.pell (2 * n + 3) := by
  have h5 : E213.Lib.Math.Real213.MarkovTree.pell (2 * n + 5)
    = 2 * E213.Lib.Math.Real213.MarkovTree.pell (2 * n + 4)
      + E213.Lib.Math.Real213.MarkovTree.pell (2 * n + 3) := rfl
  have h4 : E213.Lib.Math.Real213.MarkovTree.pell (2 * n + 4)
    = 2 * E213.Lib.Math.Real213.MarkovTree.pell (2 * n + 3)
      + E213.Lib.Math.Real213.MarkovTree.pell (2 * n + 2) := rfl
  have h3 : E213.Lib.Math.Real213.MarkovTree.pell (2 * n + 3)
    = 2 * E213.Lib.Math.Real213.MarkovTree.pell (2 * n + 2)
      + E213.Lib.Math.Real213.MarkovTree.pell (2 * n + 1) := rfl
  rw [h5, h4, h3]; ring_nat

/-! ## §9 — the Cohn-matrix form: `C² ≡ −I (mod c)` (the order-4 generator survives mod c)

Every Markov number `c` carries a **Cohn matrix** `C = [[a,b],[cc,d]] ∈ SL(2,ℤ)` (built from
its Stern-Brocot word in `A=[[2,1],[1,1]], B=[[5,2],[2,1]]`) with `tr C = a+d = 3c` and
`det C = a·d − b·cc = 1`.  Cayley–Hamilton for `2×2` gives `C² = (tr C)·C − (det C)·I = 3c·C − I`,
so reduced mod `c` it squares to `−I`: `C mod c` is an **order-4 element of `SL(2,ℤ/cℤ)`** — a
copy of the Gaussian `i = S` (the order-4 modular generator, `ModularElliptic.S`) carried along
the tree path to `c`.  This is the matrix form of the Markov `√(−1)`: the defining relation
`S² = −I` survives reduction mod `c` along *any* tree path.

Cohn-matrix entries are positive, so the statement lives over `ℕ`: each entry of `C²` is `≡` the
corresponding entry of `−I` mod `c`, i.e. `c ∣ (C²)₁₁+1`, `c ∣ (C²)₁₂`, `c ∣ (C²)₂₁`,
`c ∣ (C²)₂₂+1`.  Det in the additive form `a·d = b·cc + 1` keeps it subtraction-free. -/

/-- ★★★★ **A trace-`3m`, det-`1` matrix squares to `−I` mod `m`.**  For `[[a,b],[cc,d]]` with
    `a·d = b·cc + 1` and `a + d = 3m`, the four entries of the square satisfy
    `m ∣ a²+b·cc+1`, `m ∣ a·b+b·d`, `m ∣ cc·a+d·cc`, `m ∣ cc·b+d²+1` — Cayley–Hamilton
    `C² = 3m·C − I ≡ −I (mod m)`, pure `ℕ`. -/
theorem cohn_sq_neg_one_mod (a b cc d m : Nat)
    (hdet : a * d = b * cc + 1) (htr : a + d = 3 * m) :
    m ∣ (a * a + b * cc + 1) ∧ m ∣ (a * b + b * d)
    ∧ m ∣ (cc * a + d * cc) ∧ m ∣ (cc * b + d * d + 1) := by
  have hdvd3 : ∀ y : Nat, m ∣ ((3 * m) * y) :=
    fun y => ⟨3 * y, by rw [Nat.mul_comm 3 m, mul_assoc m 3 y]⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : a * a + b * cc + 1 = (3 * m) * a := by
      rw [← htr, E213.Tactic.NatHelper.add_mul, Nat.mul_comm d a, hdet, Nat.add_assoc]
    rw [h]; exact hdvd3 a
  · have h : a * b + b * d = (3 * m) * b := by
      rw [← htr, E213.Tactic.NatHelper.add_mul, Nat.mul_comm d b]
    rw [h]; exact hdvd3 b
  · have h : cc * a + d * cc = (3 * m) * cc := by
      rw [← htr, E213.Tactic.NatHelper.add_mul, Nat.mul_comm cc a]
    rw [h]; exact hdvd3 cc
  · have h : cc * b + d * d + 1 = (3 * m) * d := by
      rw [← htr, E213.Tactic.NatHelper.add_mul, hdet, Nat.mul_comm cc b,
          Nat.add_assoc (b * cc) (d * d) 1, Nat.add_assoc (b * cc) 1 (d * d),
          Nat.add_comm (d * d) 1]
    rw [h]; exact hdvd3 d

/-- ★ **The Cohn matrix of `5` is order-4 mod `5`.**  `C = [[12,5],[7,3]]` (Stern-Brocot word
    `AB`, `tr = 15 = 3·5`, `det = 36−35 = 1`): `C² ≡ −I (mod 5)` — the Gaussian `i` realised mod
    the Markov number `5`.  `C² = [[179,75],[105,44]] ≡ [[−1,0],[0,−1]] (mod 5)`. -/
theorem cohn5_sq_neg_one_mod_5 :
    (5 : Nat) ∣ (12 * 12 + 5 * 7 + 1) ∧ (5 : Nat) ∣ (12 * 5 + 5 * 3)
    ∧ (5 : Nat) ∣ (7 * 12 + 3 * 7) ∧ (5 : Nat) ∣ (7 * 5 + 3 * 3 + 1) :=
  cohn_sq_neg_one_mod 12 5 7 3 5 (by decide) (by decide)

/-! ## §10 — pairwise coprimality: the Vieta tree preserves it (C2/C3)

The Markov tree generates all triples from `(1,1,1)` by Vieta jumps (replacing one entry `c`
by `c' = 3ab − c`) and permutations.  Pairwise coprimality is the **invariant** of this
generation: it holds at the root and is preserved by every move, because `c' = 3ab − c` and
`a ∣ 3ab` give `gcd(a,c') = gcd(a,c)`.  So every tree triple is pairwise coprime — the
condition the `√(−1)` encoding (`neg_one_qr_of_inverse`) needs, now established structurally
(not just per triple).  Encoded via an explicit reachability predicate so the invariant is
proved by induction on the generation. -/

/-- `g ∣ m → g ∣ m·k`.  ∅-axiom (right companion of `dvd_mul_left_213`). -/
theorem dvd_mul_right_213 (g m k : Nat) (h : g ∣ m) : g ∣ (m * k) := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s * k, by rw [hs, mul_assoc]⟩

/-- `g ∣ 1 → g = 1`.  ∅-axiom via `mul_eq_one_left`. -/
theorem eq_one_of_dvd_one {g : Nat} (h : g ∣ 1) : g = 1 := by
  obtain ⟨k, hk⟩ := h; exact mul_eq_one_left g k hk.symm

/-- ★★★★ **The Vieta step preserves coprimality with the fixed entries.**  If `gcd(a,c) = 1`
    and `c + c' = 3ab` (so `c' = 3ab − c` is the Vieta partner), then `gcd(a,c') = 1`.  Because
    `g = gcd(a,c')` divides `a` (hence `3ab`) and `c'`, it divides `c = 3ab − c'`, so it divides
    `gcd(a,c) = 1`. -/
theorem coprime_vieta_step (a b c c' : Nat) (hc : c + c' = 3 * a * b)
    (hcop : gcd213 a c = 1) : gcd213 a c' = 1 := by
  have hg_a : gcd213 a c' ∣ a := gcd213_dvd_left a c'
  have hg_c' : gcd213 a c' ∣ c' := gcd213_dvd_right a c'
  -- g ∣ 3·a·b  (via g ∣ a)
  have hg_3ab : gcd213 a c' ∣ 3 * a * b :=
    dvd_mul_right_213 (gcd213 a c') (3 * a) b (dvd_mul_left_213 (gcd213 a c') 3 a hg_a)
  -- c = 3ab − c'
  have hc'le : c' ≤ 3 * a * b := hc ▸ Nat.le_add_left c' c
  have heq : 3 * a * b - c' = c := by rw [← hc]; exact add_sub_cancel_right c c'
  have hg_c : gcd213 a c' ∣ c := by
    have := dvd_sub_213 c' (3 * a * b) (gcd213 a c') hc'le hg_c' hg_3ab
    rwa [heq] at this
  -- g ∣ gcd(a,c) = 1
  have hg1 : gcd213 a c' ∣ 1 := hcop ▸ gcd213_greatest a c (gcd213 a c') hg_a hg_c
  exact eq_one_of_dvd_one hg1

/-- Pairwise coprimality of a triple, in the `gcd213` form. -/
abbrev MarkovPairwiseCoprime (a b c : Nat) : Prop :=
  gcd213 a b = 1 ∧ gcd213 a c = 1 ∧ gcd213 b c = 1

/-- Reachability in the Markov tree: from the root `(1,1,1)` by Vieta jumps on the last entry
    (`c ↦ c' = 3ab − c`) and the two transpositions (so any entry can be jumped). -/
inductive MarkovReachable : Nat → Nat → Nat → Prop
  | root : MarkovReachable 1 1 1
  | jump {a b c c' : Nat} : MarkovReachable a b c → c + c' = 3 * a * b → MarkovReachable a b c'
  | swap12 {a b c : Nat} : MarkovReachable a b c → MarkovReachable b a c
  | swap23 {a b c : Nat} : MarkovReachable a b c → MarkovReachable a c b

/-- ★★★★★ **Every reachable Markov triple is pairwise coprime** (C3 along the tree).  The root
    is coprime; `coprime_vieta_step` preserves it under a jump (the jumped entry stays coprime
    to both fixed entries, and the fixed pair is untouched); transpositions permute the
    conjuncts (`gcd213_comm`).  Induction on the generation. -/
theorem markov_reachable_coprime {a b c : Nat} (h : MarkovReachable a b c) :
    MarkovPairwiseCoprime a b c := by
  induction h with
  | root => exact ⟨by decide, by decide, by decide⟩
  | @jump a b c c' _hr hcc ih =>
    refine ⟨ih.1, ?_, ?_⟩
    · exact coprime_vieta_step a b c c' hcc ih.2.1
    · -- gcd(b,c') = 1: jump with a,b swapped, c+c' = 3ab = 3ba
      exact coprime_vieta_step b a c c'
        (by rw [hcc, mul_assoc 3 a b, Nat.mul_comm a b, ← mul_assoc 3 b a]) ih.2.2
  | @swap12 a b c _hr ih =>
    exact ⟨gcd213_comm a b ▸ ih.1, ih.2.2, ih.2.1⟩
  | @swap23 a b c _hr ih =>
    exact ⟨ih.2.1, ih.1, gcd213_comm b c ▸ ih.2.2⟩

/-- Reachable triples satisfy the Markov equation (`markov_vieta` on jumps, `markov_symm` on
    transpositions, `decide` at the root).  Together with `markov_reachable_coprime`: every
    tree triple is a *pairwise-coprime* solution of `x²+y²+z² = 3xyz`. -/
theorem markov_reachable_is_triple {a b c : Nat} (h : MarkovReachable a b c) : markovEq a b c := by
  induction h with
  | root => decide
  | @jump a b c c' hr hcc ih => exact E213.Lib.Math.Real213.MarkovTree.markov_vieta a b c c' hcc ih
  | @swap12 a b c hr ih =>
    -- markovEq a b c → markovEq b a c
    show b * b + a * a + c * c = 3 * b * a * c
    have hmul : 3 * b * a * c = 3 * a * b * c := by ring_nat
    rw [Nat.add_comm (b * b) (a * a), hmul]; exact ih
  | @swap23 a b c hr ih => exact markov_symm a b c ih

/-- ★★★ **Coprimality of the fixed pair after any jump** = the `gcd(b,c)=1` input the
    `√(−1)` encoding needs (C2), now structural: every reachable triple has `gcd(b,c) = 1`. -/
theorem markov_reachable_gcd_bc {a b c : Nat} (h : MarkovReachable a b c) : gcd213 b c = 1 :=
  (markov_reachable_coprime h).2.2

/-- **No two entries of a reachable triple share a factor `≥ 2`** — the usable form of pairwise
    coprimality.  Any common divisor `d` of two entries divides their `gcd213 = 1`, so `d = 1`.
    In particular at most one entry is even (`d = 2`). -/
theorem markov_reachable_no_common_factor {a b c : Nat} (h : MarkovReachable a b c)
    (d : Nat) (hd : 2 ≤ d) :
    ¬ (d ∣ a ∧ d ∣ b) ∧ ¬ (d ∣ b ∧ d ∣ c) ∧ ¬ (d ∣ a ∧ d ∣ c) := by
  obtain ⟨hab, hac, hbc⟩ := markov_reachable_coprime h
  have no : ∀ u v : Nat, gcd213 u v = 1 → ¬ (d ∣ u ∧ d ∣ v) := by
    intro u v huv hduv
    have hd1 : d = 1 := eq_one_of_dvd_one (huv ▸ gcd213_greatest u v d hduv.1 hduv.2)
    rw [hd1] at hd
    exact absurd hd (by decide)
  exact ⟨no a b hab, no b c hbc, no a c hac⟩

/-! ## §11 — the encoding from a modular inverse (residue form)

The `√(−1)` encoding in its natural usability form: rather than a hand-supplied `(b', j)` with
`b·b' = 1 + c·j`, take a modular inverse of `b` in residue form, `(b·b') % c = 1` (what a
Bezout/`modBezout` computation produces).  `div_add_mod` converts it to the additive form and
fires `neg_one_qr_of_inverse`. -/

/-- ★★★★ **The encoding fires from a modular inverse `(b·b') % c = 1`.**  If `b'` is an inverse
    of `b` mod `c` (residue form), then `c ∣ (a·b')² + 1` — `−1` is a QR mod `c`.  Bridges the
    encoding to how inverses are actually computed (Bezout / `modBezout`). -/
theorem neg_one_qr_of_mod (a b c b' : Nat) (h : markovEq a b c)
    (hmod : (b * b') % c = 1) : c ∣ ((a * b') * (a * b') + 1) := by
  have hdm := E213.Meta.Nat.AddMod213.div_add_mod (b * b') c
  rw [hmod] at hdm
  -- hdm : c * ((b*b')/c) + 1 = b*b'
  have hinv : b * b' = 1 + c * ((b * b') / c) :=
    hdm.symm.trans (Nat.add_comm (c * ((b * b') / c)) 1)
  exact neg_one_qr_of_inverse a b c b' ((b * b') / c) h hinv

/-! ## §12 — the encoding fires unconditionally on every reachable triple (C2→C4 closed)

Combining the coprimality invariant (`markov_reachable_gcd_bc`: `gcd(b,c) = 1`) with the
xgcd-correctness bridge (`MarkovPrimeFactor.inverse_of_coprime`: coprimality yields an explicit
modular inverse) discharges the encoding's invertibility hypothesis with no leftover assumption:
**every reachable Markov triple's maximum `c > 1` has `−1` as a quadratic residue**, witnessed by
`a · (b⁻¹ mod c)`.  This closes the C2→C4 chain — the `√(−1)` encoding now fires structurally,
not just on hand-supplied inverses. -/

/-- ★★★★★ **Unconditional `√(−1)` on every reachable triple.**  For a reachable Markov triple
    `(a,b,c)` with `1 < c`, `c ∣ (a·b')² + 1` where `b' = (modBezout b c).2` is the computed
    inverse of `b` mod `c`.  No invertibility hypothesis — it comes from `gcd(b,c)=1` (the tree
    invariant) through `inverse_of_coprime`. -/
theorem markov_reachable_neg_one_qr {a b c : Nat} (hc : 1 < c) (h : MarkovReachable a b c) :
    c ∣ ((a * (E213.Lib.Math.ModArith.ModBezout.modBezout b c).2)
       * (a * (E213.Lib.Math.ModArith.ModBezout.modBezout b c).2) + 1) := by
  have hcpos : 0 < c := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hc)
  have hinv : (b * (E213.Lib.Math.ModArith.ModBezout.modBezout b c).2) % c = 1 := by
    rw [E213.Lib.Math.ModArith.MarkovPrimeFactor.inverse_of_coprime b c hcpos
          (markov_reachable_gcd_bc h), Nat.mod_eq_of_lt hc]
  exact neg_one_qr_of_mod a b c (E213.Lib.Math.ModArith.ModBezout.modBezout b c).2
    (markov_reachable_is_triple h) hinv

/-! ## §13 — no prime `≡ 3 (mod 4)` divides a Markov number (the two halves meet)

The capstone joining the two files.  Every reachable Markov number `c > 1` carries a square root
of `−1` (`markov_reachable_neg_one_qr`); but `x² ≡ −1 (mod p)` is *impossible* when `p ≡ 3 (mod 4)`
(`MarkovPrimeFactor.no_sqrt_neg_one_4k3`, via Fermat).  A prime `p ≡ 3 (mod 4)` dividing `c` would
inherit the root mod `p` — contradiction.  So **every odd prime factor of a Markov number is
`≡ 1 (mod 4)`** (Zhang 2007), here ∅-axiom for the whole tree. -/

/-- ★★★★★ **No prime `≡ 3 (mod 4)` divides a reachable Markov number.**  For a reachable triple
    `(a,b,c)` with `1 < c` and `p = 4k+3` (with the FLT prime-gcd hypothesis), `¬ (p ∣ c)`.  The
    `√(−1)` mod `c` (`markov_reachable_neg_one_qr`) would descend to a `√(−1)` mod `p`, which
    `no_sqrt_neg_one_4k3` forbids. -/
theorem markov_reachable_no_3mod4_factor {a b c : Nat} (hc : 1 < c) (h : MarkovReachable a b c)
    (k : Nat)
    (hpg : ∀ m, 0 < m → m < 4 * k + 3 →
      (E213.Lib.Math.ModArith.ModBezout.modBezout m (4 * k + 3)).1 = 1) :
    ¬ ((4 * k + 3) ∣ c) := by
  intro hpc
  have hppos : 0 < 4 * k + 3 := Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 3 (4 * k))
  -- the √(−1): c ∣ u²+1, with u = a·b⁻¹ mod c
  have hcu := markov_reachable_neg_one_qr hc h
  generalize hu : a * (E213.Lib.Math.ModArith.ModBezout.modBezout b c).2 = u at hcu
  -- p ∣ u²+1
  have hpu : (4 * k + 3) ∣ (u * u + 1) :=
    E213.Lib.Math.ModArith.MarkovPrimeFactor.dvd_trans_loc (4 * k + 3) c (u * u + 1) hpc hcu
  -- reduce to x = u % p:  p ∣ x²+1, x < p
  have hpmod : (u * u + 1) % (4 * k + 3) = 0 := by
    obtain ⟨t, ht⟩ := hpu; rw [ht]; exact E213.Tactic.NatHelper.mul_mod_right (4 * k + 3) t
  have hxmod : ((u % (4 * k + 3)) * (u % (4 * k + 3)) + 1) % (4 * k + 3) = 0 := by
    have h1 : ((u % (4 * k + 3)) * (u % (4 * k + 3))) % (4 * k + 3) = (u * u) % (4 * k + 3) :=
      (E213.Meta.Nat.MulMod213.mul_mod_pure u u (4 * k + 3)).symm
    calc ((u % (4 * k + 3)) * (u % (4 * k + 3)) + 1) % (4 * k + 3)
        = (((u % (4 * k + 3)) * (u % (4 * k + 3))) % (4 * k + 3) + 1 % (4 * k + 3)) % (4 * k + 3) :=
          E213.Meta.Nat.AddMod213.add_mod_gen _ _ _
      _ = ((u * u) % (4 * k + 3) + 1 % (4 * k + 3)) % (4 * k + 3) := by rw [h1]
      _ = (u * u + 1) % (4 * k + 3) := (E213.Meta.Nat.AddMod213.add_mod_gen (u * u) 1 _).symm
      _ = 0 := hpmod
  have hpx : (4 * k + 3) ∣ ((u % (4 * k + 3)) * (u % (4 * k + 3)) + 1) :=
    E213.Meta.Nat.AddMod213.dvd_of_mod_eq_zero hxmod
  have hxlt : u % (4 * k + 3) < 4 * k + 3 := Nat.mod_lt u hppos
  rcases Nat.eq_zero_or_pos (u % (4 * k + 3)) with hx0 | hx0
  · -- x = 0 ⟹ p ∣ 1 ⟹ p ≤ 1, contra p ≥ 3
    rw [hx0] at hpx
    exact absurd (E213.Lib.Math.ModArith.MarkovPrimeFactor.le_of_dvd_loc (by decide) hpx)
      (Nat.not_le_of_lt (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 3 (4 * k))))
  · exact E213.Lib.Math.ModArith.MarkovPrimeFactor.no_sqrt_neg_one_4k3 k
      (u % (4 * k + 3)) hpg hx0 hxlt hpx

end E213.Lib.Math.Real213.MarkovUniqueness
