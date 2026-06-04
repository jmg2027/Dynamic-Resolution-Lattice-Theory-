import E213.Lib.Math.NumberSystems.Real213.MarkovUniqueness

/-!
# MarkovInjectivity — the residue-map injectivity analysis (Zhang/Frobenius skeleton)

The Markov uniqueness conjecture at a fixed maximum `c` reduces to **injectivity of the residue
map** `triple ↦ u`, `u = (a·b⁻¹) mod c` (a root of `x² ≡ −1`).  Following the classical
literature (Frobenius 1913; Baragar 1996, Button 1998, Lang–Tan 2005, Zhang 2007; Aigner's book),
this module records the *correct* shape of the argument and isolates what is elementary from what
is open.

**What is the easy direction.**  `triple ↦ u` is injective once one has the *window
normalization*: among the (at most two, for prime powers) roots `{r, c−r}` of `x² ≡ −1`, the one
in `(0, c/2)` is unique (`root_unique_below_half`), and the strictly monotone recovery
`u/c ↦ (a,b)` reconstructs the ordered triple.  The monotonicity (Zhang Lemma 2) needs the
Farey/Stern-Brocot slope parametrisation; the *root-window uniqueness* (Zhang **Lemma 4**, the
single place primality enters) is proved here outright from the 2-root property.

**Why there is no determinant size bound.**  Two ordered triples sharing a root `u` ARE parallel
mod `c`: `c ∣ a₁·b₂ − a₂·b₁` (`markov_same_root_parallel`).  One is tempted to finish by bounding
`|a₁b₂ − a₂b₁| < c` to force `= 0` and conclude equality (`coprime_cross_eq`).  **This bound is
false**: by Frobenius's identities `u_t·m_r − u_r·m_t = m_s`, the cross-determinant equals a
*neighbouring Markov number* (≈ `c`), a genuine nonzero multiple of `c`.  So the parallel relation,
while true and exact, does **not** self-close — recorded here to mark the dead end.

**What is open.**  For composite `c` with `≥ 2` distinct prime factors, `x² ≡ −1 (mod c)` has
`2^{ω−1}` roots in the window, and it is unknown that at most one is *Markov-realisable*.  That
root-counting — not the injectivity of `triple ↦ u` — is the open content of the Frobenius
conjecture.  (Our per-`c` `decide` certificates do this counting concretely up to `c = 1325`.)
-/

namespace E213.Lib.Math.NumberSystems.Real213.MarkovInjectivity

open E213.Lib.Math.NumberSystems.Real213.MarkovTree (markovEq)
open E213.Tactic.NatHelper (gcd213 add_sub_cancel_right mul_mod_right)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Lib.Math.NumberSystems.Real213.MarkovUniqueness
  (SqrtNegOneTwoRoots sqrtNegOneTwoRoots_prime_pow markov_ordered_coprime markov_a_pos
   MarkovMaxUnique markov_mid_lt_max markov_root_recovery dvd_mul_right_213 eq_one_of_dvd_one)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (euclid_of_coprime le_of_dvd_loc)
open E213.Meta.Nat.Gcd213 (gcd213_comm gcd213_dvd_left gcd213_dvd_right dvd_sub_213 dvd_add_213)
open E213.Lib.Math.NumberSystems.Real213.GoldenFormMarkov (add_left_cancel_pure)

/-! ## §1 — the parallel reduction (true, but does not self-close) -/

/-- ★★★ **Same-root triples are parallel mod `c`.**  If `(u·b₁) % c = a₁` and `(u·b₂) % c = a₂`
    (the two triples share the residue `u`), then `a₁·b₂ ≡ a₂·b₁ (mod c)` — the Markov pairs are
    parallel as vectors over `ℤ/c`.  (`a_i ≡ u·b_i`, so `a₁b₂ ≡ u·b₁b₂ ≡ a₂b₁`.) -/
theorem markov_same_root_parallel (a₁ b₁ a₂ b₂ c u : Nat)
    (h1 : (u * b₁) % c = a₁) (h2 : (u * b₂) % c = a₂) :
    (a₁ * b₂) % c = (a₂ * b₁) % c := by
  rw [← h1, ← h2,
      ← E213.Meta.Nat.MulMod213.mul_mod_left_pure (u * b₁) b₂ c,
      ← E213.Meta.Nat.MulMod213.mul_mod_left_pure (u * b₂) b₁ c,
      show u * b₁ * b₂ = u * b₂ * b₁ from by ring_nat]

/-- ★★★ **Coprime + *exactly* parallel ⟹ equal.**  Two coprime pairs with `a₁·b₂ = a₂·b₁` (exact,
    not merely mod `c`) coincide: `b₁ ∣ b₂` and `b₂ ∣ b₁` (Euclid, via coprimality), so `b₁ = b₂`,
    then `a₁ = a₂` by cancellation.  This is the closing step *if* the cross-determinant vanished
    — which (see header) it does not for distinct triples. -/
theorem coprime_cross_eq (a₁ b₁ a₂ b₂ : Nat) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hco₁ : gcd213 a₁ b₁ = 1) (hco₂ : gcd213 a₂ b₂ = 1)
    (hcross : a₁ * b₂ = a₂ * b₁) : a₁ = a₂ ∧ b₁ = b₂ := by
  have hb1b2 : b₁ ∣ b₂ := by
    have hd : b₁ ∣ a₁ * b₂ := ⟨a₂, by rw [hcross, Nat.mul_comm]⟩
    rcases Nat.lt_or_ge 1 b₁ with hgt | hle
    · exact euclid_of_coprime a₁ b₂ b₁ hgt (gcd213_comm a₁ b₁ ▸ hco₁) hd
    · exact (Nat.le_antisymm hle hb₁) ▸ ⟨b₂, (Nat.one_mul b₂).symm⟩
  have hb2b1 : b₂ ∣ b₁ := by
    have hd : b₂ ∣ a₂ * b₁ := ⟨a₁, by rw [← hcross, Nat.mul_comm]⟩
    rcases Nat.lt_or_ge 1 b₂ with hgt | hle
    · exact euclid_of_coprime a₂ b₁ b₂ hgt (gcd213_comm a₂ b₂ ▸ hco₂) hd
    · exact (Nat.le_antisymm hle hb₂) ▸ ⟨b₁, (Nat.one_mul b₁).symm⟩
  have hbeq : b₁ = b₂ := Nat.le_antisymm (le_of_dvd_loc hb₂ hb1b2) (le_of_dvd_loc hb₁ hb2b1)
  exact ⟨Nat.eq_of_mul_eq_mul_right hb₂ (by rw [hcross, hbeq]), hbeq⟩

/-- ★★★ **Two ordered Markov triples with vanishing cross-determinant are equal.**  Combines
    `coprime_cross_eq` with the (general, descent-theorem) pairwise coprimality of Markov triples.
    The hypothesis `a₁·b₂ = a₂·b₁` is exactly "the residue map does not separate them and the
    cross-determinant vanishes" — true iff the triples coincide. -/
theorem markov_eq_of_cross (a₁ b₁ a₂ b₂ c : Nat) (hc : 2 ≤ c)
    (h1 : markovEq a₁ b₁ c) (hab1 : a₁ ≤ b₁) (hbc1 : b₁ ≤ c)
    (h2 : markovEq a₂ b₂ c) (hab2 : a₂ ≤ b₂) (hbc2 : b₂ ≤ c)
    (hcross : a₁ * b₂ = a₂ * b₁) : a₁ = a₂ ∧ b₁ = b₂ := by
  have hco1 := (markov_ordered_coprime a₁ b₁ c h1 (markov_a_pos hc h1) hab1 hbc1).1
  have hco2 := (markov_ordered_coprime a₂ b₂ c h2 (markov_a_pos hc h2) hab2 hbc2).1
  exact coprime_cross_eq a₁ b₁ a₂ b₂
    (Nat.lt_of_lt_of_le (markov_a_pos hc h1) hab1) (Nat.lt_of_lt_of_le (markov_a_pos hc h2) hab2)
    hco1 hco2 hcross

/-! ## §2 — Zhang's Lemma 4: the root window holds ≤ 1 root (the primality lock) -/

/-- ★★★★ **At most one `√(−1)` in the window `(0, c/2)`** (Zhang Lemma 4 core).  If `x² ≡ −1` has
    at most the two roots `{r, c−r}` (`SqrtNegOneTwoRoots c`), then a root `x` with `2x < c` is
    unique: the alternative `x + y = c` is impossible when both `2x, 2y < c`.  This is the single
    ingredient that, with the (Farey-monotone) recovery, pins the triple — and the *only* place
    the root-count `≤ 2` (i.e. prime-power-ness) is used. -/
theorem root_unique_below_half (c : Nat) (h2 : SqrtNegOneTwoRoots c)
    {x y : Nat} (hx : x < c) (hy : y < c) (hxh : 2 * x < c) (hyh : 2 * y < c)
    (hrx : (x * x + 1) % c = 0) (hry : (y * y + 1) % c = 0) : x = y := by
  rcases h2 x hx y hy hrx hry with heq | hsum
  · exact heq
  · exfalso
    have hlt : 2 * x + 2 * y < c + c := Nat.add_lt_add hxh hyh
    rw [show 2 * x + 2 * y = (x + y) + (x + y) from by ring_nat, hsum] at hlt
    exact absurd hlt (Nat.lt_irrefl (c + c))

/-- ★★★★ **The window root is unique at every odd prime power** (Zhang Lemma 4).  For `c = p^(k+1)`
    (`p ≥ 3` prime), `x² ≡ −1 (mod c)` has at most one root in `(0, c/2)`.  The prime-power
    hypothesis enters *only* through `sqrtNegOneTwoRoots_prime_pow` (≤ 2 roots); everything else is
    `root_unique_below_half`.  With the Farey-monotone recovery (Zhang Lemma 2, not yet formalised)
    this yields prime-power Markov uniqueness — Button's theorem. -/
theorem root_unique_below_half_prime_pow (p k : Nat) (hp3 : 3 ≤ p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p)
    {x y : Nat} (hx : x < p ^ (k + 1)) (hy : y < p ^ (k + 1))
    (hxh : 2 * x < p ^ (k + 1)) (hyh : 2 * y < p ^ (k + 1))
    (hrx : (x * x + 1) % p ^ (k + 1) = 0) (hry : (y * y + 1) % p ^ (k + 1) = 0) : x = y :=
  root_unique_below_half (p ^ (k + 1)) (sqrtNegOneTwoRoots_prime_pow p k hp3 hpr)
    hx hy hxh hyh hrx hry

/-- ★★★★ **The ±-root pairing**: if `r` is a `√(−1)` mod `c`, so is `c − r`.  `(c−r)² ≡ r² ≡ −1`,
    via the `ℕ` identity `(c−r)² + 2cr = c² + r²` (so `(c−r)²+1 ≡ r²+1 ≡ 0`).  The two roots of
    `x²≡−1` thus form the pair `{r, c−r}` — the structural fact behind `SqrtNegOneTwoRoots`'s
    `x+y=c` branch and the window normalization. -/
theorem neg_root_is_root (c r : Nat) (hr : r ≤ c) (h : (r * r + 1) % c = 0) :
    ((c - r) * (c - r) + 1) % c = 0 := by
  obtain ⟨d, hd⟩ := Nat.le.dest hr
  have hcr : c - r = d := by rw [← hd, Nat.add_comm]; exact add_sub_cancel_right d r
  rw [hcr]
  have hid : (d * d + 1) + 2 * c * r = c * c + (r * r + 1) := by rw [← hd]; ring_nat
  have hRdvd : c ∣ c * c + (r * r + 1) :=
    dvd_add_213 c (c * c) (r * r + 1) ⟨c, rfl⟩ (dvd_of_mod_eq_zero h)
  have h2cr : c ∣ 2 * c * r := ⟨2 * r, by ring_nat⟩
  have hdvd : c ∣ (d * d + 1) := by
    have hs := dvd_sub_213 (2 * c * r) ((d * d + 1) + 2 * c * r) c
      (Nat.le_add_left _ _) h2cr (hid ▸ hRdvd)
    rwa [add_sub_cancel_right] at hs
  obtain ⟨k, hk⟩ := hdvd; rw [hk]; exact mul_mod_right c k

/-! ## §3 — the capstone reduction: uniqueness ⟸ root-count + residue injectivity -/

/-- **Residue-map injectivity up to sign** (Zhang Lemma 2).  Two ordered Markov triples at `c` whose
    recovered residues `u₁,u₂` lie in the same `±`-pair (`u₁=u₂` or `u₁+u₂=c`) coincide.  Classically
    true by the strict monotonicity of `u_t/m_t` along the Farey slope.

    **The injectivity content is closed, not bypassed.**  `triple ↦ windowed residue` *is* injective
    — that is exactly what `SternBrocotMarkov.slope_path_inj` proves (the tree recovers the path, hence
    the triple, from the slope `u/c`).  What is *superseded* is only the packaging: this
    `SamePairInjective` predicate and the size-bound route (`coprime_cross_eq` with `|a₁b₂−a₂b₁|<c`,
    which genuinely dead-ends since the cross-determinant is a neighbour Markov number ≈ `c`).  The
    *global* slope route reaches the same injectivity the local bound could not.  Consequently
    `markov_max_unique_tree` needs only `SqrtNegOneTwoRoots` (no `SamePairInjective` hypothesis) and
    `markov_prime_pow_unique` closes Button's family `∅`-axiom.  This definition +
    `markov_max_unique_of_same_pair_injective` below remain a valid (weaker, classical) reduction, kept
    for the literature mapping. -/
def SamePairInjective (c : Nat) : Prop :=
  ∀ a₁ b₁ a₂ b₂ u₁ u₂ : Nat, a₁ ≤ b₁ → b₁ ≤ c → markovEq a₁ b₁ c →
    a₂ ≤ b₂ → b₂ ≤ c → markovEq a₂ b₂ c →
    u₁ < c → (u₁ * b₁) % c = a₁ → u₂ < c → (u₂ * b₂) % c = a₂ →
    (u₁ = u₂ ∨ u₁ + u₂ = c) → a₁ = a₂ ∧ b₁ = b₂

/-- ★★★★★ **The classical reduction, formalised.**  `MarkovMaxUnique c` follows from the
    root-count input `SqrtNegOneTwoRoots c` (at most the two roots `±u`) together with the
    residue-map injectivity `SamePairInjective c`.  Proof: recover each triple's residue
    (`markov_root_recovery`); `SqrtNegOneTwoRoots` forces the two residues into one `±`-pair;
    `SamePairInjective` then identifies the triples.  This is the exact Frobenius/Aigner reduction
    — both hypotheses are honest (neither is `MarkovMaxUnique` in disguise): `SqrtNegOneTwoRoots`
    is a pure congruence fact (proved for prime powers, `sqrtNegOneTwoRoots_prime_pow`), and
    `SamePairInjective` is the Farey-monotonicity recovery (Zhang Lemma 2). -/
theorem markov_max_unique_of_same_pair_injective (c : Nat) (hc : 2 ≤ c)
    (h2 : SqrtNegOneTwoRoots c) (hinj : SamePairInjective c) : MarkovMaxUnique c := by
  intro a₁ b₁ a₂ b₂ hab1 hbc1 hab2 hbc2 hm1 hm2
  have ha1 := markov_a_pos hc hm1
  have ha2 := markov_a_pos hc hm2
  have hb1lt : b₁ < c := markov_mid_lt_max a₁ b₁ c hm1 ha1 hab1 hbc1 hc
  have hb2lt : b₂ < c := markov_mid_lt_max a₂ b₂ c hm2 ha2 hab2 hbc2 hc
  have hco1 := (markov_ordered_coprime a₁ b₁ c hm1 ha1 hab1 hbc1).2.2
  have hco2 := (markov_ordered_coprime a₂ b₂ c hm2 ha2 hab2 hbc2).2.2
  obtain ⟨u₁, hu1lt, hu1root, hu1rec⟩ :=
    markov_root_recovery a₁ b₁ c hc (Nat.lt_of_le_of_lt hab1 hb1lt) hco1 hm1
  obtain ⟨u₂, hu2lt, hu2root, hu2rec⟩ :=
    markov_root_recovery a₂ b₂ c hc (Nat.lt_of_le_of_lt hab2 hb2lt) hco2 hm2
  exact hinj a₁ b₁ a₂ b₂ u₁ u₂ hab1 hbc1 hm1 hab2 hbc2 hm2
    hu1lt hu1rec.symm hu2lt hu2rec.symm (h2 u₁ hu1lt u₂ hu2lt hu1root hu2root)

/-- `2 ≤ p^(k+1)` for `p ≥ 2` (helper for the prime-power instance). -/
private theorem two_le_pow_succ (p k : Nat) (hp : 2 ≤ p) : 2 ≤ p ^ (k + 1) := by
  induction k with
  | zero => rw [Nat.pow_one]; exact hp
  | succ n ih =>
      rw [Nat.pow_succ]
      exact Nat.le_trans ih
        (Nat.le_mul_of_pos_right (p ^ (n + 1)) (Nat.lt_of_lt_of_le (by decide) hp))

/-- ★★★★★ **Prime-power Markov uniqueness ⟸ residue injectivity (Button's theorem, packaged).**
    For an odd prime power `c = p^(k+1)`, `MarkovMaxUnique c` follows from `SamePairInjective c`
    alone — the root-count input is discharged by `sqrtNegOneTwoRoots_prime_pow`.  So the entire
    prime-power unicity conjecture (an infinite family) is reduced to the single Farey-monotonicity
    recovery `SamePairInjective`. -/
theorem markov_prime_pow_unique_of_same_pair_injective (p k : Nat) (hp3 : 3 ≤ p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (hinj : SamePairInjective (p ^ (k + 1))) :
    MarkovMaxUnique (p ^ (k + 1)) :=
  markov_max_unique_of_same_pair_injective (p ^ (k + 1))
    (two_le_pow_succ p k (Nat.le_trans (by decide) hp3))
    (sqrtNegOneTwoRoots_prime_pow p k hp3 hpr) hinj

/-! ## §4 — a Markov triple is determined by its two largest entries -/

/-- ★★★★ **The middle entry determines the smallest** (Vieta-quadratic uniqueness).  Two ordered
    Markov triples sharing the pair `(b,c)` coincide: `a` is the *unique* root `≤ b` of
    `x² − 3bc·x + (b²+c²) = 0` (the other root `3bc − a > b`).  Proof: the symmetric relation
    `a₁² + 3·a₂·b·c = a₂² + 3·a₁·b·c` forces `a₁ = a₂` or `a₁ + a₂ = 3bc`; the latter is impossible
    since `a₁+a₂ ≤ 2b < 3bc` (`c ≥ 2`).  So a Markov triple is pinned by its two largest entries —
    uniqueness at `c` reduces to *middle-entry* uniqueness. -/
theorem markov_same_mid_eq (a₁ a₂ b c : Nat) (hc : 2 ≤ c)
    (h1 : markovEq a₁ b c) (h2 : markovEq a₂ b c) (hb1 : a₁ ≤ b) (hb2 : a₂ ≤ b) :
    a₁ = a₂ := by
  have e1 : a₁ * a₁ + b * b + c * c = 3 * a₁ * b * c := h1
  have e2 : a₂ * a₂ + b * b + c * c = 3 * a₂ * b * c := h2
  have hkey : a₁ * a₁ + 3 * a₂ * b * c = a₂ * a₂ + 3 * a₁ * b * c := by
    have hL : (b * b + c * c) + (a₁ * a₁ + 3 * a₂ * b * c)
            = (b * b + c * c) + (a₂ * a₂ + 3 * a₁ * b * c) := by
      rw [show (b*b+c*c) + (a₁*a₁ + 3*a₂*b*c) = (a₁*a₁+b*b+c*c) + 3*a₂*b*c from by ring_nat,
          show (b*b+c*c) + (a₂*a₂ + 3*a₁*b*c) = (a₂*a₂+b*b+c*c) + 3*a₁*b*c from by ring_nat,
          e1, e2]; ring_nat
    exact add_left_cancel_pure _ _ _ hL
  have hbpos : 1 ≤ b := Nat.le_trans (markov_a_pos hc h1) hb1
  have hsum_le : a₁ + a₂ ≤ 2 * b := by
    rw [show 2 * b = b + b from by ring_nat]; exact Nat.add_le_add hb1 hb2
  have h6le : (6 : Nat) ≤ 3 * c := by rw [show (6:Nat) = 3 * 2 from rfl]; exact Nat.mul_le_mul_left 3 hc
  have h23c : 2 < 3 * c := Nat.lt_of_lt_of_le (by decide) h6le
  have hsum_lt : 2 * b < 3 * b * c := by
    rw [show 2 * b = b * 2 from by ring_nat, show 3 * b * c = b * (3 * c) from by ring_nat]
    exact Nat.mul_lt_mul_of_pos_left h23c hbpos
  rcases Nat.le_total a₁ a₂ with hle | hle
  · obtain ⟨d, hd⟩ := Nat.le.dest hle
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · rw [← hd, hd0, Nat.add_zero]
    · exfalso
      have hmul : d * (3 * b * c) = d * (2 * a₁ + d) := by
        have hk : a₁ * a₁ + 3 * (a₁ + d) * b * c = (a₁ + d) * (a₁ + d) + 3 * a₁ * b * c := by
          rw [hd]; exact hkey
        have hcab : (a₁*a₁ + 3*a₁*b*c) + d*(3*b*c) = (a₁*a₁ + 3*a₁*b*c) + d*(2*a₁+d) := by
          rw [show (a₁*a₁+3*a₁*b*c) + d*(3*b*c) = a₁*a₁ + 3*(a₁+d)*b*c from by ring_nat,
              show (a₁*a₁+3*a₁*b*c) + d*(2*a₁+d) = (a₁+d)*(a₁+d) + 3*a₁*b*c from by ring_nat]
          exact hk
        exact add_left_cancel_pure _ _ _ hcab
      have heq : 3 * b * c = 2 * a₁ + d := Nat.eq_of_mul_eq_mul_left hdpos hmul
      have hsum : a₁ + a₂ = 3 * b * c := by rw [heq, ← hd]; ring_nat
      exact absurd (hsum ▸ hsum_le) (Nat.not_le_of_lt hsum_lt)
  · obtain ⟨d, hd⟩ := Nat.le.dest hle
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · rw [← hd, hd0, Nat.add_zero]
    · exfalso
      have hmul : d * (3 * b * c) = d * (2 * a₂ + d) := by
        have hk : a₂ * a₂ + 3 * (a₂ + d) * b * c = (a₂ + d) * (a₂ + d) + 3 * a₂ * b * c := by
          rw [hd]; exact hkey.symm
        have hcab : (a₂*a₂ + 3*a₂*b*c) + d*(3*b*c) = (a₂*a₂ + 3*a₂*b*c) + d*(2*a₂+d) := by
          rw [show (a₂*a₂+3*a₂*b*c) + d*(3*b*c) = a₂*a₂ + 3*(a₂+d)*b*c from by ring_nat,
              show (a₂*a₂+3*a₂*b*c) + d*(2*a₂+d) = (a₂+d)*(a₂+d) + 3*a₂*b*c from by ring_nat]
          exact hk
        exact add_left_cancel_pure _ _ _ hcab
      have heq : 3 * b * c = 2 * a₂ + d := Nat.eq_of_mul_eq_mul_left hdpos hmul
      have hsum : a₁ + a₂ = 3 * b * c := by rw [heq, ← hd]; ring_nat
      exact absurd (hsum ▸ hsum_le) (Nat.not_le_of_lt hsum_lt)

/-! ## §5 — Farey foundations toward `SamePairInjective` (the open recovery)

A bridge to the Farey-monotone recovery (Zhang Lemma 2) needs the Stern-Brocot tree as the lattice
of *coprime* pairs.  Note the repo's `Mobius213SternBrocot.SternBrocotReachable` takes mediants of
*any* two reachable pairs, so it includes non-coprime pairs (e.g. `(2,2)=(1,0)+(1,2)`) — coprimality
needs the **Farey-adjacency** (det `±1`) restriction.  The foundational fact: -/

/-- ★★★★ **The mediant of two Farey-adjacent pairs is coprime.**  If `(p,q)`, `(r,s)` are Farey
    neighbours (`p·s = q·r + 1`), then `gcd(p+r, q+s) = 1`: any common divisor of `p+r` and `q+s`
    divides `(p+r)·s − (q+s)·r = p·s − q·r = 1`.  This is the coprimality engine of the
    Stern-Brocot / continued-fraction recovery — the correct (adjacency-restricted) form of the
    "SB node = coprime pair" backbone. -/
theorem farey_mediant_coprime (p q r s : Nat) (hdet : p * s = q * r + 1) :
    gcd213 (p + r) (q + s) = 1 := by
  have hgA : gcd213 (p + r) (q + s) ∣ (p + r) * s := dvd_mul_right_213 _ _ _ (gcd213_dvd_left _ _)
  have hgB : gcd213 (p + r) (q + s) ∣ (q + s) * r := dvd_mul_right_213 _ _ _ (gcd213_dvd_right _ _)
  have hkey : (p + r) * s = (q + s) * r + 1 := by
    rw [show (p+r)*s = p*s + r*s from by ring_nat, hdet,
        show (q+s)*r = q*r + s*r from by ring_nat]; ring_nat
  have hle : (q + s) * r ≤ (p + r) * s := by rw [hkey]; exact Nat.le_succ _
  have hsub := dvd_sub_213 ((q + s) * r) ((p + r) * s) (gcd213 (p + r) (q + s)) hle hgB hgA
  rw [hkey, show (q + s) * r + 1 - (q + s) * r = 1 from by
        rw [Nat.add_comm ((q + s) * r) 1]; exact add_sub_cancel_right 1 ((q + s) * r)] at hsub
  exact eq_one_of_dvd_one hsub

/-- ★★★★ **The mediant is Farey-adjacent to each parent** (the defining Stern-Brocot property).
    If `(p,q)`, `(r,s)` are Farey neighbours (`p·s = q·r + 1`), the mediant `(p+r, q+s)` inserts
    between them preserving adjacency: `p·(q+s) = q·(p+r) + 1` (left) and `(p+r)·s = (q+s)·r + 1`
    (right).  With `farey_mediant_coprime`, this is the correct (det-1) Layer-1 foundation for the
    Stern-Brocot recovery — the structure on which the residue's Farey-monotonicity (Zhang Lemma 2,
    the open `SamePairInjective`) is built. -/
theorem farey_mediant_adjacent (p q r s : Nat) (hdet : p * s = q * r + 1) :
    p * (q + s) = q * (p + r) + 1 ∧ (p + r) * s = (q + s) * r + 1 := by
  refine ⟨?_, ?_⟩
  · rw [show p * (q + s) = p * s + p * q from by ring_nat, hdet,
        show q * (p + r) = q * p + q * r from by ring_nat]; ring_nat
  · rw [show (p + r) * s = p * s + r * s from by ring_nat, hdet,
        show (q + s) * r = q * r + s * r from by ring_nat]; ring_nat

end E213.Lib.Math.NumberSystems.Real213.MarkovInjectivity
