import E213.Lib.Math.NumberSystems.Real213.ExpLog.ExpUnitModulus
import E213.Lib.Math.NumberSystems.Real213.AbCutSeq
import E213.Meta.Nat.PolyNatMTactic

/-!
# ExpRationalCut — `exp(p/q)` as a constructed fold (an `AbCutSeq` with a bracket)

The positive companion of `ExpUnitModulus` §6.  There it is **proven**
(`exp_pq_no_htel`) that for `p ≥ 2` the factorial presentation of `exp(p/q)` carries no
`Htel` rate certificate — so the e-generator cannot complete it.  This file builds what
*is* constructible from that presentation, the ζ(3) posture (`Zeta3Cut`):

  * **the fold** (`expPQAb : AbCutSeq`): the partial-sum convergents
    `expNum p q n / expUDen q n` are ab-monotone with positive denominators, so the
    whole cut interface (layer `ValidCut`s, nesting, eventual constancy, completion to
    a `ValidCut` limit *given* a modulus) is generic;
  * **the upper bracket** (`exp_pq_upper_invariant` / `exp_pq_le_upper`): past the
    ratio-test threshold `2p ≤ (N+2)q`, the doubled-tail invariant
    `S_{N+j} + 2·t_{N+j+1} ≤ S_N + 2·t_{N+1}` closes by induction (each Taylor term at
    most half the previous), so **every** later convergent is `≤ U_N/d_{N+1}` with
    `U_N = a_N·(N+1)q + 2p^{N+1}` — the analytic geometric-tail bound as one `Nat`
    inequality;
  * **`e² = exp(2)` localized** (`exp_two_localized`): `7 < e² ≤ 904/120 (= 7.5\overline{3})`
    — the lower side a `false` cut reading at layer 5 (propagating by nesting), the
    upper side the `N = 4` bracket.

**Honest boundary** (the ζ(3) symmetry): the fold is closed; the **free total modulus
is open** — by `exp_pq_no_htel` it cannot come from this presentation's rate, so it
needs either the dyadic-bracket *schedule* presentation (`CubeRootTwoCut` pattern,
fed by the bracket above) or an effective irrationality certificate for `exp(p/q)`
(the Padé route) — recorded in `modulus_degree_ladder.md` rung 0″/1.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.ExpRationalCut

open E213.Theory (Raw)
open E213.Lens.Instances.AB (abLens)
open E213.Lib.Math.Analysis.Cauchy.Archimedean (orderProj)
open E213.Lib.Math.Analysis.Cauchy.PellSeq (abLens_witness)
open E213.Lib.Math.Analysis.Cauchy.MonotonicBounded (IsAbMonotonic IsAbPositiveB)
open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)
open E213.Lib.Math.NumberSystems.Real213 (AbCutSeq)
open E213.Lib.Math.NumberSystems.Real213.Core.ValidCut (ValidCut)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.ExpUnitModulus
  (expNum expUDen expUDen_pos exp_pq_cross_det)
open E213.Meta.Nat.NatRing213 (nat_mul_lt_mul_right)

/-! ## §1 — positivity -/

/-- Numerators are positive (`q ≥ 1`). -/
theorem expNum_pos (p q : Nat) (hq : 1 ≤ q) : ∀ n, 1 ≤ expNum p q n
  | 0 => Nat.le_refl 1
  | n + 1 => by
    show 1 ≤ (n + 1) * q * expNum p q n + p ^ (n + 1)
    exact Nat.le_trans
      (Nat.mul_le_mul (Nat.mul_le_mul (Nat.succ_le_succ (Nat.zero_le n)) hq)
        (expNum_pos p q hq n))
      (Nat.le_add_right _ _)

/-! ## §2 — the fold: `exp(p/q)` as an `AbCutSeq` -/

/-- The convergent Raw at layer `n`, reading `(expNum p q n, expUDen q n)`. -/
def expPQRaw (p q : Nat) (hq : 1 ≤ q) (n : Nat) :
    {r : Raw // abLens.view r = (expNum p q n, expUDen q n)} :=
  abLens_witness (expNum p q n + expUDen q n) (expNum p q n) (expUDen q n) rfl
    (expNum_pos p q hq n) (expUDen_pos q hq n)

theorem expPQRaw_view (p q : Nat) (hq : 1 ≤ q) (n : Nat) :
    abLens.view (expPQRaw p q hq n).val = (expNum p q n, expUDen q n) :=
  (expPQRaw p q hq n).property

/-- The convergent Raw sequence. -/
def expPQRawSeq (p q : Nat) (hq : 1 ≤ q) : Nat → Raw := fun n => (expPQRaw p q hq n).val

/-- The convergents climb (ab-monotone), directly from the cross-determinant. -/
theorem expPQ_isAbMonotonic (p q : Nat) (hq : 1 ≤ q) :
    IsAbMonotonic (expPQRawSeq p q hq) := by
  intro n
  show (abLens.view (expPQRaw p q hq n).val).1
        * (abLens.view (expPQRaw p q hq (n + 1)).val).2
      ≤ (abLens.view (expPQRaw p q hq (n + 1)).val).1
        * (abLens.view (expPQRaw p q hq n).val).2
  rw [expPQRaw_view, expPQRaw_view]
  show expNum p q n * expUDen q (n + 1) ≤ expNum p q (n + 1) * expUDen q n
  exact Nat.le.intro (exp_pq_cross_det p q n).symm

/-- Positive denominators. -/
theorem expPQ_isAbPositiveB (p q : Nat) (hq : 1 ≤ q) :
    IsAbPositiveB (expPQRawSeq p q hq) := by
  intro n
  show 1 ≤ (abLens.view (expPQRaw p q hq n).val).2
  rw [expPQRaw_view]
  exact expUDen_pos q hq n

/-- ★★★ **`exp(p/q)`'s partial-sum convergents as an `AbCutSeq`** — the fold's
    carrier, for every rational argument `p/q` (`q ≥ 1`).  The whole cut interface
    (layer `ValidCut`s, nesting, eventual constancy, completion to a `ValidCut` limit
    given a modulus) applies generically — `exp` at *every* positive rational now has
    its constructed fold, the ζ(3) posture. -/
def expPQAb (p q : Nat) (hq : 1 ≤ q) : AbCutSeq :=
  ⟨expPQRawSeq p q hq, expPQ_isAbMonotonic p q hq, expPQ_isAbPositiveB p q hq⟩

/-- **`exp(p/q)`'s cut at layer `n`**: `decide (expNum p q n · k ≤ expUDen q n · m)`. -/
def expPQCut (p q : Nat) (hq : 1 ≤ q) (n : Nat) : Nat → Nat → Bool :=
  (expPQAb p q hq).cut n

/-- Each layer cut is a `ValidCut`. -/
theorem expPQCut_valid (p q : Nat) (hq : 1 ≤ q) (n : Nat) :
    ValidCut (expPQCut p q hq n) := (expPQAb p q hq).cut_valid n

/-- The `constCut` view of the layer cut. -/
theorem expPQCut_eq (p q : Nat) (hq : 1 ≤ q) (n m k : Nat) :
    expPQCut p q hq n m k = decide (expNum p q n * k ≤ expUDen q n * m) := by
  show orderProj m k (abLens.view (expPQRaw p q hq n).val) = _
  rw [expPQRaw_view]; rfl

/-! ## §3 — the upper bracket: the geometric tail as one `Nat` invariant

Past the ratio-test threshold `2p ≤ (N+2)q`, each Taylor term is at most half the
previous, so the doubled-tail quantity `S_i + 2·t_{i+1}` is non-increasing.  Over the
common denominators this is `upNum p q i / expUDen q (i+1)` with
`upNum p q i = aᵢ·(i+1)q + 2p^{i+1}` — and the invariant below says exactly that it
never exceeds its value at `N`. -/

/-- The doubled-tail upper numerator at layer `i` (over denominator `d_{i+1}`):
    `S_i + 2·t_{i+1} = (aᵢ·(i+1)q + 2p^{i+1}) / d_{i+1}`. -/
def upNum (p q i : Nat) : Nat := expNum p q i * ((i + 1) * q) + 2 * p ^ (i + 1)

/-- ★★★★ **The doubled-tail invariant**: past the threshold `2p ≤ (N+2)q`, the
    quantity `S_i + 2·t_{i+1}` is non-increasing — cross-multiplied,
    `upNum(N+j)·d_{N+1} ≤ upNum(N)·d_{N+j+1}` for every `j`.  Induction: one step
    costs exactly `t_{i+1} − 2·t_{i+2} ≥ 0`, the term-halving (`2p ≤ (i+2)q`). -/
theorem exp_pq_upper_invariant (p q N : Nat) (hN : 2 * p ≤ (N + 2) * q) :
    ∀ j, upNum p q (N + j) * expUDen q (N + 1)
        ≤ upNum p q N * expUDen q (N + j + 1)
  | 0 => Nat.le_refl _
  | j + 1 => by
    have ih := exp_pq_upper_invariant p q N hN j
    have h2p : 2 * p ≤ (N + j + 2) * q :=
      Nat.le_trans hN
        (Nat.mul_le_mul (Nat.le.intro (show N + 2 + j = N + j + 2 from by ring_nat))
          (Nat.le_refl q))
    obtain ⟨e, he⟩ := Nat.le.dest h2p
    have hstep : upNum p q (N + j + 1) ≤ upNum p q (N + j) * ((N + j + 2) * q) := by
      refine Nat.le.intro (k := p ^ (N + j + 1) * e) ?_
      show (((N + j + 1) * q * expNum p q (N + j) + p ^ (N + j + 1)) * ((N + j + 2) * q)
            + 2 * (p ^ (N + j + 1) * p)) + p ^ (N + j + 1) * e
          = (expNum p q (N + j) * ((N + j + 1) * q) + 2 * p ^ (N + j + 1))
            * ((N + j + 2) * q)
      rw [← he]
      ring_nat
    calc upNum p q (N + j + 1) * expUDen q (N + 1)
        ≤ (upNum p q (N + j) * ((N + j + 2) * q)) * expUDen q (N + 1) :=
          Nat.mul_le_mul hstep (Nat.le_refl _)
      _ = ((N + j + 2) * q) * (upNum p q (N + j) * expUDen q (N + 1)) := by ring_nat
      _ ≤ ((N + j + 2) * q) * (upNum p q N * expUDen q (N + j + 1)) :=
          Nat.mul_le_mul_left _ ih
      _ = upNum p q N * ((N + j + 2) * q * expUDen q (N + j + 1)) := by ring_nat

/-- ★★★★★ **The upper bracket**: past the threshold, **every** later convergent is
    bounded by the layer-`N` doubled-tail value — `S_{N+j} ≤ U_N/d_{N+1}` with
    `U_N = upNum p q N`, cross-multiplied.  The analytic geometric-tail bound
    (`CutExpModulus`'s halving) delivered as a single `Nat` inequality on the fold. -/
theorem exp_pq_le_upper (p q N : Nat) (hq : 1 ≤ q) (hN : 2 * p ≤ (N + 2) * q) :
    ∀ j, expNum p q (N + j) * expUDen q (N + 1) ≤ upNum p q N * expUDen q (N + j) := by
  intro j
  have hlocal : expNum p q (N + j) * expUDen q (N + j + 1)
      ≤ upNum p q (N + j) * expUDen q (N + j) := by
    show expNum p q (N + j) * ((N + j + 1) * q * expUDen q (N + j))
        ≤ (expNum p q (N + j) * ((N + j + 1) * q) + 2 * p ^ (N + j + 1))
          * expUDen q (N + j)
    refine Nat.le.intro (k := 2 * p ^ (N + j + 1) * expUDen q (N + j)) ?_
    ring_nat
  have hinv := exp_pq_upper_invariant p q N hN j
  have h2 : expUDen q (N + j + 1) * (expNum p q (N + j) * expUDen q (N + 1))
      ≤ expUDen q (N + j + 1) * (upNum p q N * expUDen q (N + j)) := by
    calc expUDen q (N + j + 1) * (expNum p q (N + j) * expUDen q (N + 1))
        = (expNum p q (N + j) * expUDen q (N + j + 1)) * expUDen q (N + 1) := by
          ring_nat
      _ ≤ (upNum p q (N + j) * expUDen q (N + j)) * expUDen q (N + 1) :=
          Nat.mul_le_mul hlocal (Nat.le_refl _)
      _ = (upNum p q (N + j) * expUDen q (N + 1)) * expUDen q (N + j) := by ring_nat
      _ ≤ (upNum p q N * expUDen q (N + j + 1)) * expUDen q (N + j) :=
          Nat.mul_le_mul hinv (Nat.le_refl _)
      _ = expUDen q (N + j + 1) * (upNum p q N * expUDen q (N + j)) := by ring_nat
  exact Nat.le_of_mul_le_mul_left h2 (expUDen_pos q hq (N + j + 1))

/-- The upper bracket as a cut reading: for every layer `n ≥ N`, the layer cut reads
    `true` at the bracket point `(upNum p q N, expUDen q (N+1))` — the whole fold sits
    below `U_N/d_{N+1}`. -/
theorem exp_pq_cut_upper (p q N : Nat) (hq : 1 ≤ q) (hN : 2 * p ≤ (N + 2) * q)
    (n : Nat) (hn : N ≤ n) :
    expPQCut p q hq n (upNum p q N) (expUDen q (N + 1)) = true := by
  rw [expPQCut_eq]
  apply decide_eq_true
  obtain ⟨j, hj⟩ := Nat.le.dest hn
  rw [← hj]
  exact Nat.le_trans (exp_pq_le_upper p q N hq hN j)
    (Nat.le_of_eq (Nat.mul_comm _ _))

/-! ## §4 — `e² = exp(2)` localized: `7 < e² ≤ 904/120` -/

/-- The concrete anchors: `S₄ = 168/24 = 7`, `S₅ = 872/120`, `U₄ = 904` over
    `d₅ = 120` (so the bracket is `(7, 904/120 = 7.5\overline{3}]`; `e² ≈ 7.389`). -/
theorem exp_two_anchors :
    expNum 2 1 4 = 168 ∧ expUDen 1 4 = 24 ∧ expNum 2 1 5 = 872 ∧ expUDen 1 5 = 120
    ∧ upNum 2 1 4 = 904 := ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **`e² > 7`**: at layer 5 the cut at `7/1` reads `false` (`872 > 840`), and by
    nesting (`cut_false_fwd`) it stays `false` at every later layer. -/
theorem exp_two_above_7 (n : Nat) (hn : 5 ≤ n) :
    expPQCut 2 1 (Nat.le_refl 1) n 7 1 = false := by
  have h5 : expPQCut 2 1 (Nat.le_refl 1) 5 7 1 = false := by
    rw [expPQCut_eq]; decide
  exact (expPQAb 2 1 (Nat.le_refl 1)).cut_false_fwd 7 1 5 h5 n hn

/-- **`e² ≤ 904/120`**: the `N = 4` upper bracket (threshold `2·2 = 4 ≤ 6 = (4+2)·1`),
    at every layer `n ≥ 4`. -/
theorem exp_two_below_904_120 (n : Nat) (hn : 4 ≤ n) :
    expPQCut 2 1 (Nat.le_refl 1) n 904 120 = true := by
  have h := exp_pq_cut_upper 2 1 4 (Nat.le_refl 1) (by decide) n hn
  rwa [show upNum 2 1 4 = 904 from by decide,
       show expUDen 1 5 = 120 from by decide] at h

/-- ★★★★ **`e²` localized in `(7, 904/120]`** — the fold's bracket, both sides
    `∅`-axiom: lower from the layer-5 convergent (nesting-stable), upper from the
    doubled-tail invariant at `N = 4`. -/
theorem exp_two_localized (n : Nat) (hn : 5 ≤ n) :
    expPQCut 2 1 (Nat.le_refl 1) n 7 1 = false
    ∧ expPQCut 2 1 (Nat.le_refl 1) n 904 120 = true :=
  ⟨exp_two_above_7 n hn, exp_two_below_904_120 n (Nat.le_trans (by decide) hn)⟩

/-! ## §5 — conditional completion: the measure-modulus schema instantiated

`exp_pq_no_htel` killed the rate route; `AbCutSeq.toCauchySep` isolates what is
genuinely missing: a **separation certificate**.  The bracket (§3) reduces it to one
arithmetic hypothesis per resolution — *no fraction of denominator `k` lies in the
`I k`-th bracket `[S_{I k}, U_{I k}/d_{I k + 1}]`* — and then `exp(p/q)` completes
with the constructed modulus `N(m,k) = I k`.  Classically the hypothesis holds with
`I k ≈ 2p/q + O(log k)` (the bracket width halves per layer; Padé/Hermite supplies the
effective irrationality) — that arithmetic is the recorded open content
(`modulus_degree_ladder.md` rung 2). -/

/-- ★★★★ **The bracket reduces separation to one hypothesis.**  If every fraction
    of denominator `k` at-or-above the `I k`-th convergent is strictly above the
    `I k`-th upper bracket (`hmeas`), then any `false` reading anywhere already shows
    at layer `I k`: below `I k` by nesting; above `I k` because the convergent sits
    inside the bracket, squeezing a strict cycle (`d·m < a·k ≤ U-bracket < d·m`). -/
theorem exp_pq_sep (p q : Nat) (hq : 1 ≤ q) (I : Nat → Nat)
    (hI : ∀ k, 2 * p ≤ (I k + 2) * q)
    (hmeas : ∀ m k, 1 ≤ k →
      expNum p q (I k) * k ≤ expUDen q (I k) * m →
      upNum p q (I k) * k < expUDen q (I k + 1) * m) :
    ∀ m k, 1 ≤ k → ∀ i,
      expPQCut p q hq i m k = false → expPQCut p q hq (I k) m k = false := by
  intro m k hk i hfalse
  cases hC : expPQCut p q hq (I k) m k with
  | false => rfl
  | true =>
    have hCle : expNum p q (I k) * k ≤ expUDen q (I k) * m := by
      have h := hC
      rw [expPQCut_eq] at h
      exact of_decide_eq_true h
    have hup := hmeas m k hk hCle
    have hilt : expUDen q i * m < expNum p q i * k := by
      have h := hfalse
      rw [expPQCut_eq] at h
      exact Nat.lt_of_not_le (of_decide_eq_false h)
    rcases Nat.le_total i (I k) with hcase | hcase
    · have h : expPQCut p q hq (I k) m k = false :=
        (expPQAb p q hq).cut_false_fwd m k i hfalse (I k) hcase
      rw [hC] at h
      exact Bool.noConfusion h
    · obtain ⟨j, hj⟩ := Nat.le.dest hcase
      have hbr : expNum p q (I k + j) * expUDen q (I k + 1)
          ≤ upNum p q (I k) * expUDen q (I k + j) :=
        exp_pq_le_upper p q (I k) hq (hI k) j
      rw [hj] at hbr
      have c1 : expUDen q i * m * expUDen q (I k + 1)
          < expNum p q i * k * expUDen q (I k + 1) :=
        nat_mul_lt_mul_right (expUDen_pos q hq (I k + 1)) hilt
      have c2 : expNum p q i * k * expUDen q (I k + 1)
          ≤ upNum p q (I k) * k * expUDen q i := by
        calc expNum p q i * k * expUDen q (I k + 1)
            = (expNum p q i * expUDen q (I k + 1)) * k := by ring_nat
          _ ≤ (upNum p q (I k) * expUDen q i) * k := Nat.mul_le_mul hbr (Nat.le_refl k)
          _ = upNum p q (I k) * k * expUDen q i := by ring_nat
      have c3 : upNum p q (I k) * k * expUDen q i
          < expUDen q (I k + 1) * m * expUDen q i :=
        nat_mul_lt_mul_right (expUDen_pos q hq i) hup
      have hcycle : expUDen q i * m * expUDen q (I k + 1)
          < expUDen q i * m * expUDen q (I k + 1) := by
        calc expUDen q i * m * expUDen q (I k + 1)
            < expNum p q i * k * expUDen q (I k + 1) := c1
          _ ≤ upNum p q (I k) * k * expUDen q i := c2
          _ < expUDen q (I k + 1) * m * expUDen q i := c3
          _ = expUDen q i * m * expUDen q (I k + 1) := by ring_nat
      exact absurd hcycle (Nat.lt_irrefl _)

/-- ★★★★★ **`exp(p/q)` completes conditionally, with a constructed modulus** — the
    measure-modulus schema (`AbCutSeq.toCauchySep`) instantiated: given a schedule
    `I` past the ratio threshold and the one bracket-separation hypothesis `hmeas`,
    `exp(p/q)` is a genuine `CauchyCutSeq` with modulus `N(m,k) = I k`.  The entire
    effective-irrationality cost of `exp` at a general rational is isolated in
    `hmeas`; everything else — fold, bracket, schema — is constructed, ∅-axiom.
    (The π-posture upgraded: not "modulus as hypothesis" but "modulus constructed
    from one arithmetic hypothesis".) -/
def expPQCauchySep (p q : Nat) (hq : 1 ≤ q) (I : Nat → Nat)
    (hI : ∀ k, 2 * p ≤ (I k + 2) * q)
    (hmeas : ∀ m k, 1 ≤ k →
      expNum p q (I k) * k ≤ expUDen q (I k) * m →
      upNum p q (I k) * k < expUDen q (I k + 1) * m) :
    CauchyCutSeq :=
  (expPQAb p q hq).toCauchySep I (exp_pq_sep p q hq I hI hmeas)

/-- The conditional completion's limit is a real (`ValidCut`) — generic. -/
theorem expPQCauchySep_limit_valid (p q : Nat) (hq : 1 ≤ q) (I : Nat → Nat)
    (hI : ∀ k, 2 * p ≤ (I k + 2) * q)
    (hmeas : ∀ m k, 1 ≤ k →
      expNum p q (I k) * k ≤ expUDen q (I k) * m →
      upNum p q (I k) * k < expUDen q (I k + 1) * m) :
    ValidCut (expPQCauchySep p q hq I hI hmeas).limit :=
  (expPQAb p q hq).toCauchy_limit_valid _ _

end E213.Lib.Math.NumberSystems.Real213.ExpLog.ExpRationalCut
