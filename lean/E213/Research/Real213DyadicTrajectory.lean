import E213.Research.Real213DyadicBracket
import E213.Research.Real213ConsistentOracle

/-!
# Research.Real213DyadicTrajectory: concrete bisection trajectories

Sister-branch `WhyBasel.lean` style decide-based concrete examples:
explicit trajectory unfoldings on simple oracles for the unit
bracket [0, 1].

## Two canonical oracles

- `alwaysTrue` : steers always-left, bracket → left endpoint.
- `alwaysFalse` : steers always-right, bracket → right endpoint.

Closed forms (by induction):
- alwaysTrue from (0, 1, 0): bracket (0, 1, n) at depth n. [0, 1/2^n].
- alwaysFalse from (0, 1, 0): bracket (2^n-1, 2^n, n). [1-1/2^n, 1].
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **Always-true oracle**: regardless of cut, returns true.
    Steers bisection always to leftHalf. -/
def alwaysTrue : DyadicOracle := fun _ => true

/-- **Always-false oracle**: regardless of cut, returns false.
    Steers bisection always to rightHalf. -/
def alwaysFalse : DyadicOracle := fun _ => false

/-- **Initial unit bracket** [0, 1] at exponent 0. -/
def unitBracket : DyadicBracket where
  numA := 0
  numB := 1
  expE := 0
  hLe := by decide

/-- Concrete: depth 0 unitBracket has numA = 0, numB = 1, expE = 0. -/
example : unitBracket.numA = 0 ∧ unitBracket.numB = 1
        ∧ unitBracket.expE = 0 := by decide

/-- Concrete: depth 1 alwaysFalse from unit gives bracket (1, 2, 1). -/
example : (DyadicBracket.bisectN alwaysFalse 1 unitBracket).numA = 1
        ∧ (DyadicBracket.bisectN alwaysFalse 1 unitBracket).numB = 2
        ∧ (DyadicBracket.bisectN alwaysFalse 1 unitBracket).expE = 1 := by
  decide

/-- Concrete: depth 2 alwaysFalse from unit gives bracket (3, 4, 2). -/
example : (DyadicBracket.bisectN alwaysFalse 2 unitBracket).numA = 3
        ∧ (DyadicBracket.bisectN alwaysFalse 2 unitBracket).numB = 4
        ∧ (DyadicBracket.bisectN alwaysFalse 2 unitBracket).expE = 2 := by
  decide

/-- Concrete: depth 3 alwaysFalse from unit gives bracket (7, 8, 3). -/
example : (DyadicBracket.bisectN alwaysFalse 3 unitBracket).numA = 7
        ∧ (DyadicBracket.bisectN alwaysFalse 3 unitBracket).numB = 8
        ∧ (DyadicBracket.bisectN alwaysFalse 3 unitBracket).expE = 3 := by
  decide

/-- **alwaysFalse_step**: bisectStep with alwaysFalse oracle reduces
    to rightHalf (oracle returns false, if-else picks else branch). -/
theorem alwaysFalse_step (db : DyadicBracket) :
    db.bisectStep alwaysFalse = db.rightHalf := rfl

/-- **alwaysTrue_step**: bisectStep with alwaysTrue oracle reduces
    to leftHalf. -/
theorem alwaysTrue_step (db : DyadicBracket) :
    db.bisectStep alwaysTrue = db.leftHalf := rfl

/-- **alwaysFalse trajectory: numB scales as 2^n × initial.numB**.
    Each rightHalf doubles numB; bisectN composes n of them. -/
theorem alwaysFalse_numB (n : Nat) (db : DyadicBracket) :
    (DyadicBracket.bisectN alwaysFalse n db).numB = 2^n * db.numB := by
  induction n generalizing db with
  | zero =>
    show db.numB = 2^0 * db.numB
    rw [show (2 : Nat)^0 = 1 from rfl, Nat.one_mul]
  | succ k ih =>
    show (DyadicBracket.bisectN alwaysFalse k (db.bisectStep alwaysFalse)).numB
       = 2^(k+1) * db.numB
    rw [alwaysFalse_step, ih]
    show 2^k * (2 * db.numB) = 2^(k+1) * db.numB
    rw [Nat.pow_succ, Nat.mul_assoc]

/-- **alwaysTrue trajectory: numA scales as 2^n × initial.numA**. -/
theorem alwaysTrue_numA (n : Nat) (db : DyadicBracket) :
    (DyadicBracket.bisectN alwaysTrue n db).numA = 2^n * db.numA := by
  induction n generalizing db with
  | zero =>
    show db.numA = 2^0 * db.numA
    rw [show (2 : Nat)^0 = 1 from rfl, Nat.one_mul]
  | succ k ih =>
    show (DyadicBracket.bisectN alwaysTrue k (db.bisectStep alwaysTrue)).numA
       = 2^(k+1) * db.numA
    rw [alwaysTrue_step, ih]
    show 2^k * (2 * db.numA) = 2^(k+1) * db.numA
    rw [Nat.pow_succ, Nat.mul_assoc]

/-! ### Unit bracket trajectory corollaries

Specialize the closed forms to unitBracket = (0, 1, 0):
- alwaysFalse: numA stays 0? NO, rightHalf gives numA + numB.
  Actually: numA evolves via numA + numB pattern.
- numB straight: 2^n.
- expE straight: n. -/

/-- **alwaysFalse from unit: numB = 2^n**. -/
theorem alwaysFalse_unit_numB (n : Nat) :
    (DyadicBracket.bisectN alwaysFalse n unitBracket).numB = 2^n := by
  rw [alwaysFalse_numB n unitBracket]
  show 2^n * 1 = 2^n
  rw [Nat.mul_one]

/-- **alwaysTrue from unit: numA = 0** (always-left preserves 0). -/
theorem alwaysTrue_unit_numA (n : Nat) :
    (DyadicBracket.bisectN alwaysTrue n unitBracket).numA = 0 := by
  rw [alwaysTrue_numA n unitBracket]
  show 2^n * 0 = 0
  rw [Nat.mul_zero]

/-- **alwaysFalse from unit: expE = n** (depth advances cleanly). -/
theorem alwaysFalse_unit_expE (n : Nat) :
    (DyadicBracket.bisectN alwaysFalse n unitBracket).expE = n := by
  rw [DyadicBracket.bisectN_expE alwaysFalse n unitBracket]
  show 0 + n = n
  exact Nat.zero_add n

/-- **alwaysTrue from unit: expE = n** (same as alwaysFalse). -/
theorem alwaysTrue_unit_expE (n : Nat) :
    (DyadicBracket.bisectN alwaysTrue n unitBracket).expE = n := by
  rw [DyadicBracket.bisectN_expE alwaysTrue n unitBracket]
  show 0 + n = n
  exact Nat.zero_add n

/-- **alwaysTrue 1-step on numA=0 bracket: numB unchanged**. -/
theorem alwaysTrue_zero_step_numB (db : DyadicBracket) (h : db.numA = 0) :
    (db.bisectStep alwaysTrue).numB = db.numB := by
  rw [alwaysTrue_step]
  show db.numA + db.numB = db.numB
  rw [h, Nat.zero_add]

/-- **alwaysTrue n-step on numA=0 bracket: numB invariant**. -/
theorem alwaysTrue_zero_numB_invariant (n : Nat) (db : DyadicBracket)
    (h : db.numA = 0) :
    (DyadicBracket.bisectN alwaysTrue n db).numB = db.numB := by
  induction n generalizing db with
  | zero => rfl
  | succ k ih =>
    show (DyadicBracket.bisectN alwaysTrue k (db.bisectStep alwaysTrue)).numB
       = db.numB
    have hAStep : (db.bisectStep alwaysTrue).numA = 0 := by
      rw [alwaysTrue_step]
      show 2 * db.numA = 0
      rw [h, Nat.mul_zero]
    rw [ih (db.bisectStep alwaysTrue) hAStep,
        alwaysTrue_zero_step_numB db h]

/-- **alwaysTrue from unit: numB invariant at 1**.
    Combined with numA = 0, expE = n, this gives the full closed
    form: bracket stays (0, 1, n) at every depth. -/
theorem alwaysTrue_unit_numB (n : Nat) :
    (DyadicBracket.bisectN alwaysTrue n unitBracket).numB = 1 :=
  alwaysTrue_zero_numB_invariant n unitBracket rfl

/-- **alwaysFalse from unit: numA = 2^n - 1**.
    Derived from numB = 2^n and lenNum invariant = 1. -/
theorem alwaysFalse_unit_numA (n : Nat) :
    (DyadicBracket.bisectN alwaysFalse n unitBracket).numA = 2^n - 1 := by
  have hB := alwaysFalse_unit_numB n
  have hLen := DyadicBracket.bisectN_lenNum alwaysFalse n unitBracket
  have h_unit_len : unitBracket.lenNum = 1 := rfl
  rw [h_unit_len] at hLen
  have hLe := (DyadicBracket.bisectN alwaysFalse n unitBracket).hLe
  have h2n : (2:Nat)^n ≥ 1 := Nat.pos_pow_of_pos n (by decide : 0 < 2)
  show (DyadicBracket.bisectN alwaysFalse n unitBracket).numA = 2^n - 1
  -- hLen: numB - numA = 1. hB: numB = 2^n.  hLe: numA ≤ numB.  h2n: 2^n ≥ 1.
  show (DyadicBracket.bisectN alwaysFalse n unitBracket).numA = 2^n - 1
  have hLen_unfold :
    (DyadicBracket.bisectN alwaysFalse n unitBracket).numB
    - (DyadicBracket.bisectN alwaysFalse n unitBracket).numA = 1 := hLen
  omega

/-- **alwaysTrue from unit: midCut = dyadicCut 1 (n+1)**.
    The midpoint at depth n is 1/2^(n+1), approaching 0 as n grows. -/
theorem alwaysTrue_unit_midCut (n : Nat) :
    (DyadicBracket.bisectN alwaysTrue n unitBracket).midCut
    = dyadicCut 1 (n+1) := by
  show dyadicCut ((DyadicBracket.bisectN alwaysTrue n unitBracket).numA
                 + (DyadicBracket.bisectN alwaysTrue n unitBracket).numB)
        ((DyadicBracket.bisectN alwaysTrue n unitBracket).expE + 1)
       = dyadicCut 1 (n+1)
  rw [alwaysTrue_unit_numA n, alwaysTrue_unit_numB n,
      alwaysTrue_unit_expE n]

/-- **alwaysFalse from unit: midCut = dyadicCut (2^(n+1) - 1) (n+1)**.
    The midpoint at depth n is (2^(n+1) - 1)/2^(n+1) = 1 - 1/2^(n+1),
    approaching 1 as n grows. -/
theorem alwaysFalse_unit_midCut (n : Nat) :
    (DyadicBracket.bisectN alwaysFalse n unitBracket).midCut
    = dyadicCut (2^(n+1) - 1) (n+1) := by
  show dyadicCut ((DyadicBracket.bisectN alwaysFalse n unitBracket).numA
                 + (DyadicBracket.bisectN alwaysFalse n unitBracket).numB)
        ((DyadicBracket.bisectN alwaysFalse n unitBracket).expE + 1)
       = dyadicCut (2^(n+1) - 1) (n+1)
  rw [alwaysFalse_unit_numA n, alwaysFalse_unit_numB n,
      alwaysFalse_unit_expE n]
  have h2n : (2:Nat)^n ≥ 1 := Nat.pos_pow_of_pos n (by decide : 0 < 2)
  have h_eq : (2^n - 1) + 2^n = 2^(n+1) - 1 := by
    rw [Nat.pow_succ]
    omega
  rw [h_eq]

/-- **Universal trajectory invariants on unit bracket**: regardless
    of oracle, after n bisection steps starting from unit bracket
    [0, 1], we have lenNum = 1 (numerator difference invariant) and
    expE = n (depth advances).  Real interval length: 1/2^n. -/
theorem unit_universal_invariants (oracle : DyadicOracle) (n : Nat) :
    (DyadicBracket.bisectN oracle n unitBracket).lenNum = 1
    ∧ (DyadicBracket.bisectN oracle n unitBracket).expE = n := by
  refine ⟨?_, ?_⟩
  · rw [DyadicBracket.bisectN_lenNum oracle n unitBracket]
    rfl
  · rw [DyadicBracket.bisectN_expE oracle n unitBracket]
    show 0 + n = n
    exact Nat.zero_add n

/-- **Power-of-two grows linearly-or-faster**: 2^(x+1) ≥ x + 1 for
    all x.  Used to bound consistency thresholds. -/
private theorem two_pow_ge_succ (x : Nat) : x + 1 ≤ 2^(x+1) := by
  induction x with
  | zero => decide
  | succ y ih =>
    show y + 1 + 1 ≤ 2^(y+1+1)
    rw [Nat.pow_succ]
    omega

/-- **alwaysTrue trajectory on unit bracket is a ConsistentOracle**.
    Threshold: thresholdN m k := k.  At depth n ≥ k, the midCut value
    at (m, k) is fully determined (cases on m: m=0 cut is constant
    immediately; m≥1 cut becomes constant true once 2^(n+1) ≥ k). -/
def ConsistentOracle.alwaysTrueUnit : ConsistentOracle unitBracket where
  oracle := alwaysTrue
  thresholdN := fun _ k => k
  consistency := by
    intro m k n1 n2 hn1 hn2
    have hk1 : n1 ≥ k := hn1
    have hk2 : n2 ≥ k := hn2
    rw [alwaysTrue_unit_midCut n1, alwaysTrue_unit_midCut n2]
    show decide (1 * k ≤ 2^(n1+1) * m) = decide (1 * k ≤ 2^(n2+1) * m)
    cases m with
    | zero =>
      show decide (1*k ≤ 2^(n1+1) * 0) = decide (1*k ≤ 2^(n2+1) * 0)
      rw [Nat.mul_zero, Nat.mul_zero]
    | succ j =>
      have h_pow1 : 2^(n1+1) ≥ k + 1 := by
        have h := two_pow_ge_succ n1; omega
      have h_pow2 : 2^(n2+1) ≥ k + 1 := by
        have h := two_pow_ge_succ n2; omega
      have h_le1 : 1*k ≤ 2^(n1+1) * (j+1) := by
        have : 2^(n1+1) * (j+1) ≥ 2^(n1+1) :=
          Nat.le_mul_of_pos_right _ (Nat.succ_pos j)
        omega
      have h_le2 : 1*k ≤ 2^(n2+1) * (j+1) := by
        have : 2^(n2+1) * (j+1) ≥ 2^(n2+1) :=
          Nat.le_mul_of_pos_right _ (Nat.succ_pos j)
        omega
      rw [decide_eq_true h_le1, decide_eq_true h_le2]

/-- Helper for alwaysFalseUnit: in m < k case, cut is false past
    threshold.  The key inequality (2^(n+1) - 1) * k > 2^(n+1) * m
    derived from 2^(n+1) ≥ k+1 and k - m ≥ 1. -/
private theorem alwaysFalse_unit_cut_false_when_m_lt_k
    (n m k : Nat) (hn : 2^(n+1) ≥ k + 1) (hmk : m < k) :
    ¬ ((2^(n+1) - 1) * k ≤ 2^(n+1) * m) := by
  intro hle
  -- Convert (2^(n+1) - 1) * k = 2^(n+1) * k - k via comm + Nat.mul_sub_left_distrib.
  have e : (2^(n+1) - 1) * k = 2^(n+1) * k - k := by
    rw [Nat.mul_comm, Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_comm k]
  rw [e] at hle
  -- hle : 2^(n+1) * k - k ≤ 2^(n+1) * m
  have hAk : 2^(n+1) * k ≥ k :=
    Nat.le_mul_of_pos_left k (by
      have := Nat.pos_pow_of_pos (n+1) (by decide : 0 < 2); omega)
  have h_le : 2^(n+1) * k ≤ 2^(n+1) * m + k := by omega
  have h_split : 2^(n+1) * k = 2^(n+1) * m + 2^(n+1) * (k - m) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [h_split] at h_le
  -- h_le: 2^(n+1) * m + 2^(n+1) * (k - m) ≤ 2^(n+1) * m + k
  have h_le2 : 2^(n+1) * (k - m) ≤ k := by omega
  have h_lower : 2^(n+1) ≤ 2^(n+1) * (k - m) :=
    Nat.le_mul_of_pos_right (2^(n+1)) (by omega : 0 < k - m)
  omega

/-- **alwaysFalse trajectory on unit bracket is a ConsistentOracle**.
    Threshold: thresholdN m k := k.  Cut splits on (m vs k):
    - k ≤ m: cut always true (midpoint ≤ 1 ≤ m/k).
    - m < k: cut becomes false once 2^(n+1) > k. -/
def ConsistentOracle.alwaysFalseUnit : ConsistentOracle unitBracket where
  oracle := alwaysFalse
  thresholdN := fun _ k => k
  consistency := by
    intro m k n1 n2 hn1 hn2
    have hk1 : n1 ≥ k := hn1
    have hk2 : n2 ≥ k := hn2
    rw [alwaysFalse_unit_midCut n1, alwaysFalse_unit_midCut n2]
    show decide ((2^(n1+1) - 1) * k ≤ 2^(n1+1) * m)
       = decide ((2^(n2+1) - 1) * k ≤ 2^(n2+1) * m)
    have h_pow1 : 2^(n1+1) ≥ k + 1 := by
      have h := two_pow_ge_succ n1; omega
    have h_pow2 : 2^(n2+1) ≥ k + 1 := by
      have h := two_pow_ge_succ n2; omega
    rcases Nat.lt_or_ge m k with hmk | hkm
    · -- m < k: both cuts false.
      rw [decide_eq_false (alwaysFalse_unit_cut_false_when_m_lt_k n1 m k h_pow1 hmk),
          decide_eq_false (alwaysFalse_unit_cut_false_when_m_lt_k n2 m k h_pow2 hmk)]
    · -- k ≤ m: both cuts true.
      have h1_true : (2^(n1+1) - 1) * k ≤ 2^(n1+1) * m := by
        have h_le_2pow : (2^(n1+1) - 1) * k ≤ 2^(n1+1) * k := by
          apply Nat.mul_le_mul_right; omega
        exact Nat.le_trans h_le_2pow (Nat.mul_le_mul_left _ hkm)
      have h2_true : (2^(n2+1) - 1) * k ≤ 2^(n2+1) * m := by
        have h_le_2pow : (2^(n2+1) - 1) * k ≤ 2^(n2+1) * k := by
          apply Nat.mul_le_mul_right; omega
        exact Nat.le_trans h_le_2pow (Nat.mul_le_mul_left _ hkm)
      rw [decide_eq_true h1_true, decide_eq_true h2_true]

/-! ### Limit values of canonical ConsistentOracles -/

/-- Limit of alwaysTrueUnit's CauchyCutSeq at (m, k):
    decide(k ≤ 2^(k+1) * m).  Represents the "0+ cut". -/
theorem alwaysTrueUnit_limit_value (m k : Nat) :
    (ConsistentOracle.alwaysTrueUnit).toCauchyCutSeq.limit m k
    = decide (k ≤ 2^(k+1) * m) := by
  show (DyadicBracket.bisectN alwaysTrue k unitBracket).midCut m k
       = decide (k ≤ 2^(k+1) * m)
  rw [alwaysTrue_unit_midCut k]
  show decide (1 * k ≤ 2^(k+1) * m) = decide (k ≤ 2^(k+1) * m)
  rw [Nat.one_mul]

/-- Limit of alwaysFalseUnit's CauchyCutSeq at (m, k):
    decide((2^(k+1) - 1) * k ≤ 2^(k+1) * m).  Represents the "1- cut". -/
theorem alwaysFalseUnit_limit_value (m k : Nat) :
    (ConsistentOracle.alwaysFalseUnit).toCauchyCutSeq.limit m k
    = decide ((2^(k+1) - 1) * k ≤ 2^(k+1) * m) := by
  show (DyadicBracket.bisectN alwaysFalse k unitBracket).midCut m k
       = decide ((2^(k+1) - 1) * k ≤ 2^(k+1) * m)
  rw [alwaysFalse_unit_midCut k]
  show dyadicCut (2^(k+1) - 1) (k+1) m k
     = decide ((2^(k+1) - 1) * k ≤ 2^(k+1) * m)
  rfl

/-! ### Concrete decide tests for limit values -/

/-- alwaysTrueUnit limit at (1, 1): true (since 1 ≤ 2^2 * 1 = 4). -/
example : (ConsistentOracle.alwaysTrueUnit).toCauchyCutSeq.limit 1 1
        = true := by decide

/-- alwaysTrueUnit limit at (0, 1): false (since 1 > 2^2 * 0 = 0). -/
example : (ConsistentOracle.alwaysTrueUnit).toCauchyCutSeq.limit 0 1
        = false := by decide

/-- alwaysFalseUnit limit at (1, 1): true (since (2^2 - 1) * 1 = 3 ≤ 4). -/
example : (ConsistentOracle.alwaysFalseUnit).toCauchyCutSeq.limit 1 1
        = true := by decide

/-- alwaysFalseUnit limit at (1, 2): false (since (2^3-1)*2 = 14 > 8). -/
example : (ConsistentOracle.alwaysFalseUnit).toCauchyCutSeq.limit 1 2
        = false := by decide

/-- alwaysFalseUnit limit at (3, 2): true (k=2 ≤ m=3). -/
example : (ConsistentOracle.alwaysFalseUnit).toCauchyCutSeq.limit 3 2
        = true := by decide

/-- alwaysFalseUnit limit at (2, 3): false (k=3 > m=2). -/
example : (ConsistentOracle.alwaysFalseUnit).toCauchyCutSeq.limit 2 3
        = false := by decide

/-- alwaysFalseUnit limit at (5, 5): true (k=5 ≤ m=5). -/
example : (ConsistentOracle.alwaysFalseUnit).toCauchyCutSeq.limit 5 5
        = true := by decide

/-- alwaysFalseUnit limit at (5, 6): false (k=6 > m=5). -/
example : (ConsistentOracle.alwaysFalseUnit).toCauchyCutSeq.limit 5 6
        = false := by decide

/-- alwaysFalseUnit limit at (10, 5): true (k=5 ≤ m=10). -/
example : (ConsistentOracle.alwaysFalseUnit).toCauchyCutSeq.limit 10 5
        = true := by decide

/-- **0+ ≤ 1- in the cut order**: the alwaysTrue limit (representing
    "infinitesimally above 0") is ≤ the alwaysFalse limit (representing
    "infinitesimally below 1") cut-wise.  Mathematical sanity. -/
theorem alwaysTrue_le_alwaysFalse_at_limit :
    cutLe (ConsistentOracle.alwaysTrueUnit).toCauchyCutSeq.limit
          (ConsistentOracle.alwaysFalseUnit).toCauchyCutSeq.limit := by
  intro m k h
  rw [alwaysFalseUnit_limit_value] at h
  rw [alwaysTrueUnit_limit_value]
  apply decide_eq_true
  have h1 : (2^(k+1) - 1) * k ≤ 2^(k+1) * m := of_decide_eq_true h
  have h_pow : 2^(k+1) ≥ 2 := by
    have := two_pow_ge_succ k; omega
  have e : (2^(k+1) - 1) * k = 2^(k+1) * k - k := by
    rw [Nat.mul_comm, Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_comm k]
  rw [e] at h1
  have h_mul_ge : 2^(k+1) * k ≥ 2 * k := Nat.mul_le_mul_right k h_pow
  omega

/-- **alwaysTrueUnit limit is NOT cutEq with constCut 0 1**.

    This formalizes the constructive distinction: 0+ (infinitesimally
    positive) is a different cut function from 0 exactly.  Witness
    at (m=0, k=1): 0+ gives false ("0+ > 0/1"), while constCut 0 1
    gives true ("0 ≤ 0").

    Constructive insight: completed-infinity equality (Cauchy limit
    = exact value) does NOT hold in 213.  The trajectory IS the
    constructive content; "limit point exists" is a ZFC fiction. -/
theorem alwaysTrueUnit_limit_distinct_from_zero :
    (ConsistentOracle.alwaysTrueUnit).toCauchyCutSeq.limit 0 1 = false
    ∧ (constCut 0 1) 0 1 = true := by
  refine ⟨?_, ?_⟩
  · rw [alwaysTrueUnit_limit_value 0 1]
    decide
  · decide

/-- **M1: Infinitesimal gap structure**.

    Cut `a` is "below" cut `b` at infinitesimal precision iff at
    every query (0, k) with k ≥ 1, a says false (x > 0) but b says
    true (x ≤ 0).  This captures the cut-distinctness of "x > 0
    strictly" from "x ≤ 0".

    The gap is "infinitesimal" because it disappears at higher m
    (positive numerator queries) — only visible at the boundary
    m = 0 with positive precision k. -/
def InfinitesimalGap (a b : Nat → Nat → Bool) : Prop :=
  ∀ k, k ≥ 1 → a 0 k = false ∧ b 0 k = true

/-- **0+ has infinitesimal gap below 0-exact**: alwaysTrueUnit's
    limit (the "0+" cut) sits below constCut 0 1 (the "0-exact"
    cut) at every infinitesimal-precision query (0, k) for k ≥ 1.
    Formal expression of: "0+ is positive infinitesimal." -/
theorem zero_plus_gap_below_zero_exact :
    InfinitesimalGap (ConsistentOracle.alwaysTrueUnit).toCauchyCutSeq.limit
                     (constCut 0 1) := by
  intro k hk
  refine ⟨?_, ?_⟩
  · rw [alwaysTrueUnit_limit_value 0 k, Nat.mul_zero]
    show decide (k ≤ 0) = false
    exact decide_eq_false (by omega)
  · show decide (0 * k ≤ 1 * 0) = true
    rw [Nat.zero_mul, Nat.mul_zero]
    rfl

/-! ### M4: Sign oracle trajectory — non-canonical mixed bisection -/

/-- **negSignOracle**: returns true iff midpoint > m/k (i.e., midCut
    at (m, k) is FALSE).  Used for binary search toward target m/k:
    when midpoint above target, go left; below target, go right. -/
def negSignOracle (m k : Nat) : DyadicOracle := fun mc => !(mc m k)

/-- Concrete: depth 0 of negSignOracle is just the unit bracket. -/
example : (DyadicBracket.bisectN (negSignOracle 1 2) 0 unitBracket).numA = 0
        ∧ (DyadicBracket.bisectN (negSignOracle 1 2) 0 unitBracket).numB = 1
        := by decide

/-- Concrete: depth 1 toward target 1/2.  At depth 0 midpoint = 1/2,
    which equals target → oracle says false (not strictly >) → go right.
    Bracket: rightHalf of (0, 1, 0) = (1, 2, 1). -/
example : (DyadicBracket.bisectN (negSignOracle 1 2) 1 unitBracket).numA = 1
        ∧ (DyadicBracket.bisectN (negSignOracle 1 2) 1 unitBracket).numB = 2
        := by decide

/-- Concrete: depth 2 toward target 1/2.  At depth 1 midpoint = 3/4,
    above 1/2 → oracle says true → go left.
    Bracket: leftHalf of (1, 2, 1) = (2, 3, 2). -/
example : (DyadicBracket.bisectN (negSignOracle 1 2) 2 unitBracket).numA = 2
        ∧ (DyadicBracket.bisectN (negSignOracle 1 2) 2 unitBracket).numB = 3
        := by decide

/-- Concrete: depth 3 toward target 1/2.  Bracket (4, 5, 3). -/
example : (DyadicBracket.bisectN (negSignOracle 1 2) 3 unitBracket).numA = 4
        ∧ (DyadicBracket.bisectN (negSignOracle 1 2) 3 unitBracket).numB = 5
        := by decide

/-- Concrete: depth 4 toward target 1/2.  Bracket (8, 9, 4). -/
example : (DyadicBracket.bisectN (negSignOracle 1 2) 4 unitBracket).numA = 8
        ∧ (DyadicBracket.bisectN (negSignOracle 1 2) 4 unitBracket).numB = 9
        := by decide

/-- Helper: bracket (2^k, 2^k + 1, k+1) form for the negSignOracle 1 2
    trajectory.  At every such bracket, the oracle picks leftHalf
    (since midpoint > 1/2 strictly), and leftHalf preserves the
    pattern.  Closed form by induction on iteration count n. -/
private def db_pattern (k : Nat) : DyadicBracket where
  numA := 2^k
  numB := 2^k + 1
  expE := k + 1
  hLe := by omega

/-- leftHalf of db_pattern k = db_pattern (k+1). -/
private theorem db_pattern_leftHalf (k : Nat) :
    (db_pattern k).leftHalf.numA = (db_pattern (k+1)).numA
    ∧ (db_pattern k).leftHalf.numB = (db_pattern (k+1)).numB
    ∧ (db_pattern k).leftHalf.expE = (db_pattern (k+1)).expE := by
  refine ⟨?_, ?_, ?_⟩
  · show 2 * 2^k = 2^(k+1)
    rw [Nat.pow_succ, Nat.mul_comm]
  · show 2^k + (2^k + 1) = 2^(k+1) + 1
    rw [Nat.pow_succ, Nat.mul_comm]; omega
  · rfl

/-- **Y1: negSignOracle 1 2 unit trajectory at depths 5, 6, 7 (decide)**.
    Closed form pattern: at depth n+1, numA = 2^n. -/
example : (DyadicBracket.bisectN (negSignOracle 1 2) 5 unitBracket).numA = 16
        := by decide

example : (DyadicBracket.bisectN (negSignOracle 1 2) 6 unitBracket).numA = 32
        := by decide

example : (DyadicBracket.bisectN (negSignOracle 1 2) 7 unitBracket).numA = 64
        := by decide

example : (DyadicBracket.bisectN (negSignOracle 1 2) 8 unitBracket).numA = 128
        := by decide

/-! ### N2: Other dyadic targets — 1/4 and 3/4 -/

/-- Concrete trajectory toward target 1/4 (negSignOracle 1 4):
    initial midpoint 1/2 > 1/4 → go left.  Then 1/4 hit exactly →
    go right.  Then bisect within [1/4, ...]. -/
example : (DyadicBracket.bisectN (negSignOracle 1 4) 1 unitBracket).numA = 0
        ∧ (DyadicBracket.bisectN (negSignOracle 1 4) 1 unitBracket).numB = 1
        ∧ (DyadicBracket.bisectN (negSignOracle 1 4) 1 unitBracket).expE = 1
        := by decide

example : (DyadicBracket.bisectN (negSignOracle 1 4) 2 unitBracket).numA = 1
        ∧ (DyadicBracket.bisectN (negSignOracle 1 4) 2 unitBracket).numB = 2
        ∧ (DyadicBracket.bisectN (negSignOracle 1 4) 2 unitBracket).expE = 2
        := by decide

example : (DyadicBracket.bisectN (negSignOracle 1 4) 4 unitBracket).numA = 4
        ∧ (DyadicBracket.bisectN (negSignOracle 1 4) 4 unitBracket).numB = 5
        ∧ (DyadicBracket.bisectN (negSignOracle 1 4) 4 unitBracket).expE = 4
        := by decide

/-- Concrete trajectory toward target 3/4 (negSignOracle 3 4):
    symmetric to 1/4 but on the right side. -/
example : (DyadicBracket.bisectN (negSignOracle 3 4) 1 unitBracket).numA = 1
        ∧ (DyadicBracket.bisectN (negSignOracle 3 4) 1 unitBracket).numB = 2
        ∧ (DyadicBracket.bisectN (negSignOracle 3 4) 1 unitBracket).expE = 1
        := by decide

example : (DyadicBracket.bisectN (negSignOracle 3 4) 2 unitBracket).numA = 3
        ∧ (DyadicBracket.bisectN (negSignOracle 3 4) 2 unitBracket).numB = 4
        ∧ (DyadicBracket.bisectN (negSignOracle 3 4) 2 unitBracket).expE = 2
        := by decide

example : (DyadicBracket.bisectN (negSignOracle 3 4) 4 unitBracket).numA = 12
        ∧ (DyadicBracket.bisectN (negSignOracle 3 4) 4 unitBracket).numB = 13
        ∧ (DyadicBracket.bisectN (negSignOracle 3 4) 4 unitBracket).expE = 4
        := by decide

/-! ### N3: Asymmetry — 0+ ≠ 0 but 1- = 1 -/

/-- **alwaysFalseUnit limit IS cut-equivalent to constCut 1 1**.

    At every (m, k) query, the alwaysFalseUnit "1- limit" equals
    constCut 1 1 (the "1-exact" cut).  ASYMMETRY: 0+ ≠ 0-exact (M1
    gap), but 1- = 1-exact (no gap).

    Why?  At m = 0 boundary: 0+ says false (positive infinitesimal
    > 0/k for k ≥ 1) while 0 says true.  But there's no "k = 0
    boundary" — k = 0 is degenerate.  So the cut model has a
    one-sided infinitesimal asymmetry. -/
theorem alwaysFalseUnit_limit_eq_one_one (m k : Nat) :
    (ConsistentOracle.alwaysFalseUnit).toCauchyCutSeq.limit m k
    = constCut 1 1 m k := by
  rw [alwaysFalseUnit_limit_value]
  show decide ((2^(k+1) - 1) * k ≤ 2^(k+1) * m) = decide (1 * k ≤ 1 * m)
  rw [Nat.one_mul, Nat.one_mul]
  have h_pow : 2^(k+1) ≥ k + 1 := by have := two_pow_ge_succ k; omega
  rcases Nat.lt_or_ge m k with hmk | hkm
  · -- m < k: both false.
    have h_lhs_false : ¬ ((2^(k+1) - 1) * k ≤ 2^(k+1) * m) :=
      alwaysFalse_unit_cut_false_when_m_lt_k k m k h_pow hmk
    have h_rhs_false : ¬ (k ≤ m) := by omega
    rw [decide_eq_false h_lhs_false, decide_eq_false h_rhs_false]
  · -- k ≤ m: both true.
    have h_lhs_true : (2^(k+1) - 1) * k ≤ 2^(k+1) * m := by
      have h1 : (2^(k+1) - 1) * k ≤ 2^(k+1) * k := by
        apply Nat.mul_le_mul_right; omega
      exact Nat.le_trans h1 (Nat.mul_le_mul_left _ hkm)
    rw [decide_eq_true h_lhs_true, decide_eq_true hkm]

/-- **Strong N3**: alwaysFalseUnit.limit is cutEq (universally
    pointwise equal) with constCut 1 1.  Strengthens N3 from
    per-(m, k) equality to full cutEq. -/
theorem alwaysFalseUnit_limit_cutEq_one :
    cutEq (ConsistentOracle.alwaysFalseUnit).toCauchyCutSeq.limit
          (constCut 1 1) :=
  fun m k => alwaysFalseUnit_limit_eq_one_one m k

/-- **V3 (forward)**: alwaysFalseUnit.limit ≤ constCut 1 1. -/
theorem alwaysFalseUnit_le_one :
    cutLe (ConsistentOracle.alwaysFalseUnit).toCauchyCutSeq.limit
          (constCut 1 1) := by
  intro m k h
  rw [← alwaysFalseUnit_limit_cutEq_one m k] at h
  exact h

/-- **V3 (backward)**: constCut 1 1 ≤ alwaysFalseUnit.limit. -/
theorem one_le_alwaysFalseUnit :
    cutLe (constCut 1 1)
          (ConsistentOracle.alwaysFalseUnit).toCauchyCutSeq.limit := by
  intro m k h
  rw [alwaysFalseUnit_limit_cutEq_one m k] at h
  exact h

/-- **T1: Strong M1 — NOT cutEq form**. The alwaysTrueUnit limit
    (0+) is NOT cutEq with constCut 0 1 (0-exact).  Derived from
    InfinitesimalGap (which gives a specific witness pair m=0, k=1
    where they differ). -/
theorem alwaysTrueUnit_limit_not_cutEq_zero :
    ¬ cutEq (ConsistentOracle.alwaysTrueUnit).toCauchyCutSeq.limit
            (constCut 0 1) := by
  intro h_eq
  have h := h_eq 0 1
  have ⟨h0, h1⟩ := alwaysTrueUnit_limit_distinct_from_zero
  rw [h0] at h
  rw [h1] at h
  exact Bool.noConfusion h

/-- **U3: alwaysTrueUnit limit AGREES with constCut 0 1 for m ≥ 1**.

    The disagreement (M1 InfinitesimalGap) is ONLY at m = 0
    boundary.  At every (m, k) with m ≥ 1, both cuts give true.

    This formalizes the precise location of the cut-distinctness
    asymmetry: it's a single-point boundary phenomenon. -/
theorem alwaysTrueUnit_limit_eq_zero_at_pos_m (m k : Nat) (hm : m ≥ 1) :
    (ConsistentOracle.alwaysTrueUnit).toCauchyCutSeq.limit m k
    = constCut 0 1 m k := by
  rw [alwaysTrueUnit_limit_value]
  show decide (k ≤ 2^(k+1) * m) = decide (0 * k ≤ 1 * m)
  rw [Nat.zero_mul, Nat.one_mul]
  -- LHS: decide(k ≤ 2^(k+1) * m).  RHS: decide(0 ≤ m).
  -- For m ≥ 1: both true.
  have h_pow : 2^(k+1) ≥ k + 1 := by have := two_pow_ge_succ k; omega
  have h_lhs : k ≤ 2^(k+1) * m := by
    have h_prod : 2^(k+1) * m ≥ 2^(k+1) :=
      Nat.le_mul_of_pos_right _ (by omega : 0 < m)
    omega
  have h_rhs : (0 : Nat) ≤ m := Nat.zero_le _
  rw [decide_eq_true h_lhs, decide_eq_true h_rhs]

/-- **T2: ConsistentOracle existence witnesses**.  Three concrete
    (db, oracle) pairs covered: any oracle on collapsed bracket,
    alwaysTrue/alwaysFalse on unit bracket. -/
theorem consistent_oracle_existence_witnesses :
    -- (1) Any oracle on collapsed bracket: ConsistentOracle exists.
    (∀ db : DyadicBracket, db.numA = db.numB →
      ∀ oracle : DyadicOracle,
      ∃ co : ConsistentOracle db, co.oracle = oracle)
    -- (2) alwaysTrue on unit: ConsistentOracle exists.
    ∧ (∃ co : ConsistentOracle unitBracket, co.oracle = alwaysTrue)
    -- (3) alwaysFalse on unit: ConsistentOracle exists.
    ∧ (∃ co : ConsistentOracle unitBracket, co.oracle = alwaysFalse) :=
  ⟨fun db h oracle => ⟨ConsistentOracle.collapsed db h oracle, rfl⟩,
   ⟨ConsistentOracle.alwaysTrueUnit, rfl⟩,
   ⟨ConsistentOracle.alwaysFalseUnit, rfl⟩⟩

/-- **Trajectory Capstone**: 8-fact conjunctive summary of dyadic
    bisection on unit bracket under the two canonical oracles.

    Inspired by physics-track AlphaEMSimplicial Capstone style. -/
theorem trajectory_capstone (n : Nat) :
    -- alwaysTrue trajectory (collapses left)
    (DyadicBracket.bisectN alwaysTrue n unitBracket).numA = 0
    ∧ (DyadicBracket.bisectN alwaysTrue n unitBracket).numB = 1
    ∧ (DyadicBracket.bisectN alwaysTrue n unitBracket).expE = n
    ∧ (DyadicBracket.bisectN alwaysTrue n unitBracket).midCut
        = dyadicCut 1 (n+1)
    -- alwaysFalse trajectory (collapses right)
    ∧ (DyadicBracket.bisectN alwaysFalse n unitBracket).numA = 2^n - 1
    ∧ (DyadicBracket.bisectN alwaysFalse n unitBracket).numB = 2^n
    ∧ (DyadicBracket.bisectN alwaysFalse n unitBracket).expE = n
    ∧ (DyadicBracket.bisectN alwaysFalse n unitBracket).midCut
        = dyadicCut (2^(n+1) - 1) (n+1) :=
  ⟨alwaysTrue_unit_numA n, alwaysTrue_unit_numB n, alwaysTrue_unit_expE n,
   alwaysTrue_unit_midCut n,
   alwaysFalse_unit_numA n, alwaysFalse_unit_numB n,
   alwaysFalse_unit_expE n, alwaysFalse_unit_midCut n⟩

end E213.Research.Real213CutSum
