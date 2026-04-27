import E213.Research.Real213DyadicBracket

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

end E213.Research.Real213CutSum
