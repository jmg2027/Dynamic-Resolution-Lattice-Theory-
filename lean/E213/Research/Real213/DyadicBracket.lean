import E213.Research.Real213.Dyadic
import E213.Research.Real213.CutPoset

/-!
# Research.Real213DyadicBracket: dyadic IVT bracket

A bisection bracket [a, b] where both endpoints are dyadic
constCut (numerator over 2^E).  Each bisection step descends one
level in the binary tree (E → E+1) and halves the bracket length
exactly.

## 213-native IVT philosophy (Phase J)

User insight: 213 is a binary tree.  cutMid is bit-shift, not
continuous halving.  IVT is not "exists c with f(c) = 0" but a
search trajectory generating ever-finer brackets.  Resolution
convergence, not point existence.
-/

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

/-- **DyadicBracket**: bracket [numA, numB] over common denom 2^E.
    Numerators ordered: numA ≤ numB. -/
structure DyadicBracket where
  numA : Nat
  numB : Nat
  expE : Nat
  hLe : numA ≤ numB

/-- Left endpoint as a cut function. -/
def DyadicBracket.leftCut (db : DyadicBracket) : Nat → Nat → Bool :=
  dyadicCut db.numA db.expE

/-- Right endpoint as a cut function. -/
def DyadicBracket.rightCut (db : DyadicBracket) : Nat → Nat → Bool :=
  dyadicCut db.numB db.expE

/-- Bracket length (numerator only; denom is 2^E). -/
def DyadicBracket.lenNum (db : DyadicBracket) : Nat :=
  db.numB - db.numA

/-- Midpoint numerator at next exponent (E+1).
    midNum = (numA + numB), denominator becomes 2^(E+1). -/
def DyadicBracket.midNum (db : DyadicBracket) : Nat :=
  db.numA + db.numB

/-- Midpoint as a cut function. -/
def DyadicBracket.midCut (db : DyadicBracket) : Nat → Nat → Bool :=
  dyadicCut db.midNum (db.expE + 1)

/-- **Left half bracket**: [2*numA, numA + numB] at denom 2^(E+1). -/
def DyadicBracket.leftHalf (db : DyadicBracket) : DyadicBracket where
  numA := 2 * db.numA
  numB := db.numA + db.numB
  expE := db.expE + 1
  hLe := by
    have : 2 * db.numA = db.numA + db.numA := by rw [Nat.two_mul]
    rw [this]
    exact Nat.add_le_add_left db.hLe db.numA

/-- **Right half bracket**: [numA + numB, 2*numB] at denom 2^(E+1). -/
def DyadicBracket.rightHalf (db : DyadicBracket) : DyadicBracket where
  numA := db.numA + db.numB
  numB := 2 * db.numB
  expE := db.expE + 1
  hLe := by
    have : 2 * db.numB = db.numB + db.numB := by rw [Nat.two_mul]
    rw [this]
    exact Nat.add_le_add_right db.hLe db.numB

/-- **lenNum invariant under leftHalf**: numerator difference unchanged.
    Real length = lenNum/2^E halves because expE increases by 1. -/
theorem DyadicBracket.leftHalf_lenNum (db : DyadicBracket) :
    db.leftHalf.lenNum = db.lenNum := by
  show (db.numA + db.numB) - 2 * db.numA = db.numB - db.numA
  omega

/-- **lenNum invariant under rightHalf**: same as left.
    Real length halves via expE increment. -/
theorem DyadicBracket.rightHalf_lenNum (db : DyadicBracket) :
    db.rightHalf.lenNum = db.lenNum := by
  show 2 * db.numB - (db.numA + db.numB) = db.numB - db.numA
  omega

/-- expE increases by 1 on left half. -/
theorem DyadicBracket.leftHalf_expE (db : DyadicBracket) :
    db.leftHalf.expE = db.expE + 1 := rfl

/-- expE increases by 1 on right half. -/
theorem DyadicBracket.rightHalf_expE (db : DyadicBracket) :
    db.rightHalf.expE = db.expE + 1 := rfl

/-- **Oracle**: sign-test on a cut function.  Returns Bool —
    interpreted as the steering wheel of the bisection: true →
    take left half (root in [a, mid]), false → take right half. -/
abbrev DyadicOracle := (Nat → Nat → Bool) → Bool

/-- **Single bisection step**: oracle decides left or right half. -/
def DyadicBracket.bisectStep (db : DyadicBracket)
    (oracle : DyadicOracle) : DyadicBracket :=
  if oracle db.midCut then db.leftHalf else db.rightHalf

/-- **n-step bisection**: iterate bisectStep n times. -/
def DyadicBracket.bisectN
    (oracle : DyadicOracle) :
    Nat → DyadicBracket → DyadicBracket
  | 0, db => db
  | n+1, db => bisectN oracle n (db.bisectStep oracle)

/-- After n bisection steps, expE increases by exactly n. -/
theorem DyadicBracket.bisectN_expE (oracle : DyadicOracle) :
    ∀ n db, (DyadicBracket.bisectN oracle n db).expE = db.expE + n
  | 0, _ => by simp [DyadicBracket.bisectN]
  | n+1, db => by
    show (DyadicBracket.bisectN oracle n (db.bisectStep oracle)).expE
       = db.expE + (n+1)
    rw [DyadicBracket.bisectN_expE oracle n (db.bisectStep oracle)]
    -- (db.bisectStep oracle).expE = db.expE + 1
    have hstep : (db.bisectStep oracle).expE = db.expE + 1 := by
      show (if oracle db.midCut
            then db.leftHalf else db.rightHalf).expE
            = db.expE + 1
      by_cases h : oracle db.midCut = true
      · rw [if_pos h]; rfl
      · rw [if_neg h]; rfl
    rw [hstep]
    omega

/-- After n bisection steps, lenNum stays the same.
    The actual bracket length halves via expE increment. -/
theorem DyadicBracket.bisectN_lenNum (oracle : DyadicOracle) :
    ∀ n db, (DyadicBracket.bisectN oracle n db).lenNum = db.lenNum
  | 0, _ => by simp [DyadicBracket.bisectN]
  | n+1, db => by
    show (DyadicBracket.bisectN oracle n (db.bisectStep oracle)).lenNum
       = db.lenNum
    rw [DyadicBracket.bisectN_lenNum oracle n (db.bisectStep oracle)]
    show (db.bisectStep oracle).lenNum = db.lenNum
    show (if oracle db.midCut
          then db.leftHalf else db.rightHalf).lenNum
          = db.lenNum
    by_cases h : oracle db.midCut = true
    · rw [if_pos h]; exact db.leftHalf_lenNum
    · rw [if_neg h]; exact db.rightHalf_lenNum

/-- **Dyadic comparison lemma**: cutLe between two dyadicCuts via
    cross-multiplication.  numA / 2^E ≤ numB / 2^F iff
    numA * 2^F ≤ numB * 2^E. -/
theorem cutLe_dyadicCut (numA E numB F : Nat)
    (h : numA * 2^F ≤ numB * 2^E) :
    cutLe (dyadicCut numA E) (dyadicCut numB F) := by
  intro m k hbk
  have hBk : numB * k ≤ 2^F * m := of_decide_eq_true hbk
  show decide (numA * k ≤ 2^E * m) = true
  apply decide_eq_true
  -- numA * k ≤ 2^E * m via numA * 2^F ≤ numB * 2^E and numB * k ≤ 2^F * m.
  -- Multiply h by k: numA * 2^F * k ≤ numB * 2^E * k.
  -- Multiply hBk by 2^E: numB * 2^E * k ≤ 2^F * m * 2^E.
  have step1 : numA * 2^F * k ≤ numB * 2^E * k :=
    Nat.mul_le_mul_right k h
  have step2 : numB * 2^E * k ≤ 2^F * m * 2^E := by
    have e : numB * 2^E * k = numB * k * 2^E := by
      rw [Nat.mul_assoc, Nat.mul_comm (2^E) k, ← Nat.mul_assoc]
    rw [e]
    exact Nat.mul_le_mul_right (2^E) hBk
  have step3 : numA * 2^F * k ≤ 2^F * m * 2^E := Nat.le_trans step1 step2
  -- step3: numA * 2^F * k ≤ 2^F * m * 2^E.
  -- Want: numA * k ≤ 2^E * m.  Rearrange both sides.
  -- LHS: numA * 2^F * k = 2^F * (numA * k).
  -- RHS: 2^F * m * 2^E = 2^F * (2^E * m).
  -- So 2^F * (numA * k) ≤ 2^F * (2^E * m).
  -- Cancel 2^F (which is ≥ 1 always since 2^anything ≥ 1).
  have hLHS : numA * 2^F * k = 2^F * (numA * k) := by
    rw [Nat.mul_comm numA (2^F), Nat.mul_assoc]
  have hRHS : 2^F * m * 2^E = 2^F * (2^E * m) := by
    rw [Nat.mul_assoc, Nat.mul_comm m (2^E)]
  rw [hLHS, hRHS] at step3
  exact Nat.le_of_mul_le_mul_left step3 (Nat.pos_pow_of_pos F (by decide : 0 < 2))

/-- Helper: numA * 2^(E+1) = 2 * numA * 2^E. -/
private theorem dyadic_pow_succ_eq (n E : Nat) :
    n * 2^(E+1) = 2 * n * 2^E := by
  rw [Nat.pow_succ, Nat.mul_comm (2^E) 2, ← Nat.mul_assoc, Nat.mul_comm n 2]

/-- **leftHalf bracket containment (left endpoint)**: original left
    endpoint is ≤ leftHalf's left endpoint (real-wise equal). -/
theorem DyadicBracket.leftHalf_left_contains (db : DyadicBracket) :
    cutLe db.leftCut db.leftHalf.leftCut := by
  show cutLe (dyadicCut db.numA db.expE)
             (dyadicCut (2*db.numA) (db.expE + 1))
  apply cutLe_dyadicCut
  rw [dyadic_pow_succ_eq]
  exact Nat.le_refl _

/-- **leftHalf bracket containment (right endpoint)**: leftHalf's
    right endpoint (the midpoint) is ≤ original right endpoint. -/
theorem DyadicBracket.leftHalf_right_contains (db : DyadicBracket) :
    cutLe db.leftHalf.rightCut db.rightCut := by
  show cutLe (dyadicCut (db.numA + db.numB) (db.expE + 1))
             (dyadicCut db.numB db.expE)
  apply cutLe_dyadicCut
  rw [dyadic_pow_succ_eq]
  have : db.numA + db.numB ≤ 2 * db.numB := by
    rw [Nat.two_mul]
    exact Nat.add_le_add_right db.hLe db.numB
  exact Nat.mul_le_mul_right (2^db.expE) this

/-- **rightHalf bracket containment (left endpoint)**: original
    left endpoint ≤ rightHalf's left endpoint (the midpoint). -/
theorem DyadicBracket.rightHalf_left_contains (db : DyadicBracket) :
    cutLe db.leftCut db.rightHalf.leftCut := by
  show cutLe (dyadicCut db.numA db.expE)
             (dyadicCut (db.numA + db.numB) (db.expE + 1))
  apply cutLe_dyadicCut
  rw [dyadic_pow_succ_eq]
  have : 2 * db.numA ≤ db.numA + db.numB := by
    rw [Nat.two_mul]
    exact Nat.add_le_add_left db.hLe db.numA
  exact Nat.mul_le_mul_right (2^db.expE) this

/-- **rightHalf bracket containment (right endpoint)**: rightHalf's
    right endpoint ≤ original right endpoint (real-wise equal). -/
theorem DyadicBracket.rightHalf_right_contains (db : DyadicBracket) :
    cutLe db.rightHalf.rightCut db.rightCut := by
  show cutLe (dyadicCut (2*db.numB) (db.expE + 1))
             (dyadicCut db.numB db.expE)
  apply cutLe_dyadicCut
  rw [dyadic_pow_succ_eq]
  exact Nat.le_refl _

/-- **One-step bisectStep containment (left)**: original left
    endpoint ≤ bisectStep's left endpoint, regardless of oracle. -/
theorem DyadicBracket.bisectStep_contains_left
    (db : DyadicBracket) (oracle : DyadicOracle) :
    cutLe db.leftCut (db.bisectStep oracle).leftCut := by
  show cutLe db.leftCut
        (if oracle db.midCut then db.leftHalf else db.rightHalf).leftCut
  by_cases h : oracle db.midCut = true
  · rw [if_pos h]; exact db.leftHalf_left_contains
  · rw [if_neg h]; exact db.rightHalf_left_contains

/-- **One-step bisectStep containment (right)**: bisectStep's right
    endpoint ≤ original right endpoint, regardless of oracle. -/
theorem DyadicBracket.bisectStep_contains_right
    (db : DyadicBracket) (oracle : DyadicOracle) :
    cutLe (db.bisectStep oracle).rightCut db.rightCut := by
  show cutLe (if oracle db.midCut
              then db.leftHalf else db.rightHalf).rightCut db.rightCut
  by_cases h : oracle db.midCut = true
  · rw [if_pos h]; exact db.leftHalf_right_contains
  · rw [if_neg h]; exact db.rightHalf_right_contains

/-- **n-step bisection bracket containment (left)**: ∀ n, original
    left endpoint ≤ bisectN's left endpoint. -/
theorem DyadicBracket.bisectN_contains_left
    (oracle : DyadicOracle) :
    ∀ n db, cutLe db.leftCut (DyadicBracket.bisectN oracle n db).leftCut
  | 0, db => cutLe_refl db.leftCut
  | n+1, db => by
    show cutLe db.leftCut
          (DyadicBracket.bisectN oracle n (db.bisectStep oracle)).leftCut
    have h1 : cutLe db.leftCut (db.bisectStep oracle).leftCut :=
      db.bisectStep_contains_left oracle
    have h2 : cutLe (db.bisectStep oracle).leftCut
              (DyadicBracket.bisectN oracle n (db.bisectStep oracle)).leftCut :=
      DyadicBracket.bisectN_contains_left oracle n (db.bisectStep oracle)
    exact cutLe_trans _ _ _ h1 h2

/-- **n-step bisection bracket containment (right)**: ∀ n, bisectN's
    right endpoint ≤ original right endpoint. -/
theorem DyadicBracket.bisectN_contains_right
    (oracle : DyadicOracle) :
    ∀ n db, cutLe (DyadicBracket.bisectN oracle n db).rightCut db.rightCut
  | 0, db => cutLe_refl db.rightCut
  | n+1, db => by
    show cutLe (DyadicBracket.bisectN oracle n (db.bisectStep oracle)).rightCut
                db.rightCut
    have h1 : cutLe (DyadicBracket.bisectN oracle n (db.bisectStep oracle)).rightCut
              (db.bisectStep oracle).rightCut :=
      DyadicBracket.bisectN_contains_right oracle n (db.bisectStep oracle)
    have h2 : cutLe (db.bisectStep oracle).rightCut db.rightCut :=
      db.bisectStep_contains_right oracle
    exact cutLe_trans _ _ _ h1 h2

/-- **Midpoint above left endpoint**: cutLe db.leftCut db.midCut. -/
theorem DyadicBracket.midCut_above_left (db : DyadicBracket) :
    cutLe db.leftCut db.midCut := by
  show cutLe (dyadicCut db.numA db.expE)
             (dyadicCut db.midNum (db.expE + 1))
  apply cutLe_dyadicCut
  rw [dyadic_pow_succ_eq]
  apply Nat.mul_le_mul_right
  show 2 * db.numA ≤ db.numA + db.numB
  rw [Nat.two_mul]
  exact Nat.add_le_add_left db.hLe db.numA

/-- **Midpoint below right endpoint**: cutLe db.midCut db.rightCut. -/
theorem DyadicBracket.midCut_below_right (db : DyadicBracket) :
    cutLe db.midCut db.rightCut := by
  show cutLe (dyadicCut db.midNum (db.expE + 1))
             (dyadicCut db.numB db.expE)
  apply cutLe_dyadicCut
  rw [dyadic_pow_succ_eq]
  apply Nat.mul_le_mul_right
  show db.numA + db.numB ≤ 2 * db.numB
  rw [Nat.two_mul]
  exact Nat.add_le_add_right db.hLe db.numB

/-- **bisectN midpoint trapped in original bracket (left side)**:
    ∀ n, original.leftCut ≤ (bisectN n).midCut. -/
theorem DyadicBracket.bisectN_midCut_above_left
    (oracle : DyadicOracle) (n : Nat) (db : DyadicBracket) :
    cutLe db.leftCut (DyadicBracket.bisectN oracle n db).midCut := by
  have h1 : cutLe db.leftCut (DyadicBracket.bisectN oracle n db).leftCut :=
    DyadicBracket.bisectN_contains_left oracle n db
  have h2 : cutLe (DyadicBracket.bisectN oracle n db).leftCut
                  (DyadicBracket.bisectN oracle n db).midCut :=
    DyadicBracket.midCut_above_left _
  exact cutLe_trans _ _ _ h1 h2

/-- **bisectN midpoint trapped in original bracket (right side)**:
    ∀ n, (bisectN n).midCut ≤ original.rightCut. -/
theorem DyadicBracket.bisectN_midCut_below_right
    (oracle : DyadicOracle) (n : Nat) (db : DyadicBracket) :
    cutLe (DyadicBracket.bisectN oracle n db).midCut db.rightCut := by
  have h1 : cutLe (DyadicBracket.bisectN oracle n db).midCut
                  (DyadicBracket.bisectN oracle n db).rightCut :=
    DyadicBracket.midCut_below_right _
  have h2 : cutLe (DyadicBracket.bisectN oracle n db).rightCut db.rightCut :=
    DyadicBracket.bisectN_contains_right oracle n db
  exact cutLe_trans _ _ _ h1 h2

/-- **Cauchy trichotomy case A**: if rightCut m k = true, then
    every bisectN midpoint is also true at (m, k).  Sequence is
    constant true; trivially Cauchy with modulus 0. -/
theorem DyadicBracket.bisectN_midCut_constTrue
    (oracle : DyadicOracle) (db : DyadicBracket) (m k : Nat)
    (hr : db.rightCut m k = true) (n : Nat) :
    (DyadicBracket.bisectN oracle n db).midCut m k = true :=
  DyadicBracket.bisectN_midCut_below_right oracle n db m k hr

/-- **Cauchy trichotomy case B**: if leftCut m k = false, then
    every bisectN midpoint is also false at (m, k).  Sequence is
    constant false; trivially Cauchy with modulus 0. -/
theorem DyadicBracket.bisectN_midCut_constFalse
    (oracle : DyadicOracle) (db : DyadicBracket) (m k : Nat)
    (hl : db.leftCut m k = false) (n : Nat) :
    (DyadicBracket.bisectN oracle n db).midCut m k = false := by
  -- Contrapositive of bisectN_midCut_above_left:
  -- midCut → leftCut, so leftCut = false → midCut = false.
  cases hmidVal : (DyadicBracket.bisectN oracle n db).midCut m k
  · rfl
  · exfalso
    have hleft : db.leftCut m k = true :=
      DyadicBracket.bisectN_midCut_above_left oracle n db m k hmidVal
    rw [hleft] at hl
    exact Bool.noConfusion hl

/-- **bisectStep preserves collapsed (numA = numB)**: regardless of
    oracle, when the bracket is a degenerate point bracket, the
    result is also a degenerate point bracket. -/
theorem DyadicBracket.bisectStep_collapsed (db : DyadicBracket)
    (oracle : DyadicOracle) (h : db.numA = db.numB) :
    (db.bisectStep oracle).numA = (db.bisectStep oracle).numB := by
  show (if oracle db.midCut then db.leftHalf else db.rightHalf).numA
     = (if oracle db.midCut then db.leftHalf else db.rightHalf).numB
  by_cases hor : oracle db.midCut = true
  · rw [if_pos hor]
    show 2 * db.numA = db.numA + db.numB
    rw [Nat.two_mul, h]
  · rw [if_neg hor]
    show db.numA + db.numB = 2 * db.numB
    rw [Nat.two_mul, h]

/-- **bisectN preserves collapsed**: by induction on n. -/
theorem DyadicBracket.bisectN_collapsed (oracle : DyadicOracle) :
    ∀ n db, db.numA = db.numB →
      (DyadicBracket.bisectN oracle n db).numA
      = (DyadicBracket.bisectN oracle n db).numB
  | 0, _, h => h
  | n+1, db, h => by
    show (DyadicBracket.bisectN oracle n (db.bisectStep oracle)).numA
       = (DyadicBracket.bisectN oracle n (db.bisectStep oracle)).numB
    exact DyadicBracket.bisectN_collapsed oracle n (db.bisectStep oracle)
            (DyadicBracket.bisectStep_collapsed db oracle h)

/-- **bisectStep on collapsed: numA doubles**. -/
theorem DyadicBracket.bisectStep_collapsed_numA
    (db : DyadicBracket) (oracle : DyadicOracle) (h : db.numA = db.numB) :
    (db.bisectStep oracle).numA = 2 * db.numA := by
  show (if oracle db.midCut then db.leftHalf else db.rightHalf).numA = 2 * db.numA
  by_cases hor : oracle db.midCut = true
  · rw [if_pos hor]
    rfl
  · rw [if_neg hor]
    show db.numA + db.numB = 2 * db.numA
    rw [Nat.two_mul, h]

/-- **bisectN on collapsed: numA scales as 2^n**. -/
theorem DyadicBracket.bisectN_collapsed_numA (oracle : DyadicOracle) :
    ∀ n db, db.numA = db.numB →
      (DyadicBracket.bisectN oracle n db).numA = 2^n * db.numA
  | 0, db, _ => by
    show db.numA = 2^0 * db.numA
    have : (2:Nat)^0 = 1 := rfl
    rw [this, Nat.one_mul]
  | n+1, db, h => by
    show (DyadicBracket.bisectN oracle n (db.bisectStep oracle)).numA
       = 2^(n+1) * db.numA
    rw [DyadicBracket.bisectN_collapsed_numA oracle n (db.bisectStep oracle)
          (DyadicBracket.bisectStep_collapsed db oracle h)]
    rw [DyadicBracket.bisectStep_collapsed_numA db oracle h]
    rw [Nat.pow_succ, Nat.mul_assoc]

/-- **Collapsed bracket midCut form**: for collapsed db, the midCut
    value at (m, k) at step n = decide(numA * k ≤ 2^expE * m),
    independent of n.  This is the formal payoff of all the
    structural lemmas. -/
theorem DyadicBracket.bisectN_collapsed_midCut_form
    (oracle : DyadicOracle) (db : DyadicBracket)
    (h : db.numA = db.numB) (n : Nat) (m k : Nat) :
    (DyadicBracket.bisectN oracle n db).midCut m k
    = decide (db.numA * k ≤ 2^db.expE * m) := by
  have hnumA : (DyadicBracket.bisectN oracle n db).numA = 2^n * db.numA :=
    DyadicBracket.bisectN_collapsed_numA oracle n db h
  have hcoll : (DyadicBracket.bisectN oracle n db).numA
             = (DyadicBracket.bisectN oracle n db).numB :=
    DyadicBracket.bisectN_collapsed oracle n db h
  have hexpE : (DyadicBracket.bisectN oracle n db).expE = db.expE + n :=
    DyadicBracket.bisectN_expE oracle n db
  show decide ((DyadicBracket.bisectN oracle n db).midNum * k
       ≤ 2^((DyadicBracket.bisectN oracle n db).expE + 1) * m)
       = decide (db.numA * k ≤ 2^db.expE * m)
  show decide (((DyadicBracket.bisectN oracle n db).numA
              + (DyadicBracket.bisectN oracle n db).numB) * k
       ≤ 2^((DyadicBracket.bisectN oracle n db).expE + 1) * m)
       = decide (db.numA * k ≤ 2^db.expE * m)
  rw [← hcoll, hnumA, hexpE]
  -- Goal: decide ((2^n * db.numA + 2^n * db.numA) * k ≤ 2^(db.expE + n + 1) * m)
  --     = decide (db.numA * k ≤ 2^db.expE * m)
  have e1 : 2^n * db.numA + 2^n * db.numA = 2^(n+1) * db.numA := by
    rw [← Nat.two_mul, ← Nat.mul_assoc, Nat.mul_comm 2 (2^n), ← Nat.pow_succ]
  have e2 : (2:Nat)^(db.expE + n + 1) = 2^(n+1) * 2^db.expE := by
    rw [show db.expE + n + 1 = (n+1) + db.expE from by omega, Nat.pow_add]
  rw [e1, e2]
  -- Goal: decide (2^(n+1) * db.numA * k ≤ 2^(n+1) * 2^db.expE * m)
  --     = decide (db.numA * k ≤ 2^db.expE * m)
  congr 1
  apply propext
  constructor
  · intro hle
    have : 2^(n+1) * db.numA * k = 2^(n+1) * (db.numA * k) :=
      Nat.mul_assoc _ _ _
    rw [this] at hle
    have h2 : 2^(n+1) * 2^db.expE * m = 2^(n+1) * (2^db.expE * m) :=
      Nat.mul_assoc _ _ _
    rw [h2] at hle
    exact Nat.le_of_mul_le_mul_left hle
      (Nat.pos_pow_of_pos (n+1) (by decide : 0 < 2))
  · intro hle
    have h1 : 2^(n+1) * db.numA * k = 2^(n+1) * (db.numA * k) :=
      Nat.mul_assoc _ _ _
    have h2 : 2^(n+1) * 2^db.expE * m = 2^(n+1) * (2^db.expE * m) :=
      Nat.mul_assoc _ _ _
    rw [h1, h2]
    exact Nat.mul_le_mul_left (2^(n+1)) hle

end E213.Research.Real213.CutSum
