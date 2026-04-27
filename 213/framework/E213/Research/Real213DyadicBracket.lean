import E213.Research.Real213Dyadic

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

namespace E213.Research.Real213CutSum

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

end E213.Research.Real213CutSum
