import E213.Math.Cohomology.Bipartite.V32

/-!
# Dyadic-bit / K_{3,2}^{(2)} conjecture — formal scaffold

Conjecture 2 (G1 memo): irrational dyadic cut patterns trace
walks on K_{3,2}^{(2)} via the multiplicity-2 parallel-edge bit.
This file lays the *language* — definitions + decidable tests —
without yet proving the universal statement.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

open E213.Math.Cohomology.Bip32 (srcFin tgtFin)

/-- The k-th binary digit of a natural number. -/
def dyadicBit (n k : Nat) : Bool := (n / 2 ^ k) % 2 == 1

/-- Periodic bit sequence: cycle through `pat` indefinitely. -/
def periodicBit (pat : List Bool) (k : Nat) : Bool :=
  if h : pat.length = 0 then false
  else pat[k % pat.length]'(Nat.mod_lt _ (Nat.pos_of_ne_zero h))

/-- Smoke: 1/3 → [F,T]; 1/5 → [F,F,T,T]; period checks. -/
theorem period_smoke :
    periodicBit [false, true] 0 = false
    ∧ periodicBit [false, true] 3 = true
    ∧ periodicBit [false, false, true, true] 0 = false
    ∧ periodicBit [false, false, true, true] 6 = true := by decide

/-! ## K_{3,2}^{(2)} bit-walk: parallel-edge bit per edge. -/

/-- Two edges share an endpoint. -/
def shareEndpoint (e₁ e₂ : Fin 12) : Bool :=
  (srcFin e₁ == srcFin e₂) || (srcFin e₁ == tgtFin e₂)
    || (tgtFin e₁ == srcFin e₂) || (tgtFin e₁ == tgtFin e₂)

/-- Validity of a bit-walk. -/
def validWalk (es : List (Fin 12)) : Bool :=
  match es with
  | [] => true
  | [_] => true
  | e₁ :: e₂ :: rest =>
    shareEndpoint e₁ e₂ && validWalk (e₂ :: rest)

/-- Bit-stream of a walk: e.val % 2 for each edge. -/
def bitStream (es : List (Fin 12)) : List Bool :=
  es.map fun e => e.val % 2 == 1

/-- Smoke: [0, 4] valid (T_0 shared); [0, 11] invalid. -/
theorem walk_smoke :
    validWalk [⟨0, by decide⟩, ⟨4, by decide⟩] = true
    ∧ validWalk [⟨0, by decide⟩, ⟨11, by decide⟩] = false :=
  ⟨by decide, by decide⟩

/-- 1/3 period [F, T] realised as walk [0, 5]: T_0 shared. -/
theorem one_third_walk :
    validWalk [⟨0, by decide⟩, ⟨5, by decide⟩] = true
    ∧ bitStream [⟨0, by decide⟩, ⟨5, by decide⟩] = [false, true] :=
  ⟨by decide, by decide⟩

/-- 1/5 period [F, F, T, T] realised as walk [0, 4, 7, 3]. -/
theorem one_fifth_walk :
    validWalk [⟨0, by decide⟩, ⟨4, by decide⟩,
               ⟨7, by decide⟩, ⟨3, by decide⟩] = true
    ∧ bitStream [⟨0, by decide⟩, ⟨4, by decide⟩,
                 ⟨7, by decide⟩, ⟨3, by decide⟩]
       = [false, false, true, true] := ⟨by decide, by decide⟩

/-- 1/7 period [F, F, T] realised over 2 periods as 6-edge walk
    [0, 2, 7, 4, 0, 3] — period 3 fits as a path. -/
theorem one_seventh_walk :
    validWalk [⟨0, by decide⟩, ⟨2, by decide⟩, ⟨7, by decide⟩,
               ⟨4, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩] = true
    ∧ bitStream [⟨0, by decide⟩, ⟨2, by decide⟩, ⟨7, by decide⟩,
                 ⟨4, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩]
       = [false, false, true, false, false, true] :=
  ⟨by decide, by decide⟩

end E213.Math.Cohomology.Dyadic.Conjecture
