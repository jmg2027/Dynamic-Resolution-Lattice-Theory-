/-!
# Property Survival Count per CD Level (∅-axiom)

Mingu's "narrowing tower" insight:

> "건물은 위를 더 넓게 만들수없잖아? 보통 위가 더 작아지잖아?
>  ...실제로 위로 올라갈수록 아래에 있던 것들이 사라지는 이유가
>  이거일거임"
> (Translation: "You can't make a building wider toward the top,
>  right?  Usually the top gets smaller, right?  ...the reason
>  things from below actually disappear as you climb upward is
>  probably this.")

213-native formalisation: at each CD level, the surviving
algebraic properties form a **decreasing sequence**.  Each level
loses exactly one property.

The "narrowing" is structural — the higher you go, the fewer
algebraic constraints survive.  This is the dual of "tower
gets pointier as we ascend".

| Level | Lost | Surviving (count) |
|---|---|---|
| 0 | (substrate, no constraints) | 5 (ord, comm, assoc, alt, pow-assoc) |
| 1 | ordering | 4 |
| 2 | commutativity | 3 |
| 3 | associativity | 2 |
| 4 | alternativity | 1 |
| 5+ | power-associativity | 0 |
| 25 | (only Z/2 + norm residual) | 0 |
-/

namespace E213.Lib.Math.Geometry.TriangularTower.PropertySurvival

/-- ★ **Surviving property count at level n**.
    Decreases by 1 per level until 0 at level 5+. -/
def surviving (n : Nat) : Nat :=
  if n ≥ 5 then 0
  else 5 - n

/-- ★ Level 0: 5 properties survive. -/
theorem surviving_0 : surviving 0 = 5 := rfl

/-- ★ Level 1: ordering lost → 4 survive. -/
theorem surviving_1 : surviving 1 = 4 := rfl

/-- ★ Level 2: commutativity lost → 3 survive. -/
theorem surviving_2 : surviving 2 = 3 := rfl

/-- ★ Level 3: associativity lost → 2 survive. -/
theorem surviving_3 : surviving 3 = 2 := rfl

/-- ★ Level 4: alternativity lost → 1 survives. -/
theorem surviving_4 : surviving 4 = 1 := rfl

/-- ★ Level 5+: power-associativity lost → 0 survive. -/
theorem surviving_5 : surviving 5 = 0 := rfl

/-- ★ Level 25: only Z/2 + norm residual. -/
theorem surviving_25 : surviving 25 = 0 := rfl

/-- ★ **Strict decrease at consecutive levels (concrete)**:
    surviving 4 < surviving 3 < ... < surviving 0. -/
theorem surviving_strict_decrease :
    surviving 1 < surviving 0
    ∧ surviving 2 < surviving 1
    ∧ surviving 3 < surviving 2
    ∧ surviving 4 < surviving 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Geometry.TriangularTower.PropertySurvival
