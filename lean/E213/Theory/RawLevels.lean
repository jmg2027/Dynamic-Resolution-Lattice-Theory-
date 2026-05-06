import E213.Theory.Raw

/-!
# Firmware: Level-≤2 enumeration

Explicit lists of the Raw terms up to depth 2 (backing §1.3
and §5.1 of the paper).  Uses only the public `Raw.slash`
API.
-/

namespace E213.Theory

-- ═══ Level-≤2 enumeration ═══

/-- Level-≤1 witnesses: the Raw terms `a`, `b`, `a/b`
    (a `List Raw`, not a ZFC set; order is the enumeration
    Lens choice, not axiomatic). -/
def Raw.level1_set : List Raw :=
  [Raw.a, Raw.b, Raw.slash Raw.a Raw.b (by decide)]

/-- Level-2 additions: the Raw terms `a/(a/b)`, `b/(a/b)`. -/
def Raw.level2_new : List Raw :=
  [Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide),
   Raw.slash Raw.b (Raw.slash Raw.a Raw.b (by decide)) (by decide)]

-- Counts.
theorem Raw.level1_card : Raw.level1_set.length = 3 := rfl
theorem Raw.level2_new_card : Raw.level2_new.length = 2 := rfl
theorem Raw.level2_total_card :
    (Raw.level1_set ++ Raw.level2_new).length = 5 := rfl

-- The combined list has no duplicates (all 5 distinct).
example : (Raw.level1_set ++ Raw.level2_new).Nodup := by decide

end E213.Theory
