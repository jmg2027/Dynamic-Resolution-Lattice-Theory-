/-
  Two13/Emerge.lean — 3: 창발

  표지(|)를 두 번 긋는다.
  두 표지 사이에 관계가 생긴다.
  표지 둘 + 관계 하나 = 셋.
  C(3,2) = 3. 자기복제. 유일한 고정점.
  3은 기호가 아니라 현상이다.
-/
prelude
import Two13.Equal

-- ═══ 3의 창발 ═══
inductive Three : Type where
  | here    : Three
  | there   : Three
  | between : Three

-- ═══ 셋의 쌍 ═══
inductive Pairs : Type where
  | ht : Pairs
  | hb : Pairs
  | tb : Pairs

-- Three → Pairs
-- here→ht, there→tb, between→hb
noncomputable def toPairs : Three → Pairs :=
  @Three.rec (fun _ => Pairs) Pairs.ht Pairs.tb Pairs.hb

-- Pairs → Three
-- ht→here, hb→between, tb→there
noncomputable def fromPairs : Pairs → Three :=
  @Pairs.rec (fun _ => Three) Three.here Three.between Three.there

-- ═══ C(3,2) = 3 증명 ═══

theorem roundtrip1 (x : Three) :
    Eq (fromPairs (toPairs x)) x :=
  @Three.rec (fun x => Eq (fromPairs (toPairs x)) x)
    (Eq.refl Three.here)
    (Eq.refl Three.there)
    (Eq.refl Three.between)
    x

theorem roundtrip2 (x : Pairs) :
    Eq (toPairs (fromPairs x)) x :=
  @Pairs.rec (fun x => Eq (toPairs (fromPairs x)) x)
    (Eq.refl Pairs.ht)
    (Eq.refl Pairs.hb)
    (Eq.refl Pairs.tb)
    x
