import E213.Firmware.Axiom
import E213.Firmware.Profile

/-
  단체 집합(simplicial set)과의 대응.
  2-단체(삼각형) = Triple. 면 사상 = relify의 구성.
  변 수 = 꼭짓점 수 ↔ 삼각형. C(3,2) = 3.
-/

-- 0-단체: 점. 1-단체: 선분. 2-단체: 삼각형 = Triple.

-- ═══ 면 사상 d_i ═══
-- d_i: 삼각형 → 선분. 꼭짓점 i를 제거.
def face0 (t : Triple α) : α × α := (t.y, t.z)
def face1 (t : Triple α) : α × α := (t.x, t.z)
def face2 (t : Triple α) : α × α := (t.x, t.y)

-- 면 3개 = 꼭짓점 3개 = C(3,2).

-- ═══ relify = 면들에 rel 적용 ═══
theorem relify_from_faces (rel : α → α → α) (t : Triple α) :
    relify rel t = ⟨rel (face2 t).1 (face2 t).2,
                    rel (face1 t).1 (face1 t).2,
                    rel (face0 t).1 (face0 t).2⟩ := rfl

-- ═══ 삼각형만 자기유사 ═══
-- n-단체: 꼭짓점 n+1개, 변 C(n+1,2)개.
-- 변 수 = 꼭짓점 수 ↔ C(n+1,2) = n+1 ↔ n = 2.
theorem only_triangle :
    (List.range 20).filter (fun n => n > 0 && n*(n+1)/2 == n+1)
    = [2] := by native_decide

-- n=1 (선분): 변 1, 꼭짓점 2. 1≠2.
-- n=2 (삼각형): 변 3, 꼭짓점 3. 3=3!
-- n=3 (사면체): 변 6, 꼭짓점 4. 6≠4.

-- ═══ 면-꼭짓점 관계 ═══
def vtx (t : Triple α) (i : Fin 3) : α :=
  match i.val with
  | 0 => t.x | 1 => t.y | _ => t.z

theorem face0_omits_x (t : Triple α) :
    (face0 t) = (t.y, t.z) := rfl
theorem face2_omits_z (t : Triple α) :
    (face2 t) = (t.x, t.y) := rfl

-- ═══ 오페라드 관점 ═══
-- 생성원: 이항 × (= rel). 합성: 모든 쌍에 × = relify.
-- Com(2) 오페라드의 3-인자 대수.
-- 교환 오페라드: ×(a,b) = ×(b,a) (대칭 비교).

-- ═══ ∞-groupoid 관점 ═══
-- n-cell = chain n의 원소. 모든 level에서 3개.
-- 특수한 ∞-구조: 모든 level이 동형 (C(3,2)=3).
-- 표준 HoTT에서는 level별 cell 수 변함.
-- 213: 자기유사 ∞-groupoid.

-- ═══ 요약 ═══
structure SimplicialMap where
  faces_count : pairs 3 = 3
  triangle_unique :
    (List.range 20).filter
      (fun n => n > 0 && n*(n+1)/2 == n+1) = [2]
  relify_is_faces : ∀ (rel : Nat → Nat → Nat) (t : Triple Nat),
    relify rel t = ⟨rel (face2 t).1 (face2 t).2,
                    rel (face1 t).1 (face1 t).2,
                    rel (face0 t).1 (face0 t).2⟩

theorem simplicial : SimplicialMap where
  faces_count := by native_decide
  triangle_unique := by native_decide
  relify_is_faces := fun _ _ => rfl
