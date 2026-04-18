import E213.Meta.CrossChain

/-
  Stream Analysis: RealPath (Cantor space) 위의 정리들.

  사용자 주장: ℝ 은 Stream (Nat → Bool) + Lens.
  이 파일: Stream 자체의 구조적 정리들.

  포함:
    - Constant streams (zero, ones).
    - Shift operations.
    - Prefix equality.
    - Specific reals (1/2, 1/3, ...).
    - Cantor-like arguments.
-/

-- ═══ Constant Streams ═══

-- 0.0000... = 0.
def RealPath.zero : RealPath := fun _ => false

-- 0.1111... = 1 (binary limit).
def RealPath.ones : RealPath := fun _ => true

-- 이미 정의: RealPath.half = 0.1000... = 1/2.

-- ═══ Shift ═══

-- shift n: stream 앞 n 개 제거.
def RealPath.shift (n : Nat) (r : RealPath) : RealPath :=
  fun k => r (k + n)

-- ═══ 기본 정리 ═══

-- SA_001: zero ≠ ones.
theorem sa_001 : RealPath.zero ≠ RealPath.ones := by
  intro h
  have h0 : RealPath.zero 0 = RealPath.ones 0 := by rw [h]
  simp [RealPath.zero, RealPath.ones] at h0

-- SA_002: zero ≠ half.
theorem sa_002 : RealPath.zero ≠ RealPath.half := by
  intro h
  have : RealPath.zero 0 = RealPath.half 0 := by rw [h]
  simp [RealPath.zero, RealPath.half] at this

-- SA_003: half ≠ ones.
theorem sa_003 : RealPath.half ≠ RealPath.ones := by
  intro h
  have : RealPath.half 1 = RealPath.ones 1 := by rw [h]
  simp [RealPath.half, RealPath.ones] at this

-- SA_004: shift 0 = id.
theorem sa_004 (r : RealPath) : RealPath.shift 0 r = r := by
  funext k; simp [RealPath.shift]

-- SA_005: zero shift = zero.
theorem sa_005 (n : Nat) : RealPath.shift n RealPath.zero = RealPath.zero := by
  funext k; simp [RealPath.shift, RealPath.zero]

-- SA_006: ones shift = ones.
theorem sa_006 (n : Nat) : RealPath.shift n RealPath.ones = RealPath.ones := by
  funext k; simp [RealPath.shift, RealPath.ones]

-- ═══ Stream equality via pointwise ═══

-- SA_007: Extensionality.
theorem sa_007 (r s : RealPath) :
    (∀ n, r n = s n) → r = s := by
  intro h; funext n; exact h n

-- SA_008: Negation (1 - x): 모든 bit flip.
def RealPath.neg (r : RealPath) : RealPath := fun n => !(r n)

-- SA_009: Double negation.
theorem sa_009 (r : RealPath) : r.neg.neg = r := by
  funext n; simp [RealPath.neg]

-- SA_010: zero.neg = ones.
theorem sa_010 : RealPath.zero.neg = RealPath.ones := by
  funext n; simp [RealPath.neg, RealPath.zero, RealPath.ones]

-- SA_011: half 의 neg.
theorem sa_011 (n : Nat) :
    RealPath.half.neg n = !(RealPath.half n) := by
  simp [RealPath.neg]

-- ═══ Dyadic lens 적용 ═══

-- SA_012: dyadic 0 = 0 (첫 0 비트).
theorem sa_012 : (StreamLens.dyadic 1).view RealPath.zero = 0 := by
  simp [StreamLens.dyadic, StreamLens.view, RealPath.zero, List.range, List.foldl]

-- SA_013: dyadic 1 (half, 1 비트) = 1.
theorem sa_013 : (StreamLens.dyadic 1).view RealPath.half = 1 := by
  simp [StreamLens.dyadic, StreamLens.view, RealPath.half, List.range, List.foldl]

-- SA_014: dyadic 1 (ones) = 1.
theorem sa_014 : (StreamLens.dyadic 1).view RealPath.ones = 1 := by
  simp [StreamLens.dyadic, StreamLens.view, RealPath.ones, List.range, List.foldl]

-- dyadic 1 렌즈 에서 half ≡ ones (1로 collapse).
-- SA_015:
theorem sa_015 :
    (StreamLens.dyadic 1).equiv RealPath.half RealPath.ones := by
  unfold StreamLens.equiv
  rw [sa_013, sa_014]
