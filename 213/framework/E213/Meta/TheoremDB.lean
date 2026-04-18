import E213.Meta.ProblemFramework

/-
  213 정리 데이터베이스.

  사용자 요청: "쉬운 문제부터 차근차근. 데이터베이스 쌓기."

  각 정리:
    - ID (순번).
    - 이름.
    - Difficulty (ProblemFramework 기준).
    - Category.
    - Verdict.
    - Path: 어느 framework layer 에서 증명되는지.

  DB 는 append-only. 기존 정리 참조해 새 정리 증명.
  증명 체인: Firmware → Hypervisor → OS → Meta → Applications.

  Difficulty 0-2: Trivial / Firmware 수준.
  Difficulty 3-5: Hypervisor 수준.
  Difficulty 6-10: OS 수준.
  Difficulty 11+: Stream / uncountable.
-/

-- ═══ DB 엔트리 구조 ═══

structure TheoremEntry where
  id : Nat
  name : String
  difficulty : Nat
  category : Category
  verdict : Verdict
  path : String
  deriving Repr

-- ═══ Difficulty 0-1: Trivial Firmware ═══

-- 001. Reflexivity.
theorem thm_001 : ∀ x : Raw, x = x := fun _ => rfl

-- 002. Atom ≠ Rel (diff_inputs 에서).
theorem thm_002 : a₀ ≠ b₀ := a_ne_b

-- 003. Slash 정의.
theorem thm_003 (h : a₀ ≠ b₀) : slash a₀ b₀ h = .rel a₀ b₀ := rfl

-- ═══ Difficulty 2: Firmware 성질 ═══

-- 004. depth 단조.
theorem thm_004 (x y : Raw) (h : x ≠ y) :
    (slash x y h).depth > x.depth :=
  grows_left x y h

-- 005. atom ≠ slash 결과.
theorem thm_005 (x y : Raw) (h : x ≠ y) (i : Fin 3) :
    slash x y h ≠ .atom i := atom_is_not_made i x y h

-- 006. v3_injective.
theorem thm_006 (a b c d : Raw) (h1 : a ≠ b) (h2 : c ≠ d) :
    slash a b h1 = slash c d h2 → a = c ∧ b = d :=
  v3_injective _ _ _ _ h1 h2

-- ═══ Difficulty 3: Reachable ═══

-- 007. 원자는 Reachable.
theorem thm_007 : Reachable a₀ := .atom 0

-- 008. ab₀ 은 Reachable.
theorem thm_008 : Reachable ab₀ := by decide

-- 009. rel x x 는 Reachable 아님.
theorem thm_009 (x : Raw) : ¬ Reachable (.rel x x) :=
  no_self_rel_reachable x

-- ═══ Difficulty 4: Hypervisor / Lens ═══

-- 010. Lens.id' view = id.
theorem thm_010 (x : Raw) : Lens.id'.view x = x :=
  lens_id_view x

-- 011. Lens kernel 은 동치관계 (refl).
theorem thm_011 {α : Type} (L : Lens α) (x : Raw) :
    L.equiv x x := L.equiv_refl x

-- 012. Pair view 분해.
theorem thm_012 {α β : Type} (L : Lens α) (M : Lens β) (x : Raw) :
    (L.pair M).view x = (L.view x, M.view x) := pair_view L M x

-- ═══ Difficulty 5: OS / Peano ═══

-- 013. Peano Zero ≠ Succ.
theorem thm_013 (n : Nat213) : Nat213.zero ≠ Nat213.succ n :=
  Nat213.zero_ne_succ n

-- 014. Peano zero_add.
theorem thm_014 (n : Nat213) : Nat213.zero + n = n :=
  Nat213.zero_add n

-- 015. Peano add_zero.
theorem thm_015 (n : Nat213) : n + Nat213.zero = n :=
  Nat213.add_zero n

-- ═══ Difficulty 6: OS / Logic ═══

-- 016. ⊥ → ⊤ tautology.
theorem thm_016 : (Prop213.imp .fls .tru).isTautology := by decide

-- 017. ⊤ → ⊥ 은 tautology 아님.
theorem thm_017 : ¬ (Prop213.imp .tru .fls).isTautology := by decide

-- ═══ Difficulty 7: OS / Set ═══

-- 018. emptySet 은 singleB 의 부분집합.
theorem thm_018 : emptySet.subsetOfSet singleB := by decide

-- 019. Set equality: 순서 무관.
theorem thm_019 : pairBC ≡s pairBC' := by decide

-- ═══ Difficulty 8: Meta ═══

-- 020. Independent → ¬ RespectsLens.
theorem thm_020 {α : Type} (L : Lens α) (φ : Raw → Prop) :
    IndependentIn L φ → ¬ RespectsLens L φ :=
  independent_iff_not_respects L φ

-- 021. Commutative h → not injective.
theorem thm_021 {α : Type} (g : Fin 3 → α) (h : α → α → α)
    (hcomm : ∀ a b, h a b = h b a) :
    ¬ Function.Injective (Raw.fold g h) :=
  fold_not_injective_of_comm g h hcomm

-- ═══ Difficulty 9-10: Rule Hierarchy ═══

-- 022. Level 3 유한.
theorem thm_022 : Fintype.card Level3Raw = 12 := Thm_R3_finite

-- 023. R3 제거 → 무한 단사 불가.
theorem thm_023 (f : Fin 13 → Level3Raw) : ¬ Function.Injective f :=
  Thm_R3_no_infinite_injection f

-- ═══ DB registry ═══

def theoremDB : List TheoremEntry := [
  ⟨1, "reflexivity", 0, .decided, .provable, "rfl"⟩,
  ⟨2, "atom distinctness", 0, .decided, .provable,
   "Fin 3 DecidableEq"⟩,
  ⟨3, "slash definition", 1, .decided, .provable, "rfl"⟩,
  ⟨4, "depth monotone", 2, .decided, .provable,
   "Firmware/Properties"⟩,
  ⟨5, "atom ≠ rel", 2, .decided, .provable,
   "atom_is_not_made"⟩,
  ⟨6, "slash injective", 2, .decided, .provable, "v3_injective"⟩,
  ⟨7, "atom reachable", 3, .decided, .provable, "Reachable.atom"⟩,
  ⟨8, "ab₀ reachable", 3, .decided, .provable, "decide"⟩,
  ⟨9, "no self rel", 3, .decided, .provable,
   "no_self_rel_reachable"⟩,
  ⟨10, "lens id view", 4, .decided, .provable, "lens_id_view"⟩,
  ⟨11, "lens equiv refl", 4, .decided, .provable, "kernel refl"⟩,
  ⟨12, "pair view", 4, .decided, .provable, "pair_view"⟩,
  ⟨13, "Peano 0 ≠ succ", 5, .decided, .provable,
   "Nat213.zero_ne_succ"⟩,
  ⟨14, "Peano zero_add", 5, .decided, .provable, "rfl"⟩,
  ⟨15, "Peano add_zero", 5, .decided, .provable, "induction"⟩,
  ⟨16, "⊥ → ⊤ tautology", 6, .decided, .provable, "decide"⟩,
  ⟨17, "¬(⊤ → ⊥) taut", 6, .decided, .provable, "decide"⟩,
  ⟨18, "∅ ⊆ {b}", 7, .decided, .provable, "decide"⟩,
  ⟨19, "set perm eq", 7, .decided, .provable, "List.Perm"⟩,
  ⟨20, "indep → ¬respects", 8, .decided, .provable,
   "Provability.lean"⟩,
  ⟨21, "comm h not inj", 8, .decided, .provable,
   "FoldInjective"⟩,
  ⟨22, "Level 3 card 12", 9, .decided, .provable,
   "RuleHierarchy"⟩,
  ⟨23, "R3 removal pigeon", 10, .decided, .provable,
   "Fintype.card_le"⟩
]

-- ═══ Query 함수 ═══

def theoremDB.count : Nat := theoremDB.length

def theoremDB.byDifficulty (d : Nat) : List TheoremEntry :=
  theoremDB.filter (fun e => e.difficulty = d)

def theoremDB.maxDifficulty : Nat :=
  theoremDB.foldl (fun acc e => max acc e.difficulty) 0

-- 검증.
example : theoremDB.count = 23 := by decide
example : theoremDB.maxDifficulty = 10 := by decide

-- ═══ Difficulty 8: Applications (ARFM, SST) ═══

-- 024. ARFM anti-reflexive.
theorem thm_024 (x : Raw) : ¬ Reachable (.rel x x) :=
  arfm_anti_reflexive x

-- 025. SST antisymmetry.
theorem thm_025 (x y : Raw) :
    Lens.signed.view (Raw.rel x y) = - Lens.signed.view (Raw.rel y x) :=
  sst_antisym x y

-- 026. SST self-cancel.
theorem thm_026 (x : Raw) : Lens.signed.view (Raw.rel x x) = 0 :=
  sst_self_cancel x

-- 027. Z3 group computation.
theorem thm_027 : Lens.Z3.view (Raw.rel a₀ b₀) = ⟨1, by decide⟩ :=
  by decide

-- 028. Raw ∞ depth (모든 n 에 존재).
theorem thm_028 (n : Nat) : ∃ x, Reachable x ∧ x.depth = n :=
  raw_has_arbitrary_depth n

-- ═══ Difficulty 11-14: Stream / Continuum ═══

-- 029. RealPath 존재 (trivial).
theorem thm_029 : ∃ r : RealPath, True := ⟨fun _ => false, trivial⟩

-- 030. r_ones ≡ r_half under firstBit lens.
theorem thm_030 : StreamLens.firstBit.equiv r_ones r_half := by
  unfold StreamLens.equiv StreamLens.firstBit
  simp [r_ones, r_half]

-- 031. 그러나 prefixN 2 에서는 다름.
theorem thm_031 : ¬ (StreamLens.prefixN 2).equiv r_ones r_half := by
  unfold StreamLens.equiv StreamLens.prefixN
  simp [r_ones, r_half, List.range]
  decide

-- 032. RH 명제 존재 (unknown verdict).
theorem thm_032 : Prop := RH_stream

-- ═══ Category 구조 ═══

-- 033. Lens refines reflexivity.
theorem thm_033 {α : Type} (L : Lens α) : L.refines L :=
  Lens.refines_refl L

-- 034. Pair refines left.
theorem thm_034 {α β : Type} (L : Lens α) (M : Lens β) :
    (L.pair M).refines L :=
  Lens.pair_refines_left L M

-- 035. Pair universal.
theorem thm_035 {α β γ : Type} (L : Lens α) (M : Lens β) (N : Lens γ)
    (hL : N.refines L) (hM : N.refines M) :
    N.refines (L.pair M) :=
  Lens.pair_universal L M N hL hM

-- ═══ AxiomaticSystem 인스턴스 (Meta) ═══

-- 036. PA profile 은 full.
theorem thm_036 : profile_PA = AxiomProfile.full := rfl

-- 037. Russell profile 은 R5 off.
theorem thm_037 : profile_Russell.r5 = false := rfl

-- 038. activeCount: PA=6, Russell=5, empty=0.
theorem thm_038 :
    profile_PA.activeCount = 6 ∧
    profile_Russell.activeCount = 5 ∧
    AxiomProfile.empty.activeCount = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ═══ 확장 DB ═══

def theoremDB_v2 : List TheoremEntry := theoremDB ++ [
  ⟨24, "ARFM anti-refl", 8, .decided, .provable,
   "Applications/ARFM"⟩,
  ⟨25, "SST antisym", 8, .decided, .provable,
   "Applications/SignedSymbol"⟩,
  ⟨26, "SST self-cancel", 8, .decided, .provable,
   "Applications/SignedSymbol"⟩,
  ⟨27, "Z3 group computation", 7, .decided, .provable,
   "OS/Algebra"⟩,
  ⟨28, "Raw ∞ depth", 10, .decided, .provable,
   "Meta/Infinity"⟩,
  ⟨29, "RealPath exists", 11, .decided, .provable, "Stream"⟩,
  ⟨30, "firstBit lens equiv", 11, .decided, .provable,
   "RealLenses"⟩,
  ⟨31, "prefix lens diff", 11, .decided, .provable,
   "RealLenses"⟩,
  ⟨32, "RH stream statement", 14, .unknown, .unknown,
   "RiemannPosition"⟩,
  ⟨33, "lens refl", 4, .decided, .provable, "Category"⟩,
  ⟨34, "pair refines left", 5, .decided, .provable, "Category"⟩,
  ⟨35, "pair universal", 6, .decided, .provable, "Category"⟩,
  ⟨36, "PA profile full", 8, .decided, .provable, "AxiomAxisMap"⟩,
  ⟨37, "Russell R5 off", 8, .decided, .provable, "AxiomAxisMap"⟩,
  ⟨38, "profile counts", 8, .decided, .provable, "AxiomAxisMap"⟩
]

example : theoremDB_v2.length = 38 := by decide

-- 최고 Difficulty.
def theoremDB_v2.maxDifficulty : Nat :=
  theoremDB_v2.foldl (fun acc e => max acc e.difficulty) 0

example : theoremDB_v2.maxDifficulty = 14 := by decide
