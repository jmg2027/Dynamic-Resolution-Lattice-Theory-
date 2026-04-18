import E213.Firmware.Axiom

/-
  레이어 위반 검출기.
  각 파일의 import를 분석하여 레이어 경계 준수 확인.
  규칙: 각 레이어는 바로 아래만 import.
-/

-- ═══ 레이어 정의 ═══

inductive Layer where
  | hw | fw | trans | hv | os | meta
  deriving DecidableEq, Repr

def layerOf (path : String) : Layer :=
  if path.containsSubstr "Firmware" then .fw
  else if path.containsSubstr "Translation" then .trans
  else if path.containsSubstr "Hypervisor" then .hv
  else if path.containsSubstr "OS" || path.containsSubstr "Goldbach"
       || path.containsSubstr "Pigeonhole" then .os
  else if path.containsSubstr "Meta" || path.containsSubstr "Test" then .meta
  else .hw

-- ═══ 허용된 의존성 ═══

-- FW → HW (Init). ✓
-- Trans → FW. ✓
-- HV → FW, Trans. ✓
-- OS → HV, Trans, FW. ✓ (FW 직접도 허용?)
-- Meta → 전부. ✓ (분석 도구이므로.)

def canImport (from_ to_ : Layer) : Bool :=
  match from_, to_ with
  | .fw, .hw => true
  | .trans, .fw => true
  | .trans, .hw => true
  | .hv, .fw => true
  | .hv, .trans => true
  | .hv, .hw => true
  | .os, .hv => true
  | .os, .trans => true
  | .os, .fw => true
  | .os, .os => true      -- OS 내부 의존
  | .os, .hw => true
  | .meta, _ => true      -- Meta는 전부 허용
  | _, _ => false

-- ═══ 위반 사례 ═══

-- OS가 직접 Meta를 import하면? 위반.
theorem lint_os_meta : canImport .os .meta = false := by native_decide

-- FW가 OS를 import하면? 위반.
theorem lint_fw_os : canImport .fw .os = false := by native_decide

-- FW가 HV를 import하면? 위반.
theorem lint_fw_hv : canImport .fw .hv = false := by native_decide

-- HV가 OS를 import하면? 위반.
theorem lint_hv_os : canImport .hv .os = false := by native_decide

-- ═══ 정상 사례 ═══

theorem lint_fw_hw : canImport .fw .hw = true := by native_decide
theorem lint_trans_fw : canImport .trans .fw = true := by native_decide
theorem lint_hv_fw : canImport .hv .fw = true := by native_decide
theorem lint_os_hv : canImport .os .hv = true := by native_decide
theorem lint_os_fw : canImport .os .fw = true := by native_decide

-- ═══ 현재 코드베이스 검사 ═══

-- 실제 import 경로를 여기서 검사할 수는 없음 (Lean 메타 불가).
-- 하지만 규칙을 정의함으로써: 외부 린트 도구가 이 규칙 사용 가능.
-- grep "import E213" + layerOf + canImport 조합.

-- ═══ 요약 ═══
-- FW→OS ✗, FW→HV ✗, HV→OS ✗: 하위가 상위 참조 금지.
-- OS→FW ✓: 상위가 하위 참조는 허용 (API 사용).
-- Meta→all ✓: 분석 도구는 전부 볼 수 있음.
