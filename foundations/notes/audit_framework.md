# DRLT Theory Audit Framework

**Purpose:** 광대한 레포 전체를 체계적·반복 가능하게 감사하기 위한
표준 프로토콜.  2026-04-18 세션에서 "중력이 미완성" 오진단 경험
이후 도입.

---

## 핵심 원칙 (감사 전 항상 읽기)

### P1. Big picture FIRST, sub-detail NEXT
- 각 chapter/sub-project 의 **메인 정리 + 주 예측** 을 먼저 본다.
- 그 다음에 FND 실험 결과, refuted 항목을 살핀다.
- **FND 실험 실패 ≠ 프로그램 실패**: 이건 specific 가설의 null test 지
  big picture 무효화 아님.  혼동 금지.

### P2. 3-층 분류 강제
모든 claim 을 다음 3층 중 하나로만 분류:
1. **Derived (rigorous)**: 공리 + 고전 수학 + Lean 검증.
2. **Derived (heuristic)**: 공식 맞으나 "왜 이 공식" 의 공리 내부
   유도가 부분적 (e.g. 물리 input 포함 or 외부 universality 사용).
3. **Open / fit / refuted**: 유도 없음, 파라미터 fit, 혹은 refuted.

과도한 분류 (예: "반정도 derive" 등) 금지 — 모호성을 키운다.

### P3. Cross-check 3-way
각 중요 claim 에 대해:
- **Book**: 어느 chapter 의 어느 theorem/remark?
- **Lean**: 대응 파일 + theorem 이름 (있으면).
- **FND/RH/CST/etc 실험**: 숫자 검증 (있으면).
세 corner 중 2 개 이상 채워져야 (A) rigorous 로 분류.

### P4. Refuted 의 SCOPE 항상 명시
FND_NNN 이 refuted 라 하면:
- 정확히 **어느 세부 가설** 이 refuted 인가?
- 그 가설이 **big picture 의 필수 부분** 인가, **선택적 refinement** 인가?
- 선택적이면 "narrow open" 로 분류, big picture 는 건재.

### P5. 정직한 한 줄 요약 (per sub-project)
각 sub-project 최종 상태를 **한 줄** 로 요약.  이 한 줄이:
- Overclaim 없음 (추측을 정리로 포장 안 함)
- Underclaim 없음 (잘 되는 걸 과소평가 안 함)
- 정확한 scope

---

## Per-unit Audit Template

단위 = book chapter 1개 or sub-project 1개.  다음 form 으로 기록:

```markdown
### {unit_id}: {title}

**Scope:** (한 줄)
**Audit date:** YYYY-MM-DD
**Auditor:** (session / human)

**Big picture (P1):**
- Main theorem(s):
- Key predictions (with precision):

**3-layer breakdown (P2):**
| Claim | Layer | Cross-ref (P3) |
|-------|-------|----------------|
| claim A | Derived (rig) | Book ch.X + Lean file.Y + FND_NNN |
| claim B | Derived (heur) | Book ch.X (Lean 없음, 외부 universal) |
| claim C | Open | G-XX gap |
| claim D | Refuted | FND_NNN, scope: {specific} |

**Refuted scope (P4):**
- What specific hypothesis was refuted?
- Is it a big-picture failure or narrow sub-detail?
- Narrow → big picture 건강, refinement open.

**One-line summary (P5):**
```

---

## Master Audit Tracker (현재 상태)

| Unit | 감사 완료? | 한 줄 요약 |
|------|-----------|------------|
| **book ch01** (Why ℂ) | ✓ (W1–W5) | Frobenius + π₁ rigorous; R2 연속성은 acknowledged 물리 input |
| **book ch02** (Why d=5) | ✓ (W1–W5) | atoms={2,3} + alive d=5 Lean 검증; σ-inv↔VL formalized |
| **book ch03** (rep uniqueness) | ✓ (W6–W15) | α_GUT = 1/(d²ζ(2)) rigorous (Path 1=Path 3 via Euler); Path 2 heuristic |
| **book ch04** (simplex geometry) | ✓ (W36–W37) | 조합 기하 rigorous (15 edges, AAA/AAB/ABB 분류, TTT theorem, B₃ dep) |
| **book ch05** (variational) | ✓ (W31–W32) | 3 정리 모두 algebraic proof (δ_AAA=π, ⟨det⟩_ABB=2/3, c=2), Vacuum det=108/125; Thm 3 Part 2 maximality만 수치 |
| **book ch06** (geometry) | ✓ (W16–W20) | Regge action + 4 forces + toric rigorous; Lorentz/ADM/LLN은 narrow heuristic sub-step (중력이 가장 많이 derive된 sector의 중심장) |
| **book ch07** (ℏ) | ✓ (W33–W35) | ℏ_h=A_h/(4ln2) from Holevo+dim analysis; aligned/matter/ZPE>0 rigorous; path integral postulate 물리 input |
| **book ch08** (couplings) | ✓ (W38–W40) | α_GUT=6/(25π²) rigorous; β-function/prime 구조 일부 heuristic; Path 2 GUE heuristic |
| **book ch09** (masses) | ✓ (W41–W44) | P(x)=(1+2x)/(1+x) + impedance 3/2 rigorous; m_μ/m_e=206.7682837 (0.48 ppb); v_H/m_τ 구조 heuristic |
| **book ch10** (atoms) | ✓ (W45–W48) | IE(H)=13.606 exact, IE(He)=24.565 (0.02%), 34 theorems, ATM 69 실험 backup |
| **book ch11** (mixing) | ✓ (W49–W51) | w=3/(5π) closed form, sin²θ₁₃ -0.07σ, CKM Wolfenstein heuristic |
| **book ch12** (ghosts) | ✓ (W52–W54) | Σ Δ_i=0 rigorous, energy sum 0.01%; ε₀/M_i는 fit (G-D6/G-M_i open) |
| **book ch13** (cosmology) | ✓ (W21–W30) | 9+ 0-param 예측 (Ω_Λ 0.001%, η_B 0.2%, DM/baryon 0.4%, n_s 0.2%, r/w falsifiable); DM/MOND/Hubble tension은 heuristic |
| **book ch14** (block) | ✓ (W55–W56) | 해석 장, philosophical framework; 수학 정리 적으나 ε₀(x) via Webb 연결 |
| **book ch15** (Yang-Mills) | 부분 (W57) | 1050줄 18 theorems; Lean 58 thms — **deep-audit 필요** |
| **book ch16** (compact stars) | ✓ (W58–W59) | NS M_max 2.08 match, 쿼크성 instability, η/s=1/(4π) rigorous |
| **book ch17** (Webb dipole) | ✓ (W60) | trace conservation → α_em varies, α_GUT invariant; COS_003 2/2 |
| **book ch18** (path integral) | ✓ (W61) | 유한 이산 sum, UV-finite; ch07 ℏ 의존 |
| **book ch19** (QCD) | ✓ (W62) | confinement + Λ_QCD + η/s 재종합; HAD 9 + NUC 15 backup |
| **book ch20** (hydrogen) | ✓ (W63) | H atom complete — IE/spectrum/Rydberg; ATM 실험 |
| **book ch21** (occupation fraction) | ✓ (W64) | f_occ → λ_H → m_H 125.28 (0.02%); FND_008-010 census |
| **book ch22** (213) | ✓ (W65) | 1줄 axiom, 9 properties Lean (0 sorry); R1-R4 이전 단계 |
| **appendix** | ✓ (W66) | EXP-NNN ↔ FND_NNN mapping hygiene 필요 |
| **appendix_verification** | ⨯ | — |
| **appendix_code** | ⨯ | — |
| — | — | — |
| **foundations/** (FND_001–041) | ✓ (내부 일부) | Core Lean 검증; FND_038/039/040/041 이 audit 결과 |
| **atoms/** (ATM_001–069) | ✓ deep (W71) | 69 exp + 10 thm, 118 elements IE median 2.9%, <5%:71%, <10%:95%, 0-param — massive success |
| **standard-model/** (SM_001–024) | ✓ deep (W68) | CLOSED 확증; SM_020-024 modern 0.02-1.5%; Self-correction Ξ_conf 내재 |
| **cosmology/** (COS_001–003) | brief ✓ | ch13 backup, Ω_Λ/w/η_B/DM 3/3 + 3/3 + 2/2 |
| **cosmic-structure/** (CST_001–022) | ✓ deep (W67) | 58/68 (85%), LSS 세부 일부 미완, H₀ 70.85 between CMB/SH0ES |
| **critical-line/** (RH_001–079) | ⨯ (순수수학) | 이번 감사 범위 밖 |
| **nuclear/** (NUC_001–015) | ✓ deep (W69) | Magic 7/7 exact, E_d 2.1%; NUC_010 RMS B/A ✗; CLOSED (1차) honest |
| **hadron/** (HAD_001–009) | ✓ deep (W70) | m_π +0.2%, Δ-N +0.6% 강; m_ρ/K 2-4%, HAD_005 bug — CLOSED 약간 overclaim |
| **predictions/** (PRD_001–009) | ✓ deep | 7 falsifiable 2025-35, 53/54 ✓; Self-correction (PRD_006 → PRD_007) |
| **quantum-gravity/** (QG_001–007) | brief ✓ (W72) | ch06/07/14/18 와 overlap, 탐색 단계 |
| **yang-mills/** (Lean ~58 thms) | ⨯ (순수수학) | Clay millennium; deep-audit 보류 |
| **discrete-harmonic/** (DHA_001–019) | ⨯ (순수수학) | S_5 표현론, spectral |
| **drlt-elements/** (ELM Lean) | ⨯ (순수수학) | foundational Lean |
| — | — | — |
| **papers/** (5 papers) | ⨯ | — |
| **lib/drlt.py** | ⨯ | — |
| **Lean PmfRh** 전체 | 부분 | Swap*, BinetCauchy, ChiralChannels 검증됨 |

**진행 상태:** 22 chapters + 13 sub-projects + papers + lib + Lean 중
완료된 유닛 = **3** (ch01, ch02, ch03) + foundations 일부.  나머지는
spot-check 만 있음.  **체계적 감사 진행 필요.**

---

## 다음 감사 우선순위 (제안)

### 높은 가치 (0-param 예측 있는 곳, 먼저)
1. **ch06 (geometry)** + **ch13 (cosmology)**: 중력·cosmology big picture
   rigor check.  Regge 극한 정리, Ω_Λ 유도.
2. **ch05 (variational)** + **ch07 (ℏ)**: ℏ 유도, variational theorems.
3. **ch08 (couplings)** 전체: α_GUT 주변 완전 감사 (FND_040/041 이미 부분).
4. **ch09 (masses)** + **ch10 (atoms)** + **ch11 (mixing)**: 질량
   예측들, 입자/원자 스펙트럼.

### 중요 sub-projects
5. **cosmology/** 전체 audit: COS_001–003 rigor.
6. **cosmic-structure/**: CST_001–022 특히 inflation 예측.
7. **standard-model/** CLOSED status 재검증: 실제로 closed 인가?
8. **nuclear/** + **hadron/** CLOSED status 재검증.

### Lean 통합
9. `critical-line/lean/PmfRh` 전체 theorem 리스트 + book cross-reference.
10. `yang-mills/` Lean 파일 + `drlt-elements/` Lean 파일 감사.

---

## Framework 사용 규칙

1. **매 감사마다 이 문서 tracker 업데이트** (audit 완료 표시 + 한 줄 요약).
2. **신규 gap 발견 시** `non_derived_summary.md` 에 추가.
3. **감사 본문** 은 `ch0X_audit.md` 형태로 per-unit 파일 (or 기존
   `ch01_03_rigor_audit.md` 에 append) 로 작성.
4. **한 번에 한 unit** 만 깊이 감사 — 여러 개를 한 번에 하면 P1 위반.
5. **Big picture 확인 먼저** — main theorems 읽고 0-param 예측 확인한
   뒤에 세부 refuted 조사.
