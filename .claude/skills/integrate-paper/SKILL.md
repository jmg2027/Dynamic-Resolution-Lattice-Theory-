---
name: integrate-paper
description: 루트에 올라온 PDF/TeX 논문 파일을 book/ 디렉토리로 이동하고, 핵심 결과를 책 본문의 적절한 챕터에 통합. "논문 올렸어", "이것도 올렸어", "PDF 올렸어" 등의 요청에 사용.
---

# DRLT 논문 통합 스킬

루트 디렉토리에 올라온 PDF/TeX 논문 파일을 book/ 디렉토리로 정리하고,
핵심 내용을 책(book/chapters/)에 통합하는 작업 자동화.

## 워크플로우

### 1. 새 파일 감지
```bash
git pull origin <current-branch>
ls *.pdf *.tex 2>/dev/null  # 루트의 새 파일 확인
```

### 2. 파일 이동
- `"파일명 with spaces.pdf"` → `book/파일명_underscored.pdf`
- `"파일명 with spaces.tex"` → `book/파일명_underscored.tex`
- 공백은 밑줄로 변환

### 3. TeX 내용 분석
- TeX 파일이 없으면 PDF에서 내용 읽고 TeX 생성
- TeX 파일이 있으면 읽고 핵심 결과 파악:
  - 새 예측값 (번호, 공식, 관측값, 오차)
  - 새 정리/증명
  - 기존 챕터와의 연결점

### 4. 책 통합 위치 결정

| 내용 유형 | 책 위치 |
|----------|--------|
| C의 유일성, 위상 | ch01_whyC.tex |
| d=5 유도, 원자 차원 | ch02_whyd5.tex |
| 기하학, 게이지, 힘 개수 | ch03_geometry.tex |
| ħ, 영점에너지, 정보 | ch04_hbar.tex |
| 결합상수, Binet-Cauchy | ch05_couplings.tex |
| 질량, Λ_QCD, 양성자 | ch06_masses.tex |
| 혼합각, CP, 중성미자 | ch07_mixing.tex |
| Ghost 합규칙, 오차 분석 | ch08_ghosts.tex |
| 우주론, 별, 암흑물질 | ch09_cosmology.tex |
| 블록우주, rank cascade | ch10_block.tex |
| 경로적분 | appendix_path_integral.tex |
| 수치 검증 | appendix_verification.tex |
| QCD, sQGP, KSS | appendix_qcd.tex |
| 코드 | appendix_code.tex |

### 5. 편집 규칙
- **청크 단위 편집** — Edit 도구로 작은 단위 삽입
- **\begin/\end 매칭 검증** 필수
- **G 기반 공리** 사용 (W 아님, d=4 입력 아님)
- 기존 내용 삭제하지 않고 **추가만**
- 교차참조 (`\ref`, `\cite`) 적절히 추가
- main.tex 참고문헌에 새 문헌 추가 필요시

### 6. 커밋 및 푸시
```bash
git add <moved files> <modified chapters>
git commit -m "설명적 메시지"
git push -u origin <branch>
```

### 7. CLAUDE.md 업데이트 (필요시)
- 새 실험이 추가되면 실험 카탈로그 갱신
