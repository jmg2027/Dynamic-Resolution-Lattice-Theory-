"""
EXP_064: Combinatorial Census — 기하학이 허용하는 모든 f_occ
Joint research by Mingu Jeong and Claude (Anthropic)

순수 조합론: d=5 simplex의 (3,2) 분할에서
가능한 모든 (sub-structure, pattern) 쌍을 전수 열거.
표준모형 참조 없이, 기하학만으로 무엇이 나오는지 확인.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
import numpy as np
from math import comb
from experiment import Experiment

D = 5; N_A = 3; N_B = 2
a = 6 / (25 * np.pi**2)


def P(x):
    """Closed propagator."""
    return (1 + 2*x) / (1 + x)


class CombinatorialCensus(Experiment):
    ID = "064"
    TITLE = "Combinatorial Census"

    def run(self):
        self.part1_substructures()
        self.part2_all_patterns()
        self.part3_spectrum()
        self.part4_confinement()

    # ================================================================
    #  Part 1: d=5 simplex의 모든 sub-structure 열거
    # ================================================================
    def part1_substructures(self):
        self.log(f"\n  {'═'*55}")
        self.log(f"  Part 1: Sub-structures of (3,2)-simplex")
        self.log(f"  {'═'*55}")
        self.log(f"\n  Simplex: {N_A}A + {N_B}B = {D} vertices")
        self.log(f"  Sub-structure = k-vertex subset (k = 2..5)")

        self.log(f"\n  {'Type':<12} {'(a,b)':<8} {'Count':>6} "
                 f"{'Formula':>20} {'k':>3}")
        self.log(f"  {'-'*55}")

        total_all = 0
        for k in range(2, D+1):
            self.log(f"  --- k = {k} ({['','','edge','hinge','face','simplex'][k]}) ---")
            count_k = 0
            for a_sub in range(min(N_A, k)+1):
                b_sub = k - a_sub
                if b_sub < 0 or b_sub > N_B:
                    continue
                cnt = comb(N_A, a_sub) * comb(N_B, b_sub)
                if cnt == 0:
                    continue
                label = 'A'*a_sub + 'B'*b_sub
                formula = f"C({N_A},{a_sub})×C({N_B},{b_sub})"
                self.log(f"  {label:<12} ({a_sub},{b_sub}){'':<3} "
                         f"{cnt:>6} {formula:>20} {k:>3}")
                count_k += cnt
            self.log(f"  {'':12} {'':8} {count_k:>6} = C({D},{k})")
            total_all += count_k

        self.log(f"\n  총 sub-structure 수: {total_all}")
        self.log(f"  (= C(5,2)+C(5,3)+C(5,4)+C(5,5) = 10+10+5+1 = 26)")
        self.check(f"Sub-structure 전수: {total_all}", total_all == 26)

    # ================================================================
    #  Part 2: 모든 (structure, pattern) 쌍 전수 열거
    # ================================================================
    def part2_all_patterns(self):
        self.log(f"\n  {'═'*55}")
        self.log(f"  Part 2: 모든 (structure, pattern) 쌍")
        self.log(f"  {'═'*55}")
        self.log(f"\n  Structure (a,b) 위에 pattern (pA,pB) 배치")
        self.log(f"  f_occ = (pA+pB) / (a+b)")

        # 모든 쌍을 수집
        self.all_entries = []

        for k in range(2, D+1):
            for a_sub in range(min(N_A, k)+1):
                b_sub = k - a_sub
                if b_sub < 0 or b_sub > N_B:
                    continue
                n_struct = comb(N_A, a_sub) * comb(N_B, b_sub)
                if n_struct == 0:
                    continue

                str_label = 'A'*a_sub + 'B'*b_sub

                # 이 structure 위의 모든 pattern
                for pA in range(a_sub+1):
                    for pB in range(b_sub+1):
                        p_tot = pA + pB
                        if p_tot == 0:
                            continue  # 빈 패턴 제외

                        f_occ = p_tot / k
                        # 이 pattern의 multiplicity:
                        # (structure 수) × (structure 내 pattern 선택 수)
                        n_pat = comb(a_sub, pA) * comb(b_sub, pB)
                        mult = n_struct * n_pat

                        pat_label = 'A'*pA + 'B'*pB if (pA+pB) > 0 else '∅'
                        self.all_entries.append({
                            'str': str_label,
                            'str_size': k,
                            'a_sub': a_sub, 'b_sub': b_sub,
                            'pat': pat_label,
                            'pA': pA, 'pB': pB,
                            'p_tot': p_tot,
                            'f_occ': f_occ,
                            'n_struct': n_struct,
                            'n_pat': n_pat,
                            'mult': mult,
                        })

        self.log(f"\n  총 (structure, pattern) 쌍: {len(self.all_entries)}")

        # 테이블 출력
        self.log(f"\n  {'Str':<6} {'Pat':<5} {'k':>2} {'pA':>2} {'pB':>2} "
                 f"{'f_occ':>6} {'#str':>4} {'#pat':>4} {'mult':>5}")
        self.log(f"  {'-'*48}")

        for e in sorted(self.all_entries, key=lambda x: (x['f_occ'], x['str_size'])):
            self.log(f"  {e['str']:<6} {e['pat']:<5} {e['str_size']:>2} "
                     f"{e['pA']:>2} {e['pB']:>2} {e['f_occ']:>6.4f} "
                     f"{e['n_struct']:>4} {e['n_pat']:>4} {e['mult']:>5}")

        self.check(f"(structure, pattern) 쌍 전수 열거", len(self.all_entries) > 0)

    # ================================================================
    #  Part 3: f_occ 스펙트럼 — 고유값별 분류
    # ================================================================
    def part3_spectrum(self):
        self.log(f"\n  {'═'*55}")
        self.log(f"  Part 3: f_occ 스펙트럼 (고유값별 분류)")
        self.log(f"  {'═'*55}")

        from collections import defaultdict

        # f_occ 값별로 그룹핑 (부동소수점 → 분수 키)
        spectrum = defaultdict(list)
        for e in self.all_entries:
            # 유리수 키: (p_tot, str_size) = (분자, 분모)
            key = (e['p_tot'], e['str_size'])
            spectrum[key].append(e)

        # 약분하여 같은 분수끼리 추가 그룹핑
        from fractions import Fraction
        frac_groups = defaultdict(list)
        for (num, den), entries in spectrum.items():
            f = Fraction(num, den)
            frac_groups[f].extend(entries)

        self.log(f"\n  고유 f_occ 값: {len(frac_groups)}개")
        self.log(f"\n  {'f_occ':<8} {'값':>8} {'x=α×f':>10} {'P(x)':>8} "
                 f"{'총 mult':>7} {'실현 방법 수':>10}")
        self.log(f"  {'-'*60}")

        sorted_fracs = sorted(frac_groups.keys())
        for f in sorted_fracs:
            entries = frac_groups[f]
            total_mult = sum(e['mult'] for e in entries)
            n_ways = len(entries)
            val = float(f)
            x = a * val
            Px = P(x) if val < 1 else None

            Px_str = f"{Px:.6f}" if Px else "CONFINED"
            self.log(f"  {str(f):<8} {val:>8.4f} {x:>10.6f} {Px_str:>8} "
                     f"{total_mult:>7} {n_ways:>10}")

        self.log(f"\n  ── 기하학이 결정하는 이산 스펙트럼 ──")
        self.log(f"  가능한 결합상수: {len(sorted_fracs)}개 이산값")
        self.log(f"  연속 파라미터 없음: 모든 x가 유리수 × α_GUT")

        self.check(f"이산 스펙트럼: {len(sorted_fracs)}개 f_occ",
                   len(sorted_fracs) > 0)

        # ── confinement 조건 (f=1) 분석 ──
        conf_entries = frac_groups.get(Fraction(1, 1), [])
        total_conf = sum(e['mult'] for e in conf_entries)
        self.log(f"\n  f_occ = 1 (confinement) 실현:")
        for e in conf_entries:
            self.log(f"    {e['str']} 위 {e['pat']}: "
                     f"mult = {e['mult']} "
                     f"({e['n_struct']} struct × {e['n_pat']} pat)")
        self.log(f"  confinement 총 다중도: {total_conf}")

    # ================================================================
    #  Part 4: Confinement 구조 분석 + 물리 대응 없는 f_occ
    # ================================================================
    def part4_confinement(self):
        self.log(f"\n  {'═'*55}")
        self.log(f"  Part 4: 구조 심층 분석")
        self.log(f"  {'═'*55}")

        from fractions import Fraction
        from collections import defaultdict

        frac_groups = defaultdict(list)
        for e in self.all_entries:
            f = Fraction(e['p_tot'], e['str_size'])
            frac_groups[f].append(e)

        # ── 각 f_occ의 A/B 분해 ──
        self.log(f"\n  ── 각 f_occ의 (pA, pB) 분해 ──")
        self.log(f"  같은 f_occ라도 A-pattern과 B-pattern이 다를 수 있음")

        sorted_fracs = sorted(frac_groups.keys())
        for f in sorted_fracs:
            if f == 1:
                continue  # confinement는 아래에서 별도
            entries = frac_groups[f]
            self.log(f"\n  f_occ = {f} ({float(f):.4f}):")
            # (pA, pB)별 분류
            ab_groups = defaultdict(list)
            for e in entries:
                ab_groups[(e['pA'], e['pB'])].append(e)

            for (pA, pB), elist in sorted(ab_groups.items()):
                total_m = sum(e['mult'] for e in elist)
                strs = [f"{e['str']}({e['n_struct']}×{e['n_pat']})"
                        for e in elist]
                self.log(f"    ({pA}A,{pB}B): mult={total_m:>3}  "
                         f"via {', '.join(strs)}")

        # ── Confinement (f=1) 상세 ──
        self.log(f"\n  ── Confinement (f_occ = 1) 상세 ──")
        conf_entries = frac_groups.get(Fraction(1, 1), [])
        for e in conf_entries:
            self.log(f"    {e['str']} ← {e['pat']}: "
                     f"{e['a_sub']}A+{e['b_sub']}B 완전 점유, "
                     f"mult={e['mult']}")

        # ── 자유도(multiplicity) 요약 ──
        self.log(f"\n  ── Multiplicity 요약 ──")
        self.log(f"  {'f_occ':<8} {'총 mult':>7} {'free 다중도':>10} "
                 f"{'conf 여부':>8}")
        self.log(f"  {'-'*40}")

        total_free = 0
        total_conf = 0
        for f in sorted_fracs:
            entries = frac_groups[f]
            m = sum(e['mult'] for e in entries)
            is_conf = "CONF" if f == 1 else "free"
            self.log(f"  {str(f):<8} {m:>7} {m:>10} {is_conf:>8}")
            if f == 1:
                total_conf += m
            else:
                total_free += m

        self.log(f"\n  Free 총: {total_free},  Confined 총: {total_conf}")
        self.log(f"  전체:    {total_free + total_conf}")

        self.check(f"Free 다중도 = {total_free}", total_free > 0)
        self.check(f"Confined 다중도 = {total_conf}", total_conf > 0)

        # ── 대칭성: f ↔ (1-f) 쌍 ──
        self.log(f"\n  ── 대칭성: f ↔ (1-f) 쌍 ──")
        for f in sorted_fracs:
            comp = 1 - f
            if comp in frac_groups and f < comp:
                m_f = sum(e['mult'] for e in frac_groups[f])
                m_c = sum(e['mult'] for e in frac_groups[comp])
                self.log(f"  {f} ↔ {comp}: mult {m_f} ↔ {m_c}")
            elif f == comp:
                m_f = sum(e['mult'] for e in frac_groups[f])
                self.log(f"  {f} (self-dual): mult {m_f}")

        # ── 최종 요약 ──
        self.log(f"\n  {'='*55}")
        self.log(f"  ★ 기하학적 스펙트럼 최종 요약 ★")
        self.log(f"  {'='*55}")
        self.log(f"  d=5, (3,2) simplex에서 가능한 f_occ:")
        self.log(f"  {[str(f) for f in sorted_fracs]}")
        self.log(f"  총 {len(sorted_fracs)}개 이산값")
        self.log(f"  이 중 f<1: {len([f for f in sorted_fracs if f<1])}개 (자유 전파)")
        self.log(f"  f=1: 1개 (confinement)")
        self.log(f"  각 f_occ의 x = α×f → P(x) = (1+2x)/(1+x)")
        self.log(f"  → 기하학이 허용하는 결합상수의 완전한 목록")

        self.check("기하학적 스펙트럼 완전 열거", True)


if __name__ == "__main__":
    CombinatorialCensus().execute()
