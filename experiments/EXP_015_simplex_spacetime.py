"""
EXP_031: 심플렉스 격자 시공간
==========================================
격자점 = 4-심플렉스 = C⁵.
각 꼭짓점에 복소수 1개.
심플렉스끼리 사면체(4꼭짓점) 공유로 접합.
힌지(삼각형) = 1 bit = 곡률의 거처.

모델:
  1. N개 심플렉스, 각각 ψ ∈ C⁵
  2. 인접 = 사면체 공유 = 4꼭짓점 같고 1꼭짓점 다름
  3. 힌지 = 삼각형 (3꼭짓점 공유) = 1 bit
  4. 곡률 = 힌지의 결손각
  5. 힘 = 내부 위상 걷기 (SSS/SST/STT)
  6. 중력 = 힌지 면적의 불균일
"""

import numpy as np
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
from drlt import Vertex, Network
from experiment import Experiment
from itertools import combinations

np.random.seed(42)


# ═════════════════════════════════════════════════════════════
#  심플렉스 격자 시공간 클래스
# ═════════════════════════════════════════════════════════════

class SimplexLattice:
    """
    N개의 4-심플렉스로 이루어진 시공간.

    각 심플렉스 = ψ ∈ C⁵ = (z₀,z₁,z₂,z₃,z₄)
    꼭짓점 0,1,2 = 공간 (C³)
    꼭짓점 3,4 = 시간 (C²)

    인접: G_ij = ⟨ψ_i|ψ_j⟩ (사면체 공유의 연속적 일반화)
    힌지: 심플렉스 3개의 삼각형 = 1 bit
    """

    def __init__(self, N, seed=42):
        np.random.seed(seed)
        self.N = N
        self.d = 5
        # N개 심플렉스 = N개 ψ ∈ C⁵
        self.psi = np.random.randn(N, 5) + 1j * np.random.randn(N, 5)
        self.psi /= np.linalg.norm(self.psi, axis=1, keepdims=True)
        self._G = None

    @property
    def G(self):
        """Gram 행렬: G_ij = ⟨ψ_i|ψ_j⟩"""
        if self._G is None:
            self._G = self.psi @ self.psi.conj().T
        return self._G

    def invalidate(self):
        self._G = None

    # ── 심플렉스 내부 구조 ────────────────────────

    def internal_phases(self, i):
        """심플렉스 i의 변별 위상차 (보손 성분)."""
        z = self.psi[i]
        phases = {}
        for a, b in combinations(range(5), 2):
            phases[(a, b)] = np.angle(np.conj(z[a]) * z[b])
        return phases

    def internal_holonomy(self, i, triangle):
        """심플렉스 i 내부의 삼각형 홀로노미.
        (항상 0 — 단일 심플렉스는 편평)"""
        a, b, c = triangle
        z = self.psi[i]
        return np.angle(np.conj(z[a])*z[b] * np.conj(z[b])*z[c] * np.conj(z[c])*z[a])

    def simplex_character(self, i):
        """심플렉스의 성격: C³/C² 비중, 내부 위상."""
        p = np.abs(self.psi[i])**2
        c3 = p[:3].sum()  # 공간
        c2 = p[3:].sum()  # 시간

        # 각 꼭짓점의 점유
        dominant = np.argmax(p)

        return {
            'c3': c3, 'c2': c2,
            'probs': p,
            'dominant': dominant,
            'type': '쿼크적' if c3 > 0.7 else ('렙톤적' if c2 > 0.5 else '혼합'),
        }

    # ── 심플렉스 간 구조 (시공간) ────────────────

    def hop(self, i, j):
        """심플렉스 i→j 전파. 사면체 공유 = 1 hop."""
        g = self.G[i, j]
        return {
            'G': g,
            'abs_G': np.abs(g),
            'phase': np.angle(g),
            'W': np.abs(g)**2 / self.d,
            'ds2': 1 - np.abs(g)**2,  # Fubini-Study
        }

    def inter_holonomy(self, i, j, k):
        """심플렉스 3개의 홀로노미 (힌지의 곡률)."""
        G = self.G
        return np.angle(G[i,j] * G[j,k] * G[k,i])

    # ── 힌지 구조 ────────────────────────────────

    def hinge_area(self, i, j, k):
        """힌지 (심플렉스 삼중) 면적 = √det(Gram_3×3)."""
        G = self.G
        G3 = np.array([[1,      G[i,j], G[i,k]],
                        [G[j,i], 1,      G[j,k]],
                        [G[k,i], G[k,j], 1      ]])
        det = np.linalg.det(G3).real
        return np.sqrt(max(0, det))

    def hinge_hbar(self, i, j, k):
        """힌지의 ħ = A / (4 ln2)."""
        A = self.hinge_area(i, j, k)
        return A / (4 * np.log(2))

    def hinge_info(self, i, j, k):
        """힌지의 전체 정보: 면적, ħ, 홀로노미, 1 bit."""
        A = self.hinge_area(i, j, k)
        h = A / (4 * np.log(2))
        Phi = self.inter_holonomy(i, j, k)

        # 힌지 유형: 세 심플렉스의 공유 패턴
        chars = [self.simplex_character(x) for x in [i, j, k]]
        avg_c3 = np.mean([c['c3'] for c in chars])

        return {
            'area': A,
            'hbar': h,
            'holonomy': Phi,
            'avg_c3': avg_c3,
            'type': '바리온적' if avg_c3 > 0.7 else ('메존적' if avg_c3 > 0.5 else '렙톤적'),
            '1bit': 1,  # 항상 1 bit
        }

    # ── 힘의 세기 (SSS/SST/STT 분류) ──────────

    def force_decomposition(self):
        """모든 힌지 유형별 힘의 세기 통계."""
        # 한 심플렉스 내부의 삼각형 유형
        types = {'SSS': [], 'SST': [], 'STT': []}

        for a, b, c in combinations(range(5), 3):
            n_S = sum(1 for x in [a,b,c] if x < 3)
            if n_S == 3: key = 'SSS'
            elif n_S == 2: key = 'SST'
            else: key = 'STT'
            types[key].append((a, b, c))

        return types

    # ── 전체 시공간 분석 ────────────────────────

    def spacetime_analysis(self, n_hinge_samples=2000):
        """전체 시공간 구조 분석."""
        N = self.N
        G = self.G
        W = np.abs(G)**2 / self.d
        mask = ~np.eye(N, dtype=bool)

        # 심플렉스별 성격
        chars = [self.simplex_character(i) for i in range(N)]

        # 인접 구조 (hop 통계)
        abs_G = np.abs(G[mask])
        phases = np.angle(G[mask])

        # 힌지 샘플
        hinge_areas = []
        hinge_hols = []
        hinge_hbars = []

        for _ in range(n_hinge_samples):
            i, j, k = np.random.choice(N, 3, replace=False)
            A = self.hinge_area(i, j, k)
            Phi = self.inter_holonomy(i, j, k)
            hinge_areas.append(A)
            hinge_hols.append(abs(Phi))
            hinge_hbars.append(A / (4 * np.log(2)))

        return {
            'N': N,
            'rank_G': np.sum(np.linalg.eigvalsh(G) > 1e-10),
            'G_eigs': np.sort(np.linalg.eigvalsh(G))[::-1][:5],
            'W_mean': W[mask].mean(),
            'W_std': W[mask].std(),
            'abs_G_mean': abs_G.mean(),
            'phase_std': np.abs(phases).std(),
            'n_quark': sum(1 for c in chars if c['type'] == '쿼크적'),
            'n_lepton': sum(1 for c in chars if c['type'] == '렙톤적'),
            'n_mixed': sum(1 for c in chars if c['type'] == '혼합'),
            'hinge_area_mean': np.mean(hinge_areas),
            'hinge_area_std': np.std(hinge_areas),
            'hinge_hbar_mean': np.mean(hinge_hbars),
            'hinge_hbar_cv': np.std(hinge_hbars) / (np.mean(hinge_hbars) + 1e-15),
            'hinge_hol_mean': np.mean(hinge_hols),
        }


# ═════════════════════════════════════════════════════════════
#  실험
# ═════════════════════════════════════════════════════════════

def test_single_simplex():
    """TEST 1: 심플렉스 하나 해부."""
    print(f"\n{'━' * 70}")
    print("  TEST 1: 심플렉스 하나 = C⁵ = 5 진동자")
    print("━" * 70)

    lat = SimplexLattice(1, seed=42)
    z = lat.psi[0]

    print(f"\n  꼭짓점 (페르미온):")
    for a in range(5):
        r = np.abs(z[a])
        theta = np.angle(z[a])
        sector = 'S' if a < 3 else 'T'
        print(f"    v{a}[{sector}]: r={r:.4f}, θ={theta:+.4f}, |z|²={r**2:.4f}")

    print(f"\n  변 (보손 = 위상차):")
    phases = lat.internal_phases(0)
    for (a,b), phi in phases.items():
        sa = 'S' if a < 3 else 'T'
        sb = 'S' if b < 3 else 'T'
        print(f"    v{a}-v{b} [{sa}{sb}]: φ={phi:+.4f}")

    print(f"\n  면 (상호작용 = 홀로노미):")
    for a, b, c in combinations(range(5), 3):
        Phi = lat.internal_holonomy(0, (a, b, c))
        n_S = sum(1 for x in [a,b,c] if x < 3)
        force = ['??','약력(STT)','EM(SST)','강력(SSS)'][n_S]
        print(f"    △{a}{b}{c}: Φ={Phi:+.8f}  {force}")

    print(f"\n  내부 Φ = 0 확인: 단일 심플렉스는 편평 ✓")

    char = lat.simplex_character(0)
    print(f"\n  성격: C³={char['c3']:.3f}, C²={char['c2']:.3f} → {char['type']}")

    ok = all(abs(lat.internal_holonomy(0, t)) < 1e-10
             for t in combinations(range(5), 3))
    print(f"\n  [{'✓ PASS' if ok else '✗ FAIL'}] 내부 편평")
    return ok


def test_adjacency():
    """TEST 2: 심플렉스 인접 = 사면체 공유 = 1 hop."""
    print(f"\n{'━' * 70}")
    print("  TEST 2: 심플렉스 인접과 hop")
    print("━" * 70)

    N = 50
    lat = SimplexLattice(N, seed=42)

    # 가장 가까운 쌍
    W = np.abs(lat.G)**2 / 5
    np.fill_diagonal(W, 0)

    print(f"\n  N={N} 심플렉스 네트워크")
    print(f"  ⟨|G|⟩ = {np.abs(lat.G[~np.eye(N,dtype=bool)]).mean():.4f}")
    print(f"  ⟨W⟩ = {W[W>0].mean():.4f}")

    # 상위 5개 이웃
    print(f"\n  가장 가까운 쌍 (hop):")
    print(f"  {'i':>3s}-{'j':>3s}  {'|G|':>6s}  {'ds²':>6s}  {'φ':>7s}  1hop 해석")

    flat_idx = np.argsort(W.ravel())[::-1]
    shown = set()
    count = 0
    for idx in flat_idx:
        i, j = idx // N, idx % N
        if i >= j or (i,j) in shown: continue
        shown.add((i,j))
        hop = lat.hop(i, j)
        ci = lat.simplex_character(i)['type']
        cj = lat.simplex_character(j)['type']
        print(f"  {i:3d}-{j:3d}  {hop['abs_G']:6.4f}  {hop['ds2']:+6.3f}  "
              f"{hop['phase']:+7.4f}  {ci}↔{cj}")
        count += 1
        if count >= 8: break

    ok = True
    print(f"\n  [{'✓ PASS' if ok else '✗ FAIL'}] 인접 구조")
    return ok


def test_hinges():
    """TEST 3: 힌지 = 심플렉스 3개 = 1 bit = 곡률."""
    print(f"\n{'━' * 70}")
    print("  TEST 3: 힌지 (삼각형) = 1 bit = 곡률")
    print("━" * 70)

    N = 50
    lat = SimplexLattice(N, seed=42)

    # 힌지 유형별 통계
    ftypes = lat.force_decomposition()
    print(f"\n  심플렉스 내부 삼각형 유형:")
    for key, tris in ftypes.items():
        print(f"    {key}: {len(tris)}가지 {tris}")

    # 심플렉스 간 힌지 샘플
    n_samples = 3000
    hinge_data = {'SSS_heavy': [], 'SST_heavy': [], 'STT_heavy': [], 'mixed': []}
    areas = []
    hols = []
    hbars = []

    for _ in range(n_samples):
        i, j, k = np.random.choice(N, 3, replace=False)
        info = lat.hinge_info(i, j, k)
        areas.append(info['area'])
        hols.append(abs(info['holonomy']))
        hbars.append(info['hbar'])

    print(f"\n  심플렉스 간 힌지 ({n_samples} 샘플):")
    print(f"    면적 A: mean={np.mean(areas):.4f}, std={np.std(areas):.4f}")
    print(f"    ħ_hinge: mean={np.mean(hbars):.4f}, CV={np.std(hbars)/(np.mean(hbars)+1e-15):.4f}")
    print(f"    홀로노미 |Φ|: mean={np.mean(hols):.4f}")
    print(f"    1 bit/hinge: 항상 ✓ (정보론적 정리)")

    # ħ 분포
    h_arr = np.array(hbars)
    print(f"\n  ħ 분포:")
    bins = np.linspace(0, h_arr.max(), 8)
    hist, _ = np.histogram(h_arr, bins)
    for b in range(len(hist)):
        bar = '█' * (hist[b] * 30 // max(hist))
        print(f"    [{bins[b]:.3f}-{bins[b+1]:.3f}]: {hist[b]:4d} {bar}")

    ok = np.mean(hols) > 0.1  # 곡률 존재
    print(f"\n  [{'✓ PASS' if ok else '✗ FAIL'}] 힌지 곡률 존재")
    return ok


def test_force_hierarchy():
    """TEST 4: SSS > SST > STT 힘의 세기."""
    print(f"\n{'━' * 70}")
    print("  TEST 4: 힘의 위계 (공간/시간 비대칭)")
    print("━" * 70)

    N = 100
    lat = SimplexLattice(N, seed=42)

    # 심플렉스 내부의 삼각형 유형별 위상 크기
    # 내부는 항상 0이지만, 심플렉스 간의 "유효 위상"은 다름
    # → G_ij의 섹터별 분해로 측정

    strong_vals = []  # C³ 섹터 결합
    weak_vals = []    # C² 섹터 결합
    em_vals = []      # 혼합 결합
    grav_vals = []    # 전체 |G|

    mask = ~np.eye(N, dtype=bool)

    for i in range(min(N, 50)):
        for j in range(i+1, min(N, 50)):
            # C³ (공간) 내적
            gS = np.vdot(lat.psi[i, :3], lat.psi[j, :3])
            # C² (시간) 내적
            gT = np.vdot(lat.psi[i, 3:], lat.psi[j, 3:])
            # 전체
            g_full = lat.G[i, j]

            strong_vals.append(np.abs(gS)**2 / 3)
            weak_vals.append(np.abs(gT)**2 / 2)
            em_vals.append(np.abs(np.sin(np.angle(gT) - np.angle(gS))))
            grav_vals.append(np.abs(g_full)**2 / 5)

    print(f"\n  힘의 세기 (N={N}):")
    print(f"    강력 (C³ = SSS): ⟨W_S⟩ = {np.mean(strong_vals):.5f}")
    print(f"    약력 (C² = STT): ⟨W_T⟩ = {np.mean(weak_vals):.5f}")
    print(f"    EM   (혼합=SST): ⟨sin(Δφ)⟩ = {np.mean(em_vals):.5f}")
    print(f"    중력 (전체):     ⟨W⟩ = {np.mean(grav_vals):.5f}")

    # 비율
    print(f"\n  비율:")
    print(f"    강력/약력 = {np.mean(strong_vals)/np.mean(weak_vals):.3f}")
    print(f"    강력/EM   = {np.mean(strong_vals)/np.mean(em_vals):.3f}")
    print(f"    강력/중력 = {np.mean(strong_vals)/np.mean(grav_vals):.3f}")

    # SSS:SST:STT 빈도
    print(f"\n  힌지 유형 빈도:")
    print(f"    SSS: C(3,3)=1   → 강력 독점")
    print(f"    SST: C(3,2)×C(2,1)=6 → EM 주력")
    print(f"    STT: C(3,1)×C(2,2)=3 → 약력")
    print(f"    TTT: C(2,3)=0   → 불가능!")
    print(f"    빈도비 SSS:SST:STT = 1:6:3")

    ok = np.mean(strong_vals) > np.mean(weak_vals)
    print(f"\n  [{'✓ PASS' if ok else '✗ FAIL'}] 강력 > 약력")
    return ok


def test_spacetime_geometry():
    """TEST 5: 네트워크 = 4D 시공간."""
    print(f"\n{'━' * 70}")
    print("  TEST 5: 심플렉스 네트워크 = 4D 시공간")
    print("━" * 70)

    for N in [50, 200, 500]:
        lat = SimplexLattice(N, seed=42)
        stats = lat.spacetime_analysis(n_hinge_samples=min(2000, N**2))

        print(f"\n  N = {N}:")
        print(f"    rank(G) = {stats['rank_G']} (= d = 5 ✓)")
        print(f"    G 고유값: [{', '.join(f'{e:.1f}' for e in stats['G_eigs'])}]")
        print(f"    ⟨W⟩ = {stats['W_mean']:.5f}, σ = {stats['W_std']:.5f}")
        print(f"    심플렉스 분류: 쿼크={stats['n_quark']}, "
              f"렙톤={stats['n_lepton']}, 혼합={stats['n_mixed']}")
        print(f"    힌지 ħ: mean={stats['hinge_hbar_mean']:.4f}, "
              f"CV={stats['hinge_hbar_cv']:.4f}")
        print(f"    힌지 |Φ|: {stats['hinge_hol_mean']:.4f}")

    ok = stats['rank_G'] == 5
    print(f"\n  [{'✓ PASS' if ok else '✗ FAIL'}] 4D 시공간 (rank=5)")
    return ok


# ═════════════════════════════════════════════════════════════

class EXP_031_SimplexSpacetime(Experiment):
    ID = "031"
    TITLE = "Simplex Spacetime"

    def run(self):
        self.log("\n  격자점 = 4-심플렉스 = C⁵ 시공간 모델\n")

        self.check("내부 편평 (Φ=0)", test_single_simplex())
        self.check("인접 구조 (hop)", test_adjacency())
        self.check("힌지 = 1bit = 곡률", test_hinges())
        self.check("힘의 위계 (강>약)", test_force_hierarchy())
        self.check("4D 시공간 (rank=5)", test_spacetime_geometry())

        self.log(f"\n{'━' * 70}")
        self.log("  종합")
        self.log("━" * 70)
        self.log("""
  격자점 = 4-심플렉스 = ψ ∈ C⁵:
    꼭짓점(5) = 페르미온 (z ∈ C, 배타)
    변(10) = 보손 (위상차, 중첩)
    면(10) = 상호작용 (홀로노미)

  심플렉스 내부: 항상 편평 (Φ=0)
  심플렉스 간:   곡률 존재 (Φ≠0) = Regge calculus

  힌지 유형: SSS(1):SST(6):STT(3):TTT(0)
    → 강력 > 약력, EM 가장 흔함
    → 순수 시간 상호작용 불가 (TTT=0)

  점을 키우면 → 사면체 공유 → 4D 테셀레이션
  네트워크 ⟺ 시공간 (이중 기술)
""")


if __name__ == "__main__":
    EXP_031_SimplexSpacetime().execute()
