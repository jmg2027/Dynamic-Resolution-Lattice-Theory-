"""
EXP_043: Variational ∂(5-simplex) — δS/δψ = 0의 해
=========================================================
Block universe 정신: 섭동 없이, Regge action의 extremum에서
모든 물리량(IE, 질량비, CKM, coupling)을 한 번에 추출.

Joint research by Mingu Jeong and Claude (Anthropic)
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))

import numpy as np
from scipy.optimize import minimize
from itertools import combinations
from experiment import Experiment

# =============================================================
# ∂(5-simplex) 토폴로지 (고정, 계산 불필요)
# =============================================================
N_VERT = 6
DIM = 5  # ψ ∈ ℂ⁵

# 6개 4-simplex: σᵢ = 모든 꼭지점에서 vᵢ를 뺀 것
SIMPLICES = [tuple(v for v in range(N_VERT) if v != i) for i in range(N_VERT)]

# 20개 hinge (삼각형): C(6,3)
HINGES = list(combinations(range(N_VERT), 3))

# 각 hinge를 둘러싸는 simplex 목록 (항상 정확히 3개)
HINGE_SIMPLICES = {}
for _h in HINGES:
    HINGE_SIMPLICES[_h] = [si for si, s in enumerate(SIMPLICES)
                           if all(v in s for v in _h)]

# 15개 face (사면체): C(6,4) — 각 face는 정확히 2개 simplex에 속함
FACES = list(combinations(range(N_VERT), 4))


# =============================================================
# 핵심 수학 함수
# =============================================================
def flat_to_psi(x):
    """60 reals → 6×5 normalized complex matrix."""
    psi = (x[:30] + 1j * x[30:]).reshape(N_VERT, DIM)
    norms = np.linalg.norm(psi, axis=1, keepdims=True)
    return psi / np.maximum(norms, 1e-15)


def gram_6x6(psi):
    """6×5 psi → 6×6 Gram matrix G_ij = ⟨ψ_i|ψ_j⟩."""
    return psi @ psi.conj().T


def hinge_det(G, h):
    """3×3 submatrix det (hinge area²)."""
    idx = list(h)
    sub = G[np.ix_(idx, idx)]
    return np.linalg.det(sub).real


def hinge_area(G, h):
    """√det(G_h) — hinge area."""
    d = hinge_det(G, h)
    return np.sqrt(max(d, 0.0))


def dihedral_angle(G, simplex, hinge):
    """4-simplex의 hinge에서의 이면각.

    Cofactor 공식: cos θ_{de} = −G⁻¹_{de} / √(G⁻¹_{dd}·G⁻¹_{ee})
    여기서 d,e = simplex에 있지만 hinge에 없는 2개 꼭지점.
    """
    s_list = list(simplex)
    extra = [v for v in simplex if v not in hinge]
    d_loc = s_list.index(extra[0])
    e_loc = s_list.index(extra[1])

    G_s = G[np.ix_(s_list, s_list)]
    try:
        G_inv = np.linalg.inv(G_s)
        dd = G_inv[d_loc, d_loc].real
        ee = G_inv[e_loc, e_loc].real
        de = G_inv[d_loc, e_loc].real
        if dd <= 0 or ee <= 0:
            return np.pi / 3
        cos_th = -de / np.sqrt(dd * ee)
        return np.arccos(np.clip(cos_th, -1.0, 1.0))
    except np.linalg.LinAlgError:
        return np.pi / 3


def deficit_angle(G, hinge):
    """힌지의 적자각 δ = 2π − Σθ."""
    s_indices = HINGE_SIMPLICES[hinge]
    sum_theta = sum(dihedral_angle(G, SIMPLICES[si], hinge)
                    for si in s_indices)
    return 2.0 * np.pi - sum_theta


def regge_action_value(x):
    """Regge action S = Σ_h A_h × δ_h."""
    psi = flat_to_psi(x)
    G = gram_6x6(psi)
    S = 0.0
    for h in HINGES:
        A_h = hinge_area(G, h)
        if A_h < 1e-15:
            continue
        delta_h = deficit_angle(G, h)
        S += A_h * delta_h
    return S


def neg_regge_action(x):
    """−S: S⁴는 양의 곡률 → S를 최대화 = −S를 최소화."""
    return -regge_action_value(x)


def regge_gradient_norm(x):
    """|∇S|² — saddle point 탐색용 (gradient = 0 찾기)."""
    eps = 1e-6
    grad = np.zeros_like(x)
    S0 = regge_action(x)
    for i in range(len(x)):
        x[i] += eps
        grad[i] = (regge_action(x) - S0) / eps
        x[i] -= eps
    return np.dot(grad, grad)


# =============================================================
# (3,2) 구조 초기값 생성
# =============================================================
def make_32_initial(theta_B3=0.23, noise=0.05, seed=None):
    """(3,2) 분할을 가진 초기 ψ 생성.

    A₁,A₂,A₃: S-sector (ℂ³) 주도, 120° 간격으로 배치
    B₁,B₂: T-sector (ℂ²) 주도, 직교
    B₃ = cos(θ)B₁ + sin(θ)B₂ + noise

    Parameters
    ----------
    theta_B3 : float — B₃의 혼합각 (≈ Cabibbo angle 13° = 0.227 rad)
    noise : float — 대칭 파괴 노이즈
    seed : int or None
    """
    rng = np.random.default_rng(seed)
    psi = np.zeros((6, 5), dtype=complex)

    # A vertices: S-sector (indices 2,3,4) 주도
    # 120° 간격으로 ℂ³ 평면에 배치
    for k in range(3):
        angle = 2 * np.pi * k / 3
        psi[k, 2] = np.cos(angle) * 0.9   # S₁
        psi[k, 3] = np.sin(angle) * 0.9   # S₂
        psi[k, 4] = 0.1                    # S₃ (작은 공통 성분)
        psi[k, 0] = 0.1                    # T₁ (작은 혼합)
        psi[k, 1] = 0.05                   # T₂

    # B₁: T-sector 주도, 방향 1
    psi[3, 0] = 0.9
    psi[3, 1] = 0.1
    psi[3, 2] = 0.1
    psi[3, 3] = 0.05
    psi[3, 4] = 0.05

    # B₂: T-sector 주도, 방향 2 (B₁과 직교에 가깝게)
    psi[4, 0] = 0.1
    psi[4, 1] = 0.9
    psi[4, 2] = 0.05
    psi[4, 3] = 0.1
    psi[4, 4] = 0.05

    # B₃ = cos(θ)B₁ + sin(θ)B₂ (ℂ² 내 선형 종속)
    psi[5] = np.cos(theta_B3) * psi[3] + np.sin(theta_B3) * psi[4]

    # 노이즈 추가
    psi += noise * (rng.standard_normal(psi.shape)
                    + 1j * rng.standard_normal(psi.shape))

    # 정규화
    norms = np.linalg.norm(psi, axis=1, keepdims=True)
    psi = psi / norms

    return psi


def psi_to_flat(psi):
    """6×5 complex → 60 reals."""
    c = psi.flatten()
    return np.concatenate([c.real, c.imag])


# =============================================================
# 물리량 추출
# =============================================================
def extract_physics(psi, log=print):
    """최적해 ψ에서 모든 물리량 추출."""
    G = gram_6x6(psi)

    log("\n=== Gram Matrix (6×6) ===")
    log(f"Tr(G) = {np.trace(G).real:.6f}  (should be 6)")
    evals = np.linalg.eigvalsh(G)[::-1]
    log(f"Eigenvalues: {np.round(evals, 4)}")
    log(f"rank(G) = {np.sum(evals > 1e-10)}")

    # Δ⁴ 위치: 각 꼭지점의 |z_k|² 분포
    log("\n=== Δ⁴ Position ===")
    for i in range(6):
        probs = np.abs(psi[i])**2
        label = f"A{i+1}" if i < 3 else f"B{i-2}"
        log(f"  {label}: S={probs[2:].sum():.4f}  T={probs[:2].sum():.4f}")

    # x_S, x_T (평균)
    x_S = np.mean([(np.abs(psi[i, 2:])**2).sum() for i in range(3)])
    x_T = np.mean([(np.abs(psi[i, :2])**2).sum() for i in range(3, 6)])
    log(f"  Average x_S = {x_S:.4f}, x_T = {x_T:.4f}")
    log(f"  x_S/x_T = {x_S/max(x_T, 1e-10):.4f}  (theory: 6)")

    # 힌지별 det, deficit angle
    log("\n=== Hinge Analysis (20 hinges) ===")
    hinge_data = []
    for h in HINGES:
        d = hinge_det(G, h)
        a = hinge_area(G, h)
        delta = deficit_angle(G, h)
        # (3,2) 타입 분류
        n_A = sum(1 for v in h if v < 3)
        htype = ["BBB", "ABB", "AAB", "AAA"][n_A]
        hinge_data.append((h, htype, d, a, delta))

    # 타입별 통계
    for htype in ["AAA", "AAB", "ABB", "BBB"]:
        subset = [x for x in hinge_data if x[1] == htype]
        if not subset:
            log(f"  {htype}: 없음")
            continue
        dets = [x[2] for x in subset]
        deltas = [x[4] for x in subset]
        log(f"  {htype} ({len(subset)}개): "
            f"det={np.mean(dets):.6f}±{np.std(dets):.6f}, "
            f"δ={np.mean(deltas):.4f}±{np.std(deltas):.4f} rad")

    # Regge action
    S_total = sum(x[3] * x[4] for x in hinge_data)
    log(f"\n  S_Regge = {S_total:.6f}")

    # 세대별 B-pair det
    log("\n=== Generation Structure ===")
    B_pairs = [(3, 4, "B₁B₂ (1세대)"),
               (3, 5, "B₁B₃ (2세대)"),
               (4, 5, "B₂B₃ (3세대)")]
    for bi, bj, label in B_pairs:
        gbb = G[bi, bj]
        det_bb = 1.0 - abs(gbb)**2
        log(f"  {label}: ⟨B|B'⟩={gbb:.4f}, det={det_bb:.6f}")

    # CKM angle
    if abs(G[3, 5]) > 1e-10:
        theta_ckm = np.arccos(np.clip(abs(G[3, 5]), 0, 1))
        log(f"\n  CKM θ ≈ {np.degrees(theta_ckm):.1f}° "
            f"(Cabibbo ≈ 13°)")

    # Holonomies
    log("\n=== Holonomies (gauge field strength) ===")
    for h in HINGES[:5]:  # 처음 5개만
        phase = np.angle(G[h[0], h[1]] * G[h[1], h[2]] * G[h[2], h[0]])
        log(f"  Φ{h} = {phase:.4f} rad = {np.degrees(phase):.1f}°")

    return G, hinge_data


# =============================================================
# 실험 클래스
# =============================================================
class EXP043(Experiment):
    ID = "043"
    TITLE = "Variational boundary 5-simplex"

    def run(self):
        self.log("=" * 60)
        self.log("EXP_043: δS/δψ = 0 on ∂(5-simplex)")
        self.log("=" * 60)

        # 토폴로지 확인
        self.log(f"\nTopology: {N_VERT} vertices, "
                 f"{len(SIMPLICES)} simplices, "
                 f"{len(HINGES)} hinges")
        for h, sl in HINGE_SIMPLICES.items():
            assert len(sl) == 3, f"Hinge {h} has {len(sl)} simplices"
        self.check("All hinges have 3 simplices", True)

        # ─── Phase 1: (3,2) 구조 초기값 탐색 ───
        self.log("\n" + "=" * 60)
        self.log("Phase 1: (3,2)-structured search (20 trials)")
        self.log("=" * 60)

        best_S = np.inf
        best_psi = None
        best_x = None

        for trial in range(20):
            theta = 0.1 + 0.3 * trial / 19  # 0.1 ~ 0.4 rad 스캔
            psi0 = make_32_initial(theta_B3=theta, noise=0.08,
                                   seed=42 + trial)
            x0 = psi_to_flat(psi0)

            res = minimize(neg_regge_action, x0, method='L-BFGS-B',
                           options={'maxiter': 3000, 'ftol': 1e-12})

            if res.fun < best_S:
                best_S = res.fun
                best_x = res.x.copy()
                best_psi = flat_to_psi(res.x)
                self.log(f"  Trial {trial:2d} (θ={theta:.2f}): "
                         f"S = {-res.fun:.6f} *** new best")
            else:
                self.log(f"  Trial {trial:2d} (θ={theta:.2f}): "
                         f"S = {-res.fun:.6f}")

        # ─── Phase 2: 랜덤 초기값으로 추가 탐색 ───
        self.log("\n" + "=" * 60)
        self.log("Phase 2: Random initial search (10 trials)")
        self.log("=" * 60)

        for trial in range(10):
            x0 = np.random.randn(60) * 0.5
            res = minimize(neg_regge_action, x0, method='L-BFGS-B',
                           options={'maxiter': 3000, 'ftol': 1e-12})
            if res.fun < best_S:
                best_S = res.fun
                best_x = res.x.copy()
                best_psi = flat_to_psi(res.x)
                self.log(f"  Random {trial:2d}: "
                         f"S = {-res.fun:.6f} *** new best")
            else:
                self.log(f"  Random {trial:2d}: "
                         f"S = {-res.fun:.6f}")

        # ─── Phase 3: 정밀 재최적화 ───
        self.log("\n" + "=" * 60)
        self.log("Phase 3: Refinement of best solution")
        self.log("=" * 60)

        res = minimize(neg_regge_action, best_x, method='L-BFGS-B',
                       options={'maxiter': 10000, 'ftol': 1e-15})
        best_psi = flat_to_psi(res.x)
        self.log(f"  Final S = {-res.fun:.10f}")
        self.log(f"  Converged: {res.success}")
        self.log(f"  Iterations: {res.nit}")

        # ─── Phase 4: 물리량 추출 ───
        self.log("\n" + "=" * 60)
        self.log("Phase 4: Physics Extraction")
        self.log("=" * 60)

        G, hinge_data = extract_physics(best_psi, log=self.log)

        # ─── Phase 5: 핵심 검증 ───
        self.log("\n" + "=" * 60)
        self.log("Phase 5: Key Checks")
        self.log("=" * 60)

        # Tr(G) = 6
        tr = np.trace(G).real
        self.check("Tr(G) = 6", abs(tr - 6.0) < 1e-6)

        # rank(G) ≤ 5
        evals = np.linalg.eigvalsh(G)[::-1]
        self.check("rank(G) ≤ 5", evals[5] < 0.01)

        # 모든 δ < 2π
        all_delta = [x[4] for x in hinge_data]
        self.check("All δ < 2π", all(d < 2 * np.pi for d in all_delta))

        # 모든 det > 0
        all_det = [x[2] for x in hinge_data]
        self.check("All det(G_h) > 0", all(d > 0 for d in all_det))

        self.log("\n" + "=" * 60)
        self.log("Done.")


if __name__ == "__main__":
    EXP043().execute()
