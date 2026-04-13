"""
EXP_043b: SDP approach — G에서 직접 25개 물리 상수 추출
===========================================================
(3,2) 구속 + x_S/x_T = 6 (c=2) + complex ψ.
δS/δψ = 0의 해에서 모든 물리량을 한 번에.

Joint research by Mingu Jeong and Claude (Anthropic)
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))

import numpy as np
from scipy.optimize import minimize, differential_evolution
from itertools import combinations
from experiment import Experiment

# ∂(5-simplex) topology (EXP_043에서 그대로)
N_VERT = 6
DIM = 5
SIMPLICES = [tuple(v for v in range(N_VERT) if v != i) for i in range(N_VERT)]
HINGES = list(combinations(range(N_VERT), 3))
HINGE_SIMPLICES = {}
for _h in HINGES:
    HINGE_SIMPLICES[_h] = [si for si, s in enumerate(SIMPLICES)
                           if all(v in s for v in _h)]

# 물리 상수
ALPHA = 1 / 137.036
ALPHA_GUT = 6 / (25 * np.pi**2)
N_S, N_T, D = 3, 2, 5


# =============================================================
# (3,2)-constrained ψ builder
# =============================================================
def make_B(eps, theta):
    """B vertex: S-sector에 eps 혼합, T-sector에 main weight."""
    c = np.sqrt(max(1 - 3 * eps**2, 0.01))
    return np.array([eps, eps, eps, c * np.cos(theta), c * np.sin(theta)])


def build_psi_32(params):
    """네 성공 코드와 동일한 convention. A=e₀,e₁,e₂. B=T주도+eps혼합.

    Convention: S-sector = indices 0,1,2.  T-sector = indices 3,4.

    params (5 real):
      [0] eps       : B→S 혼합 강도 (0.001~0.3)
      [1] theta_B3  : B₃의 T-sector 방향각
      [2] phi_B3    : B₃ CP phase (complex)
      [3] eps_B3    : B₃의 S-sector 혼합 (독립)
      [4] cp_pert   : CP-violating perturbation
    """
    eps = ALPHA / np.sqrt(3)  # Z=1: Zα/√3 = 물리적 A-B 혼합
    theta3 = params[1]
    phi3 = params[2]
    eps3 = 0.001 + 0.199 / (1 + np.exp(-params[3]))  # B₃ 독립 혼합
    cp_p = 0.05 * np.tanh(params[4])

    psi = np.zeros((6, 5), dtype=complex)

    # A₁, A₂, A₃ = S-sector 표준 기저
    psi[0] = [1, 0, 0, 0, 0]
    psi[1] = [0, 1, 0, 0, 0]
    psi[2] = [0, 0, 1, 0, 0]

    # B₁: spin up (θ=0)
    psi[3] = make_B(eps, 0)

    # B₂: spin down (θ=π/2)
    psi[4] = make_B(eps, np.pi / 2)

    # B₃: 독립적 direction + CP phase
    B3_real = make_B(eps3, theta3)
    psi[5] = B3_real * np.exp(1j * phi3 * np.array([0, 0, 0, 1, 0]))
    psi[5, 4] += cp_p * 1j  # CP violation (imaginary perturbation)

    # 정규화
    for k in range(6):
        n = np.linalg.norm(psi[k])
        if n > 1e-15:
            psi[k] /= n

    return psi


# =============================================================
# Regge action on ∂(5-simplex)
# =============================================================
def gram(psi):
    return psi @ psi.conj().T

def hinge_det3(G, h):
    idx = list(h)
    return np.linalg.det(G[np.ix_(idx, idx)]).real

def dihedral(G, simplex, hinge):
    s_list = list(simplex)
    extra = [v for v in simplex if v not in hinge]
    dl, el = s_list.index(extra[0]), s_list.index(extra[1])
    Gs = G[np.ix_(s_list, s_list)]
    try:
        Gi = np.linalg.inv(Gs)
        dd, ee, de = Gi[dl, dl].real, Gi[el, el].real, Gi[dl, el].real
        if dd <= 0 or ee <= 0:
            return np.pi / 3
        return np.arccos(np.clip(-de / np.sqrt(dd * ee), -1, 1))
    except np.linalg.LinAlgError:
        return np.pi / 3

def regge_action(psi):
    G = gram(psi)
    S = 0.0
    for h, si_list in HINGE_SIMPLICES.items():
        d = hinge_det3(G, h)
        if d < 1e-15:
            continue
        A = np.sqrt(d)
        delta = 2 * np.pi - sum(dihedral(G, SIMPLICES[si], h) for si in si_list)
        S += A * delta
    return S

def objective(params):
    """−S (최대화 = −최소화) + 구속 penalty."""
    psi = build_psi_32(params)
    S = regge_action(psi)

    # x_S/x_T = 6 soft constraint (S=0,1,2; T=3,4)
    G = gram(psi)
    xs = np.mean([(np.abs(psi[i, :3])**2).sum() for i in range(3)])
    xt = np.mean([(np.abs(psi[i, 3:])**2).sum() for i in range(3, 6)])
    ratio_penalty = 500.0 * (xs / max(xt, 1e-10) - 6.0)**2

    # rank ≤ 5 (자동 만족, 하지만 det(G)≈0 확인)
    det6 = abs(np.linalg.det(G))
    rank_penalty = 100.0 * det6

    return -S + ratio_penalty + rank_penalty


# =============================================================
# 25개 물리 채널 추출
# =============================================================
def extract_25_channels(psi, log=print):
    G = gram(psi)
    W = np.abs(G)**2 / D

    log("=" * 70)
    log("  25 PHYSICAL CHANNELS from ∂(5-simplex)")
    log("=" * 70)

    # ─── 기본 구조 ───
    evals_G = np.sort(np.linalg.eigvalsh(G))[::-1]
    evals_W = np.sort(np.linalg.eigvalsh(W))[::-1]
    log(f"\nG eigenvalues: {np.round(evals_G, 5)}")
    log(f"W eigenvalues (top 10): {np.round(evals_W[:10], 5)}")
    log(f"Tr(G) = {np.trace(G).real:.6f}")
    log(f"rank(G) = {np.sum(evals_G > 1e-8)}")

    # ─── Δ⁴ 위치 ───
    log(f"\n--- Δ⁴ Position ---")
    # Convention: S = indices 0,1,2.  T = indices 3,4.
    xs = np.mean([(np.abs(psi[i, :3])**2).sum() for i in range(3)])
    xt = np.mean([(np.abs(psi[i, 3:])**2).sum() for i in range(3, 6)])
    log(f"x_S(A verts) = {xs:.5f},  x_T(B verts) = {xt:.5f}")
    log(f"x_S/x_T = {xs/max(xt,1e-10):.4f}  (theory: 6.0)")
    log(f"x_T = {xt:.5f}  (theory: 1/7 = {1/7:.5f})")

    # ─── Hinge det by type ───
    log(f"\n--- Hinge Det (averaged by type) ---")
    htype_data = {}
    for h in HINGES:
        n_A = sum(1 for v in h if v < 3)
        ht = ["BBB", "ABB", "AAB", "AAA"][n_A]
        d = hinge_det3(G, h)
        htype_data.setdefault(ht, []).append(d)
    for ht in ["AAA", "AAB", "ABB", "BBB"]:
        vals = htype_data.get(ht, [])
        if vals:
            log(f"  {ht} ({len(vals):2d}): det = {np.mean(vals):.6f} ± {np.std(vals):.6f}")

    # σ = det(ABB)/det(AAB) * (n_AAB/n_ABB)?
    if "ABB" in htype_data and "AAB" in htype_data:
        sigma_det = np.mean(htype_data["ABB"])
        log(f"  → det(ABB) mean = {sigma_det:.6f}  (theory σ = 2/3 = {2/3:.6f})")

    # ─── Regge action & curvature ───
    S = regge_action(psi)
    log(f"\n--- Regge Action ---")
    log(f"  S = {S:.6f}")
    log(f"  S/(8π²) = {S/(8*np.pi**2):.6f}  (χ=2 → should be ≈ 1)")

    # ─── 세대 구조 (B-pair overlaps) ───
    log(f"\n--- Generation Structure ---")
    gen_names = [("B₁B₂", 3, 4), ("B₁B₃", 3, 5), ("B₂B₃", 4, 5)]
    for name, i, j in gen_names:
        g = G[i, j]
        det_bb = 1 - abs(g)**2
        log(f"  {name}: ⟨B|B'⟩ = {g:.5f},  |⟨B|B'⟩|² = {abs(g)**2:.5f},  "
            f"det = {det_bb:.5f}")

    # ─── CKM parameters ───
    log(f"\n--- CKM Parameters ---")
    # B₃ = α B₁ + β B₂ (overlap으로 추출)
    alpha_ckm = G[3, 5]  # ⟨B₁|B₃⟩
    beta_ckm = G[4, 5]   # ⟨B₂|B₃⟩
    theta_cab = np.arctan2(abs(beta_ckm), abs(alpha_ckm))
    delta_cp = np.angle(alpha_ckm * beta_ckm.conj())
    log(f"  α = ⟨B₁|B₃⟩ = {alpha_ckm:.5f}  (|α|={abs(alpha_ckm):.5f})")
    log(f"  β = ⟨B₂|B₃⟩ = {beta_ckm:.5f}  (|β|={abs(beta_ckm):.5f})")
    log(f"  θ_Cabibbo = {np.degrees(theta_cab):.2f}°  (obs: 13.0°)")
    log(f"  δ_CP = {np.degrees(delta_cp):.2f}°  (obs: 68.8°)")

    # ─── Holonomies (gauge field strengths) ───
    log(f"\n--- Holonomies (top gauge fluxes) ---")
    holos = []
    for h in HINGES:
        phi_h = np.angle(G[h[0], h[1]] * G[h[1], h[2]] * G[h[2], h[0]])
        n_A = sum(1 for v in h if v < 3)
        ht = ["BBB", "ABB", "AAB", "AAA"][n_A]
        holos.append((h, ht, phi_h))
    for h, ht, phi in sorted(holos, key=lambda x: -abs(x[2]))[:8]:
        log(f"  Φ{h} ({ht}) = {np.degrees(phi):+7.2f}°")

    # ─── 결합 상수 추정 ───
    log(f"\n--- Coupling Constants ---")
    # α_GUT from hinge structure
    if "AAB" in htype_data:
        det_aab = np.mean(htype_data["AAB"])
        # α ≈ 1 - det (leading order deviation from 1)
        alpha_est = (1 - det_aab) / N_S
        log(f"  α_est (from AAB det) = {alpha_est:.6f}  "
            f"(α_GUT = {ALPHA_GUT:.6f})")

    # ─── IE 추정 (수소 = AAAB face) ───
    log(f"\n--- Ionization Energy (H-like) ---")
    # AAAB face = {A₁,A₂,A₃,B₁} → B₂ 빠짐
    # 3개 AAB hinge의 det 변화량 합
    aab_dets_H = []
    for h in HINGES:
        if all(v in (0, 1, 2, 3) for v in h):
            n_A = sum(1 for v in h if v < 3)
            if n_A == 2:  # AAB type in AAAB face
                aab_dets_H.append(hinge_det3(G, h))
    if aab_dets_H:
        delta_det = sum(1 - d for d in aab_dets_H)
        # IE = m_e × delta_det / n_T
        IE_eV = 511000 * delta_det / N_T  # m_e c² in eV
        log(f"  Σ(1-det) for AAAB face = {delta_det:.6f}")
        log(f"  IE = m_e × Σ(1-det) / n_T = {IE_eV:.1f} eV  (obs: 13.6 eV)")
        log(f"  Ratio to Rydberg: {IE_eV/13.606:.4f}")

    # ─── 질량비 ───
    log(f"\n--- Mass Ratios ---")
    det_12 = 1 - abs(G[3, 4])**2  # 1세대 (B₁B₂)
    det_13 = 1 - abs(G[3, 5])**2  # 2세대 (B₁B₃)
    det_23 = 1 - abs(G[4, 5])**2  # 3세대 (B₂B₃)
    if det_13 > 1e-10 and det_23 > 1e-10:
        log(f"  det(B₁B₂) = {det_12:.6f} (1st gen)")
        log(f"  det(B₁B₃) = {det_13:.6f} (2nd gen)")
        log(f"  det(B₂B₃) = {det_23:.6f} (3rd gen)")
        log(f"  m₂/m₁ ~ det₁/det₂ = {det_12/det_13:.2f}")
        log(f"  m₃/m₁ ~ det₁/det₃ = {det_12/det_23:.2f}")
        log(f"  (1/α_GUT)^{N_S} = {(1/ALPHA_GUT)**N_S:.0f}  (theory: m_t/m_u)")

    # ─── W 고유값 25개 ───
    log(f"\n--- W Spectrum (25 channels) ---")
    w_evals = np.sort(np.linalg.eigvalsh(W))[::-1]
    for i, ev in enumerate(w_evals):
        if ev > 1e-10:
            log(f"  λ_W[{i:2d}] = {ev:.6f}")
    log(f"  Non-zero W eigenvalues: {np.sum(w_evals > 1e-8)}")
    log(f"  Σ W eigenvalues = {w_evals.sum():.6f}")

    return G, W


# =============================================================
# Experiment
# =============================================================
class EXP043b(Experiment):
    ID = "043b"
    TITLE = "SDP 25 channels"

    def run(self):
        self.log("=" * 70)
        self.log("EXP_043b: SDP on ∂(5-simplex) — 25 physical channels")
        self.log("=" * 70)

        # ─── Phase 1: Coarse scan with differential_evolution ───
        self.log("\nPhase 1: Global search (differential evolution)")
        bounds = [(-3, 3)] * 5  # 5 real parameters

        result_de = differential_evolution(
            objective, bounds, seed=42,
            maxiter=200, tol=1e-8, popsize=20,
            mutation=(0.5, 1.5), recombination=0.9
        )
        self.log(f"  DE: −S + penalty = {result_de.fun:.6f}")
        best_params = result_de.x.copy()

        psi_de = build_psi_32(best_params)
        S_de = regge_action(psi_de)
        self.log(f"  S = {S_de:.6f}")

        xs = np.mean([(np.abs(psi_de[i, 2:])**2).sum() for i in range(3)])
        xt = np.mean([(np.abs(psi_de[i, :2])**2).sum()
                       for i in range(3, 6)])
        self.log(f"  x_S/x_T = {xs/max(xt,1e-10):.3f}")

        # ─── Phase 2: Local refinement (L-BFGS-B) ───
        self.log("\nPhase 2: Local refinement (L-BFGS-B)")
        result_lb = minimize(objective, best_params, method='L-BFGS-B',
                             options={'maxiter': 5000, 'ftol': 1e-14})
        self.log(f"  Converged: {result_lb.success}")
        best_params = result_lb.x.copy()

        # ─── Phase 3: Multi-start refinement ───
        self.log("\nPhase 3: Multi-start refinement (10 trials)")
        best_obj = result_lb.fun
        for trial in range(10):
            p0 = best_params + 0.1 * np.random.randn(5)
            r = minimize(objective, p0, method='L-BFGS-B',
                         options={'maxiter': 2000, 'ftol': 1e-14})
            if r.fun < best_obj:
                best_obj = r.fun
                best_params = r.x.copy()
                self.log(f"  Trial {trial}: improved → obj = {r.fun:.6f}")

        # ─── Phase 4: Extract 25 channels ───
        psi_opt = build_psi_32(best_params)
        S_opt = regge_action(psi_opt)
        self.log(f"\nFinal S = {S_opt:.6f}")

        G, W = extract_25_channels(psi_opt, log=self.log)

        # ─── Phase 5: Checks ───
        self.log("\n" + "=" * 70)
        self.log("CHECKS")
        self.log("=" * 70)

        tr = np.trace(G).real
        self.check("Tr(G) = 6", abs(tr - 6.0) < 0.01)

        evals = np.linalg.eigvalsh(G)[::-1]
        self.check("rank(G) ≤ 5", evals[5] < 0.05)

        all_det = [hinge_det3(G, h) for h in HINGES]
        self.check("All det(G_h) > 0", all(d > -0.01 for d in all_det))

        xs = np.mean([(np.abs(psi_opt[i, :3])**2).sum() for i in range(3)])
        xt = np.mean([(np.abs(psi_opt[i, 3:])**2).sum()
                       for i in range(3, 6)])
        ratio = xs / max(xt, 1e-10)
        self.check("x_S/x_T ≈ 6", abs(ratio - 6.0) < 2.0)

        self.log("\n" + "=" * 70)
        self.log("Done.")


if __name__ == "__main__":
    EXP043b().execute()
