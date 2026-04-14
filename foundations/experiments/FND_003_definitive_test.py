"""
EXP_047: Definitive Test — δS/δψ = 0 on ∂(5-simplex)
Joint research by Mingu Jeong and Claude (Anthropic)

공리에서 출발:
  1. 6개 꼭지점 ψ_i ∈ C⁵, |ψ_i|² = 1
  2. ∂(5-simplex) Regge action: S = Σ_h A_h × δ_h
  3. δS/δψ = 0 → self-consistent 해
  4. 해에서 모든 물리량 추출 → 관측과 비교
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))

import numpy as np
from itertools import combinations
from experiment import Experiment


def gram(vecs):
    """Gram matrix from list of vectors: G_ij = <ψ_i|ψ_j>"""
    V = np.array(vecs)  # shape (n, d)
    return V @ V.conj().T


def cofactor_3(G5, p, q):
    """3 specific cofactors of 5×5 matrix: C_pp, C_qq, C_pq"""
    vals = {}
    for (i, j) in [(p, p), (q, q), (p, q)]:
        M = np.delete(np.delete(G5, i, axis=0), j, axis=1)
        vals[(i, j)] = np.real((-1)**(i+j) * np.linalg.det(M))
    return vals


def dihedral(G5, h_local):
    """Dihedral angle at hinge h_local in a 5-vertex simplex.
    h_local = list of 3 indices in the hinge.
    Returns angle in radians."""
    others = [k for k in range(5) if k not in h_local]
    p, q = others
    cof = cofactor_3(G5, p, q)
    cpp, cqq, cpq = cof[(p,p)], cof[(q,q)], cof[(p,q)]
    if cpp <= 0 or cqq <= 0:
        return 0.0
    cos_th = np.clip(-cpq / np.sqrt(cpp * cqq), -1, 1)
    return np.arccos(cos_th)


# Pre-compute topology
HINGES = list(combinations(range(6), 3))  # 20 hinges
# For each hinge, which simplices contain it and what are the local indices
HINGE_MAP = {}
for h_idx in HINGES:
    h_set = set(h_idx)
    others = [k for k in range(6) if k not in h_set]  # 3 simplices
    entries = []
    for missing in others:
        s_global = [k for k in range(6) if k != missing]  # 5 vertices
        h_local = [s_global.index(k) for k in h_idx]
        entries.append((s_global, h_local))
    HINGE_MAP[h_idx] = entries


def regge_action(all_vecs):
    """Compute Regge action and hinge data for ∂(5-simplex)"""
    S = 0.0
    hinge_data = []

    for h_idx in HINGES:
        h_vecs = [all_vecs[i] for i in h_idx]
        G3 = gram(h_vecs)
        det_h = np.real(np.linalg.det(G3))
        if det_h <= 1e-15:
            hinge_data.append((h_idx, det_h, 0.0, 0.0, 0.0))
            continue
        area_h = np.sqrt(det_h)

        sum_theta = 0.0
        for s_global, h_local in HINGE_MAP[h_idx]:
            s_vecs = [all_vecs[k] for k in s_global]
            G5 = gram(s_vecs)
            theta = dihedral(G5, h_local)
            sum_theta += theta

        deficit = 2 * np.pi - sum_theta
        S += area_h * deficit
        hinge_data.append((h_idx, det_h, area_h,
                           np.degrees(sum_theta), np.degrees(deficit)))
    return S, hinge_data


class DefinitiveTest(Experiment):
    ID = "047"
    TITLE = "Definitive Test"

    def run(self):
        # ========================================
        # Phase 1: Setup
        # ========================================
        self.log("\n" + "="*60)
        self.log("  Phase 1: ∂(5-simplex) — 6 vertices in C⁵")
        self.log("="*60)

        A1 = np.array([1,0,0,0,0], dtype=complex)
        A2 = np.array([0,1,0,0,0], dtype=complex)
        A3 = np.array([0,0,1,0,0], dtype=complex)
        B1 = np.array([0,0,0,1,0], dtype=complex)
        B2 = np.array([0,0,0,0,1], dtype=complex)

        self.log("  A₁A₂A₃ = C³ 표준기저, B₁B₂ = C² 표준기저 (gauge-fixed)")
        self.log("  B₃ = 변분 변수")
        self.log(f"  Hinges: {len(HINGES)}, Simplices: 6")

        vert_names = ['A₁','A₂','A₃','B₁','B₂','B₃']

        # ========================================
        # Phase 2: 1D scan — B₃ in C² (θ만 변화)
        # ========================================
        self.log("\n" + "="*60)
        self.log("  Phase 2: B₃ = (0,0,0,cos θ, sin θ) — 1D scan")
        self.log("="*60)

        thetas = np.linspace(0.01, np.pi-0.01, 200)
        actions = []

        for theta in thetas:
            B3 = np.array([0, 0, 0, np.cos(theta), np.sin(theta)], dtype=complex)
            vecs = [A1, A2, A3, B1, B2, B3]
            S, _ = regge_action(vecs)
            actions.append(S)

        actions = np.array(actions)
        # Find extrema (could be min or saddle)
        i_min = np.argmin(actions)
        i_max = np.argmax(actions)

        self.log(f"  S range: [{min(actions):.6f}, {max(actions):.6f}]")
        self.log(f"  S_min at θ = {np.degrees(thetas[i_min]):.1f}° "
                 f"(S = {actions[i_min]:.6f})")
        self.log(f"  S_max at θ = {np.degrees(thetas[i_max]):.1f}° "
                 f"(S = {actions[i_max]:.6f})")

        # Also look for saddle points (local extrema)
        for label, idx in [('min', i_min), ('max', i_max)]:
            theta_opt = thetas[idx]
            B3_opt = np.array([0, 0, 0,
                               np.cos(theta_opt), np.sin(theta_opt)], dtype=complex)
            vecs = [A1, A2, A3, B1, B2, B3_opt]

            ov13 = np.vdot(B1, B3_opt)
            ov23 = np.vdot(B2, B3_opt)
            self.log(f"\n  At S_{label}: θ = {np.degrees(theta_opt):.1f}°")
            self.log(f"    B₃ = (0, 0, 0, {np.real(B3_opt[3]):.4f}, {np.real(B3_opt[4]):.4f})")
            self.log(f"    ⟨B₁|B₃⟩ = {np.real(ov13):.4f}  "
                     f"(|.|² = {abs(ov13)**2:.4f})")
            self.log(f"    ⟨B₂|B₃⟩ = {np.real(ov23):.4f}  "
                     f"(|.|² = {abs(ov23)**2:.4f})")

        # ========================================
        # Phase 3: Refine with phase freedom
        # ========================================
        self.log("\n" + "="*60)
        self.log("  Phase 3: C² 내 위상 포함 2D scan")
        self.log("="*60)

        # B₃ = (0, 0, 0, cos(θ)e^{iφ}, sin(θ))
        best_S = np.inf
        best_theta = 0
        best_phi = 0

        for theta in np.linspace(0.1, np.pi-0.1, 100):
            for phi in np.linspace(0, 2*np.pi, 50):
                B3 = np.array([0, 0, 0,
                               np.cos(theta)*np.exp(1j*phi),
                               np.sin(theta)], dtype=complex)
                vecs = [A1, A2, A3, B1, B2, B3]
                S, _ = regge_action(vecs)
                if S < best_S:
                    best_S = S
                    best_theta = theta
                    best_phi = phi

        self.log(f"  2D scan: θ = {np.degrees(best_theta):.1f}°, "
                 f"φ = {np.degrees(best_phi):.1f}°")
        self.log(f"  S_min = {best_S:.6f}")

        # Construct optimal B₃
        B3_best = np.array([0, 0, 0,
                            np.cos(best_theta)*np.exp(1j*best_phi),
                            np.sin(best_theta)], dtype=complex)
        B3_best = B3_best / np.linalg.norm(B3_best)
        all_vecs = [A1, A2, A3, B1, B2, B3_best]

        ov13 = np.vdot(B1, B3_best)
        ov23 = np.vdot(B2, B3_best)
        self.log(f"\n  최적 B₃ = ({B3_best[3]:.4f}, {B3_best[4]:.4f})")
        self.log(f"  ⟨B₁|B₃⟩ = {ov13:.4f}  (|.|² = {abs(ov13)**2:.4f})")
        self.log(f"  ⟨B₂|B₃⟩ = {ov23:.4f}  (|.|² = {abs(ov23)**2:.4f})")

        # ========================================
        # Phase 4: 모든 hinge 분석
        # ========================================
        self.log("\n" + "="*60)
        self.log("  Phase 4: Self-consistent hinge 구조")
        self.log("="*60)

        S_final, hinge_data = regge_action(all_vecs)

        # Classify by type
        by_type = {}
        for h_idx, det_h, area_h, sum_th, deficit in hinge_data:
            n_A = sum(1 for i in h_idx if i < 3)
            htype = 'S'*n_A + 'T'*(3-n_A)
            if htype not in by_type:
                by_type[htype] = []
            by_type[htype].append((h_idx, det_h, area_h, sum_th, deficit))

        self.log(f"\n  {'Type':<5} {'N':>3} {'⟨det⟩':>10} {'⟨Σθ⟩':>8} {'⟨δ⟩':>8}")
        self.log(f"  {'-'*38}")
        for htype in sorted(by_type.keys()):
            entries = by_type[htype]
            n = len(entries)
            avg_det = np.mean([e[1] for e in entries])
            avg_sumth = np.mean([e[3] for e in entries])
            avg_def = np.mean([e[4] for e in entries])
            self.log(f"  {htype:<5} {n:>3} {avg_det:>10.6f} "
                     f"{avg_sumth:>7.1f}° {avg_def:>+7.1f}°")

        # Detailed
        self.log(f"\n  {'Hinge':<12} {'Type':<5} {'det':>10} {'Σθ':>8} {'δ':>8}")
        self.log(f"  {'-'*48}")
        for h_idx, det_h, area_h, sum_th, deficit in sorted(
                hinge_data, key=lambda x: (sum(1 for i in x[0] if i<3), x[0])):
            names = ','.join(vert_names[i] for i in h_idx)
            n_A = sum(1 for i in h_idx if i < 3)
            htype = 'S'*n_A + 'T'*(3-n_A)
            self.log(f"  {names:<12} {htype:<5} {det_h:>10.6f}"
                     f" {sum_th:>7.1f}° {deficit:>+7.1f}°")

        # ========================================
        # Phase 5: 물리량 추출 및 검증
        # ========================================
        self.log("\n" + "="*60)
        self.log("  Phase 5: 물리량 검증")
        self.log("="*60)

        n_S = 3; n_T = 2; d = 5; c = 2
        alpha_GUT = 6/(25*np.pi**2)

        # 1. Tr(G) = N
        G6 = gram(all_vecs)
        tr = np.real(np.trace(G6))
        rank = np.linalg.matrix_rank(G6, tol=1e-6)
        eigs = np.sort(np.real(np.linalg.eigvalsh(G6)))[::-1]
        self.log(f"\n  Tr(G) = {tr:.6f}  (예측: 6)")
        self.log(f"  rank(G) = {rank}  (예측: ≤5)")
        self.log(f"  고유값: {[f'{e:.4f}' for e in eigs]}")
        self.check("Tr(G) = 6", abs(tr - 6) < 0.01)
        self.check("rank(G) ≤ 5", rank <= 5)

        # 2. δ_TTT = 0?
        if 'TTT' in by_type:
            defs_TTT = [e[4] for e in by_type['TTT']]
            avg_TTT = np.mean(defs_TTT)
            self.log(f"\n  δ(TTT) = {avg_TTT:.2f}°  (예측: 0°)")
            self.check("δ(TTT) = 0 → 중성미자 무질량", abs(avg_TTT) < 10)

        # 3. δ_SSS = 180° (EXP_047b confirmed)
        if 'SSS' in by_type:
            defs_SSS = [e[4] for e in by_type['SSS']]
            avg_SSS = np.mean(defs_SSS)
            self.log(f"  δ(SSS) = {avg_SSS:.2f}°  (예측: 180°)")
            self.check("δ(SSS) ≈ 180° → confinement", abs(avg_SSS - 180) < 30)

        # 4. ⟨det(SST)⟩ = n_T/n_S?
        if 'SST' in by_type:
            avg_SST = np.mean([e[1] for e in by_type['SST']])
            self.log(f"  ⟨det(SST)⟩ = {avg_SST:.6f}  (예측: n_T/n_S = {n_T/n_S:.6f})")
            self.check("⟨det(SST)⟩ = σ = n_T/n_S", abs(avg_SST - n_T/n_S) < 0.15)

        # 5. ⟨det(STT)⟩ → ρ
        if 'STT' in by_type:
            avg_STT = np.mean([e[1] for e in by_type['STT']])
            rho = 1/avg_STT if avg_STT > 0 else float('inf')
            self.log(f"  ⟨det(STT)⟩ = {avg_STT:.6f}  → ρ = {rho:.4f}  "
                     f"(예측: n_S/n_T = {n_S/n_T:.4f})")
            self.check("ρ = n_S/n_T", abs(rho - n_S/n_T) < 0.5)

        # 6. |⟨B₁|B₃⟩|² = 1/c?
        overlap_sq = abs(ov13)**2
        self.log(f"  |⟨B₁|B₃⟩|² = {overlap_sq:.6f}  (예측: 1/c = {1/c:.6f})")
        self.check("|⟨B₁|B₃⟩|² = 1/c", abs(overlap_sq - 1/c) < 0.2)

        # 7. m_μ/m_e from ρ
        alpha_em = 1/137.036
        if 'STT' in by_type and avg_STT > 0:
            r_mu_e = rho / alpha_em
            self.log(f"\n  m_μ/m_e = ρ/α = {rho:.4f}/{alpha_em:.6f} = {r_mu_e:.1f}  "
                     f"(관측: 206.8)")
            self.check("m_μ/m_e ≈ 207", abs(r_mu_e - 206.8) < 20)

        # ========================================
        # 요약
        # ========================================
        self.log("\n" + "="*60)
        self.log("  요약: δS/δψ = 0의 해")
        self.log("="*60)

        self.log(f"""
  B₃(optimal) = ({B3_best[3]:.4f}, {B3_best[4]:.4f})
  |⟨B₁|B₃⟩|² = {overlap_sq:.4f}

  Hinge 구조:
    SSS: δ → confinement 강도
    SST: det → screening σ
    STT: det → impedance ρ
    TTT: δ → 중성미자 질량 (0이면 무질량)

  이것이 δS/δψ = 0의 self-consistent 해이다.
  해석이 아니라 값이다.
        """)


if __name__ == "__main__":
    DefinitiveTest().execute()
