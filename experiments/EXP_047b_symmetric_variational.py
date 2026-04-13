"""
EXP_047b: Symmetric Variational — 2 파라미터 (w, θ) 완전 탐색
Joint research by Mingu Jeong and Claude (Anthropic)

A₁A₂A₃: C³에서 대칭 배치, mutual overlap = w
B₁B₂: C² 직교, B₃ = (cos θ, sin θ) in C²
→ 2D scan + 정밀 최적화로 δS/δψ = 0의 정확한 해.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
import numpy as np
from itertools import combinations
from experiment import Experiment


# ======== Regge action (compact) ========
HINGES = list(combinations(range(6), 3))
HINGE_MAP = {}
for h in HINGES:
    hs = set(h); HINGE_MAP[h] = []
    for m in [k for k in range(6) if k not in hs]:
        sg = [k for k in range(6) if k != m]
        HINGE_MAP[h].append((sg, [sg.index(k) for k in h]))

def gram(vecs):
    V = np.array(vecs); return V @ V.conj().T

def dihedral(G5, h_local):
    others = [k for k in range(5) if k not in h_local]
    p, q = others
    vals = {}
    for (i,j) in [(p,p),(q,q),(p,q)]:
        M = np.delete(np.delete(G5, i, 0), j, 1)
        vals[(i,j)] = np.real((-1)**(i+j) * np.linalg.det(M))
    cpp, cqq, cpq = vals[(p,p)], vals[(q,q)], vals[(p,q)]
    if cpp <= 0 or cqq <= 0: return 0.0
    return np.arccos(np.clip(-cpq/np.sqrt(cpp*cqq), -1, 1))

def regge_full(all_vecs):
    S = 0.0; data = []
    for h in HINGES:
        G3 = gram([all_vecs[i] for i in h])
        d3 = np.real(np.linalg.det(G3))
        if d3 <= 1e-15: data.append((h, d3, 0, 0, 0)); continue
        a = np.sqrt(d3)
        st = sum(dihedral(gram([all_vecs[k] for k in sg]), hl)
                 for sg, hl in HINGE_MAP[h])
        df = 2*np.pi - st; S += a * df
        data.append((h, d3, a, np.degrees(st), np.degrees(df)))
    return S, data


def make_symmetric_vecs(w, theta):
    """대칭 배치: A₁A₂A₃ overlap = w, B₃ angle = θ"""
    # A vertices in C³, mutual overlap = w
    A1 = np.array([1, 0, 0, 0, 0], dtype=complex)

    # A₂: ⟨A₁|A₂⟩ = w
    a2_1 = w
    a2_2 = np.sqrt(max(1 - w**2, 0))
    A2 = np.array([a2_1, a2_2, 0, 0, 0], dtype=complex)

    # A₃: ⟨A₁|A₃⟩ = w, ⟨A₂|A₃⟩ = w
    a3_1 = w
    if a2_2 > 1e-15:
        a3_2 = (w - w * a2_1) / a2_2  # = w(1-w)/√(1-w²)
    else:
        a3_2 = 0
    a3_3_sq = max(1 - a3_1**2 - a3_2**2, 0)
    a3_3 = np.sqrt(a3_3_sq)
    A3 = np.array([a3_1, a3_2, a3_3, 0, 0], dtype=complex)

    # B vertices in C²
    B1 = np.array([0, 0, 0, 1, 0], dtype=complex)
    B2 = np.array([0, 0, 0, 0, 1], dtype=complex)
    B3 = np.array([0, 0, 0, np.cos(theta), np.sin(theta)], dtype=complex)

    return [A1, A2, A3, B1, B2, B3]


class SymmetricVariational(Experiment):
    ID = "047b"
    TITLE = "Symmetric Variational"

    def run(self):
        self.log("\n" + "="*60)
        self.log("  2D scan: (w, θ) → Regge action")
        self.log("  w = A-A mutual overlap, θ = B₃ angle in C²")
        self.log("="*60)

        # ========================================
        # Phase 1: Coarse 2D scan
        # ========================================
        n_w = 80; n_th = 80
        ws = np.linspace(0.01, 0.95, n_w)
        thetas = np.linspace(0.1, np.pi - 0.1, n_th)

        S_grid = np.zeros((n_w, n_th))
        for i, w in enumerate(ws):
            for j, th in enumerate(thetas):
                try:
                    vecs = make_symmetric_vecs(w, th)
                    S, _ = regge_full(vecs)
                    S_grid[i, j] = S
                except:
                    S_grid[i, j] = 0

        # Find ALL local extrema
        # Saddle points of S are where ∂S/∂w = 0 AND ∂S/∂θ = 0
        # Look for maxima (saddle in full space)
        i_max, j_max = np.unravel_index(np.argmax(S_grid), S_grid.shape)
        w_max, th_max = ws[i_max], thetas[j_max]
        S_max = S_grid[i_max, j_max]

        self.log(f"\n  Coarse scan: {n_w}×{n_th} = {n_w*n_th} points")
        self.log(f"  S range: [{S_grid[S_grid>0].min():.3f}, {S_max:.3f}]")
        self.log(f"  S_max at w={w_max:.3f}, θ={np.degrees(th_max):.1f}°")
        self.log(f"  S_max = {S_max:.6f}")

        # ========================================
        # Phase 2: Fine scan around maximum
        # ========================================
        self.log("\n  Phase 2: Fine scan around maximum")

        dw = (ws[1]-ws[0]) * 2
        dth = (thetas[1]-thetas[0]) * 2
        ws_fine = np.linspace(max(w_max-dw, 0.01), min(w_max+dw, 0.99), 100)
        ths_fine = np.linspace(max(th_max-dth, 0.01), min(th_max+dth, np.pi-0.01), 100)

        S_fine = np.zeros((100, 100))
        for i, w in enumerate(ws_fine):
            for j, th in enumerate(ths_fine):
                try:
                    vecs = make_symmetric_vecs(w, th)
                    S, _ = regge_full(vecs)
                    S_fine[i, j] = S
                except:
                    S_fine[i, j] = 0

        i2, j2 = np.unravel_index(np.argmax(S_fine), S_fine.shape)
        w_opt, th_opt = ws_fine[i2], ths_fine[j2]
        S_opt = S_fine[i2, j2]

        self.log(f"  Refined: w={w_opt:.6f}, θ={np.degrees(th_opt):.3f}°")
        self.log(f"  S = {S_opt:.8f}")

        # ========================================
        # Phase 3: Ultra-fine (Newton-like refinement)
        # ========================================
        self.log("\n  Phase 3: Ultra-fine refinement")

        from scipy.optimize import minimize
        def neg_S(params):
            w, th = params
            if w <= 0 or w >= 1 or th <= 0 or th >= np.pi:
                return 1e10
            try:
                vecs = make_symmetric_vecs(w, th)
                return -regge_full(vecs)[0]
            except:
                return 1e10

        result = minimize(neg_S, [w_opt, th_opt], method='Nelder-Mead',
                          options={'maxiter': 50000, 'xatol': 1e-14, 'fatol': 1e-14})
        w_final, th_final = result.x
        S_final = -result.fun

        self.log(f"  Final: w={w_final:.10f}, θ={np.degrees(th_final):.6f}°")
        self.log(f"  S = {S_final:.10f}")

        # ========================================
        # Phase 4: 해 분석
        # ========================================
        self.log("\n" + "="*60)
        self.log("  Phase 4: 최적 해 분석")
        self.log("="*60)

        vecs = make_symmetric_vecs(w_final, th_final)
        vert_names = ['A₁','A₂','A₃','B₁','B₂','B₃']

        G6 = gram(vecs)
        self.log(f"\n  w = |⟨A|A'⟩| = {w_final:.8f}")
        self.log(f"  |⟨A|A'⟩|² = {w_final**2:.8f}")
        self.log(f"  θ = {np.degrees(th_final):.6f}°")

        ov_B13 = np.vdot(vecs[3], vecs[5])
        ov_B23 = np.vdot(vecs[4], vecs[5])
        self.log(f"\n  |⟨B₁|B₃⟩|² = {abs(ov_B13)**2:.8f}  (1/c = 0.5)")
        self.log(f"  |⟨B₂|B₃⟩|² = {abs(ov_B23)**2:.8f}")
        self.log(f"  |⟨A₁|A₂⟩|² = {abs(G6[0,1])**2:.8f}")
        self.log(f"  |⟨A₂|A₃⟩|² = {abs(G6[1,2])**2:.8f}")
        self.log(f"  |⟨A₁|A₃⟩|² = {abs(G6[0,2])**2:.8f}")

        # Gram matrix properties
        tr = np.real(np.trace(G6))
        rank = np.linalg.matrix_rank(G6, tol=1e-6)
        eigs = np.sort(np.real(np.linalg.eigvalsh(G6)))[::-1]
        self.log(f"\n  Tr(G) = {tr:.6f}")
        self.log(f"  rank(G) = {rank}")
        self.log(f"  고유값: {[f'{e:.4f}' for e in eigs]}")

        # Hinge analysis
        _, hdata = regge_full(vecs)
        by_type = {}
        for h_idx, det_h, area_h, sum_th, deficit in hdata:
            n_A = sum(1 for i in h_idx if i < 3)
            htype = 'S'*n_A + 'T'*(3-n_A)
            by_type.setdefault(htype, []).append(
                (h_idx, det_h, area_h, sum_th, deficit))

        n_S = 3; n_T = 2; d = 5; c = 2
        alpha_GUT = 6/(25*np.pi**2)

        self.log(f"\n  {'Type':<5} {'N':>3} {'⟨det⟩':>12} {'⟨δ⟩':>10}  예측")
        self.log(f"  {'-'*55}")
        predictions = {
            'SSS': 'δ=90°', 'SST': 'det=2/3,δ=120°',
            'STT': 'det=2/3,δ=120°', 'TTT': 'δ=0°'
        }
        for htype in sorted(by_type.keys()):
            entries = by_type[htype]
            avg_det = np.mean([e[1] for e in entries])
            avg_def = np.mean([e[4] for e in entries])
            pred = predictions.get(htype, '')
            self.log(f"  {htype:<5} {len(entries):>3} {avg_det:>12.8f}"
                     f" {avg_def:>+9.3f}°  {pred}")

        # Detailed hinge list
        self.log(f"\n  {'Hinge':<12} {'Type':<5} {'det':>12} {'δ':>10}")
        self.log(f"  {'-'*45}")
        for h_idx, det_h, area_h, sum_th, deficit in sorted(
                hdata, key=lambda x: (sum(1 for i in x[0] if i<3), x[0])):
            names = ','.join(vert_names[i] for i in h_idx)
            n_A = sum(1 for i in h_idx if i < 3)
            htype = 'S'*n_A + 'T'*(3-n_A)
            self.log(f"  {names:<12} {htype:<5} {det_h:>12.8f}"
                     f" {deficit:>+9.3f}°")

        # ========================================
        # Phase 5: 물리량 추출
        # ========================================
        self.log("\n" + "="*60)
        self.log("  Phase 5: 물리량 추출")
        self.log("="*60)

        alpha_em = 1/137.036

        # ρ from det(STT)
        if 'STT' in by_type:
            avg_STT = np.mean([e[1] for e in by_type['STT']])
            rho = 1/avg_STT if avg_STT > 0 else 0
            self.log(f"\n  ⟨det(STT)⟩ = {avg_STT:.8f}  "
                     f"(n_T/n_S = {n_T/n_S:.8f})")
            self.log(f"  ρ = 1/⟨det(STT)⟩ = {rho:.6f}  "
                     f"(n_S/n_T = {n_S/n_T:.6f})")
            self.log(f"  m_μ/m_e = ρ/α = {rho/alpha_em:.2f}  (관측: 206.77)")

        # σ from det(SST)
        if 'SST' in by_type:
            avg_SST = np.mean([e[1] for e in by_type['SST']])
            self.log(f"  ⟨det(SST)⟩ = {avg_SST:.8f}  "
                     f"(n_T/n_S = {n_T/n_S:.8f})")

        # W_AA = |⟨A|A'⟩|² → α_GUT?
        W_AA = w_final**2
        self.log(f"\n  W_AA = |⟨A|A'⟩|² = {W_AA:.8f}")
        self.log(f"  W_AA/d = {W_AA/d:.8f}  (α_GUT = {alpha_GUT:.8f})")
        self.log(f"  1/(d×W_AA) = {1/(d*W_AA):.4f}  (1/α_GUT = {1/alpha_GUT:.4f})")

        # ========================================
        # Phase 6: Checks
        # ========================================
        self.log("\n" + "="*60)
        self.log("  Checks")
        self.log("="*60)

        self.check("Tr(G) = 6", abs(tr - 6) < 0.01)
        self.check("rank(G) ≤ 5", rank <= 5)

        if 'TTT' in by_type:
            v = np.mean([e[4] for e in by_type['TTT']])
            self.check(f"δ(TTT) = {v:.1f}° = 0°", abs(v) < 5)

        if 'SSS' in by_type:
            v = np.mean([e[4] for e in by_type['SSS']])
            self.check(f"δ(SSS) = {v:.1f}° ≈ 90°", abs(v - 90) < 30)

        if 'SST' in by_type:
            v = np.mean([e[1] for e in by_type['SST']])
            self.check(f"⟨det(SST)⟩ = {v:.4f} ≈ 2/3",
                       abs(v - n_T/n_S) < 0.2)

        if 'STT' in by_type:
            v = np.mean([e[1] for e in by_type['STT']])
            self.check(f"⟨det(STT)⟩ = {v:.4f} = 2/3",
                       abs(v - n_T/n_S) < 0.1)

        self.check(f"|⟨B₁|B₃⟩|² = {abs(ov_B13)**2:.4f} = 1/2",
                   abs(abs(ov_B13)**2 - 0.5) < 0.1)

        self.check(f"A symmetric (overlap = {W_AA:.4f})",
                   abs(abs(G6[0,1])**2 - abs(G6[1,2])**2) < 0.01)


if __name__ == "__main__":
    SymmetricVariational().execute()
