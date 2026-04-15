"""
ATM_027: Free A Vectors — Does 22 → 25?
Joint research by Mingu Jeong and Claude (Anthropic)

ATM_026 found: S_total = 22*pi with fixed A vectors (rigid spatial basis).
22 = d^2 - N_S = 25 - 3. If the 3 frozen DOF correspond to A being rigid,
then freeing the A vectors (adding small perturbation delta_A) should
change the effective count from 22 toward 25.

Test: perturb A vectors with parameter eta (A_i gets small temporal component),
then compute S_total(eta, eps→0) and check if it approaches 25*pi.

Configuration:
  A_i = [eta_i0, eta_i1, (original spatial)]  (eta = temporal "leakage")
  B1 = [t, 0, eps, eps, eps]  (electron)
  B2, B3 = [0, ±1, 0, 0, 0]  (temporal, symmetric)

If S_total(eta) = (22 + f(eta))*pi → check whether f(eta→max) → 3.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from itertools import combinations
from experiment import Experiment

ALPHA_GUT = 6 / (25 * np.pi**2)
D = 5; N_S = 3; N_T = 2

S1 = (0,1,2,3,4)
S2 = (0,1,2,3,5)
SIMPLICES = [S1, S2]


def make_psi6(eps, eta):
    """6 vectors with A perturbation eta in temporal sector.
    eta = small temporal component added to A vectors.
    Each A_i gets a different phase to avoid degeneracy."""
    psi = np.zeros((6, 5), dtype=complex)
    # A vectors: mostly spatial, small temporal leakage
    # A1 = [eta*cos(0), eta*sin(0), sqrt(1-eta^2), 0, 0]
    # A2 = [eta*cos(2pi/3), eta*sin(2pi/3), 0, sqrt(1-eta^2), 0]
    # A3 = [eta*cos(4pi/3), eta*sin(4pi/3), 0, 0, sqrt(1-eta^2)]
    for i in range(3):
        phase = 2 * np.pi * i / 3
        s = np.sqrt(max(0, 1 - eta**2))
        psi[i, 0] = eta * np.cos(phase)
        psi[i, 1] = eta * np.sin(phase)
        psi[i, 2+i] = s

    # B1 = electron
    t1 = np.sqrt(max(0, 1 - 3*eps**2))
    psi[3] = [t1, 0, eps, eps, eps]
    # B2, B3 = symmetric temporal
    psi[4] = [0, 1, 0, 0, 0]
    psi[5] = [0, -1, 0, 0, 0]
    return psi


def build_G(psi6):
    return psi6 @ psi6.conj().T


def hinge_det(G, tri):
    idx = list(tri)
    return float(np.linalg.det(G[np.ix_(idx, idx)]).real)


def dihedral_in_simplex(G_global, simplex_verts, hinge):
    sv = list(simplex_verts)
    opp = [v for v in sv if v not in hinge]
    G_local = G_global[np.ix_(sv, sv)]
    det_local = np.linalg.det(G_local).real
    if abs(det_local) < 1e-15:
        return np.pi
    G_inv = np.linalg.inv(G_local)
    l, m = sv.index(opp[0]), sv.index(opp[1])
    num = -G_inv[l, m].real
    den = np.sqrt(max(1e-30, abs(G_inv[l,l].real * G_inv[m,m].real)))
    return float(np.arccos(np.clip(num / den, -1, 1)))


def deficit_angle_manifold(G, hinge):
    theta_sum = 0.0
    for sx in SIMPLICES:
        if set(hinge).issubset(set(sx)):
            theta_sum += dihedral_in_simplex(G, sx, hinge)
    return 2 * np.pi - theta_sum


def get_all_hinges():
    all_tris = set()
    for sx in SIMPLICES:
        for tri in combinations(sx, 3):
            all_tris.add(tri)
    return sorted(all_tris)

ALL_HINGES = get_all_hinges()


def classify_fine(tri):
    nA = sum(1 for v in tri if v < 3)
    has_B1 = 3 in tri
    has_Bt = any(v in tri for v in [4, 5])
    if nA == 3:
        return 'AAA'
    elif nA == 2:
        return 'AABe' if has_B1 else 'AABt'
    elif nA == 1:
        if has_B1 and has_Bt:
            return 'ABet'
        elif not has_B1:
            return 'ABtt'
        return 'ABee'
    return 'BBB'


def regge_action(G):
    S = 0.0
    for tri in ALL_HINGES:
        d = hinge_det(G, tri)
        if d > 0:
            S += np.sqrt(d) * deficit_angle_manifold(G, tri)
    return S


def hinge_binet_cauchy(psi, tri):
    Phi = psi[list(tri)]
    k0, k1, k2 = 0.0, 0.0, 0.0
    for cols in combinations(range(5), 3):
        sub = Phi[:, cols]
        d2 = abs(np.linalg.det(sub))**2
        n_temp = sum(1 for c in cols if c < N_T)
        if n_temp == 0:
            k0 += d2
        elif n_temp == 1:
            k1 += d2
        else:
            k2 += d2
    return k0, k1, k2


class FreeAVectors(Experiment):
    ID = "ATM_027"
    TITLE = "Free A Vectors"

    def run(self):
        self.test1_S_vs_eta()
        self.test2_channel_ratio_vs_eta()
        self.test3_delta_vs_eta()
        self.test4_combined_search()

    def test1_S_vs_eta(self):
        """S_total(eta) at eps=0. Does S approach 25*pi?"""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 1: S_total vs eta (A-vector temporal leakage)")
        self.log(f"  At eps=0.001 (electron nearly pure temporal)")
        self.log(f"  Prediction: S(eta=0) = 22*pi, S(eta→?) → 25*pi?")
        self.log(f"  {'='*60}")

        eps = 0.001  # nearly zero
        eta_vals = np.concatenate([
            np.linspace(0, 0.01, 5),
            np.linspace(0.02, 0.1, 9),
            np.linspace(0.15, 0.5, 8),
            np.linspace(0.55, 0.99, 5),
        ])

        self.log(f"\n  {'eta':>8} {'S_total':>12} {'S/pi':>10}"
                 f" {'delta_AAA':>10} {'dAAA/pi':>8}")

        for eta in eta_vals:
            psi = make_psi6(eps, eta)
            G = build_G(psi)
            S = regge_action(G)
            delta_aaa = deficit_angle_manifold(G, (0,1,2))
            self.log(f"  {eta:8.4f} {S:12.5f} {S/np.pi:10.5f}"
                     f" {delta_aaa:10.5f} {delta_aaa/np.pi:8.4f}")

        # Key check
        psi0 = make_psi6(eps, 0.0)
        S0 = regge_action(build_G(psi0))
        self.log(f"\n  S(eta=0)/pi = {S0/np.pi:.5f} (expect 22.000)")
        self.log(f"  Target: 25*pi = {25*np.pi:.5f}")
        self.check("S_total vs eta mapped", True)

    def test2_channel_ratio_vs_eta(self):
        """R_SSS(eta) at eps=0. Does R approach alpha_GUT?"""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 2: R_SSS = S_SSS/S_total vs eta")
        self.log(f"  {'='*60}")

        eps = 0.001
        eta_vals = np.concatenate([
            np.linspace(0, 0.01, 5),
            np.linspace(0.02, 0.1, 9),
            np.linspace(0.15, 0.5, 8),
        ])

        self.log(f"\n  {'eta':>8} {'R_SSS':>10} {'R/aGUT':>8}"
                 f" {'1/(R*z2)':>10}")

        for eta in eta_vals:
            psi = make_psi6(eps, eta)
            G = build_G(psi)

            s_sss, s_tot = 0.0, 0.0
            for tri in ALL_HINGES:
                d = hinge_det(G, tri)
                if d <= 0:
                    continue
                area = np.sqrt(d)
                delta = deficit_angle_manifold(G, tri)
                s_tot += area * delta
                k0, k1, k2 = hinge_binet_cauchy(psi, tri)
                total_bc = k0 + k1 + k2
                if total_bc > 0:
                    s_sss += area * delta * k0 / total_bc

            r_sss = s_sss / s_tot if abs(s_tot) > 1e-15 else 0
            zeta2 = np.pi**2 / 6
            inv_r_z2 = 1 / (r_sss * zeta2) if r_sss > 0 else float('inf')
            self.log(f"  {eta:8.4f} {r_sss:10.6f}"
                     f" {r_sss/ALPHA_GUT:8.4f}"
                     f" {inv_r_z2:10.4f}")

        self.log(f"\n  Target: R_SSS = alpha_GUT = {ALPHA_GUT:.6f}")
        self.log(f"  Or: R_SSS = 1/25 = {1/25:.6f}")
        self.check("R_SSS vs eta mapped", True)

    def test3_delta_vs_eta(self):
        """How do deficit angles change with eta?"""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 3: Deficit angles vs eta (eps=0.001)")
        self.log(f"  {'='*60}")

        eps = 0.001
        ftypes = {}
        for tri in ALL_HINGES:
            t = classify_fine(tri)
            ftypes.setdefault(t, []).append(tri)

        eta_vals = [0, 0.01, 0.05, 0.1, 0.2, 0.3, 0.4, 0.5]
        order = ['AAA', 'AABe', 'AABt', 'ABet']

        header = f"  {'eta':>8}"
        for t in order:
            if t in ftypes:
                header += f" {'d_'+t+'/pi':>10}"
        self.log(header)

        for eta in eta_vals:
            psi = make_psi6(eps, eta)
            G = build_G(psi)
            line = f"  {eta:8.4f}"
            for t in order:
                if t not in ftypes:
                    continue
                deltas = [deficit_angle_manifold(G, tri)
                          for tri in ftypes[t]]
                avg = np.mean(deltas)
                line += f" {avg/np.pi:10.5f}"
            self.log(line)

        self.check("Deficit vs eta mapped", True)

    def test4_combined_search(self):
        """Search (eta, eps) space for R_SSS = alpha_GUT or 1/25."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 4: 2D search — does (eta,eps) exist with")
        self.log(f"          R_SSS = alpha_GUT = {ALPHA_GUT:.6f}?")
        self.log(f"  {'='*60}")

        best_dist_agut = 1e10
        best_params_agut = None
        best_dist_25 = 1e10
        best_params_25 = None

        eta_vals = np.linspace(0, 0.6, 30)
        eps_vals = np.linspace(0.001, 0.4, 30)

        for eta in eta_vals:
            for eps in eps_vals:
                psi = make_psi6(eps, eta)
                G = build_G(psi)
                s_sss, s_tot = 0.0, 0.0
                for tri in ALL_HINGES:
                    d = hinge_det(G, tri)
                    if d <= 0:
                        continue
                    area = np.sqrt(d)
                    delta = deficit_angle_manifold(G, tri)
                    s_tot += area * delta
                    k0, k1, k2 = hinge_binet_cauchy(psi, tri)
                    total_bc = k0 + k1 + k2
                    if total_bc > 0:
                        s_sss += area * delta * k0 / total_bc

                r_sss = s_sss / s_tot if abs(s_tot) > 1e-15 else 0

                dist_agut = abs(r_sss - ALPHA_GUT)
                if dist_agut < best_dist_agut:
                    best_dist_agut = dist_agut
                    best_params_agut = (eta, eps, r_sss, s_tot)

                dist_25 = abs(r_sss - 1/25)
                if dist_25 < best_dist_25:
                    best_dist_25 = dist_25
                    best_params_25 = (eta, eps, r_sss, s_tot)

        self.log(f"\n  Closest to alpha_GUT = {ALPHA_GUT:.6f}:")
        if best_params_agut:
            eta, eps, r, s = best_params_agut
            self.log(f"    eta={eta:.4f}, eps={eps:.4f}")
            self.log(f"    R_SSS={r:.6f}, dist={best_dist_agut:.6f}")
            self.log(f"    S_total={s:.4f}, S/pi={s/np.pi:.4f}")

        self.log(f"\n  Closest to 1/25 = {1/25:.6f}:")
        if best_params_25:
            eta, eps, r, s = best_params_25
            self.log(f"    eta={eta:.4f}, eps={eps:.4f}")
            self.log(f"    R_SSS={r:.6f}, dist={best_dist_25:.6f}")
            self.log(f"    S_total={s:.4f}, S/pi={s/np.pi:.4f}")

        # Also check: does S_total ever reach 25*pi?
        self.log(f"\n  S_total range:")
        s_min, s_max = 1e10, -1e10
        for eta in np.linspace(0, 0.8, 20):
            for eps in np.linspace(0.001, 0.5, 20):
                psi = make_psi6(eps, eta)
                G = build_G(psi)
                s = regge_action(G)
                s_min = min(s_min, s)
                s_max = max(s_max, s)
        self.log(f"    [{s_min/np.pi:.3f}*pi, {s_max/np.pi:.3f}*pi]")
        self.log(f"    Target: 25*pi = {25*np.pi:.4f}")

        reached_25 = s_max >= 25 * np.pi * 0.99
        self.check("25pi reachable", reached_25)
        self.check("2D search done", True)


if __name__ == "__main__":
    FreeAVectors().execute()
