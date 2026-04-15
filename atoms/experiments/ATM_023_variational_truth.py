"""
ATM_023: What Does δS/δψ=0 Actually Give?
Joint research by Mingu Jeong and Claude (Anthropic)

THE fundamental test: do screening constants EMERGE from the
variational principle, or were they just pattern-matched?

Framework: ∂(Δ⁵) with 6 vertices
  A₁,A₂,A₃ = spatial basis (nucleus, fixed)
  B₁,B₂,B₃ = electrons (variable)

For each atom: optimize binding functional over B-positions,
extract the coupling ε and screening σ that EMERGE.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from scipy.optimize import minimize
from itertools import combinations
from experiment import Experiment

ALPHA = 1 / 137.035999084
D = 5; N_S = 3; N_T = 2
Ry = 13.606

# Fixed A-vertices
A = np.array([[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]], dtype=complex)
ALL_TRIS = list(combinations(range(6), 3))   # 20 hinges
ALL_4S = list(combinations(range(6), 5))      # 6 four-simplices


# ═══════════════════════════════════════════════
#  Geometry engine
# ═══════════════════════════════════════════════

def hinge_det(G, tri):
    idx = list(tri)
    return float(np.linalg.det(G[np.ix_(idx, idx)]).real)


def dihedral_angle(G, simplex, hinge):
    sv = list(simplex)
    opp = [v for v in sv if v not in hinge]
    G_sub = G[np.ix_(sv, sv)]
    det_sub = np.linalg.det(G_sub).real
    if abs(det_sub) < 1e-15:
        return np.pi / 2
    G_inv = np.linalg.inv(G_sub)
    pd, pe = sv.index(opp[0]), sv.index(opp[1])
    num = -G_inv[pd, pe].real
    den = np.sqrt(max(1e-30, abs(G_inv[pd, pd].real * G_inv[pe, pe].real)))
    return float(np.arccos(np.clip(num / den, -1, 1)))


def deficit_angle(G, hinge):
    hv = set(hinge)
    s = sum(dihedral_angle(G, sx, hinge)
            for sx in ALL_4S if hv.issubset(set(sx)))
    return 2 * np.pi - s


def regge_action(G):
    S = 0.0
    for tri in ALL_TRIS:
        d = hinge_det(G, tri)
        if d > 0:
            S += np.sqrt(d) * deficit_angle(G, tri)
    return S


def classify(tri):
    """Number of A-vertices in triangle."""
    return sum(1 for v in tri if v < 3)


def all_functionals(G):
    """Compute all candidate energy functionals."""
    f = {'AAA': 0, 'AAB': 0, 'ABB': 0, 'BBB': 0}
    for tri in ALL_TRIS:
        c = classify(tri)
        key = {3: 'AAA', 2: 'AAB', 1: 'ABB', 0: 'BBB'}[c]
        f[key] += (1 - hinge_det(G, tri))
    f['S'] = regge_action(G)
    f['bind'] = f['AAB'] - (N_T / N_S) * f['ABB']
    return f


# ═══════════════════════════════════════════════
#  B-vertex parametrization and optimization
# ═══════════════════════════════════════════════

def make_psi_symmetric(params, n_elec):
    """Symmetric ansatz: ψ_B = [t cosφ, t sinφ, ε, ε, ε]."""
    psi = np.zeros((6, 5), dtype=complex)
    psi[:3] = A
    for i in range(n_elec):
        eps = params[2 * i]
        phi = params[2 * i + 1]
        t = np.sqrt(max(0, 1 - 3 * eps**2))
        psi[3 + i] = [t * np.cos(phi), t * np.sin(phi), eps, eps, eps]
    # Unused B-slots: orthogonal temporal
    for i in range(n_elec, 3):
        ang = np.pi / 4 * (i + 1)
        psi[3 + i] = [np.cos(ang), np.sin(ang), 0, 0, 0]
    return psi


def extract_coupling(psi, idx):
    """Extract electron-nucleus coupling for B-vertex idx."""
    v = psi[idx]
    eps_sq = sum(abs(v[k])**2 for k in range(2, 5))  # spatial components
    return np.sqrt(eps_sq)


def solve_atom(Z, n_elec, n_trials=50, log=None):
    """
    Find ALL critical points for atom with Z, n_elec electrons.
    Uses symmetric ansatz + landscape scan.
    """
    n_params = 2 * n_elec  # (eps, phi) per electron
    eps_max = 1 / np.sqrt(3) - 0.001  # normalization limit

    results = []

    # Strategy 1: systematic eps sweep (most important!)
    eps_vals = np.linspace(0.001, eps_max, 50)
    for eps_init in eps_vals:
        phis = [np.pi / (n_elec + 1) * (i + 1) for i in range(n_elec)]
        p0 = []
        for i in range(n_elec):
            p0.extend([eps_init, phis[i]])
        p0 = np.array(p0)

        for sign in [-1, 1]:  # both max and min
            def objective(p, s=sign):
                psi = make_psi_symmetric(np.abs(p), n_elec)
                G = psi @ psi.conj().T
                return s * regge_action(G)

            bounds = [(0.0001, eps_max), (0, 2*np.pi)] * n_elec
            try:
                res = minimize(objective, p0, method='L-BFGS-B',
                               bounds=bounds,
                               options={'maxiter': 3000, 'ftol': 1e-15})
                psi = make_psi_symmetric(np.abs(res.x), n_elec)
                G = psi @ psi.conj().T
                f = all_functionals(G)
                S = regge_action(G)
                bind = Z * f['AAB'] - (N_T / N_S) * f['ABB']
                eps_list = [np.abs(res.x[2*i]) for i in range(n_elec)]
                results.append({
                    'bind': bind, 'S': S,
                    'eps': sorted(eps_list, reverse=True),
                    'funcs': f, 'sign': sign
                })
            except Exception:
                pass

    # Strategy 2: random starts
    for trial in range(n_trials):
        p0 = np.random.uniform(0.001, eps_max, n_params)
        for i in range(n_elec):
            p0[2*i+1] = np.random.uniform(0, 2*np.pi)

        for sign in [-1, 1]:
            def objective(p, s=sign):
                psi = make_psi_symmetric(np.abs(p), n_elec)
                G = psi @ psi.conj().T
                return s * regge_action(G)

            bounds = [(0.0001, eps_max), (0, 2*np.pi)] * n_elec
            try:
                res = minimize(objective, p0, method='L-BFGS-B',
                               bounds=bounds,
                               options={'maxiter': 3000, 'ftol': 1e-15})
                psi = make_psi_symmetric(np.abs(res.x), n_elec)
                G = psi @ psi.conj().T
                f = all_functionals(G)
                S = regge_action(G)
                bind = Z * f['AAB'] - (N_T / N_S) * f['ABB']
                eps_list = [np.abs(res.x[2*i]) for i in range(n_elec)]
                results.append({
                    'bind': bind, 'S': S,
                    'eps': sorted(eps_list, reverse=True),
                    'funcs': f, 'sign': sign
                })
            except Exception:
                pass

    if not results:
        return []

    # Cluster by (S, sign) to find distinct critical points
    results.sort(key=lambda r: r['S'], reverse=True)
    unique = [results[0]]
    for r in results[1:]:
        if all(abs(r['S'] - u['S']) > 1e-4 for u in unique):
            unique.append(r)
    return unique[:15]


# ═══════════════════════════════════════════════
#  Experiment
# ═══════════════════════════════════════════════

class VariationalTruth(Experiment):
    ID = "ATM_023"
    TITLE = "Variational Truth Test"

    def run(self):
        self.test_landscape()
        self.test_hydrogen()
        self.test_helium()
        self.test_lithium()

    def test_landscape(self):
        """Scan S(ε) to see the action landscape directly."""
        self.log(f"\n  {'='*60}")
        self.log(f"  ACTION LANDSCAPE: S(eps) for 1 electron")
        self.log(f"  {'='*60}")
        self.log(f"  eps      S(eps)       F_AAB     F_ABB")
        eps_max = 1/np.sqrt(3) - 0.001
        for eps in np.concatenate([
            np.linspace(0.001, 0.02, 20),
            np.linspace(0.02, 0.1, 10),
            np.linspace(0.1, eps_max, 10)]):
            psi = make_psi_symmetric([eps, 0.0], 1)
            G = psi @ psi.conj().T
            f = all_functionals(G)
            self.log(f"  {eps:.5f}  {f['S']:10.5f}  {f['AAB']:9.6f}"
                     f"  {f['ABB']:9.6f}")
        self.check("Landscape scanned", True)

    def report_solutions(self, name, Z, n_elec, solutions):
        self.log(f"\n  {name} (Z={Z}, {n_elec}e): {len(solutions)} solutions")
        for i, sol in enumerate(solutions):
            eps_str = ', '.join(f'{e:.6f}' for e in sol['eps'])
            self.log(f"  #{i+1}: S={sol['S']:.6f}  bind={sol['bind']:.6f}"
                     f"  eps=[{eps_str}]")
            f = sol['funcs']
            self.log(f"       AAB={f['AAB']:.6f} ABB={f['ABB']:.6f}"
                     f" BBB={f['BBB']:.6f}")

    def test_hydrogen(self):
        self.log(f"\n  {'='*60}")
        self.log(f"  HYDROGEN: Z=1, 1 electron")
        self.log(f"  Expected: eps = alpha/sqrt(3) = {ALPHA/np.sqrt(3):.6f}")
        self.log(f"  {'='*60}")

        sols = solve_atom(Z=1, n_elec=1, n_trials=50)
        self.report_solutions("H", 1, 1, sols)

        if sols:
            best = sols[0]
            eps_H = best['eps'][0]
            eps_expected = ALPHA / np.sqrt(3)
            self.log(f"\n  Best: eps = {eps_H:.6f}")
            self.log(f"  Expected:  {eps_expected:.6f}")
            self.log(f"  Ratio:     {eps_H/eps_expected:.4f}")
            self.bind_H = best['bind']
            self.log(f"  F_bind(H) = {self.bind_H:.8f}")
        self.check("H solutions found", len(sols) > 0)

    def test_helium(self):
        self.log(f"\n  {'='*60}")
        self.log(f"  HELIUM: Z=2, 2 electrons")
        self.log(f"  Question: does screening 4*alpha_GUT emerge?")
        self.log(f"  {'='*60}")

        # He: 2 electrons
        sols_He = solve_atom(Z=2, n_elec=2, n_trials=50)
        self.report_solutions("He", 2, 2, sols_He)

        # He+: 1 electron (Z=2)
        sols_Hep = solve_atom(Z=2, n_elec=1, n_trials=100)
        self.report_solutions("He+", 2, 1, sols_Hep)

        if sols_He and sols_Hep:
            F_He = sols_He[0]['bind']
            F_Hep = sols_Hep[0]['bind']
            IE_ratio = (F_He - F_Hep) / self.bind_H if hasattr(self, 'bind_H') and self.bind_H > 0 else 0
            self.log(f"\n  F_bind(He)  = {F_He:.8f}")
            self.log(f"  F_bind(He+) = {F_Hep:.8f}")
            self.log(f"  Delta_F     = {F_He - F_Hep:.8f}")
            self.log(f"  IE(He)/IE(H) = {IE_ratio:.4f}")
            self.log(f"  Expected:     {24.587/13.606:.4f}")

            # Extract screening
            eps_He = sols_He[0]['eps']
            self.log(f"\n  He electron couplings: {eps_He}")
            if len(eps_He) >= 2:
                avg_eps = np.mean(eps_He)
                eps_Z2 = 2 * ALPHA / np.sqrt(3)
                sigma_eff = 1 - avg_eps / eps_Z2 if eps_Z2 > 0 else 0
                self.log(f"  Avg eps = {avg_eps:.6f}")
                self.log(f"  Bare Z=2 eps = {eps_Z2:.6f}")
                self.log(f"  Effective sigma = {sigma_eff:.4f}")

        self.check("He solutions found", len(sols_He) > 0)

    def test_lithium(self):
        self.log(f"\n  {'='*60}")
        self.log(f"  LITHIUM: Z=3, 3 electrons")
        self.log(f"  Question: do shells emerge? sigma=7/8?")
        self.log(f"  {'='*60}")

        sols_Li = solve_atom(Z=3, n_elec=3, n_trials=50)
        self.report_solutions("Li", 3, 3, sols_Li)

        # Li+: 2 electrons (Z=3)
        sols_Lip = solve_atom(Z=3, n_elec=2, n_trials=50)
        self.report_solutions("Li+", 3, 2, sols_Lip)

        if sols_Li and sols_Lip and hasattr(self, 'bind_H'):
            F_Li = sols_Li[0]['bind']
            F_Lip = sols_Lip[0]['bind']
            IE_ratio = (F_Li - F_Lip) / self.bind_H if self.bind_H > 0 else 0
            self.log(f"\n  F_bind(Li)  = {F_Li:.8f}")
            self.log(f"  F_bind(Li+) = {F_Lip:.8f}")
            self.log(f"  IE(Li)/IE(H) = {IE_ratio:.4f}")
            self.log(f"  Expected:     {5.392/13.606:.4f}")

            # Shell structure
            eps_Li = sols_Li[0]['eps']
            self.log(f"\n  Li electron couplings: {eps_Li}")
            if len(eps_Li) >= 3:
                # Two 1s electrons should have similar eps
                # One 2s electron should have smaller eps
                self.log(f"  eps_1 = {eps_Li[0]:.6f} (1s?)")
                self.log(f"  eps_2 = {eps_Li[1]:.6f} (1s?)")
                self.log(f"  eps_3 = {eps_Li[2]:.6f} (2s?)")
                if eps_Li[0] > 0:
                    ratio = eps_Li[2] / eps_Li[0]
                    self.log(f"  eps_3/eps_1 = {ratio:.4f}")
                    self.log(f"  (if shells: inner~outer ratio)")

        self.check("Li solutions found", len(sols_Li) > 0)
        self.check("Li shows shell structure",
                    len(sols_Li) > 0 and len(sols_Li[0]['eps']) >= 3
                    and sols_Li[0]['eps'][0] > 1.5 * sols_Li[0]['eps'][2])


if __name__ == "__main__":
    VariationalTruth().execute()
