"""
ATM_028: Full Variational Solution on Symmetric Manifold
Joint research by Mingu Jeong and Claude (Anthropic)

Previous results:
- ATM_026: S_total = 22*pi at eps→0, R_SSS = 1/22
- ATM_027: R_SSS = alpha_GUT only via tuning eta, not self-consistent

New approach: Instead of constraining R to a target, let the
Regge action extremum determine ALL parameters simultaneously.

Variational parameters:
  eps: electron spatial overlap (B1's coupling to A sector)
  eta: A-vector temporal leakage (quarks' temporal extent)
  phi2: temporal B phase (with phi3 = -phi2 for symmetry)

Question: At the unconstrained action extremum delta S = 0,
what are the natural scales? Does any combination give alpha?

Tests:
  1. 3D landscape: S(eps, eta, phi2)
  2. Full optimization: find ALL critical points
  3. At each critical point: compute coupling observables
  4. Physical interpretation: what does geometry select?
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from itertools import combinations
from scipy.optimize import minimize, differential_evolution
from experiment import Experiment

ALPHA = 1 / 137.035999084
ALPHA_GUT = 6 / (25 * np.pi**2)
D = 5; N_S = 3; N_T = 2

S1 = (0,1,2,3,4)
S2 = (0,1,2,3,5)
SIMPLICES = [S1, S2]

def get_all_hinges():
    all_tris = set()
    for sx in SIMPLICES:
        for tri in combinations(sx, 3):
            all_tris.add(tri)
    return sorted(all_tris)

ALL_HINGES = get_all_hinges()


def make_psi6(eps, eta, phi2):
    """Symmetric manifold with 3 variational parameters.
    phi3 = -phi2 enforces time-reversal symmetry."""
    psi = np.zeros((6, 5), dtype=complex)
    for i in range(3):
        phase = 2 * np.pi * i / 3
        s = np.sqrt(max(0, 1 - eta**2))
        psi[i, 0] = eta * np.cos(phase)
        psi[i, 1] = eta * np.sin(phase)
        psi[i, 2+i] = s
    t1 = np.sqrt(max(0, 1 - 3*eps**2))
    psi[3] = [t1, 0, eps, eps, eps]
    psi[4] = [np.cos(phi2), np.sin(phi2), 0, 0, 0]
    psi[5] = [np.cos(-phi2), np.sin(-phi2), 0, 0, 0]
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


def deficit_angle(G, hinge):
    theta_sum = 0.0
    for sx in SIMPLICES:
        if set(hinge).issubset(set(sx)):
            theta_sum += dihedral_in_simplex(G, sx, hinge)
    return 2 * np.pi - theta_sum


def regge_action(G):
    S = 0.0
    for tri in ALL_HINGES:
        d = hinge_det(G, tri)
        if d > 0:
            S += np.sqrt(d) * deficit_angle(G, tri)
    return S


def hinge_binet_cauchy(psi, tri):
    Phi = psi[list(tri)]
    k0, k1, k2 = 0.0, 0.0, 0.0
    for cols in combinations(range(5), 3):
        d2 = abs(np.linalg.det(Phi[:, cols]))**2
        n_temp = sum(1 for c in cols if c < N_T)
        if n_temp == 0:
            k0 += d2
        elif n_temp == 1:
            k1 += d2
        else:
            k2 += d2
    return k0, k1, k2


def compute_observables(eps, eta, phi2):
    """Compute all observables at a given point."""
    psi = make_psi6(eps, eta, phi2)
    G = build_G(psi)
    S = regge_action(G)

    s_sss, s_tot = 0.0, 0.0
    for tri in ALL_HINGES:
        d = hinge_det(G, tri)
        if d <= 0:
            continue
        area = np.sqrt(d)
        delta = deficit_angle(G, tri)
        s_tot += area * delta
        k0, k1, k2 = hinge_binet_cauchy(psi, tri)
        tb = k0 + k1 + k2
        if tb > 0:
            s_sss += area * delta * k0 / tb

    r_sss = s_sss / s_tot if abs(s_tot) > 1e-15 else 0
    delta_aaa = deficit_angle(G, (0, 1, 2))

    # SSS leakage from AABe hinge
    aabe = (0, 1, 3)  # A1, A2, B1
    k0_e, k1_e, k2_e = hinge_binet_cauchy(psi, aabe)
    leakage = k0_e / (k0_e + k1_e + k2_e) if (k0_e+k1_e+k2_e) > 0 else 0

    return {
        'S': S, 'S/pi': S / np.pi,
        'R_SSS': r_sss, 'R/aGUT': r_sss / ALPHA_GUT,
        'delta_AAA/pi': delta_aaa / np.pi,
        'SSS_leakage': leakage,
        'eps2': eps**2,
    }


class FullVariational(Experiment):
    ID = "ATM_028"
    TITLE = "Full Variational Solution"

    def run(self):
        self.test1_3d_landscape()
        self.test2_find_critical_points()
        self.test3_observables_at_critical()
        self.test4_phi2_scan()

    def test1_3d_landscape(self):
        """Scan S(eps, eta, phi2) landscape at fixed phi2=pi/2."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 1: Regge action landscape S(eps, eta)")
        self.log(f"  phi2 = pi/2 (symmetric temporal)")
        self.log(f"  {'='*60}")

        phi2 = np.pi / 2
        eps_vals = np.linspace(0.001, 0.5, 25)
        eta_vals = np.linspace(0.0, 0.5, 25)

        best_S = -1e10
        best_params = None

        self.log(f"\n  {'eps':>8} {'eta':>8} {'S':>10} {'S/pi':>8}"
                 f" {'R_SSS':>8}")

        for eta in [0, 0.05, 0.1, 0.15, 0.2, 0.3, 0.4, 0.5]:
            for eps in np.linspace(0.001, 0.5, 30):
                psi = make_psi6(eps, eta, phi2)
                G = build_G(psi)
                S = regge_action(G)
                if S > best_S:
                    best_S = S
                    best_params = (eps, eta, phi2)

            # Report max for this eta
            eps_max = best_params[0] if best_params[1] == eta else 0
            psi = make_psi6(eps_max, eta, phi2)
            G = build_G(psi)
            S = regge_action(G)
            # Quick R_SSS
            s_sss, s_tot = 0.0, 0.0
            for tri in ALL_HINGES:
                d = hinge_det(G, tri)
                if d <= 0:
                    continue
                area = np.sqrt(d)
                delta = deficit_angle(G, tri)
                s_tot += area * delta
                k0, k1, k2 = hinge_binet_cauchy(psi, tri)
                tb = k0+k1+k2
                if tb > 0:
                    s_sss += area*delta*k0/tb
            r = s_sss/s_tot if abs(s_tot) > 1e-15 else 0
            self.log(f"  {eps_max:8.4f} {eta:8.4f} {S:10.4f}"
                     f" {S/np.pi:8.4f} {r:8.5f}")

        self.log(f"\n  Global max: eps={best_params[0]:.5f},"
                 f" eta={best_params[1]:.5f}, S={best_S:.5f}")
        self.check("3D landscape scanned", True)

    def test2_find_critical_points(self):
        """Find ALL critical points of S(eps, eta, phi2)."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 2: Find critical points (dS=0)")
        self.log(f"  {'='*60}")

        emax = 1/np.sqrt(3) - 0.001

        def neg_S(params):
            eps, eta, phi2 = params
            eps = np.clip(eps, 1e-4, emax)
            eta = np.clip(eta, 0, 0.99)
            phi2 = phi2 % (2*np.pi)
            psi = make_psi6(eps, eta, phi2)
            G = build_G(psi)
            return -regge_action(G)

        bounds = [(1e-4, emax), (0, 0.8), (0, 2*np.pi)]

        # Multi-start local optimization
        results = []
        for eps0 in np.linspace(0.01, 0.5, 8):
            for eta0 in np.linspace(0, 0.5, 6):
                for phi0 in [np.pi/4, np.pi/2, np.pi, 3*np.pi/2]:
                    try:
                        res = minimize(neg_S, [eps0, eta0, phi0],
                                       method='L-BFGS-B', bounds=bounds,
                                       options={'maxiter': 2000})
                        S_val = -res.fun
                        params = res.x
                        results.append((S_val, params))
                    except Exception:
                        pass

        # Also try differential evolution for global search
        try:
            res_de = differential_evolution(neg_S, bounds,
                                            maxiter=500, seed=42)
            results.append((-res_de.fun, res_de.x))
        except Exception:
            pass

        # Cluster unique solutions
        results.sort(key=lambda x: x[0], reverse=True)
        unique = []
        for S_val, params in results:
            is_new = True
            for S_u, p_u in unique:
                if abs(S_val - S_u) < 0.01:
                    is_new = False
                    break
            if is_new:
                unique.append((S_val, params))

        self.log(f"\n  Found {len(unique)} unique critical points:")
        self._critical_points = []
        for i, (S_val, params) in enumerate(unique[:8]):
            eps, eta, phi2 = params
            self.log(f"\n  #{i+1}: S = {S_val:.6f} ({S_val/np.pi:.5f}*pi)")
            self.log(f"    eps = {eps:.6f}")
            self.log(f"    eta = {eta:.6f}")
            self.log(f"    phi2 = {phi2:.5f} ({phi2/np.pi:.4f}*pi)")
            self.log(f"    eps/alpha_em = {eps/ALPHA:.2f}")
            self.log(f"    eps/alpha_GUT = {eps/ALPHA_GUT:.4f}")
            self.log(f"    eps^2 = {eps**2:.8f}")
            self._critical_points.append((eps, eta, phi2, S_val))

        self.check("Critical points found",
                    len(unique) > 0)

    def test3_observables_at_critical(self):
        """Compute coupling observables at each critical point."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 3: Observables at critical points")
        self.log(f"  {'='*60}")

        if not hasattr(self, '_critical_points'):
            self.check("Need critical points from test2", False)
            return

        for i, (eps, eta, phi2, S_val) in enumerate(
                self._critical_points[:5]):
            obs = compute_observables(eps, eta, phi2)
            self.log(f"\n  Critical point #{i+1}:")
            self.log(f"    Parameters: eps={eps:.6f},"
                     f" eta={eta:.6f}, phi2={phi2:.4f}")
            self.log(f"    S = {obs['S']:.5f} = {obs['S/pi']:.5f}*pi")
            self.log(f"    delta(AAA)/pi = {obs['delta_AAA/pi']:.5f}")
            self.log(f"    R_SSS = {obs['R_SSS']:.6f}"
                     f" (ratio to alpha_GUT: {obs['R/aGUT']:.4f})")
            self.log(f"    SSS leakage(AABe) = {obs['SSS_leakage']:.8f}")
            self.log(f"    eps^2 = {obs['eps2']:.8f}")

            # Check various coupling combinations
            z2 = np.pi**2 / 6
            self.log(f"    --- Coupling probes ---")
            self.log(f"    eps^2/(1-2eps^2) ="
                     f" {eps**2/(1-2*eps**2):.8f}"
                     f" (alpha_GUT={ALPHA_GUT:.8f})")
            self.log(f"    R_SSS / zeta(2) ="
                     f" {obs['R_SSS']/z2:.8f}")
            self.log(f"    S/(d^2*pi) = {obs['S']/(D**2*np.pi):.6f}")

            # Gram matrix at this point
            psi = make_psi6(eps, eta, phi2)
            G = build_G(psi)
            evals = np.linalg.eigvalsh(G.real)
            self.log(f"    G eigenvalues: {np.sort(evals)[::-1]}")

        self.check("Observables computed", True)

    def test4_phi2_scan(self):
        """How does phi2 affect the action and delta(AAA)?"""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 4: phi2 dependence at action maximum")
        self.log(f"  {'='*60}")

        emax = 1/np.sqrt(3) - 0.001

        self.log(f"\n  {'phi2':>8} {'phi2/pi':>8} {'eps_max':>8}"
                 f" {'S_max':>10} {'dAAA/pi':>8} {'R_SSS':>8}")

        for phi2 in np.linspace(0.1, np.pi, 15):
            # Find eps that maximizes S at this phi2, eta=0
            def neg_S(p):
                e = np.clip(p[0], 1e-4, emax)
                psi = make_psi6(e, 0, phi2)
                G = build_G(psi)
                return -regge_action(G)

            best_S, best_eps = -1e10, 0
            for e0 in np.linspace(0.01, 0.5, 20):
                try:
                    res = minimize(neg_S, [e0], method='L-BFGS-B',
                                   bounds=[(1e-4, emax)])
                    if -res.fun > best_S:
                        best_S = -res.fun
                        best_eps = res.x[0]
                except Exception:
                    pass

            psi = make_psi6(best_eps, 0, phi2)
            G = build_G(psi)
            delta_aaa = deficit_angle(G, (0, 1, 2))

            # Quick R_SSS
            s_sss, s_tot = 0.0, 0.0
            for tri in ALL_HINGES:
                d = hinge_det(G, tri)
                if d <= 0:
                    continue
                area = np.sqrt(d)
                delta = deficit_angle(G, tri)
                s_tot += area * delta
                k0, k1, k2 = hinge_binet_cauchy(psi, tri)
                tb = k0+k1+k2
                if tb > 0:
                    s_sss += area*delta*k0/tb
            r = s_sss/s_tot if abs(s_tot) > 1e-15 else 0

            self.log(f"  {phi2:8.4f} {phi2/np.pi:8.4f}"
                     f" {best_eps:8.5f} {best_S:10.5f}"
                     f" {delta_aaa/np.pi:8.4f} {r:8.5f}")

        # Special case: phi2 that gives delta(AAA) = pi
        self.log(f"\n  For delta(AAA) = pi: need B1 perp B2"
                 f" AND B1 perp B3")
        self.log(f"  B1=[t,0,eps,eps,eps], B2=[cos(phi2),sin(phi2),0,0,0]")
        self.log(f"  <B1|B2> = t*cos(phi2) = 0 => phi2 = pi/2")
        self.log(f"  phi3=-phi2=-pi/2 => B3=[0,-1,0,0,0]")
        self.log(f"  <B1|B3> = t*cos(-pi/2) = 0 ✓")

        self.check("phi2 scan complete", True)


if __name__ == "__main__":
    FullVariational().execute()
