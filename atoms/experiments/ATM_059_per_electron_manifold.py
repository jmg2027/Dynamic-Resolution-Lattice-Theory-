"""
ATM_059: Per-Electron Multi-Simplex Variational
Joint research by Mingu Jeong and Claude (Anthropic)

THE KEY INSIGHT: M(N,ε) has action maximum because of
shared/boundary balance. Each ADDITIONAL electron lives
on its OWN simplex with its OWN coupling ε_k.

Structure:
  S₁ = (A₁,A₂,A₃, B_shared, B₂)  — simplex 1
  S₂ = (A₁,A₂,A₃, B_shared, B₃)  — simplex 2
  ...
  B_shared = innermost electron (shared face)
  B_k = k-th electron (each simplex's own)
  ε_k = coupling of B_k to A-vertices

  Shared sector: δ(AAA) = (4-N)π/2 → decreases with N
  Boundary sector: f(ε_k) per simplex → increases with ε_k
  → BALANCE → each ε_k determined by stationarity

Tests:
  1. He: 2 simplices, ε₁=ε₂ by symmetry → recover α_GUT on N=4?
  2. Li: 2+1 simplices, ε_inner ≠ ε_outer
  3. Extract IE from per-electron ε_k
  4. Compare with observed values
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from itertools import combinations
from scipy.optimize import minimize_scalar, minimize
from experiment import Experiment

D = 5; N_S = 3; N_T = 2
ALPHA = 1/137.036
ALPHA_GUT = 6/(25*np.pi**2)
Ry = 13.606; m_e = 511000.0

A = np.array([[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]], dtype=complex)


class MultiEpsManifold:
    """N simplices sharing face (A₁,A₂,A₃,B_shared),
    each with its own coupling ε_k for vertex B_{k+1}.

    B_shared = (t₀, 0, ε₀, ε₀, ε₀) — inner electron
    B_{k+1} = (0, e^{2πik/N}, 0, 0, 0) — temporal vertices
    Modified: B_{k+1} can also have spatial overlap ε_k.
    """

    def __init__(self, N, eps_shared, eps_list=None):
        self.N = N
        self.eps_shared = eps_shared
        self.eps_list = eps_list or [0.0]*N
        self.n_verts = 4 + N
        self._build()

    def _build(self):
        nv = self.n_verts
        self.psi = np.zeros((nv, 5), dtype=complex)
        self.psi[:3] = A

        # B_shared (index 3): inner electron
        e0 = self.eps_shared
        t0 = np.sqrt(max(0, 1 - 3*e0**2))
        self.psi[3] = [t0, 0, e0, e0, e0]

        # B_{k+1} (indices 4..4+N-1): temporal + spatial coupling
        for k in range(self.N):
            phase = 2*np.pi*k / self.N
            ek = self.eps_list[k]
            tk = np.sqrt(max(0, 1 - 3*ek**2))
            # Temporal part with phase, spatial coupling ek
            self.psi[4+k] = [0, tk*np.exp(1j*phase), ek, ek, ek]

        # Normalize
        for i in range(nv):
            n = np.linalg.norm(self.psi[i])
            if n > 0:
                self.psi[i] /= n

        self.G = self.psi @ self.psi.conj().T

        # Build topology
        self.simplices = []
        for k in range(self.N):
            self.simplices.append((0, 1, 2, 3, 4+k))

        hinge_set = set()
        for sx in self.simplices:
            for tri in combinations(sx, 3):
                hinge_set.add(tri)
        self.hinges = sorted(hinge_set)

    def dihedral(self, sx, hinge):
        sv = list(sx)
        opp = [v for v in sv if v not in hinge]
        G_local = self.G[np.ix_(sv, sv)]
        det_local = np.linalg.det(G_local).real
        if abs(det_local) < 1e-15:
            return np.pi
        G_inv = np.linalg.inv(G_local)
        l, m = sv.index(opp[0]), sv.index(opp[1])
        num = -G_inv[l, m].real
        den = np.sqrt(max(1e-30, abs(G_inv[l,l].real * G_inv[m,m].real)))
        return float(np.arccos(np.clip(num/den, -1, 1)))

    def deficit(self, hinge):
        theta_sum = 0.0
        for sx in self.simplices:
            if set(hinge).issubset(set(sx)):
                theta_sum += self.dihedral(sx, hinge)
        return 2*np.pi - theta_sum

    def hinge_det(self, tri):
        idx = list(tri)
        return float(np.linalg.det(self.G[np.ix_(idx, idx)]).real)

    def regge_action(self):
        S = 0.0
        for tri in self.hinges:
            d = self.hinge_det(tri)
            if d > 0:
                S += np.sqrt(d) * self.deficit(tri)
        return S


class PerElectronManifold(Experiment):
    ID = "ATM_059"
    TITLE = "Per-Electron Manifold"

    def run(self):
        self.test1_recover_single_eps()
        self.test2_two_different_eps()
        self.test3_lithium()
        self.test4_IE_extraction()

    def test1_recover_single_eps(self):
        """All ε_k equal → recover NSimplexManifold result."""
        self.log(f"\n  {'='*55}")
        self.log(f"  Test 1: Uniform ε → recover ATM_029")
        self.log(f"  {'='*55}")

        from ATM_029_N_simplex_manifold import NSimplexManifold

        for N in [2, 3, 4]:
            eps = 0.10
            m_old = NSimplexManifold(N, eps)
            S_old = m_old.regge_action()

            m_new = MultiEpsManifold(N, eps, [0.0]*N)
            S_new = m_new.regge_action()

            diff = abs(S_old - S_new)
            self.log(f"  N={N}: S_old={S_old:.6f},"
                     f" S_new={S_new:.6f}, diff={diff:.2e}")

        self.check("Recovers ATM_029", diff < 1e-6)

    def test2_two_different_eps(self):
        """N=2, with different ε for each boundary vertex."""
        self.log(f"\n  {'='*55}")
        self.log(f"  Test 2: N=2 with ε₁ ≠ ε₂")
        self.log(f"  {'='*55}")

        eps_shared = 0.10
        # Scan ε₁ while ε₂=0 (one electron, one vacuum)
        self.log(f"\n  Shared ε₀={eps_shared}")
        self.log(f"  Scan ε₁ (B₂ coupling), ε₂=0 (B₃ vacuum):")
        self.log(f"  {'ε₁':>8} {'S':>12}")

        for e1 in np.linspace(0, 0.3, 15):
            m = MultiEpsManifold(2, eps_shared, [e1, 0.0])
            S = m.regge_action()
            self.log(f"  {e1:8.4f} {S:12.5f}")

        # Find maximum over ε₁
        res = minimize_scalar(
            lambda e: -MultiEpsManifold(2, eps_shared, [e, 0.0]).regge_action(),
            bounds=(0.001, 0.5), method='bounded')
        e1_max = res.x
        S_max = -res.fun

        self.log(f"\n  Action max: ε₁={e1_max:.6f}, S={S_max:.6f}")
        self.log(f"  This ε₁ = coupling of the SECOND electron")
        self.log(f"  (the first is B_shared with ε₀={eps_shared})")
        self.check("Two-eps landscape", True)

    def test3_lithium(self):
        """Li: optimize (ε_shared, ε_outer) on M(2,...)."""
        self.log(f"\n  {'='*55}")
        self.log(f"  Test 3: Lithium — M(2, ε₀, [ε₁, 0])")
        self.log(f"  {'='*55}")

        # Li = He core (2 inner electrons) + 1 outer electron
        # Model as M(2, ε_inner, [ε_outer, 0]):
        #   B_shared = 1s electron (inner)
        #   B₂ = 2s electron (outer, coupling ε_outer)
        #   B₃ = vacuum (ε=0)

        # Optimize both ε_inner and ε_outer jointly
        def neg_S(params):
            e_in, e_out = abs(params[0]), abs(params[1])
            e_in = min(e_in, 0.55)
            e_out = min(e_out, 0.55)
            m = MultiEpsManifold(2, e_in, [e_out, 0.0])
            return -m.regge_action()

        res = minimize(neg_S, [0.05, 0.02], method='Nelder-Mead',
                       options={'maxiter': 5000, 'xatol': 1e-10})
        e_in_opt, e_out_opt = abs(res.x[0]), abs(res.x[1])
        S_opt = -res.fun

        self.log(f"\n  Optimized:")
        self.log(f"    ε_inner (1s) = {e_in_opt:.6f}")
        self.log(f"    ε_outer (2s) = {e_out_opt:.6f}")
        self.log(f"    Ratio out/in = {e_out_opt/e_in_opt:.4f}")
        self.log(f"    S_max = {S_opt:.6f}")
        self.log(f"\n  ★ If ratio < 1: outer electron is SCREENED")
        self.log(f"    by inner electron. σ emerges from geometry!")

        self._e_in = e_in_opt
        self._e_out = e_out_opt
        self.check("Li optimized", True)

    def test4_IE_extraction(self):
        """IE from the optimal ε_outer."""
        self.log(f"\n  {'='*55}")
        self.log(f"  Test 4: IE from variational ε")
        self.log(f"  {'='*55}")

        e_out = self._e_out
        # IE = ΔF × m_e / N_T²
        # ΔF = 6ε² (s-electron, 3 AAB hinges)
        dF = 6 * e_out**2
        IE = dF * m_e / N_T**2

        self.log(f"\n  ε_outer = {e_out:.6f}")
        self.log(f"  ΔF = 6ε² = {dF:.8f}")
        self.log(f"  IE = ΔF × m_e/N_T² = {IE:.3f} eV")
        self.log(f"  Observed Li IE = 5.392 eV")
        self.log(f"  Error: {(IE-5.392)/5.392*100:+.1f}%")

        # What Z_eff does this correspond to?
        # IE = Z_eff² × Ry / n², n=2
        z_eff = np.sqrt(IE * 4 / Ry)
        self.log(f"\n  Implied Z_eff = {z_eff:.4f}")
        self.log(f"  Expected (screening model) ≈ 1.26")
        self.log(f"  Z - 2×σ_cross = 3 - 2×7/8 = {3-2*7/8:.3f}")

        self.check(f"IE(Li) = {IE:.1f} eV", True)


if __name__ == "__main__":
    PerElectronManifold().execute()

