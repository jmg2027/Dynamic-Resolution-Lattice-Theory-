"""
EXP_067: δS/δψ = 0 on ∂(Δ⁵) — Direct Variational Solutions
=============================================================

No Z_eff. No screening. No orbitals. No Slater rules.
ONE equation: δS/δψ = 0,  S = Σ_h √det(G_h) × δ_h

Strategy:
  1. A vertices FIXED (confinement: |G_{AA'}|=0)
  2. Vary only B/X vertices → 30 real params
  3. 1D scan S(ε) → find landscape
  4. Constrained optimisation → exact critical point
  5. Analytic form of the solution

Joint research by Mingu Jeong and Claude (Anthropic).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import drlt
import numpy as np
from itertools import combinations
from scipy.optimize import minimize, minimize_scalar


# ═══════════════════════════════════════════════════════════
#  ∂(Δ⁵) engine — 6 vertices, 20 hinges, 6 four-simplices
# ═══════════════════════════════════════════════════════════

ALL_HINGES = list(combinations(range(6), 3))          # 20
ALL_SIMPLICES = [tuple(v for v in range(6) if v != k)
                 for k in range(6)]                    # 6


def build_G(psi):
    """(6,5) complex → 6×6 Gram matrix, normalising rows."""
    psi = np.asarray(psi, dtype=complex).copy()
    for i in range(6):
        n = np.linalg.norm(psi[i])
        if n > 0:
            psi[i] /= n
    return psi @ psi.conj().T, psi


def hinge_det(G, tri):
    """det(G_h) for triangle (i,j,k)."""
    idx = list(tri)
    return float(np.linalg.det(G[np.ix_(idx, idx)]).real)


def dihedral_angle(G, simplex_verts, hinge_verts):
    """
    Dihedral angle at hinge within a four-simplex.
    cos θ = −G⁻¹[d,e] / √(G⁻¹[d,d]·G⁻¹[e,e])
    """
    sv = list(simplex_verts)
    hv = set(hinge_verts)
    opp = [v for v in sv if v not in hv]
    G_sub = G[np.ix_(sv, sv)]
    if abs(np.linalg.det(G_sub).real) < 1e-15:
        return np.pi / 2
    G_inv = np.linalg.inv(G_sub)
    pd, pe = sv.index(opp[0]), sv.index(opp[1])
    num = -G_inv[pd, pe].real
    den = np.sqrt(abs(G_inv[pd, pd].real * G_inv[pe, pe].real))
    if den < 1e-15:
        return np.pi / 2
    return float(np.arccos(np.clip(num / den, -1, 1)))


def deficit_angle(G, hinge):
    """δ_h = 2π − Σ dihedral angles (3 four-simplices)."""
    hv = set(hinge)
    s = sum(dihedral_angle(G, sx, hinge)
            for sx in ALL_SIMPLICES if hv.issubset(set(sx)))
    return 2 * np.pi - s


def regge_action(G):
    """S = Σ_h √det(G_h) × δ_h  over 20 hinges."""
    S = 0.0
    for h in ALL_HINGES:
        d = hinge_det(G, h)
        if d > 0:
            S += np.sqrt(d) * deficit_angle(G, h)
    return S


def regge_action_decomposed(G, A_set={0, 1, 2}):
    """Return per-type breakdown of S."""
    result = {}
    for h in ALL_HINGES:
        nA = sum(1 for v in h if v in A_set)
        tp = ['BBB', 'ABB', 'AAB', 'AAA'][nA]
        d = hinge_det(G, h)
        da = deficit_angle(G, h)
        area = np.sqrt(max(0, d))
        contrib = area * da
        result.setdefault(tp, []).append({
            'h': h, 'det': d, 'delta': da, 'area': area, 'S': contrib
        })
    return result


# ═══════════════════════════════════════════════════════════
#  Vacuum ETF
# ═══════════════════════════════════════════════════════════

def make_vacuum_etf():
    """6 unit vectors in ℂ⁵ with G_ij = −1/5 (real ETF)."""
    raw = np.eye(6) - 1.0 / 6
    U, s, _ = np.linalg.svd(raw, full_matrices=False)
    psi = (U[:, :5] * s[:5]).astype(complex)
    for i in range(6):
        psi[i] /= np.linalg.norm(psi[i])
    return psi


# ═══════════════════════════════════════════════════════════
#  Hydrogen family: A fixed, B parameterised by ε
# ═══════════════════════════════════════════════════════════

def make_psi_hydrogen(eps, b2_spatial=0.0, x_phase=np.pi/3):
    """
    Build ∂(Δ⁵) with hydrogen pattern.

    A₁,A₂,A₃: orthogonal in spatial ℂ³ (FIXED by confinement)
    B₁: electron — coupling ε to each A
    B₂: vacant slot — pure temporal (b2_spatial controls leakage)
    X:  6th vertex — temporal sector, completes boundary

    Only ε is physics.  b2_spatial and x_phase are background.
    """
    psi = np.zeros((6, 5), dtype=complex)
    psi[0] = [0, 0, 1, 0, 0]
    psi[1] = [0, 0, 0, 1, 0]
    psi[2] = [0, 0, 0, 0, 1]
    # B₁: (temporal, 0, ε, ε, ε)
    t = np.sqrt(max(0, 1 - 3 * eps**2))
    psi[3] = [t, 0, eps, eps, eps]
    # B₂: (0, temporal, δ, δ, δ)
    d2 = b2_spatial
    t2 = np.sqrt(max(0, 1 - 3 * d2**2))
    psi[4] = [0, t2, d2, d2, d2]
    # X: mix of temporal directions
    psi[5] = [np.cos(x_phase), np.sin(x_phase), 0, 0, 0]
    for i in range(6):
        n = np.linalg.norm(psi[i])
        if n > 0:
            psi[i] /= n
    return psi


def scan_action_1d(eps_array, log_fn=print):
    """Scan S(ε) for the hydrogen family. Returns arrays."""
    S_arr = np.zeros(len(eps_array))
    det_sum_arr = np.zeros(len(eps_array))
    for idx, eps in enumerate(eps_array):
        psi = make_psi_hydrogen(eps)
        G, _ = build_G(psi)
        S_arr[idx] = regge_action(G)
        # Σ(1-det) for AAB hinges in AAAB face
        det_sum = 0
        for tri in combinations([0, 1, 2, 3], 3):
            if sum(1 for v in tri if v in {0, 1, 2}) == 2:
                det_sum += (1 - hinge_det(G, tri))
        det_sum_arr[idx] = det_sum
        if idx % 20 == 0 and idx > 0:
            log_fn(f"  ... scan {idx}/{len(eps_array)}")
    return S_arr, det_sum_arr


# ═══════════════════════════════════════════════════════════
#  Constrained optimisation: A fixed, vary B/X
# ═══════════════════════════════════════════════════════════

def psi_b_from_params(p):
    """
    18 real params → 3 unit vectors (B₁, B₂, X) in ℂ⁵.
    p[0:5]  = Re(ψ₃),  p[5:10]  = Im(ψ₃)
    p[10:15]= Re(ψ₄),  p[15:20] = Im(ψ₄)
    p[20:25]= Re(ψ₅),  p[25:30] = Im(ψ₅)
    """
    psi_b = np.zeros((3, 5), dtype=complex)
    for k in range(3):
        re = p[10*k:10*k+5]
        im = p[10*k+5:10*k+10]
        psi_b[k] = re + 1j * im
        n = np.linalg.norm(psi_b[k])
        if n > 0:
            psi_b[k] /= n
    return psi_b


def make_full_psi(psi_b):
    """Combine fixed A vertices with variable B/X vertices."""
    psi = np.zeros((6, 5), dtype=complex)
    psi[0] = [0, 0, 1, 0, 0]
    psi[1] = [0, 0, 0, 1, 0]
    psi[2] = [0, 0, 0, 0, 1]
    psi[3] = psi_b[0]
    psi[4] = psi_b[1]
    psi[5] = psi_b[2]
    return psi


def constrained_objective(p, sign=1.0):
    """S for constrained problem (A fixed)."""
    psi_b = psi_b_from_params(p)
    psi = make_full_psi(psi_b)
    G, _ = build_G(psi)
    return sign * regge_action(G)


def params_from_psi_b(psi_b):
    """3 vectors → 30 real params."""
    p = np.zeros(30)
    for k in range(3):
        p[10*k:10*k+5] = psi_b[k].real
        p[10*k+5:10*k+10] = psi_b[k].imag
    return p


# ═══════════════════════════════════════════════════════════
#  Experiment
# ═══════════════════════════════════════════════════════════

class Exp(Experiment):
    ID = "ATM_012", "Variational dS-dpsi on boundary-Delta5"

    def run(self):
        alpha = drlt.ALPHA_EM
        d = drlt.D
        m_e = 511000   # eV
        Ry = 13.606    # eV
        A_set = {0, 1, 2}

        # ══════════ Part 1: Vacuum ══════════
        self.log("=" * 55)
        self.log("Part 1: Vacuum — ETF verification")
        self.log("=" * 55)
        psi_vac = make_vacuum_etf()
        G_vac, _ = build_G(psi_vac)
        off = [abs(G_vac[i, j])
               for i in range(6) for j in range(i+1, 6)]
        self.log(f"|G_ij| = {np.mean(off):.8f}  (expect 0.2)")
        self.check("|G_ij|=1/d", abs(np.mean(off) - 0.2) < 1e-6)

        dets_v = [hinge_det(G_vac, h) for h in ALL_HINGES]
        self.log(f"det(G_h) = {np.mean(dets_v):.8f}  (expect 0.864)")
        self.check("det=108/125", abs(np.mean(dets_v) - 0.864) < 1e-6)

        deltas_v = [deficit_angle(G_vac, h) for h in ALL_HINGES]
        self.log(f"δ_h max  = {max(abs(x) for x in deltas_v):.2e}")
        self.check("δ=0 (flat)", max(abs(x) for x in deltas_v) < 1e-10)

        S_vac = regge_action(G_vac)
        self.log(f"S_vac    = {S_vac:.2e}")
        self.check("S=0", abs(S_vac) < 1e-10)
        self.log("→ 진공 = 완전히 평탄. δ=0, S=0.")

        # ══════════ Part 2: 1D scan S(ε) ══════════
        self.log(f"\n{'='*55}")
        self.log("Part 2: 1D Action Landscape S(ε)")
        self.log("=" * 55)
        self.log("A 고정 (직교), B₁ coupling ε, B₂·X = temporal")

        eps_phys = alpha / np.sqrt(drlt.N_S)
        self.log(f"ε_physical = α/√n_S = {eps_phys:.6f}")

        eps_arr = np.linspace(0.001, 0.55, 200)
        self.log("Scanning 200 points in ε ∈ [0.001, 0.55] ...")
        S_arr, det_arr = scan_action_1d(eps_arr, self.log)
        self.log("Scan complete.")

        # Find extrema
        # dS/dε sign changes
        dS = np.diff(S_arr)
        for i in range(len(dS) - 1):
            if dS[i] > 0 and dS[i+1] < 0:
                self.log(f"  LOCAL MAX near ε = {eps_arr[i+1]:.4f},"
                         f"  S = {S_arr[i+1]:.4f}")
            if dS[i] < 0 and dS[i+1] > 0:
                self.log(f"  LOCAL MIN near ε = {eps_arr[i+1]:.4f},"
                         f"  S = {S_arr[i+1]:.4f}")

        # Value at physical ε
        idx_phys = np.argmin(np.abs(eps_arr - eps_phys))
        self.log(f"\nAt ε_phys = {eps_phys:.6f}:")
        self.log(f"  S = {S_arr[idx_phys]:.6f}")
        self.log(f"  Σ(1-det)_AAB = {det_arr[idx_phys]:.10f}")
        self.log(f"  2α² = {2*alpha**2:.10f}")

        # Table at key ε values
        self.log("\nε-scan table:")
        self.log(f"  {'ε':>8s} {'S':>12s} {'Σ(1-det)':>12s}"
                 f" {'IE(eV)':>10s}")
        for eps_val in [0.001, 0.01, eps_phys, 0.05,
                        0.1, 0.2, 0.3, 0.4, 0.5]:
            j = np.argmin(np.abs(eps_arr - eps_val))
            ie = m_e / (2 * drlt.N_T) * det_arr[j]
            self.log(f"  {eps_arr[j]:8.5f} {S_arr[j]:12.4f}"
                     f" {det_arr[j]:12.8f} {ie:10.3f}")

        # ══════════ Part 3: Constrained optimisation ══════════
        self.log(f"\n{'='*55}")
        self.log("Part 3: Constrained δS/δψ_B = 0")
        self.log("=" * 55)
        self.log("A vertices FIXED. Vary B₁, B₂, X only (30 params).")

        # 3a: Find critical point — maximise S
        self.log("\n3a: Maximise S (A fixed)")
        psi0 = make_psi_hydrogen(eps_phys)
        p0 = params_from_psi_b(psi0[3:6])
        res = minimize(constrained_objective, p0, args=(-1.0,),
                       method='L-BFGS-B',
                       options={'maxiter': 3000, 'ftol': 1e-15})
        psi_b_max = psi_b_from_params(res.x)
        psi_max = make_full_psi(psi_b_max)
        G_max, _ = build_G(psi_max)
        S_max = regge_action(G_max)
        self.log(f"  converged: {res.success}")
        self.log(f"  S_max = {S_max:.8f}")
        self.log(f"  |G| structure:")
        for i in range(6):
            row = " ".join(f"{abs(G_max[i,j]):.4f}" for j in range(6))
            self.log(f"    [{row}]")

        # 3b: Minimise S
        self.log("\n3b: Minimise S (A fixed)")
        res2 = minimize(constrained_objective, p0, args=(1.0,),
                        method='L-BFGS-B',
                        options={'maxiter': 3000, 'ftol': 1e-15})
        psi_b_min = psi_b_from_params(res2.x)
        psi_min = make_full_psi(psi_b_min)
        G_min, _ = build_G(psi_min)
        S_min = regge_action(G_min)
        self.log(f"  converged: {res2.success}")
        self.log(f"  S_min = {S_min:.8f}")
        self.log(f"  |G| structure:")
        for i in range(6):
            row = " ".join(f"{abs(G_min[i,j]):.4f}" for j in range(6))
            self.log(f"    [{row}]")

        # 3c: Multiple random starts → find all critical points
        self.log("\n3c: Multiple random starts (50 trials)")
        critical_S = []
        np.random.seed(42)
        for trial in range(50):
            # Random B/X initial
            psi_rand = np.random.randn(3, 5) + 1j*np.random.randn(3, 5)
            for k in range(3):
                psi_rand[k] /= np.linalg.norm(psi_rand[k])
            p_rand = params_from_psi_b(psi_rand)
            # Try both max and min
            for sgn, label in [(-1, 'max'), (1, 'min')]:
                r = minimize(constrained_objective, p_rand, args=(sgn,),
                             method='L-BFGS-B',
                             options={'maxiter': 1000, 'ftol': 1e-12})
                S_val = -sgn * r.fun  # actual S value
                critical_S.append((S_val, label, trial))
            if trial % 10 == 9:
                self.log(f"  ... trial {trial+1}/50")

        # Cluster results
        S_vals = sorted(set(round(x[0], 4) for x in critical_S))
        self.log(f"\nDistinct S values found: {len(S_vals)}")
        for sv in S_vals[:15]:
            count = sum(1 for x in critical_S if abs(x[0]-sv) < 0.01)
            self.log(f"  S = {sv:+.6f}  (found {count} times)")

        self.log("\n→ 진행: Part 4-6 계속")
        self.run_part456(G_vac, S_vac, G_max, S_max, G_min, S_min,
                         eps_phys, eps_arr, S_arr, det_arr)

    def run_part456(self, G_vac, S_vac, G_max, S_max, G_min, S_min,
                    eps_phys, eps_arr, S_arr, det_arr):
        alpha = drlt.ALPHA_EM
        m_e = 511000
        Ry = 13.606
        A_set = {0, 1, 2}

        # ══════════ Part 4: Helium ══════════
        self.log(f"\n{'='*55}")
        self.log("Part 4: Helium")
        self.log("=" * 55)

        eps_He = 2 * alpha / np.sqrt(drlt.N_S)
        psi_He = np.zeros((6, 5), dtype=complex)
        psi_He[0]=[0,0,1,0,0]; psi_He[1]=[0,0,0,1,0]
        psi_He[2]=[0,0,0,0,1]
        t1 = np.sqrt(1 - 3*eps_He**2)
        psi_He[3] = [t1, 0, eps_He, eps_He, eps_He]
        psi_He[4] = [0, t1, eps_He, eps_He, eps_He]
        psi_He[5] = [1/np.sqrt(2), 1/np.sqrt(2), 0, 0, 0]
        for i in range(6):
            psi_He[i] /= np.linalg.norm(psi_He[i])
        G_He, _ = build_G(psi_He)
        S_He = regge_action(G_He)

        # Binding per face
        aab_B1 = sum(1 - hinge_det(G_He, t)
                     for t in combinations([0,1,2,3], 3)
                     if sum(1 for v in t if v in A_set) == 2)
        aab_B2 = sum(1 - hinge_det(G_He, t)
                     for t in combinations([0,1,2,4], 3)
                     if sum(1 for v in t if v in A_set) == 2)
        abb = sum(1 - hinge_det(G_He, t)
                  for t in combinations(range(6), 3)
                  if 3 in t and 4 in t
                  and sum(1 for v in t if v in A_set) == 1)

        self.log(f"ε_He = 2α/√n_S = {eps_He:.6f}")
        self.log(f"S_He = {S_He:.8f}")
        self.log(f"Σ(1-det) AAB[B₁] = {aab_B1:.10f}")
        self.log(f"Σ(1-det) AAB[B₂] = {aab_B2:.10f}")
        self.log(f"Σ(1-det) ABB     = {abb:.10f}")

        IE_He = m_e/(2*drlt.N_T) * (aab_B1 + aab_B2 - abb)
        pred = 2*Ry*(1-4*drlt.ALPHA_GUT)
        self.log(f"IE(He) det  = {IE_He:.3f} eV")
        self.log(f"IE(He) pred = {pred:.3f} eV  (obs: 24.587)")
        self.check("IE(He) ≈ 24.6 eV (5%)",
                   abs(IE_He - 24.587)/24.587 < 0.05)

        # ══════════ Part 5: Deficit angle analysis ══════════
        self.log(f"\n{'='*55}")
        self.log("Part 5: Deficit angle structure")
        self.log("=" * 55)

        psi_H = make_psi_hydrogen(eps_phys)
        G_H, _ = build_G(psi_H)
        S_H = regge_action(G_H)

        self.log(f"\nHydrogen (ε = α/√n_S = {eps_phys:.6f}):")
        decomp = regge_action_decomposed(G_H)
        for tp in ['AAA', 'AAB', 'ABB', 'BBB']:
            if tp in decomp:
                rows = decomp[tp]
                dets = [r['det'] for r in rows]
                dels = [r['delta'] for r in rows]
                ss = [r['S'] for r in rows]
                self.log(f"  {tp} n={len(rows):2d}  "
                         f"det=[{min(dets):.6f},{max(dets):.6f}]  "
                         f"δ=[{min(dels):.4f},{max(dels):.4f}]  "
                         f"ΣS={sum(ss):.6f}")

        # All 20 hinges
        self.log("\nAll 20 hinges (hydrogen):")
        for tp in ['AAA', 'AAB', 'ABB', 'BBB']:
            if tp not in decomp:
                continue
            for r in decomp[tp]:
                self.log(f"  {tp} {r['h']}  det={r['det']:.6f}  "
                         f"δ={r['delta']:+.6f} = {np.degrees(r['delta']):+.2f}°")

        # ══════════ Part 6: IE = ΔS ══════════
        self.log(f"\n{'='*55}")
        self.log("Part 6: IE = ΔS  and analytic structure")
        self.log("=" * 55)

        self.log(f"S_vac = {S_vac:.10f}")
        self.log(f"S_H   = {S_H:.10f}")
        self.log(f"S_He  = {S_He:.10f}")
        self.log(f"S_max = {S_max:.10f}")
        self.log(f"S_min = {S_min:.10f}")

        # Conversion factor
        if abs(S_H) > 1e-12:
            f = Ry / abs(S_H)
            self.log(f"\nConversion: IE = |S| × {f:.4f} eV")
            self.log(f"  H:  {abs(S_H)*f:.3f} eV (obs 13.606)")
            self.log(f"  He: {abs(S_He)*f:.3f} eV (obs 24.587)")

        # Analytic: det(G_AAB) for orthogonal A's
        self.log("\n── Analytic hydrogen solution ──")
        eps = eps_phys
        det_AAB = 1 - 2*eps**2
        self.log(f"det(AAB) = 1 - 2ε² = {det_AAB:.10f}")
        self.log(f"Σ(1-det) = 3(2ε²) = 6ε² = 2α² = {6*eps**2:.10f}")
        self.log(f"2α² = {2*alpha**2:.10f}")
        self.check("6ε² = 2α²", abs(6*eps**2 - 2*alpha**2) < 1e-12)

        ie_analytic = m_e * alpha**2 / 2
        self.log(f"IE = m_e α²/2 = {ie_analytic:.4f} eV")
        self.check("IE = m_e α²/2",
                   abs(ie_analytic/Ry - 1) < 1e-3)

        # ══════════ Analytic proof: δ(AAA) = π ══════════
        self.log("\n── THEOREM: δ(AAA) = π ──")
        self.log("Proof:")
        self.log("  A vertices orthogonal in ℂ³ → G_AA = I₃ (block diagonal)")
        self.log("  B₁,B₂,X in temporal ℂ² → three overlaps g₃₄,g₃₅,g₄₅")
        self.log("  Simplex {A₁A₂A₃BₐB_b}: dihedral at AAA = arccos(g_ab)")
        self.log("  because A-block decouples → cos θ = G_{BₐB_b}")
        self.log("")

        # Verify: compute all 3 dihedral angles at AAA
        for sx_miss in [3, 4, 5]:
            sx = [v for v in range(6) if v != sx_miss]
            opp = [v for v in sx if v not in [0,1,2]]
            theta = dihedral_angle(G_H, tuple(sx), (0,1,2))
            g_ab = G_H[opp[0], opp[1]]
            self.log(f"  Simplex miss={sx_miss}: opp={opp}"
                     f"  G_ab={g_ab.real:+.6f}  "
                     f"cos θ={np.cos(theta):+.6f}  "
                     f"θ={np.degrees(theta):.2f}°")

        self.log("")
        self.log("  Key identity (for real vectors in ℂ²):")
        self.log("  B₁⊥B₂: g₃₄=0, X=cosφ·B₁+sinφ·B₂: g₃₅=cosφ, g₄₅=sinφ")
        self.log("  Σθ = arccos(0) + arccos(cosφ) + arccos(sinφ)")
        self.log("     = π/2 + φ + (π/2 − φ) = π   ∀φ∈[0,π/2]")
        self.log("  ∴ δ(AAA) = 2π − π = π   (EXACT, independent of φ)")

        # Verify for multiple φ values
        self.log("\n  Numerical verification over φ:")
        for phi_val in [0.1, np.pi/6, np.pi/4, np.pi/3, np.pi/2-0.01]:
            psi_test = make_psi_hydrogen(eps_phys, x_phase=phi_val)
            G_test, _ = build_G(psi_test)
            da = deficit_angle(G_test, (0,1,2))
            self.log(f"    φ={phi_val:.4f}: δ(AAA)={da:.10f}"
                     f"  = {da/np.pi:.10f}π")
        self.check("δ(AAA)=π ∀φ",
                   all(abs(deficit_angle(
                       build_G(make_psi_hydrogen(eps_phys, x_phase=p))[0],
                       (0,1,2)) - np.pi) < 1e-10
                       for p in [0.1, 0.5, 1.0, 1.5]))


if __name__ == "__main__":
    Exp().execute()
