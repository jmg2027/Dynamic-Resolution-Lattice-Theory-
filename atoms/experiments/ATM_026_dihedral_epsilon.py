"""
ATM_026: Dihedral Angles as Functions of epsilon
Joint research by Mingu Jeong and Claude (Anthropic)

Missing puzzle piece: AAB and ABB hinge dihedral angles depend on epsilon.
If delta(AAB, eps) and delta(ABB, eps) are nontrivial, the Regge action
S(eps) = Sum sqrt(det) * delta gives a richer landscape.

Combined with Binet-Cauchy channel structure, we may get TWO independent
equations in epsilon, potentially pinning eps = alpha.

Tests:
  1. Map dihedral angles theta(type, eps) for all hinge types
  2. Map deficit angles delta(type, eps) on the manifold
  3. Full Regge action decomposed by channel: S_SSS, S_SST, S_STT
  4. Channel-weighted Regge ratio R_Regge(eps) vs bare ratio R_bare(eps)
  5. Coupled equation: dS/deps = 0 AND R_Regge = target
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
import numpy as np
from itertools import combinations
from experiment import Experiment

ALPHA = 1 / 137.035999084
ALPHA_GUT = 6 / (25 * np.pi**2)
D = 5; N_S = 3; N_T = 2; C_LATTICE = 2

A = np.array([[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]], dtype=complex)

S1 = (0,1,2,3,4)
S2 = (0,1,2,3,5)
SIMPLICES = [S1, S2]


def make_psi6_physical(eps, phi1=0.0, phi2=np.pi/2, phi3=-np.pi/2):
    """Symmetric manifold: B1=electron(eps), B2,B3=anti-parallel temporal.
    B1 perp B2, B1 perp B3, B3=-B2 (time-reversal symmetry).
    This gives delta(AAA)=pi exactly and det(S1)=det(S2)."""
    psi = np.zeros((6, 5), dtype=complex)
    psi[:3] = A
    t1 = np.sqrt(max(0, 1 - 3*eps**2))
    psi[3] = [t1*np.cos(phi1), t1*np.sin(phi1), eps, eps, eps]
    psi[4] = [np.cos(phi2), np.sin(phi2), 0, 0, 0]
    psi[5] = [np.cos(phi3), np.sin(phi3), 0, 0, 0]
    return psi


def make_psi6_uniform(eps, phi1=0.0, phi2=np.pi/2, phi3=np.pi/4):
    """Uniform config: all B share same eps."""
    psi = np.zeros((6, 5), dtype=complex)
    psi[:3] = A
    for i, ph in enumerate([phi1, phi2, phi3]):
        t = np.sqrt(max(0, 1 - 3*eps**2))
        psi[3+i] = [t*np.cos(ph), t*np.sin(ph), eps, eps, eps]
    return psi


def build_G(psi6):
    return psi6 @ psi6.conj().T


def hinge_det(G, tri):
    idx = list(tri)
    return float(np.linalg.det(G[np.ix_(idx, idx)]).real)


def dihedral_in_simplex(G_global, simplex_verts, hinge):
    """Dihedral angle at triangular hinge within one 4-simplex."""
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
    """delta_h = 2pi - sum of dihedral angles from each simplex."""
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


def classify(tri):
    nA = sum(1 for v in tri if v < 3)
    return {3: 'AAA', 2: 'AAB', 1: 'ABB', 0: 'BBB'}[nA]


def classify_fine(tri):
    """Fine classification: distinguish B1(electron) from B2,B3(temporal).
    B1=vertex 3, B2=vertex 4, B3=vertex 5."""
    nA = sum(1 for v in tri if v < 3)
    has_B1 = 3 in tri  # electron
    has_Bt = any(v in tri for v in [4, 5])  # temporal B
    if nA == 3:
        return 'AAA'
    elif nA == 2:
        if has_B1:
            return 'AABe'  # A,A,electron
        else:
            return 'AABt'  # A,A,temporal
    elif nA == 1:
        if has_B1 and has_Bt:
            return 'ABet'  # A,electron,temporal
        elif not has_B1:
            return 'ABtt'  # A,temporal,temporal
        else:
            return 'ABee'  # shouldn't happen (only 1 electron)
    else:
        return 'BBB'


def hinge_binet_cauchy(psi, tri):
    """Binet-Cauchy decomposition of a single hinge into k=0,1,2 channels."""
    Phi = psi[list(tri)]  # 3x5
    k0, k1, k2 = 0.0, 0.0, 0.0
    for cols in combinations(range(5), 3):
        sub = Phi[:, cols]
        d2 = abs(np.linalg.det(sub))**2
        n_temp = sum(1 for c in cols if c < N_T)  # cols 0,1 = temporal
        if n_temp == 0:
            k0 += d2
        elif n_temp == 1:
            k1 += d2
        else:
            k2 += d2
    return k0, k1, k2


class DihedralEpsilon(Experiment):
    ID = "ATM_026"
    TITLE = "Dihedral Angles vs Epsilon"

    def run(self):
        self.test1_dihedral_map()
        self.test2_deficit_map()
        self.test3_regge_by_channel()
        self.test4_channel_weighted_regge_ratio()
        self.test5_coupled_equations()

    def test1_dihedral_map(self):
        """Map dihedral angle theta(type, eps) — fine classification."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 1: Dihedral angles theta(eps) — PHYSICAL config")
        self.log(f"  B1=electron(eps), B2,B3=pure temporal(eps=0)")
        self.log(f"  {'='*60}")

        # Group hinges by fine type
        ftypes = {}
        for tri in ALL_HINGES:
            t = classify_fine(tri)
            ftypes.setdefault(t, []).append(tri)

        self.log(f"\n  Fine hinge counts:")
        for t in sorted(ftypes):
            self.log(f"    {t}: {len(ftypes[t])} hinges — "
                     f"{[str(h) for h in ftypes[t][:3]]}")

        eps_vals = np.concatenate([
            np.linspace(0.001, 0.01, 5),
            np.linspace(0.02, 0.1, 9),
            np.linspace(0.15, 0.55, 9),
        ])

        order = ['AAA', 'AABe', 'AABt', 'ABet', 'ABtt']
        header = f"  {'eps':>8}"
        for t in order:
            if t in ftypes:
                header += f" {'th_'+t:>10}"
        self.log(header)

        theta_data = {t: [] for t in ftypes}

        for eps in eps_vals:
            psi = make_psi6_physical(eps)
            G = build_G(psi)
            line = f"  {eps:8.4f}"
            for t in order:
                if t not in ftypes:
                    continue
                tri = ftypes[t][0]
                thetas = []
                for sx in SIMPLICES:
                    if set(tri).issubset(set(sx)):
                        thetas.append(dihedral_in_simplex(G, sx, tri))
                avg_th = np.mean(thetas)
                theta_data[t].append((eps, avg_th))
                line += f" {avg_th:10.5f}"
            self.log(line)

        # Check: AAA dihedral ~ pi/2
        aaa = [d[1] for d in theta_data.get('AAA', [])]
        if aaa:
            self.log(f"\n  AAA dihedral range: [{min(aaa):.5f},"
                     f" {max(aaa):.5f}], pi/2={np.pi/2:.5f}")
            self.log(f"  AAA spread: {max(aaa)-min(aaa):.6f}")

        # Check variation in each type
        for t in order:
            if t in theta_data and len(theta_data[t]) > 2:
                vals = [d[1] for d in theta_data[t]]
                spread = max(vals) - min(vals)
                self.log(f"  {t} spread: {spread:.6f} rad"
                         f" ({np.degrees(spread):.3f} deg)")

        self.check("Dihedral map (physical)", True)

    def test2_deficit_map(self):
        """Map deficit angle delta(type, eps) — fine classification."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 2: Deficit angles delta(eps) — PHYSICAL config")
        self.log(f"  {'='*60}")

        ftypes = {}
        for tri in ALL_HINGES:
            t = classify_fine(tri)
            ftypes.setdefault(t, []).append(tri)

        eps_vals = np.concatenate([
            np.linspace(0.001, 0.01, 5),
            np.linspace(0.02, 0.1, 9),
            np.linspace(0.15, 0.55, 9),
        ])

        order = ['AAA', 'AABe', 'AABt', 'ABet', 'ABtt']
        header = f"  {'eps':>8}"
        for t in order:
            if t in ftypes:
                header += f" {'d_'+t:>10} {'d/pi':>6}"
        self.log(header)

        delta_data = {t: [] for t in ftypes}

        for eps in eps_vals:
            psi = make_psi6_physical(eps)
            G = build_G(psi)
            line = f"  {eps:8.4f}"
            for t in order:
                if t not in ftypes:
                    continue
                deltas = [deficit_angle_manifold(G, tri)
                          for tri in ftypes[t]]
                avg = np.mean(deltas)
                delta_data[t].append((eps, avg, np.std(deltas)))
                line += f" {avg:10.5f} {avg/np.pi:6.3f}"
            self.log(line)

        # Key check: AAA deficit = pi
        aaa = delta_data.get('AAA', [])
        if aaa:
            aaa_near_pi = all(abs(d[1]/np.pi - 1.0) < 0.01 for d in aaa)
            self.check("delta(AAA) = pi (physical config)", aaa_near_pi)

        # Report variation per fine type
        for t in order:
            if t in delta_data and len(delta_data[t]) > 2:
                vals = [d[1] for d in delta_data[t]]
                stds = [d[2] for d in delta_data[t]]
                spread = max(vals) - min(vals)
                avg_std = np.mean(stds)
                self.log(f"\n  {t}: spread={spread:.6f} rad"
                         f" ({np.degrees(spread):.3f} deg),"
                         f" intra-type std={avg_std:.4f}")
                self.log(f"    range: [{min(vals)/np.pi:.4f}pi,"
                         f" {max(vals)/np.pi:.4f}pi]")

        self.check("Deficit map (physical)", True)

    def test3_regge_by_channel(self):
        """Decompose Regge action by Binet-Cauchy channel."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 3: Regge action decomposed by channel")
        self.log(f"  S_k = Sum_h sqrt(det_k(h)) * delta_h")
        self.log(f"  {'='*60}")

        eps_vals = np.concatenate([
            np.linspace(0.001, 0.01, 5),
            np.linspace(0.02, 0.1, 9),
            np.linspace(0.15, 0.55, 9),
        ])

        self.log(f"\n  {'eps':>8} {'S_total':>10} {'S_SSS':>10}"
                 f" {'S_mixed':>10} {'S_SSS/S':>10} {'S_mix/S':>10}")

        s_data = []
        for eps in eps_vals:
            psi = make_psi6_physical(eps)
            G = build_G(psi)

            s_sss, s_mix, s_tot = 0.0, 0.0, 0.0
            for tri in ALL_HINGES:
                det_full = hinge_det(G, tri)
                if det_full <= 0:
                    continue
                delta = deficit_angle_manifold(G, tri)
                area = np.sqrt(det_full)
                s_tot += area * delta

                k0, k1, k2 = hinge_binet_cauchy(psi, tri)
                # Weighted channels: c^k
                w0 = k0
                w1 = k1 * C_LATTICE
                w2 = k2 * C_LATTICE**2
                w_total = w0 + w1 + w2
                if w_total > 0:
                    frac_sss = w0 / w_total
                    frac_mix = (w1 + w2) / w_total
                    s_sss += area * delta * frac_sss
                    s_mix += area * delta * frac_mix

            r_sss = s_sss / s_tot if abs(s_tot) > 1e-15 else 0
            r_mix = s_mix / s_tot if abs(s_tot) > 1e-15 else 0
            s_data.append((eps, s_tot, s_sss, s_mix, r_sss, r_mix))
            self.log(f"  {eps:8.4f} {s_tot:10.5f} {s_sss:10.5f}"
                     f" {s_mix:10.5f} {r_sss:10.6f} {r_mix:10.6f}")

        # Check: does the ratio vary with eps?
        ratios = [d[4] for d in s_data if abs(d[1]) > 1e-10]
        if ratios:
            spread = max(ratios) - min(ratios)
            self.log(f"\n  S_SSS/S_total ratio spread: {spread:.6f}")
            self.log(f"  Range: [{min(ratios):.6f}, {max(ratios):.6f}]")
            self.log(f"  For reference: alpha_GUT = {ALPHA_GUT:.6f}")
            self.log(f"  For reference: 1/25 = {1/25:.6f}")

        self.check("Regge channel decomposition done", True)

    def test4_channel_weighted_regge_ratio(self):
        """Compare bare BC ratio vs Regge-weighted (sqrt(det)*delta) ratio."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 4: Bare vs Regge-weighted channel ratios")
        self.log(f"  Bare: R = sum(SST+STT) / sum(all)")
        self.log(f"  Regge: R = sum(w_mix * sqrt(det) * delta) / S_total")
        self.log(f"  {'='*60}")

        eps_vals = np.concatenate([
            np.linspace(0.001, 0.01, 5),
            np.linspace(0.02, 0.1, 9),
            np.linspace(0.15, 0.55, 9),
        ])

        self.log(f"\n  {'eps':>8} {'R_bare':>10} {'R_regge':>10}"
                 f" {'diff':>10} {'dS/deps':>12}")

        prev_S, prev_eps = None, None
        results = []

        for eps in eps_vals:
            psi = make_psi6_physical(eps)
            G = build_G(psi)

            # Bare ratio (no delta weighting)
            tot_sss_bare, tot_mix_bare = 0.0, 0.0
            # Regge-weighted ratio
            s_sss, s_mix, s_tot = 0.0, 0.0, 0.0

            for tri in ALL_HINGES:
                det_full = hinge_det(G, tri)
                if det_full <= 0:
                    continue
                area = np.sqrt(det_full)
                delta = deficit_angle_manifold(G, tri)
                s_tot += area * delta

                k0, k1, k2 = hinge_binet_cauchy(psi, tri)
                w0 = k0
                w1 = k1 * C_LATTICE
                w2 = k2 * C_LATTICE**2
                w_total = w0 + w1 + w2

                # Bare: just sum the channel weights
                tot_sss_bare += w0
                tot_mix_bare += w1 + w2

                # Regge-weighted
                if w_total > 0:
                    s_sss += area * delta * w0 / w_total
                    s_mix += area * delta * (w1 + w2) / w_total

            tot_bare = tot_sss_bare + tot_mix_bare
            r_bare = tot_mix_bare / tot_bare if tot_bare > 0 else 0
            r_regge = s_mix / s_tot if abs(s_tot) > 1e-15 else 0

            # Numerical derivative
            ds_deps = 0.0
            if prev_S is not None and prev_eps is not None:
                ds_deps = (s_tot - prev_S) / (eps - prev_eps)
            prev_S, prev_eps = s_tot, eps

            results.append((eps, r_bare, r_regge, s_tot, ds_deps))
            self.log(f"  {eps:8.4f} {r_bare:10.6f} {r_regge:10.6f}"
                     f" {r_regge-r_bare:10.6f} {ds_deps:12.4f}")

        # Find where dS/deps ~ 0 (sign change)
        sign_changes = []
        for i in range(1, len(results)):
            if results[i][4] * results[i-1][4] < 0 and i > 1:
                # Linear interpolation
                e1, ds1 = results[i-1][0], results[i-1][4]
                e2, ds2 = results[i][0], results[i][4]
                e_zero = e1 - ds1 * (e2 - e1) / (ds2 - ds1)
                sign_changes.append(e_zero)

        if sign_changes:
            self.log(f"\n  dS/deps = 0 at eps ~ {sign_changes}")
            for ez in sign_changes:
                self.log(f"    eps={ez:.6f}, eps/alpha={ez/ALPHA:.2f},"
                         f" eps/alpha_GUT={ez/ALPHA_GUT:.2f}")

        # Key question: does R_regge differ from R_bare?
        r_bare_vals = [r[1] for r in results]
        r_regge_vals = [r[2] for r in results]
        max_diff = max(abs(rb - rr) for rb, rr in
                       zip(r_bare_vals, r_regge_vals))
        self.log(f"\n  Max |R_bare - R_regge|: {max_diff:.6f}")
        self.log(f"  -> Deficit angle {'DOES' if max_diff > 0.01 else 'does NOT'}"
                 f" significantly modify channel ratio")

        self.check("Bare vs Regge ratio compared", True)

    def test5_coupled_equations(self):
        """Find eps where BOTH dS/deps=0 AND R=target simultaneously."""
        self.log(f"\n  {'='*60}")
        self.log(f"  Test 5: Coupled equations")
        self.log(f"  Eq1: dS_Regge/deps = 0  (action extremum)")
        self.log(f"  Eq2: R_channel(eps) = target")
        self.log(f"  Question: do these determine eps = alpha?")
        self.log(f"  {'='*60}")

        from scipy.optimize import brentq

        eps_fine = np.linspace(0.001, 0.55, 500)

        def compute_S_and_R(eps):
            psi = make_psi6_physical(eps)
            G = build_G(psi)
            s_tot = 0.0
            tot_k0, tot_k1, tot_k2 = 0.0, 0.0, 0.0

            for tri in ALL_HINGES:
                det_full = hinge_det(G, tri)
                if det_full <= 0:
                    continue
                area = np.sqrt(det_full)
                delta = deficit_angle_manifold(G, tri)
                s_tot += area * delta

                k0, k1, k2 = hinge_binet_cauchy(psi, tri)
                # Weight by area * delta (Regge weight)
                w = area * abs(delta)
                tot_k0 += k0 * w
                tot_k1 += k1 * w
                tot_k2 += k2 * w

            total_bc = tot_k0 + tot_k1 + tot_k2
            r_sss = tot_k0 / total_bc if total_bc > 0 else 0
            return s_tot, r_sss

        # Sweep
        S_vals, R_vals = [], []
        for eps in eps_fine:
            s, r = compute_S_and_R(eps)
            S_vals.append(s)
            R_vals.append(r)

        S_vals = np.array(S_vals)
        R_vals = np.array(R_vals)

        # Numerical dS/deps
        dS = np.gradient(S_vals, eps_fine)

        # Find all extrema of S
        extrema = []
        for i in range(1, len(dS)-1):
            if dS[i-1] * dS[i] < 0:
                try:
                    def f_dS(e):
                        s, _ = compute_S_and_R(e)
                        return s
                    # Use finite diff around the crossing
                    e_lo, e_hi = eps_fine[i-1], eps_fine[i]
                    # Refine
                    for _ in range(20):
                        e_mid = (e_lo + e_hi) / 2
                        s_lo = f_dS(e_lo)
                        s_mid = f_dS(e_mid)
                        # Check gradient sign
                        ds_lo = f_dS(e_lo + 1e-6) - s_lo
                        ds_mid = f_dS(e_mid + 1e-6) - s_mid
                        if ds_lo * ds_mid < 0:
                            e_hi = e_mid
                        else:
                            e_lo = e_mid
                    e_ext = (e_lo + e_hi) / 2
                    s_ext, r_ext = compute_S_and_R(e_ext)
                    is_max = dS[i-1] > 0
                    extrema.append((e_ext, s_ext, r_ext, is_max))
                except Exception:
                    pass

        self.log(f"\n  Action extrema found: {len(extrema)}")
        for j, (e, s, r, is_max) in enumerate(extrema):
            label = "MAX" if is_max else "min"
            self.log(f"    #{j+1} ({label}): eps={e:.6f},"
                     f" S={s:.5f}, R_SSS={r:.6f}")
            self.log(f"      eps/alpha = {e/ALPHA:.2f},"
                     f" eps/alpha_GUT = {e/ALPHA_GUT:.2f}")

        # For each extremum, report what R value it gives
        self.log(f"\n  At action extrema, R_SSS values:")
        for j, (e, s, r, is_max) in enumerate(extrema):
            self.log(f"    eps={e:.6f}: R_SSS={r:.6f}")
            # What target R would make eps=alpha the solution?

        # Inverse: what eps gives R_SSS = 1/25 = alpha_GUT?
        targets = {
            '1/25': 1/25,
            'alpha_GUT': ALPHA_GUT,
            'alpha_GUT^2': ALPHA_GUT**2,
            '1/d^2': 1/D**2,
            'alpha_em': ALPHA,
        }
        self.log(f"\n  Finding eps for various R_SSS targets:")
        for name, target in targets.items():
            # Find crossing
            found = False
            for i in range(1, len(R_vals)):
                if (R_vals[i-1] - target) * (R_vals[i] - target) < 0:
                    # Linear interpolation
                    e1, r1 = eps_fine[i-1], R_vals[i-1]
                    e2, r2 = eps_fine[i], R_vals[i]
                    e_cross = e1 + (target - r1) * (e2 - e1) / (r2 - r1)
                    self.log(f"    R_SSS = {target:.6f} ({name}):"
                             f" eps = {e_cross:.6f},"
                             f" eps/alpha = {e_cross/ALPHA:.1f},"
                             f" eps/alpha_GUT = {e_cross/ALPHA_GUT:.2f}")
                    found = True
                    break
            if not found:
                self.log(f"    R_SSS = {target:.6f} ({name}):"
                         f" NOT in range [eps=0.001..0.55]")
                self.log(f"      R range: [{min(R_vals):.6f},"
                         f" {max(R_vals):.6f}]")

        # Summary
        self.log(f"\n  === SUMMARY ===")
        self.log(f"  alpha_em = {ALPHA:.8f}")
        self.log(f"  alpha_GUT = {ALPHA_GUT:.8f}")
        if extrema:
            e0 = extrema[0][0]
            self.log(f"  First action extremum at eps = {e0:.6f}")
            self.log(f"  Ratio eps/alpha = {e0/ALPHA:.1f}")
            self.log(f"  Ratio eps/alpha_GUT = {e0/ALPHA_GUT:.2f}")
        self.log(f"  R_SSS(eps->0) ~ {R_vals[0]:.6f}")
        self.log(f"  R_SSS(eps=0.5) ~ {R_vals[-5]:.6f}")

        self.check("Coupled equation analysis done", True)


if __name__ == "__main__":
    DihedralEpsilon().execute()
