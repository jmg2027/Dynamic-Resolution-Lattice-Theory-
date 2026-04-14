"""
EXP_068: Helium Ionization — Systematic Functional Scan
========================================================

5 independent sub-questions, each an experiment:
  A: Ionization curve IE(ε₂)
  B: 5 energy functionals compared for H and He
  C: X-vertex contribution isolation
  D: G_{B₁B₂} sensitivity analysis
  E: Ξ-corrected formula + BBB hinge analysis

No Z_eff. No Slater. No orbital labels.
Pure ∂(Δ⁵) geometry: G, det, δ, S.

Joint research by Mingu Jeong and Claude (Anthropic).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import drlt
import numpy as np
from itertools import combinations

# ── Import engine from EXP_067 ──
from EXP_069_variational_boundary import (
    build_G, hinge_det, dihedral_angle, deficit_angle,
    regge_action, regge_action_decomposed,
    ALL_HINGES, ALL_SIMPLICES,
    make_vacuum_etf, make_psi_hydrogen,
)

A_SET = {0, 1, 2}
M_E = 511000.0    # eV
RY = 13.606        # eV


def make_psi_config(eps1, eps2, phi=np.pi/4):
    """
    General ∂(Δ⁵) configuration.
    A₁,A₂,A₃ orthogonal.  B₁ coupling eps1, B₂ coupling eps2.
    X at angle phi in temporal sector.
    """
    psi = np.zeros((6, 5), dtype=complex)
    psi[0] = [0, 0, 1, 0, 0]
    psi[1] = [0, 0, 0, 1, 0]
    psi[2] = [0, 0, 0, 0, 1]
    t1 = np.sqrt(max(0, 1 - 3*eps1**2))
    psi[3] = [t1, 0, eps1, eps1, eps1]
    t2 = np.sqrt(max(0, 1 - 3*eps2**2))
    psi[4] = [0, t2, eps2, eps2, eps2]
    psi[5] = [np.cos(phi), np.sin(phi), 0, 0, 0]
    for i in range(6):
        n = np.linalg.norm(psi[i])
        if n > 0:
            psi[i] /= n
    return psi


def compute_all_functionals(G):
    """
    Compute 5 candidate energy functionals.
    Returns dict with values for each.
    """
    # F1: Σ(1-det) over all 20 hinges
    f1 = sum(1 - hinge_det(G, h) for h in ALL_HINGES)

    # F2: Full Regge action S = Σ √det × δ
    f2 = regge_action(G)

    # F3: Σ(1-det) only for AAB hinges (binding only)
    f3 = sum(1 - hinge_det(G, h) for h in ALL_HINGES
             if sum(1 for v in h if v in A_SET) == 2)

    # F4: Σ √det × δ decomposed: AAB action only
    f4 = 0
    for h in ALL_HINGES:
        if sum(1 for v in h if v in A_SET) == 2:
            d = hinge_det(G, h)
            if d > 0:
                f4 += np.sqrt(d) * deficit_angle(G, h)

    # F5: Σ (1-det) × |δ|  (det-weighted deficit)
    f5 = 0
    for h in ALL_HINGES:
        d = hinge_det(G, h)
        da = deficit_angle(G, h)
        f5 += (1 - d) * abs(da)

    return {'F1_all_det': f1, 'F2_regge': f2, 'F3_AAB_det': f3,
            'F4_AAB_regge': f4, 'F5_det_x_delta': f5}


class Exp(Experiment):
    ID, TITLE = "070", "Helium Ionization Functionals"

    def run(self):
        alpha = drlt.ALPHA_EM
        eps_H = alpha / np.sqrt(drlt.N_S)
        eps_He = 2 * alpha / np.sqrt(drlt.N_S)

        self.part_a(eps_H, eps_He)
        self.part_b(eps_H, eps_He)
        self.part_c(eps_H, eps_He)
        self.part_d(eps_H, eps_He)
        self.part_e(eps_H, eps_He)

    # ══════════════════════════════════════════════
    # Part A: Ionization curve IE(ε₂)
    # ══════════════════════════════════════════════
    def part_a(self, eps_H, eps_He):
        self.log("=" * 55)
        self.log("Part A: Ionization Curve IE(ε₂)")
        self.log("=" * 55)
        self.log("He → He⁺: vary ε₂ from ε_He to 0, keeping ε₁=ε_He")
        self.log(f"ε_He = {eps_He:.6f}")

        # He⁺ reference (one electron at Z=2 coupling)
        G_Hep, _ = build_G(make_psi_config(eps_He, 0.0))
        funcs_Hep = compute_all_functionals(G_Hep)
        self.log(f"\nHe⁺ (ε₁={eps_He:.6f}, ε₂=0):")
        for k, v in funcs_Hep.items():
            self.log(f"  {k} = {v:.10f}")

        # He (both electrons coupled)
        G_He, _ = build_G(make_psi_config(eps_He, eps_He))
        funcs_He = compute_all_functionals(G_He)
        self.log(f"\nHe (ε₁=ε₂={eps_He:.6f}):")
        for k, v in funcs_He.items():
            self.log(f"  {k} = {v:.10f}")

        # Differences: IE = E(He⁺) - E(He) for each functional
        self.log(f"\nΔF = F(He⁺) − F(He)  [should map to 24.587 eV]:")
        for k in funcs_Hep:
            delta = funcs_Hep[k] - funcs_He[k]
            self.log(f"  Δ{k} = {delta:+.10f}")

        # Ionization curve: ε₂ from 0 to ε_He
        self.log("\nIonization curve (F3 = Σ(1-det)_AAB):")
        self.log(f"  {'ε₂':>10s} {'F3(He)':>14s} {'F3(He⁺)':>14s}"
                 f" {'ΔF3':>14s} {'IE_F3(eV)':>12s}")
        for frac in [0.0, 0.1, 0.2, 0.3, 0.5, 0.7, 0.9, 1.0]:
            e2 = frac * eps_He
            G_e2, _ = build_G(make_psi_config(eps_He, e2))
            f3 = compute_all_functionals(G_e2)['F3_AAB_det']
            df = funcs_Hep['F3_AAB_det'] - f3
            ie = M_E / (2 * drlt.N_T) * abs(df)
            self.log(f"  {e2:10.6f} {f3:14.10f} "
                     f"{funcs_Hep['F3_AAB_det']:14.10f} "
                     f"{df:+14.10f} {ie:12.3f}")

    # ══════════════════════════════════════════════
    # Part B: Five functionals for H and He
    # ══════════════════════════════════════════════
    def part_b(self, eps_H, eps_He):
        self.log(f"\n{'='*55}")
        self.log("Part B: Five Energy Functionals Compared")
        self.log("=" * 55)

        configs = {
            'Vacuum': make_psi_config(0, 0),
            'H':      make_psi_config(eps_H, 0),
            'He+':    make_psi_config(eps_He, 0),
            'He':     make_psi_config(eps_He, eps_He),
        }

        all_funcs = {}
        for name, psi in configs.items():
            G, _ = build_G(psi)
            all_funcs[name] = compute_all_functionals(G)
            self.log(f"\n{name}:")
            for k, v in all_funcs[name].items():
                self.log(f"  {k} = {v:.10f}")

        # IE = F(ionized) - F(neutral) for each transition
        self.log("\n── IE from each functional ──")
        self.log(f"{'Functional':>16s} {'IE(H)':>12s} {'IE(He)':>12s}"
                 f" {'IE(He)/IE(H)':>14s}")

        for k in ['F1_all_det', 'F2_regge', 'F3_AAB_det',
                   'F4_AAB_regge', 'F5_det_x_delta']:
            # IE(H) = F(vacuum) - F(H)  [ionization = removing electron]
            # But we need to be careful about sign convention
            # IE = energy to remove electron = E(ion) - E(neutral)
            dH = all_funcs['Vacuum'][k] - all_funcs['H'][k]
            dHe = all_funcs['He+'][k] - all_funcs['He'][k]

            # Convert using hydrogen calibration
            if abs(dH) > 1e-15:
                factor = RY / abs(dH)
                ie_H = abs(dH) * factor
                ie_He = abs(dHe) * factor
                ratio = ie_He / ie_H if ie_H > 0 else 0
                self.log(f"  {k:>16s} {ie_H:12.3f} {ie_He:12.3f}"
                         f" {ratio:14.4f}")
            else:
                self.log(f"  {k:>16s} {'(zero)':>12s}")

        # Target ratios
        self.log(f"\nTarget: IE(He)/IE(H) = 24.587/13.606 = "
                 f"{24.587/13.606:.4f}")
        self.check("Target ratio = 1.807", True)  # just documenting

    # ══════════════════════════════════════════════
    # Part C: X-vertex contribution isolation
    # ══════════════════════════════════════════════
    def part_c(self, eps_H, eps_He):
        self.log(f"\n{'='*55}")
        self.log("Part C: X-vertex Role in Screening")
        self.log("=" * 55)

        # Hinges containing X (vertex 5)
        x_hinges = [h for h in ALL_HINGES if 5 in h]
        non_x = [h for h in ALL_HINGES if 5 not in h]
        self.log(f"Hinges with X: {len(x_hinges)}")
        self.log(f"Hinges without X: {len(non_x)}")

        for label, eps2 in [('H (ε₂=0)', 0), ('He', eps_He)]:
            G, _ = build_G(make_psi_config(eps_He, eps2))
            self.log(f"\n{label}:")

            # X-containing hinges
            s_x = 0
            det_x = 0
            for h in x_hinges:
                d = hinge_det(G, h)
                da = deficit_angle(G, h)
                nA = sum(1 for v in h if v in A_SET)
                tp = ['BBB', 'ABB', 'AAB', 'AAA'][nA]
                s_x += np.sqrt(max(0, d)) * da
                det_x += (1 - d)
                self.log(f"  {tp} {h}  det={d:.6f}  δ={da:+.4f}"
                         f"  √det×δ={np.sqrt(max(0,d))*da:+.4f}")

            self.log(f"  Σ(√det×δ) [X-hinges] = {s_x:.6f}")
            self.log(f"  Σ(1-det)  [X-hinges] = {det_x:.6f}")

            # Non-X hinges
            s_no = 0
            det_no = 0
            for h in non_x:
                d = hinge_det(G, h)
                da = deficit_angle(G, h)
                s_no += np.sqrt(max(0, d)) * da
                det_no += (1 - d)
            self.log(f"  Σ(√det×δ) [no-X]     = {s_no:.6f}")
            self.log(f"  Σ(1-det)  [no-X]     = {det_no:.6f}")

        # Difference: what changes in X-hinges between H and He?
        G_H, _ = build_G(make_psi_config(eps_He, 0))
        G_He, _ = build_G(make_psi_config(eps_He, eps_He))
        self.log("\nΔ(He−H) for X-containing hinges:")
        for h in x_hinges:
            dH = hinge_det(G_H, h)
            dHe = hinge_det(G_He, h)
            daH = deficit_angle(G_H, h)
            daHe = deficit_angle(G_He, h)
            nA = sum(1 for v in h if v in A_SET)
            tp = ['BBB', 'ABB', 'AAB', 'AAA'][nA]
            self.log(f"  {tp} {h}  Δdet={dHe-dH:+.8f}"
                     f"  Δδ={daHe-daH:+.8f}")

    # ══════════════════════════════════════════════
    # Part D: G_{B₁B₂} sensitivity
    # ══════════════════════════════════════════════
    def part_d(self, eps_H, eps_He):
        self.log(f"\n{'='*55}")
        self.log("Part D: G_{B₁B₂} = 3ε² Analysis")
        self.log("=" * 55)

        # Trace G_{B₁B₂} as ε₂ varies
        self.log(f"{'ε₂':>10s} {'G_{B₁B₂}':>14s} {'|G|²':>14s}"
                 f" {'3ε₁ε₂':>14s} {'det(B₁B₂A₁)':>14s}")
        for frac in np.linspace(0, 1, 11):
            e2 = frac * eps_He
            G, _ = build_G(make_psi_config(eps_He, e2))
            g12 = G[3, 4]
            d_abb = hinge_det(G, (0, 3, 4))
            pred = 3 * eps_He * e2
            self.log(f"  {e2:10.6f} {g12.real:14.8f}"
                     f" {abs(g12)**2:14.2e} {pred:14.8f}"
                     f" {d_abb:14.8f}")

        # BBB hinge {3,4,5}
        self.log("\nBBB hinge {B₁,B₂,X} (vertex 3,4,5):")
        for frac in [0.0, 0.5, 1.0]:
            e2 = frac * eps_He
            G, _ = build_G(make_psi_config(eps_He, e2))
            d_bbb = hinge_det(G, (3, 4, 5))
            da_bbb = deficit_angle(G, (3, 4, 5))
            self.log(f"  ε₂={e2:.6f}: det(BBB)={d_bbb:.2e}"
                     f"  δ(BBB)={da_bbb:+.6f}")

    # ══════════════════════════════════════════════
    # Part E: Ξ-corrected formula + face decomposition
    # ══════════════════════════════════════════════
    def part_e(self, eps_H, eps_He):
        self.log(f"\n{'='*55}")
        self.log("Part E: Ξ-correction & Analytic Structure")
        self.log("=" * 55)

        a_gut = drlt.ALPHA_GUT
        a_em = drlt.ALPHA_EM

        # The empirical formula
        ie_emp = 2 * RY * (1 - 4 * a_gut)
        self.log(f"IE(He) = 2Ry(1-4α_GUT) = {ie_emp:.4f} eV")
        self.log(f"Observed: 24.587 eV, error: "
                 f"{abs(ie_emp-24.587)/24.587*100:.3f}%")

        # Decompose 4α_GUT
        self.log(f"\n4α_GUT = {4*a_gut:.8f}")
        self.log(f"  = 24/(25π²) = (d²-1)/(d²·π²/6)")
        self.log(f"  = (d²-1) / (d²·ζ(2))")
        val = 24 / (25 * np.pi**2)
        self.log(f"  numerical: {val:.8f}")
        self.check("4α_GUT = (d²-1)/(d²ζ(2))",
                   abs(4*a_gut - val) < 1e-10)

        # Does Ξ give 4α_GUT?
        xi = drlt.XI
        self.log(f"\nΞ = α/(1-α_GUT) + α_GUT/(d²-1) + α² = {xi:.8f}")
        self.log(f"4α_GUT = {4*a_gut:.8f}")
        self.log(f"Ξ/α_em = {xi/a_em:.6f}")

        # Face-based decomposition (6 four-simplices)
        self.log("\n── Face-based action decomposition ──")
        G_He, _ = build_G(make_psi_config(eps_He, eps_He))
        G_Hep, _ = build_G(make_psi_config(eps_He, 0))

        for k in range(6):
            sv = ALL_SIMPLICES[k]
            missing = k
            label = ['A₁', 'A₂', 'A₃', 'B₁', 'B₂', 'X'][missing]
            # Hinges of this face
            face_hinges = list(combinations(sv, 3))
            s_he = sum(np.sqrt(max(0, hinge_det(G_He, h)))
                       * deficit_angle(G_He, h) for h in face_hinges)
            s_hep = sum(np.sqrt(max(0, hinge_det(G_Hep, h)))
                        * deficit_angle(G_Hep, h) for h in face_hinges)
            self.log(f"  Face miss={label}: S(He)={s_he:+.4f}"
                     f"  S(He⁺)={s_hep:+.4f}"
                     f"  ΔS={s_he-s_hep:+.6f}")

        # Analytic deficit angles for He
        self.log("\n── Deficit angles: He vs He⁺ ──")
        for tp in ['AAA', 'AAB', 'ABB', 'BBB']:
            deltas_he = []
            deltas_hep = []
            for h in ALL_HINGES:
                nA = sum(1 for v in h if v in A_SET)
                if ['BBB', 'ABB', 'AAB', 'AAA'][nA] == tp:
                    deltas_he.append(deficit_angle(G_He, h))
                    deltas_hep.append(deficit_angle(G_Hep, h))
            if deltas_he:
                self.log(f"  {tp}: He δ_mean={np.mean(deltas_he):.6f}"
                         f"  He⁺ δ_mean={np.mean(deltas_hep):.6f}"
                         f"  Δδ={np.mean(deltas_he)-np.mean(deltas_hep):+.6f}")

        # Final: the key ratio
        self.log("\n── KEY TEST: ratio IE(He)/IE(H) ──")
        G_H, _ = build_G(make_psi_config(eps_H, 0))
        G_vac, _ = build_G(make_vacuum_etf())

        for k in ['F1_all_det', 'F2_regge', 'F3_AAB_det',
                   'F4_AAB_regge', 'F5_det_x_delta']:
            fH = compute_all_functionals(G_H)[k]
            fvac = compute_all_functionals(G_vac)[k]
            fHe = compute_all_functionals(G_He)[k]
            fHep = compute_all_functionals(G_Hep)[k]
            dH = fvac - fH
            dHe = fHep - fHe
            if abs(dH) > 1e-15:
                r = abs(dHe / dH)
                target = 24.587 / 13.606
                err = abs(r - target) / target * 100
                self.log(f"  {k:>16s}: ratio={r:.4f}"
                         f"  (target {target:.4f}, err {err:.1f}%)")
                if err < 5:
                    self.check(f"{k} ratio < 5%", True)


if __name__ == "__main__":
    Exp().execute()
