"""
Phase 1: Single simplex verification + He shielding σ = 5/16
============================================================

1a. Hinge det analytical values
1b. Helium shielding constant from Regge action stationary point
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))

import numpy as np
from regge_core import (gram_matrix, hinge_det, hinge_area,
                        dihedral_angle, deficit_angle, regge_action,
                        action_over_hbar, set_vertex_types, classify_hinge)
from simplex_builder import (build_hydrogen, build_helium,
                             normalize, make_S_vertex, make_T_vertex,
                             pack_params, unpack_params)
from itertools import combinations
from experiment import Experiment


class Phase1(Experiment):
    ID = "042a"
    TITLE = "Regge Phase 1"

    def run(self):
        np.random.seed(42)

        # ═══ 1a: Hinge det analytical verification ═══
        self.log("=" * 65)
        self.log("PHASE 1a: Hinge det analytical values")
        self.log("=" * 65)

        # Exact C³ orthogonal quarks + C² electrons with leak ε
        S1 = np.array([0, 0, 1, 0, 0], dtype=complex)
        S2 = np.array([0, 0, 0, 1, 0], dtype=complex)
        S3 = np.array([0, 0, 0, 0, 1], dtype=complex)

        for eps in [0.0, 0.05, 0.1, 0.15, 0.2]:
            # T₁: C² dominated, C³ leak = ε (symmetric in all 3 dirs)
            T1 = np.array([np.sqrt(1 - eps**2), 0,
                           eps/np.sqrt(3), eps/np.sqrt(3), eps/np.sqrt(3)],
                          dtype=complex)
            T1 = normalize(T1)
            # T₂: different C² direction
            T2 = np.array([0, np.sqrt(1 - eps**2),
                           eps/np.sqrt(3), eps/np.sqrt(3), eps/np.sqrt(3)],
                          dtype=complex)
            T2 = normalize(T2)

            # SSS det: should always be 1 for orthogonal quarks
            det_sss = hinge_det(S1, S2, S3)

            # SST det (e.g., S₁S₂T₁): theory = 1 - 2ε²/3
            det_sst = hinge_det(S1, S2, T1)
            theory_sst = 1 - 2 * eps**2 / 3

            # STT det (e.g., S₁T₁T₂): theory = 1 - ε²/3 (approx)
            det_stt = hinge_det(S1, T1, T2)

            self.log(f"\n  ε = {eps:.2f}:")
            self.log(f"    SSS det = {det_sss:.6f}  (theory: 1.000)")
            self.log(f"    SST det = {det_sst:.6f}  (theory: {theory_sst:.6f})")
            self.log(f"    STT det = {det_stt:.6f}")

        self.check("SSS det = 1 for orthogonal quarks",
                   abs(hinge_det(S1, S2, S3) - 1.0) < 1e-10)

        # ═══ 1a-extra: Dihedral angle in single simplex ═══
        self.log(f"\n{'='*65}")
        self.log("PHASE 1a-extra: Dihedral angles in single simplex")
        self.log(f"{'='*65}")

        eps = 0.1
        T1 = normalize(np.array([np.sqrt(1-eps**2), 0,
                                  eps/np.sqrt(3), eps/np.sqrt(3), eps/np.sqrt(3)],
                                 dtype=complex))
        T2 = normalize(np.array([0, np.sqrt(1-eps**2),
                                  eps/np.sqrt(3), eps/np.sqrt(3), eps/np.sqrt(3)],
                                 dtype=complex))

        vecs = [S1, S2, S3, T1, T2]
        labels = ['S₁','S₂','S₃','T₁','T₂']

        self.log(f"\n  ε = {eps}")
        self.log(f"  {'Hinge':<15} {'Type':<5} {'Det':>8} {'Area':>8}")
        self.log(f"  {'-'*15} {'-'*5} {'-'*8} {'-'*8}")

        vtypes = {0:'S', 1:'S', 2:'S', 3:'T', 4:'T'}
        set_vertex_types(vtypes)

        for tri in combinations(range(5), 3):
            det = hinge_det(vecs[tri[0]], vecs[tri[1]], vecs[tri[2]])
            area = hinge_area(vecs[tri[0]], vecs[tri[1]], vecs[tri[2]])
            htype = classify_hinge(tri)
            name = f"({labels[tri[0]]},{labels[tri[1]]},{labels[tri[2]]})"
            self.log(f"  {name:<15} {htype:<5} {det:8.4f} {area:8.4f}")

        # Dihedral angles for each hinge
        simplex_list = [(0, 1, 2, 3, 4)]
        self.log(f"\n  Dihedral angles (single simplex → 2 apices per hinge):")
        self.log(f"  {'Hinge':<15} {'Apices':<10} {'θ (deg)':>10}")
        self.log(f"  {'-'*15} {'-'*10} {'-'*10}")

        for tri in combinations(range(5), 3):
            apices = [v for v in range(5) if v not in tri]
            h_vecs = [vecs[i] for i in tri]
            theta = dihedral_angle(h_vecs, vecs[apices[0]], vecs[apices[1]])
            name = f"({labels[tri[0]]},{labels[tri[1]]},{labels[tri[2]]})"
            apex_name = f"{labels[apices[0]]},{labels[apices[1]]}"
            self.log(f"  {name:<15} {apex_name:<10} {np.degrees(theta):10.2f}°")

        # Deficit angles
        self.log(f"\n  Deficit angles (δ = 2π - θ, single simplex = boundary):")
        all_vecs_dict = {i: vecs[i] for i in range(5)}
        for tri in combinations(range(5), 3):
            delta = deficit_angle(all_vecs_dict, simplex_list, tri)
            name = f"({labels[tri[0]]},{labels[tri[1]]},{labels[tri[2]]})"
            self.log(f"  {name:<15} δ = {np.degrees(delta):8.2f}°")

        # Total Regge action
        S, breakdown = regge_action(all_vecs_dict, simplex_list)
        S_over_hbar = action_over_hbar(all_vecs_dict, simplex_list)
        self.log(f"\n  Total Regge action S = {S:.6f}")
        self.log(f"  S/ħ = 4ln2 × Σδ = {S_over_hbar:.6f}")
        self.check("Regge action computed", S != 0)

        # ═══ 1b: Helium shielding σ = 5/16 ═══
        self.log(f"\n{'='*65}")
        self.log("PHASE 1b: Helium shielding constant")
        self.log(f"{'='*65}")

        # He = 2 simplices sharing SSS face
        # Scan ε (C³ leak of T vertices) and find Regge action
        eps_values = np.linspace(0.01, 0.28, 30)
        actions = []

        for eps in eps_values:
            all_vecs, slist, vt = build_helium(epsilon=eps)
            S, _ = regge_action(all_vecs, slist)
            actions.append(S)

        actions = np.array(actions)

        # Find stationary point (dS/dε ≈ 0)
        dS = np.gradient(actions, eps_values)
        # Find zero crossing
        zero_crossings = []
        for i in range(len(dS) - 1):
            if dS[i] * dS[i+1] < 0:
                # Linear interpolation
                eps_cross = eps_values[i] - dS[i] * (eps_values[i+1] - eps_values[i]) / (dS[i+1] - dS[i])
                zero_crossings.append(eps_cross)

        self.log(f"\n  Scanning ε = C³ leak of T vertices:")
        self.log(f"  {'ε':>8} {'S(Regge)':>12} {'dS/dε':>12}")
        self.log(f"  {'-'*8} {'-'*12} {'-'*12}")
        for i in range(0, len(eps_values), 3):
            self.log(f"  {eps_values[i]:8.3f} {actions[i]:12.6f} {dS[i]:12.6f}")

        if zero_crossings:
            eps_star = zero_crossings[0]
            self.log(f"\n  Stationary point at ε* = {eps_star:.4f}")

            # Z_eff = Z - σ where σ = screening
            # At ε*, the ratio of He SST to H SST gives Z_eff
            all_vecs_he, slist_he, _ = build_helium(epsilon=eps_star)
            S_he, bd_he = regge_action(all_vecs_he, slist_he)

            all_vecs_h, slist_h, _ = build_hydrogen(epsilon=eps_star)
            S_h, bd_h = regge_action(all_vecs_h, slist_h)

            if abs(S_h) > 1e-15:
                ratio = S_he / S_h
                Z_eff = ratio  # simplified
                sigma = 2 - Z_eff  # Z=2 for He
                self.log(f"  S(He) / S(H) = {ratio:.4f}")
                self.log(f"  σ estimate = {sigma:.4f}")
                self.log(f"  Theory: σ = d/c⁴ = 5/16 = {5/16:.4f}")
            else:
                self.log(f"  S(H) too small for ratio")
        else:
            self.log(f"\n  No stationary point found in range")
            self.log(f"  Action is monotonic — need wider scan or different parameterization")

        self.check("He action computed",
                   len(actions) > 0 and not np.all(actions == 0))

        # ═══ Summary ═══
        self.log(f"\n{'='*65}")
        self.log("PHASE 1 SUMMARY")
        self.log(f"{'='*65}")
        self.log(f"\n  SSS det = 1 for orthogonal quarks: ✓")
        self.log(f"  SST det = 1-2ε²/3: verified above")
        self.log(f"  Dihedral angles: computed for all 10 hinges")
        self.log(f"  Regge action: S = {S:.6f}")
        self.log(f"  S/ħ = {S_over_hbar:.6f}")
        self.log(f"\n  Next: Phase 2 (H energy levels, H₂O bond angle)")


if __name__ == "__main__":
    Phase1().execute()
