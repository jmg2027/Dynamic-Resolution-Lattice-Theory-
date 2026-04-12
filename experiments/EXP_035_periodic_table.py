"""
EXP_035: Periodic Table from C⁵ — Ionization Energies Z=1..20
=============================================================

Each electron = ψ ∈ C⁵ with spin.
Shell structure from C⁵ = C² ⊕ C³:
  Shell 1 (C² dir 1): 2 electrons  → period 1
  Shell 2 (C² dir 2): 2 electrons  → period 2 (s)
  Shell 3 (C³):        6 electrons  → period 2 (p)
  Total C⁵ capacity:  10 electrons (first 2 periods)
  Shell 4+ : beyond C⁵ orthogonal → new "rank"

Energy: variational optimization of Z electron ψ-vectors.
  - Nuclear: -Z × α_em × |⟨ψ_e|ψ_nuc⟩|² per electron
  - Repulsion: +α_em × |⟨ψ_i|ψ_j⟩|² per electron pair
  - Pauli: penalty for |⟨ψ_i|ψ_j⟩|² > threshold (same spin)
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
from experiment import Experiment
import numpy as np
from scipy.optimize import minimize


D = 5
ALPHA_EM = 1 / 137.036
E_H = 13.606  # eV (positive, hydrogen ionization)

# Nuclear reference states (quarks in C³ = spatial sector)
# The nucleus "lives" along spatial directions
NUC_DIRS = [
    np.array([0, 0, 1, 0, 0], dtype=complex),  # spatial 1
    np.array([0, 0, 0, 1, 0], dtype=complex),  # spatial 2
    np.array([0, 0, 0, 0, 1], dtype=complex),  # spatial 3
]


def nuclear_coupling(psi):
    """How strongly electron ψ couples to the C³ nuclear sector.
    SST hinge requires 2 spatial + 1 temporal.
    Coupling ∝ product of spatial and temporal components."""
    temporal = np.sum(np.abs(psi[:2])**2)  # C² weight
    spatial = np.sum(np.abs(psi[2:])**2)   # C³ weight
    # SST coupling: need both sectors to be nonzero
    # Maximum when temporal ≈ spatial ≈ 0.5
    return 2 * np.sqrt(temporal * spatial)  # geometric mean, max=1


def atom_energy(x, Z, N_elec, spins):
    """Total energy for N electrons around nucleus Z.

    Key physics: each electron sees Z_eff = Z - screening from others.
    Screening from electron j on electron i = |⟨ψ_i|ψ_j⟩|² (overlap).
    This is the DRLT version of Slater shielding.
    """
    psi_list = []
    for i in range(N_elec):
        re = x[i*10 : i*10+5]
        im = x[i*10+5 : i*10+10]
        psi = re + 1j * im
        norm = np.linalg.norm(psi)
        if norm < 1e-15:
            return 1e10
        psi = psi / norm
        psi_list.append(psi)

    E = 0.0

    # For each electron: compute screened nuclear attraction
    for i in range(N_elec):
        # Screening: other electrons reduce effective Z
        screening = 0.0
        for j in range(N_elec):
            if j != i:
                overlap_sq = np.abs(np.vdot(psi_list[i], psi_list[j]))**2
                screening += overlap_sq  # each overlapping electron screens

        Z_eff = Z - screening
        if Z_eff < 0:
            Z_eff = 0.01

        coupling = nuclear_coupling(psi_list[i])
        # Hydrogen-like: E ∝ -Z_eff² (not linear)
        E -= Z_eff**2 * coupling

    # Pauli exclusion: same-spin electrons can't have large overlap
    PAULI_PENALTY = 100.0
    for i in range(N_elec):
        for j in range(i+1, N_elec):
            if spins[i] == spins[j]:
                overlap_sq = np.abs(np.vdot(psi_list[i], psi_list[j]))**2
                if overlap_sq > 0.3:
                    E += PAULI_PENALTY * (overlap_sq - 0.3)**2

    return E


def make_initial_electrons(N_elec):
    """Initialize electrons in C⁵ shell structure."""
    psi_list = []
    # Basis of C⁵: 2 temporal + 3 spatial
    basis = [
        np.array([1, 0, 0, 0, 0], dtype=complex),    # T1 (1s-like)
        np.array([0, 1, 0, 0, 0], dtype=complex),    # T2 (2s-like)
        np.array([0, 0, 1, 0, 0], dtype=complex),    # S1 (2p-like)
        np.array([0, 0, 0, 1, 0], dtype=complex),    # S2 (2p-like)
        np.array([0, 0, 0, 0, 1], dtype=complex),    # S3 (2p-like)
    ]
    for i in range(N_elec):
        dir_idx = i // 2  # each direction holds 2 (spin up/down)
        if dir_idx < 5:
            psi = basis[dir_idx].copy()
        else:
            # Beyond C⁵: superposition states
            psi = np.random.randn(5) + 1j * np.random.randn(5)
        # Add temporal component for SST coupling
        if dir_idx >= 2:  # spatial electrons need temporal admixture
            psi[0] += 0.3
            psi[1] += 0.2
        psi += 0.1 * (np.random.randn(5) + 1j * np.random.randn(5))
        psi_list.append(psi / np.linalg.norm(psi))
    return psi_list


def assign_spins(N_elec):
    """Assign spins: fill each direction with ↑ then ↓."""
    spins = []
    for i in range(N_elec):
        spins.append(i % 2)  # 0=up, 1=down, alternating
    return spins


def optimize_atom(Z, N_elec=None, n_restarts=15):
    """Find ground state of atom with Z protons, N electrons."""
    if N_elec is None:
        N_elec = Z  # neutral atom
    spins = assign_spins(N_elec)

    best_E = np.inf
    best_x = None

    for trial in range(n_restarts):
        psi_init = make_initial_electrons(N_elec)
        x0 = []
        for psi in psi_init:
            x0.extend(psi.real)
            x0.extend(psi.imag)
        x0 = np.array(x0) + 0.03 * np.random.randn(len(x0))

        result = minimize(atom_energy, x0, args=(Z, N_elec, spins),
                         method='L-BFGS-B',
                         options={'maxiter': 3000, 'ftol': 1e-14})

        if result.fun < best_E:
            best_E = result.fun
            best_x = result.x

    return best_E, best_x


# Observed first ionization energies (eV) Z=1..20
IE_OBS = {
    1: 13.598, 2: 24.587, 3: 5.392, 4: 9.323, 5: 8.298,
    6: 11.260, 7: 14.534, 8: 13.618, 9: 17.423, 10: 21.565,
    11: 5.139, 12: 7.646, 13: 5.986, 14: 8.152, 15: 10.487,
    16: 10.360, 17: 12.968, 18: 15.760, 19: 4.341, 20: 6.113,
}


class EXP_035(Experiment):
    ID = "035"
    TITLE = "Periodic Table"

    def run(self):
        self.log("=" * 70)
        self.log("Periodic Table from C⁵: Ionization Energies Z=1..20")
        self.log("=" * 70)
        self.log("")
        self.log("Shell structure from C⁵ = C² ⊕ C³:")
        self.log("  C² directions (temporal): 2 dirs × 2 spins = 4 electrons")
        self.log("  C³ directions (spatial):  3 dirs × 2 spins = 6 electrons")
        self.log("  C⁵ total capacity: 10 electrons (periods 1-2)")
        self.log("  Beyond C⁵: superposition states (periods 3+)")
        self.log("")

        results = {}
        energies_neutral = {}
        energies_ion = {}

        self.log(f"{'Z':>3s} {'Elem':>4s} {'E_neutral':>12s} {'E_ion':>12s} "
                 f"{'IE_DRLT':>10s} {'IE_obs':>8s} {'Err%':>7s} {'Shell':>8s}")
        self.log("-" * 70)

        for Z in range(1, 21):
            elem = ['H','He','Li','Be','B','C','N','O','F','Ne',
                    'Na','Mg','Al','Si','P','S','Cl','Ar','K','Ca'][Z-1]

            # Neutral atom: Z electrons
            E_neutral, x_neutral = optimize_atom(Z, Z, n_restarts=10)
            energies_neutral[Z] = E_neutral

            # Ion: Z-1 electrons (remove outermost)
            if Z > 1:
                E_ion, x_ion = optimize_atom(Z, Z-1, n_restarts=10)
            else:
                E_ion = 0.0  # bare proton
            energies_ion[Z] = E_ion

            # Ionization energy (in lattice units)
            IE_lattice = E_ion - E_neutral  # positive (costs energy)

            # Scale: calibrate using hydrogen
            if Z == 1:
                scale = IE_OBS[1] / IE_lattice if abs(IE_lattice) > 1e-10 else 1.0

            IE_drlt = IE_lattice * scale
            ie_obs = IE_OBS[Z]
            err = (IE_drlt - ie_obs) / ie_obs * 100

            # Shell label
            if Z <= 2:
                shell = "1s(C²)"
            elif Z <= 4:
                shell = "2s(C²)"
            elif Z <= 10:
                shell = "2p(C³)"
            elif Z <= 12:
                shell = "3s"
            elif Z <= 18:
                shell = "3p"
            else:
                shell = "4s"

            results[Z] = (elem, IE_drlt, ie_obs, err, shell)
            self.log(f"{Z:3d} {elem:>4s} {E_neutral:12.4f} {E_ion:12.4f} "
                     f"{IE_drlt:10.2f} {ie_obs:8.3f} {err:+7.1f}% {shell:>8s}")

        # ═══ Analysis ═══
        self.log("")
        self.log("=" * 70)
        self.log("ANALYSIS")
        self.log("=" * 70)

        # Period breaks
        self.log("")
        self.log("Period structure (should show 2, 8, 8 pattern):")
        ie_values = [results[Z][1] for Z in range(1, 21)]

        # Noble gas peaks
        noble = [2, 10, 18]
        for Z in noble:
            self.log(f"  Z={Z:2d} ({results[Z][0]}): IE = {results[Z][1]:.1f} eV (noble gas peak)")

        # Alkali drops
        alkali = [3, 11, 19]
        for Z in alkali:
            prev = results[Z-1][1]
            curr = results[Z][1]
            self.log(f"  Z={Z:2d} ({results[Z][0]}): IE = {curr:.1f} eV "
                     f"(drop from {prev:.1f}, ratio {curr/prev:.2f})")

        # Check noble gas > alkali pattern
        noble_higher = all(results[n][1] > results[a][1]
                          for n, a in zip(noble, alkali))
        self.check("noble gas IE > next alkali", noble_higher)

        # Check He is highest in period 1-2
        he_highest = results[2][1] > results[1][1]
        self.check("He has highest IE in period 1", he_highest)

        # Overall correlation
        ie_drlt = np.array([results[Z][1] for Z in range(1, 21)])
        ie_obs = np.array([IE_OBS[Z] for Z in range(1, 21)])
        correlation = np.corrcoef(ie_drlt, ie_obs)[0, 1]
        self.log(f"")
        self.log(f"  Pearson correlation r = {correlation:.4f}")
        self.check("IE correlation r > 0.7", correlation > 0.7)

        # Mean absolute error
        mae = np.mean(np.abs(ie_drlt - ie_obs))
        mape = np.mean(np.abs((ie_drlt - ie_obs) / ie_obs)) * 100
        self.log(f"  MAE = {mae:.2f} eV")
        self.log(f"  MAPE = {mape:.1f}%")
        self.check("MAPE < 50%", mape < 50)

        # ═══ Summary ═══
        self.log("")
        self.log("=" * 70)
        self.log("SUMMARY")
        self.log("=" * 70)
        self.log("")
        self.log("  C⁵ shell structure: 2(C²) + 2(C²) + 6(C³) = 10 = periods 1-2")
        self.log("  Matches real periodic table: 2 + 8 = 10 elements")
        self.log("  Period 3+: electrons in superposition states (beyond C⁵ basis)")
        self.log("")
        self.log("  Each atom = Z electrons in C⁵, optimized by hinge energy")
        self.log("  Ionization energy = E(ion) - E(neutral)")
        self.log("  Calibration: 1 free parameter (overall scale from H)")
        self.log("  All Z-dependent structure from C⁵ geometry")


if __name__ == "__main__":
    EXP_035().execute()
