"""
EXP_037: Complete Simplex Chemistry — H, He, H₂ from First Principles
=====================================================================

Every atom/molecule = simplices with ψ ∈ C⁵ at each vertex.
S vertices = quarks (C³), T vertices = leptons (C²).
All forces automatic: SSS=strong, SST=EM, STT=weak, hinge-hinge=gravity.

Computation: assign ψ, compute G_ij, compute det(G_h), sum hinge energies.
No Schrödinger equation. No basis sets. Just 5×5 complex linear algebra.

Systems:
  1. H atom (1 simplex, 5 vertices, 10 hinges)
  2. H⁺ ion (remove electron = set T₁→vacuum)
  3. He atom (2 simplices sharing SSS core, 2 electrons)
  4. He⁺ ion (1 electron removed)
  5. H₂ molecule (2 simplices sharing T₂)
  6. H + H separated (2 independent simplices)
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
from experiment import Experiment
import numpy as np
from itertools import combinations
from scipy.optimize import minimize


# ═══════════════════════════════════════════════════════════════
#  Core: G and det from ψ vectors
# ═══════════════════════════════════════════════════════════════

def overlap(a, b):
    """G_ij = ⟨ψ_i|ψ_j⟩"""
    return complex(np.vdot(a, b))

def hinge_det(a, b, c):
    """det(G_h) for triangle {a,b,c}."""
    Gab, Gac, Gbc = overlap(a,b), overlap(a,c), overlap(b,c)
    return float(np.real(
        1 - abs(Gab)**2 - abs(Gac)**2 - abs(Gbc)**2
        + 2 * Gab * Gbc * np.conj(Gac)))

def hinge_type(tri_labels):
    """Classify by S/T content."""
    ns = sum(1 for l in tri_labels if l.startswith('S'))
    return {3:"SSS", 2:"SST", 1:"STT", 0:"TTT"}[ns]

# Coupling weights (from DRLT: ch05)
ALPHA_S = 1/8.47      # strong
ALPHA_EM = 1/137.036   # electromagnetic
ALPHA_W = 1/29.6       # weak


# ═══════════════════════════════════════════════════════════════
#  Simplex energy: sum over all hinges with proper couplings
# ═══════════════════════════════════════════════════════════════

def system_energy(psi_dict):
    """Compute total energy of a system defined by labeled ψ vectors.

    psi_dict: {"S1": ψ₁, "S2": ψ₂, "T1": ψ₃, ...}
    Returns: total energy, breakdown by type
    """
    labels = list(psi_dict.keys())
    psi = [psi_dict[l] for l in labels]
    N = len(labels)

    E = {"SSS": 0.0, "SST": 0.0, "STT": 0.0, "TTT": 0.0, "total": 0.0}
    details = []

    for tri in combinations(range(N), 3):
        tri_labels = [labels[i] for i in tri]
        ht = hinge_type(tri_labels)
        det = hinge_det(psi[tri[0]], psi[tri[1]], psi[tri[2]])
        area = np.sqrt(max(det, 0))

        # Energy contribution with proper coupling
        if ht == "SSS":
            dE = -ALPHA_S * area      # attractive (nuclear binding)
        elif ht == "SST":
            dE = -ALPHA_EM * area     # attractive (EM binding)
        elif ht == "STT":
            dE = +ALPHA_W * area      # repulsive/weak
        elif ht == "TTT":
            dE = 0  # impossible in real physics (n_T=2<3), but can appear with 3+ T vertices

        E[ht] += dE
        E["total"] += dE
        details.append((tri_labels, ht, det, area, dE))

    return E, details


# ═══════════════════════════════════════════════════════════════
#  Build systems from ψ vectors
# ═══════════════════════════════════════════════════════════════

def normalize(v):
    return v / np.linalg.norm(v)

def make_quark(direction, perturbation=0.05):
    """Quark = mostly along one spatial direction."""
    psi = np.zeros(5, dtype=complex)
    psi[2 + direction] = 1.0  # spatial component
    psi += perturbation * (np.random.randn(5) + 1j*np.random.randn(5))
    return normalize(psi)

def make_electron(alpha=1.0, beta=0.0, spatial_leak=0.0):
    """Electron = C² state with optional C³ leak.
    alpha, beta: spin components (T₁, T₂ weights)
    spatial_leak: how much leaks into C³ (excited states)
    """
    psi = np.zeros(5, dtype=complex)
    psi[0] = alpha           # T₁
    psi[1] = beta            # T₂
    if spatial_leak > 0:
        psi[2:5] = spatial_leak / np.sqrt(3)  # equal leak to all S
    return normalize(psi)

def make_vacuum_T(direction=1):
    """Vacuum T vertex = nearly aligned with a quark (part of SSS background).
    In vacuum, the T slot merges with the proton structure → becomes S-like.
    This makes det(SST involving this T) ≈ 0 → no EM binding from this slot."""
    psi = np.zeros(5, dtype=complex)
    # Vacuum T aligns with spatial (quark) direction → orthogonal to active electron
    psi[2] = 0.7    # mostly spatial (merging with proton)
    psi[direction] = 0.3  # small temporal remnant
    psi += 0.02 * (np.random.randn(5) + 1j*np.random.randn(5))
    return normalize(psi)

def make_neutrino():
    """Neutrino = nearly empty T (almost vacuum)."""
    psi = np.zeros(5, dtype=complex)
    psi[0] = 0.001   # tiny T₁
    psi[1] = 0.999   # almost vacuum
    return normalize(psi)


# ═══════════════════════════════════════════════════════════════
#  Variational optimization
# ═══════════════════════════════════════════════════════════════

def optimize_system(build_fn, n_restarts=20):
    """Optimize ψ configuration to minimize energy."""
    best_E = np.inf
    best_psi = None

    for _ in range(n_restarts):
        psi_dict = build_fn()
        labels = list(psi_dict.keys())

        # Pack into flat array
        def objective(x):
            pd = {}
            for i, l in enumerate(labels):
                re = x[i*10:i*10+5]
                im = x[i*10+5:i*10+10]
                v = re + 1j*im
                n = np.linalg.norm(v)
                pd[l] = v/n if n > 1e-15 else normalize(np.random.randn(5)+1j*np.random.randn(5))
            E, _ = system_energy(pd)
            return E["total"]

        x0 = []
        for l in labels:
            x0.extend(psi_dict[l].real)
            x0.extend(psi_dict[l].imag)
        x0 = np.array(x0, dtype=float)
        x0 += 0.02 * np.random.randn(len(x0))

        res = minimize(objective, x0, method='L-BFGS-B',
                      options={'maxiter':3000, 'ftol':1e-15})

        if res.fun < best_E:
            best_E = res.fun
            # Unpack best
            best_psi = {}
            for i, l in enumerate(labels):
                re = res.x[i*10:i*10+5]
                im = res.x[i*10+5:i*10+10]
                v = re + 1j*im
                best_psi[l] = normalize(v)

    return best_psi, best_E


# ═══════════════════════════════════════════════════════════════
#  System builders
# ═══════════════════════════════════════════════════════════════

def build_hydrogen():
    """H: 1 simplex = {S₁,S₂,S₃,T₁,T₂}"""
    return {
        "S1": make_quark(0), "S2": make_quark(1), "S3": make_quark(2),
        "T1": make_electron(alpha=1.0, beta=0.0),
        "T2": make_vacuum_T(),
    }

def build_H_ion():
    """H⁺: proton only = {S₁,S₂,S₃,T₁_vac,T₂_vac}"""
    return {
        "S1": make_quark(0), "S2": make_quark(1), "S3": make_quark(2),
        "T1": make_vacuum_T(),
        "T2": make_vacuum_T(),
    }

def build_helium():
    """He: 2 simplices sharing SSS core.
    {S₁,S₂,S₃,T₁,T₂} + {S₁,S₂,S₃,T₁,T₃}
    = 6 unique vertices: S₁,S₂,S₃(Z=2 nucleus),T₁,T₂(e↑),T₃(e↓)"""
    return {
        "S1": make_quark(0), "S2": make_quark(1), "S3": make_quark(2),
        "T1": make_electron(alpha=1.0, beta=0.0),         # e₁ spin up
        "T2": make_electron(alpha=0.0, beta=1.0),         # e₂ spin down
        "T3": make_vacuum_T(),                             # vacuum
    }

def build_He_ion():
    """He⁺: 1 electron removed"""
    return {
        "S1": make_quark(0), "S2": make_quark(1), "S3": make_quark(2),
        "T1": make_electron(alpha=1.0, beta=0.0),
        "T2": make_vacuum_T(),
        "T3": make_vacuum_T(),
    }

def build_H2_molecule():
    """H₂: 2 simplices sharing T₂ (covalent bond)
    Simplex A: {S₁,S₂,S₃,T₁,T₂}
    Simplex B: {S₄,S₅,S₆,T₂,T₃}
    T₂ shared = covalent bond!"""
    return {
        "S1": make_quark(0), "S2": make_quark(1), "S3": make_quark(2),
        "S4": make_quark(0), "S5": make_quark(1), "S6": make_quark(2),
        "T1": make_electron(alpha=1.0, beta=0.0),
        "T2": make_electron(alpha=0.5, beta=0.5),   # shared electron
        "T3": make_electron(alpha=0.0, beta=1.0),
    }

def build_H_separated():
    """Two H atoms far apart (no shared vertices).
    Just 2× hydrogen with no overlap."""
    return {
        "S1": make_quark(0), "S2": make_quark(1), "S3": make_quark(2),
        "T1": make_electron(alpha=1.0, beta=0.0),
        "T2_a": make_vacuum_T(),
        "S4": make_quark(0, perturbation=0.2),
        "S5": make_quark(1, perturbation=0.2),
        "S6": make_quark(2, perturbation=0.2),
        "T3": make_electron(alpha=0.7, beta=0.7),
        "T2_b": make_vacuum_T(),
    }


class EXP_037(Experiment):
    ID = "037"
    TITLE = "Simplex Chemistry"

    def run(self):
        np.random.seed(42)

        self.log("=" * 70)
        self.log("COMPLETE SIMPLEX CHEMISTRY")
        self.log("=" * 70)
        self.log("")
        self.log("  Recipe: draw simplices → assign ψ ∈ C⁵ → compute det(G_h)")
        self.log("  → sum hinge energies with SSS/SST/STT couplings → done")
        self.log("")

        results = {}

        # ═══ 1. Hydrogen ═══
        self.log("━" * 70)
        self.log("1. HYDROGEN ATOM (1 simplex, 5 vertices, 10 hinges)")
        self.log("━" * 70)
        psi_H, E_H = optimize_system(build_hydrogen, n_restarts=10)
        E_H_detail, det_H = system_energy(psi_H)
        results["H"] = E_H_detail
        self.log(f"   SSS = {E_H_detail['SSS']:.6f}  (nuclear binding)")
        self.log(f"   SST = {E_H_detail['SST']:.6f}  (EM binding)")
        self.log(f"   STT = {E_H_detail['STT']:.6f}  (weak)")
        self.log(f"   Total = {E_H_detail['total']:.6f}")

        # ═══ 2. H⁺ ion ═══
        self.log("")
        self.log("━" * 70)
        self.log("2. H⁺ ION (proton only, T→vacuum)")
        self.log("━" * 70)
        psi_Hp, E_Hp = optimize_system(build_H_ion, n_restarts=10)
        E_Hp_detail, _ = system_energy(psi_Hp)
        results["H+"] = E_Hp_detail
        self.log(f"   SSS = {E_Hp_detail['SSS']:.6f}")
        self.log(f"   SST = {E_Hp_detail['SST']:.6f}")
        self.log(f"   STT = {E_Hp_detail['STT']:.6f}")
        self.log(f"   Total = {E_Hp_detail['total']:.6f}")

        # Ionization energy of H
        IE_H_lattice = E_Hp_detail['total'] - E_H_detail['total']
        self.log(f"\n   IE(H) = E(H⁺) - E(H) = {IE_H_lattice:.6f} (lattice units)")

        # Calibrate: IE(H) = 13.606 eV
        if abs(IE_H_lattice) > 1e-10:
            eV_scale = 13.606 / IE_H_lattice
        else:
            eV_scale = 1.0
        self.log(f"   Scale: 1 lattice unit = {eV_scale:.2f} eV")
        self.log(f"   IE(H) = 13.606 eV (calibration point)")

        # ═══ 3. He⁺ ion ═══
        self.log("")
        self.log("━" * 70)
        self.log("3. He⁺ ION (Z=2, 1 electron)")
        self.log("━" * 70)
        psi_Hep, E_Hep = optimize_system(build_He_ion, n_restarts=10)
        E_Hep_detail, _ = system_energy(psi_Hep)
        results["He+"] = E_Hep_detail
        self.log(f"   SSS = {E_Hep_detail['SSS']:.6f}")
        self.log(f"   SST = {E_Hep_detail['SST']:.6f}")
        self.log(f"   STT = {E_Hep_detail['STT']:.6f}")
        self.log(f"   Total = {E_Hep_detail['total']:.6f}")

        # He⁺ ionization (He⁺ → He²⁺, compare with bare nucleus)
        # For now compare SST binding: He⁺ vs H
        ratio_HeP_H = E_Hep_detail['SST'] / E_H_detail['SST']
        self.log(f"\n   SST(He⁺)/SST(H) = {ratio_HeP_H:.2f}")
        self.log(f"   Theory (Z²=4): 4.00")
        self.check("He⁺/H SST ratio ~ Z²", 2 < abs(ratio_HeP_H) < 8)

        # ═══ 4. Helium ═══
        self.log("")
        self.log("━" * 70)
        self.log("4. HELIUM ATOM (6 vertices: 3S + 2e + 1vac)")
        self.log("━" * 70)
        psi_He, E_He = optimize_system(build_helium, n_restarts=10)
        E_He_detail, _ = system_energy(psi_He)
        results["He"] = E_He_detail
        self.log(f"   SSS = {E_He_detail['SSS']:.6f}")
        self.log(f"   SST = {E_He_detail['SST']:.6f}  (2 electrons binding)")
        self.log(f"   STT = {E_He_detail['STT']:.6f}  (e-e repulsion + weak)")
        self.log(f"   Total = {E_He_detail['total']:.6f}")

        # He ionization (He → He⁺)
        IE_He_lattice = E_Hep_detail['total'] - E_He_detail['total']
        IE_He_eV = IE_He_lattice * eV_scale
        self.log(f"\n   IE(He) = {IE_He_lattice:.6f} lattice = {IE_He_eV:.2f} eV")
        self.log(f"   Observed: 24.587 eV")
        if abs(IE_He_eV) > 0:
            err_He = (IE_He_eV - 24.587) / 24.587 * 100
            self.log(f"   Error: {err_He:+.1f}%")
        self.check("He IE in right ballpark", 5 < abs(IE_He_eV) < 100)

        # ═══ 5. H₂ molecule ═══
        self.log("")
        self.log("━" * 70)
        self.log("5. H₂ MOLECULE (9 vertices, T₂ shared = covalent bond)")
        self.log("━" * 70)
        psi_H2, E_H2 = optimize_system(build_H2_molecule, n_restarts=10)
        E_H2_detail, _ = system_energy(psi_H2)
        results["H2"] = E_H2_detail
        self.log(f"   SSS = {E_H2_detail['SSS']:.6f}")
        self.log(f"   SST = {E_H2_detail['SST']:.6f}")
        self.log(f"   STT = {E_H2_detail['STT']:.6f}")
        self.log(f"   Total = {E_H2_detail['total']:.6f}")

        # ═══ 6. H + H separated ═══
        self.log("")
        self.log("━" * 70)
        self.log("6. H + H SEPARATED (10 vertices, no sharing)")
        self.log("━" * 70)
        psi_HH, E_HH = optimize_system(build_H_separated, n_restarts=10)
        E_HH_detail, _ = system_energy(psi_HH)
        results["H+H"] = E_HH_detail
        self.log(f"   SSS = {E_HH_detail['SSS']:.6f}")
        self.log(f"   SST = {E_HH_detail['SST']:.6f}")
        self.log(f"   STT = {E_HH_detail['STT']:.6f}")
        self.log(f"   Total = {E_HH_detail['total']:.6f}")

        # Bond energy
        BE_lattice = E_HH_detail['total'] - E_H2_detail['total']
        BE_eV = BE_lattice * eV_scale
        self.log(f"\n   Bond energy = E(H+H) - E(H₂) = {BE_lattice:.6f} = {BE_eV:.2f} eV")
        self.log(f"   Observed H₂ bond energy: 4.52 eV")
        self.check("H₂ is more bound than 2H", E_H2_detail['total'] < E_HH_detail['total'])

        # ═══ Summary ═══
        self.log("")
        self.log("=" * 70)
        self.log("SUMMARY: All quantities from simplex hinge geometry")
        self.log("=" * 70)
        self.log("")
        self.log(f"  {'System':<12} {'E_SSS':>10} {'E_SST':>10} {'E_STT':>10} {'E_total':>10} {'IE(eV)':>10}")
        self.log(f"  {'-'*12} {'-'*10} {'-'*10} {'-'*10} {'-'*10} {'-'*10}")

        for name in ["H+", "H", "He+", "He", "H2", "H+H"]:
            r = results[name]
            ie_str = ""
            if name == "H": ie_str = "13.61"
            elif name == "He":
                ie_str = f"{IE_He_eV:.2f}"
            self.log(f"  {name:<12} {r['SSS']:10.4f} {r['SST']:10.4f} "
                     f"{r['STT']:10.4f} {r['total']:10.4f} {ie_str:>10}")

        self.log("")
        self.log("  Method: ψ ∈ C⁵ at each vertex → G_ij → det(G_h) → Σ coupling×√det")
        self.log("  Schrödinger equation: not used")
        self.log("  Basis sets: none")
        self.log("  Free parameters: 1 (overall eV scale from H)")


if __name__ == "__main__":
    EXP_037().execute()
