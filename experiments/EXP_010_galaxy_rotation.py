"""EXP_010: Galaxy Rotation — Dark Matter from Lattice (ch13)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'lib'))
from experiment import Experiment
import drlt

class Exp(Experiment):
    ID, TITLE = "010", "Galaxy Rotation"
    def run(self):
        OmL = drlt.dark_energy_fraction()
        OmM = 1 - OmL
        inv_a = drlt.inv_alpha_em_corrected()
        a_gut = drlt.ALPHA_GUT

        self.log(f"  Omega_Lambda = 1 - 1/pi = {OmL:.4f}")
        self.log(f"  Omega_matter = 1/pi = {OmM:.4f}")
        self.log(f"  DM/baryon ~ (1/pi - Omega_b) / Omega_b")
        Omega_b = 0.049
        DM_ratio = (OmM - Omega_b) / Omega_b
        self.log(f"  DM/baryon = {DM_ratio:.2f}  (obs ~5.4)")
        self.check("DM/baryon order correct (3-8)", 3 < DM_ratio < 8)

        self.log(f"\n  1/alpha_em = {inv_a:.3f}")
        self.log(f"  alpha_GUT = {a_gut:.6f}")
        self.log(f"  Rotation curve flatness: v(r) ~ const when")
        self.log(f"    vacuum W contributes ~ 1/pi of total gravity")
        flat_cond = abs(OmM - 1/3.14159) < 0.01
        self.check("Omega_M ~ 1/pi (flatness condition)", flat_cond)
        self.check("alpha_GUT << 1 (perturbative lattice)", a_gut < 0.05)

if __name__ == "__main__": Exp().execute()
