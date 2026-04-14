"""EXP_048: Neutrino PMNS Angles (ch11)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'lib'))
from experiment import Experiment
import drlt

class Exp(Experiment):
    ID, TITLE = "048", "Neutrino PMNS"
    def run(self):
        pmns = drlt.pmns_angles()
        seesaw = drlt.democratic_seesaw()

        obs = {'sin2_12': (0.307, 0.013), 'sin2_23': (0.546, 0.021),
               'sin2_13': (0.0220, 0.0007), 'delta_cp': (197.0, 25.0)}

        self.log(f"  PMNS angles from drlt.pmns_angles():")
        for key in ['sin2_12', 'sin2_23', 'sin2_13', 'delta_cp']:
            pred = pmns[key]
            ob, unc = obs[key]
            sigma = (pred - ob) / unc
            self.log(f"  {key:>10} = {pred:.4f}  (obs {ob}, {sigma:+.2f}sigma)")
            self.check(f"{key} within 2sigma", abs(sigma) < 2)

        self.log(f"\n  Democratic seesaw eigenvalue ratios: {seesaw}")
        self.check("Seesaw ratio < 50 (not 283)", seesaw[0]/seesaw[1] < 50)

if __name__ == "__main__": Exp().execute()
