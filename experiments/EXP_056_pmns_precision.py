"""EXP_056: PMNS Precision — All 4 Angles with Sigma (ch11)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'lib'))
from experiment import Experiment
import drlt

class Exp(Experiment):
    ID, TITLE = "056", "PMNS Precision"
    def run(self):
        pmns = drlt.pmns_angles()
        obs = {'sin2_12': (0.307, 0.013), 'sin2_23': (0.546, 0.021),
               'sin2_13': (0.0220, 0.0007), 'delta_cp': (197.0, 25.0)}

        self.log(f"  {'Parameter':>10} {'DRLT':>8} {'Obs':>8} {'1sigma':>6} {'Sigma':>6}")
        self.log(f"  {'-'*44}")
        all_ok = True
        for key in ['sin2_12', 'sin2_23', 'sin2_13', 'delta_cp']:
            pred = pmns[key]
            ob, unc = obs[key]
            sigma = (pred - ob) / unc
            if abs(sigma) > 2: all_ok = False
            self.log(f"  {key:>10} {pred:>8.4f} {ob:>8.4f} {unc:>6.4f} {sigma:>+5.2f}s")

        self.log(f"\n  alpha_GUT = {drlt.ALPHA_GUT:.6f}")
        self.log(f"  Derivation: axiom -> C5 -> (3,2) -> TBM -> trace corrections")

        self.check("sin2_12 < 0.2sigma", abs((pmns['sin2_12']-0.307)/0.013) < 0.2)
        self.check("sin2_23 < 0.2sigma", abs((pmns['sin2_23']-0.546)/0.021) < 0.2)
        self.check("sin2_13 < 0.5sigma", abs((pmns['sin2_13']-0.022)/0.0007) < 0.5)
        self.check("delta_cp < 0.2sigma", abs((pmns['delta_cp']-197.0)/25.0) < 0.2)
        self.check("All PMNS within 2sigma", all_ok)

if __name__ == "__main__": Exp().execute()
