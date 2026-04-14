"""EXP_054: Rigorous PMNS Derivation — C(n,2)=n => n=3 (ch11)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'lib'))
from experiment import Experiment
import drlt
from math import comb

class Exp(Experiment):
    ID, TITLE = "054", "Rigorous PMNS"
    def run(self):
        # Step 1: C(n,2) = n uniqueness
        solutions = [n for n in range(1, 100) if comb(n, 2) == n]
        self.log(f"  C(n,2)=n => n=3 (unique). Solutions: {solutions}")
        self.check("C(n,2)=n unique solution is n=3", solutions == [3])

        # Step 2: All 4 PMNS parameters from drlt
        pmns = drlt.pmns_angles()
        obs = {'sin2_12': (0.307, 0.013), 'sin2_23': (0.546, 0.021),
               'sin2_13': (0.0220, 0.0007), 'delta_cp': (197.0, 25.0)}

        self.log(f"\n  PMNS angles (0 free parameters):")
        all_ok = True
        for key in ['sin2_12', 'sin2_23', 'sin2_13', 'delta_cp']:
            pred = pmns[key]
            ob, unc = obs[key]
            sigma = (pred - ob) / unc
            err = (pred - ob) / ob * 100
            if abs(sigma) > 2: all_ok = False
            self.log(f"  {key:>10} = {pred:.4f}  (obs {ob}, {sigma:+.2f}sigma, {err:+.3f}%)")

        self.check("All PMNS parameters within 2sigma", all_ok)
        self.check("sin2_13 < 1%", abs(pmns['sin2_13'] - 0.022)/0.022 < 0.01)
        self.check("N_gen = n_S = 3", drlt.generation_count() == drlt.N_S)

if __name__ == "__main__": Exp().execute()
