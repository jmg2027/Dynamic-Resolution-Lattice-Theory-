"""EXP_009: Fine Structure Constant — 1/α_em via Ξ correction (ch08-09)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import drlt

class Exp(Experiment):
    ID, TITLE = "009", "Fine Structure Constant"
    def run(self):
        bare = drlt.inv_alpha_em_bare()
        self.log(f"1/α₁ (bare) = {bare:.2f} = 6π²")
        self.check("6π² = 59.22", abs(bare - 59.22) < 0.01)

        corrected = drlt.inv_alpha_em_corrected()
        self.log(f"1/α_em (Ξ corrected) = {corrected:.3f}")
        self.check("1/α_em = 137.036 (0.0004%)", abs(corrected - 137.036) < 0.1)

        gut = drlt.inv_alpha_gut()
        self.log(f"1/α_GUT = {gut:.2f} = 25π²/6")
        self.check("1/α_GUT = 41.12", abs(gut - 41.12) < 0.01)

if __name__ == "__main__": Exp().execute()
