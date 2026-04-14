"""EXP_049: Folded Dimension — C(n,2)=n iff n=3 (ch02-ch03)"""
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))
from experiment import Experiment
import drlt
from math import comb

class Exp(Experiment):
    ID, TITLE = "049", "Folded Dimension"
    def run(self):
        n_gen = drlt.generation_count()
        self.log(f"  N_gen = C(n_S, n_T) = C({drlt.N_S},{drlt.N_T}) = {n_gen}")

        # C(n,2) = n uniqueness proof
        self.log(f"\n  C(n,2) = n(n-1)/2 = n  =>  n = 3  QED")
        solutions = [n for n in range(1, 100) if comb(n, 2) == n]
        self.log(f"  Solutions in n=1..99: {solutions}")
        self.check("C(n,2)=n unique solution is n=3", solutions == [3])

        self.log(f"\n  n_gen = C(3,2) = 3 = n_S")
        self.log(f"  'Number of generations = number of spatial dimensions'")
        self.check("n_gen = 3", n_gen == 3)
        self.check("n_gen = n_S", n_gen == drlt.N_S)

if __name__ == "__main__": Exp().execute()
