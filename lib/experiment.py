"""
DRLT Experiment Runner Framework
==================================
Provides base class for all experiments.
Auto-numbers, auto-saves results, prints summary.

Results are saved to the sub-project's results/ directory automatically.
If the experiment is in {sub-project}/experiments/, results go to
{sub-project}/results/. Fallback: root results/ for legacy experiments.

Usage:
    class MyExperiment(Experiment):
        ID = "ATM_014"
        TITLE = "My cool experiment"

        def run(self):
            self.log("doing stuff...")
            self.check("thing works", True)

    if __name__ == "__main__":
        MyExperiment().execute()
"""

import inspect
import os
import sys
import time
from datetime import datetime
from io import StringIO


ROOT_RESULTS_DIR = os.path.join(os.path.dirname(__file__), "..", "results")


class Experiment:
    """Base class for all DRLT experiments."""

    ID = "000"
    TITLE = "Unnamed Experiment"

    def __init__(self):
        self.checks = []
        self._log_lines = []
        self._start_time = None

    def run(self):
        """Override this. Do the experiment here."""
        raise NotImplementedError

    def execute(self):
        """Run the experiment with logging and result saving."""
        self._start_time = time.time()
        tag = f"EXP_{self.ID}_{self.TITLE.replace(' ', '_')}"

        self.log(f"{'='*60}")
        self.log(f"  {tag}")
        self.log(f"  {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        self.log(f"{'='*60}")

        try:
            self.run()
        except Exception as e:
            self.log(f"\n  ERROR: {e}")
            import traceback
            self.log(traceback.format_exc())

        elapsed = time.time() - self._start_time

        # Summary
        self.log(f"\n{'='*60}")
        self.log(f"  SUMMARY: {tag}")
        self.log(f"{'='*60}")
        passed = sum(1 for _, ok in self.checks if ok)
        total = len(self.checks)
        for name, ok in self.checks:
            self.log(f"  [{'✓' if ok else '✗'}] {name}")
        if total > 0:
            self.log(f"\n  {passed}/{total} checks passed")
        self.log(f"  Time: {elapsed:.1f}s")

        # Save results
        self._save_results(tag)

    def log(self, msg: str = ""):
        """Print and record."""
        print(msg)
        self._log_lines.append(msg)

    def check(self, name: str, condition: bool):
        """Record a pass/fail check."""
        self.checks.append((name, condition))
        status = "✓ PASS" if condition else "✗ FAIL"
        self.log(f"  [{status}] {name}")

    def _get_results_dir(self):
        """Auto-detect results dir from experiment file location.

        Priority:
          1. Explicit RESULTS_DIR class attribute on the subclass
          2. {sub-project}/results/ if experiment is in {sub-project}/experiments/
          3. Root results/ as fallback
        """
        # 1. Explicit override
        cls_rd = self.__class__.__dict__.get('RESULTS_DIR')
        if cls_rd is not None:
            return cls_rd
        # 2. Auto-detect: experiment in {sub-project}/experiments/ → ../results/
        try:
            exp_file = inspect.getfile(self.__class__)
            exp_dir = os.path.dirname(os.path.abspath(exp_file))
            if os.path.basename(exp_dir) == 'experiments':
                return os.path.join(os.path.dirname(exp_dir), 'results')
        except (TypeError, OSError):
            pass
        # 3. Fallback
        return ROOT_RESULTS_DIR

    def _save_results(self, tag: str):
        """Save results to the auto-detected sub-project results/ dir."""
        results_dir = self._get_results_dir()
        os.makedirs(results_dir, exist_ok=True)
        path = os.path.join(results_dir, f"{tag}.txt")
        with open(path, "w") as f:
            f.write("\n".join(self._log_lines))
        self.log(f"\n  Results saved to: {path}")
