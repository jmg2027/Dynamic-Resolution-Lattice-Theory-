"""
DRLT Experiment Runner Framework
==================================
Provides base class for all experiments.
Auto-numbers, auto-saves results, prints summary.

Usage:
    class MyExperiment(Experiment):
        ID = "008"
        TITLE = "My cool experiment"

        def run(self):
            self.log("doing stuff...")
            self.check("thing works", True)

    if __name__ == "__main__":
        MyExperiment().execute()
"""

import os
import sys
import time
from datetime import datetime
from io import StringIO


RESULTS_DIR = os.path.join(os.path.dirname(__file__), "..", "results")


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

    def _save_results(self, tag: str):
        """Save output to the sub-project's results/ directory."""
        # Locate results/ relative to the calling experiment file
        caller = sys.modules[self.__class__.__module__]
        caller_dir = os.path.dirname(os.path.abspath(caller.__file__))
        # Go up from experiments/ to sub-project root, then into results/
        subproj_results = os.path.join(caller_dir, "..", "results")
        if os.path.isdir(os.path.join(caller_dir, "..")):
            results_dir = subproj_results
        else:
            results_dir = RESULTS_DIR
        os.makedirs(results_dir, exist_ok=True)
        path = os.path.join(results_dir, f"{tag}.txt")
        with open(path, "w") as f:
            f.write("\n".join(self._log_lines))
        self.log(f"\n  Results saved to: {path}")
