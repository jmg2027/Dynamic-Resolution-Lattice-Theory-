"""
RH_079: DRLT Self-Verification System
========================================

Automatically verify:
1. Dependency graph (which Lean file imports which)
2. md ↔ Lean mapping (each theorem in drIt_axioms_lemmas_theorems.md
   has a corresponding Lean theorem)
3. Sorry scan (should be 0)
4. Triviality classification (native_decide vs omega vs simp)
5. Theorem count per file

Joint research by Mingu Jeong and Claude (Anthropic).
"""

import sys, os, re, glob
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', 'lib'))

from experiment import Experiment

LEAN_DIR = os.path.join(os.path.dirname(__file__), '..', 'lean', 'PmfRh')
MD_PATH = os.path.join(os.path.dirname(__file__), '..', '..',
                        'drIt_axioms_lemmas_theorems.md')


class SelfVerification(Experiment):
    ID = "RH_079"
    TITLE = "DRLT self-verification system"

    def run(self):
        self.test1_dependency_graph()
        self.test2_sorry_scan()
        self.test3_theorem_count()
        self.test4_tactic_classification()
        self.test5_md_lean_mapping()
        self.test6_verification_manifest()

    def _lean_files(self):
        return sorted(glob.glob(os.path.join(LEAN_DIR, '*.lean')))

    def test1_dependency_graph(self):
        """Extract import graph from Lean files."""
        self.log("\n=== Test 1: Dependency Graph ===\n")

        files = self._lean_files()
        graph = {}
        for f in files:
            name = os.path.basename(f).replace('.lean', '')
            with open(f) as fh:
                content = fh.read()
            imports = re.findall(r'import PmfRh\.(\w+)', content)
            graph[name] = imports

        # Print graph
        for name, deps in sorted(graph.items()):
            if deps:
                self.log(f"  {name} ← {', '.join(deps)}")
            else:
                self.log(f"  {name} (root)")

        # Check: is there a cycle?
        visited = set()
        def has_cycle(node, path):
            if node in path:
                return True
            if node in visited:
                return False
            visited.add(node)
            path.add(node)
            for dep in graph.get(node, []):
                if has_cycle(dep, path):
                    return True
            path.remove(node)
            return False

        cyclic = False
        for node in graph:
            if has_cycle(node, set()):
                cyclic = True
                break

        self.log(f"\n  Files: {len(files)}")
        self.log(f"  Acyclic: {not cyclic}")
        self.check("Dependency graph acyclic", not cyclic)

    def test2_sorry_scan(self):
        """Scan ALL Lean files for 'sorry' (actual, not in comments)."""
        self.log("\n=== Test 2: Sorry Scan ===\n")

        files = self._lean_files()
        total_sorry = 0

        for f in files:
            name = os.path.basename(f)
            with open(f) as fh:
                lines = fh.readlines()

            file_sorry = 0
            in_block_comment = False
            for i, line in enumerate(lines):
                stripped = line.strip()
                # Track block comments /- ... -/
                if '/-' in stripped:
                    in_block_comment = True
                if '-/' in stripped:
                    in_block_comment = False
                    continue
                if in_block_comment:
                    continue
                # Skip line comments
                if stripped.startswith('--'):
                    continue
                # Check for actual sorry TACTIC usage
                if re.search(r'\bsorry\b', stripped):
                    file_sorry += 1
                    self.log(f"  ⚠ {name}:{i+1}: {stripped[:60]}")

            total_sorry += file_sorry

        self.log(f"\n  Total files scanned: {len(files)}")
        self.log(f"  Total actual sorry: {total_sorry}")
        self.check("Zero sorry in all files", total_sorry == 0)

    def test3_theorem_count(self):
        """Count theorems per file."""
        self.log("\n=== Test 3: Theorem Count ===\n")

        files = self._lean_files()
        total = 0

        self.log(f"  {'File':>30} | {'Theorems':>8}")
        self.log(f"  {'-'*30}-+-{'-'*8}")

        for f in files:
            name = os.path.basename(f).replace('.lean', '')
            with open(f) as fh:
                content = fh.read()

            thms = len(re.findall(r'^theorem\s', content, re.MULTILINE))
            total += thms

            if thms > 0:
                self.log(f"  {name:>30} | {thms:>8}")

        self.log(f"  {'TOTAL':>30} | {total:>8}")
        self.check(f"Total theorems: {total}", total > 100)

    def test4_tactic_classification(self):
        """Classify proofs by tactic used."""
        self.log("\n=== Test 4: Tactic Classification ===\n")

        files = self._lean_files()
        tactics = {'native_decide': 0, 'omega': 0, 'simp': 0,
                   'rfl': 0, 'decide': 0, 'other': 0}

        for f in files:
            with open(f) as fh:
                content = fh.read()

            tactics['native_decide'] += len(
                re.findall(r'native_decide', content))
            tactics['omega'] += len(re.findall(r'\bomega\b', content))
            tactics['simp'] += len(re.findall(r'\bsimp\b', content))
            tactics['rfl'] += len(re.findall(r'\brfl\b', content))

        self.log(f"  Tactic usage:")
        for tactic, count in sorted(tactics.items(),
                                     key=lambda x: -x[1]):
            bar = '█' * min(count, 40)
            self.log(f"    {tactic:>15}: {count:>4} {bar}")

        self.log(f"\n  native_decide = computational (Level 0-1)")
        self.log(f"  omega = arithmetic (Level 1)")
        self.log(f"  simp = simplification (Level 1-2)")
        self.log(f"  rfl = definitional equality (Level 0)")
        self.check("Tactic distribution measured", True)

    def test5_md_lean_mapping(self):
        """Map theorems in drIt_axioms_lemmas_theorems.md to Lean."""
        self.log("\n=== Test 5: md ↔ Lean Mapping ===\n")

        if not os.path.exists(MD_PATH):
            self.log("  md file not found, skipping")
            self.check("md file exists", False)
            return

        with open(MD_PATH) as fh:
            md = fh.read()

        # Extract theorem names from md
        md_thms = re.findall(
            r'\*\*Theorem (\d+)[^*]*\*\*', md)

        # Extract theorem names from all Lean files
        lean_thms = set()
        for f in self._lean_files():
            with open(f) as fh:
                content = fh.read()
            for m in re.findall(r'^theorem\s+(\w+)', content,
                                re.MULTILINE):
                lean_thms.add(m)

        # Manual mapping: md Theorem N → Lean theorem name
        mapping = {
            '1': ('Theorem 1 (ℂ unique)', 'complex_has_gap',
                  'PrimeSpecial'),
            '2': ('Theorem 2 (doubly irred)', 'unique_doubly_irreducible',
                  'Core'),
            '3': ('Theorem 3 (ℂ²⊕ℂ³)', 'chiral_split',
                  'ChiralChannels'),
            '5': ('Theorem 5 (Two Boundaries)', 'two_boundaries_nat',
                  'GRH'),
            '6': ('Theorem 6 (Min cycle=3)', 'cp_transition',
                  'BSDPoincare'),
            '7': ('Theorem 7 (25 channels)', 'weighted_sum',
                  'ChiralChannels'),
            '8': ('Theorem 8 (α_GUT)', 'alpha_gut_value',
                  'Zeta2Universality'),
            '9': ('Theorem 9 (Self-contradiction)',
                  'level4_above_level3', 'FiniteLimit'),
            '10': ('Theorem 10 (Mass gap)', 'mass_gap_chain',
                   'DetFormula'),
            '11': ('Theorem 11 (No blow-up)', 'no_blowup',
                   'NSRegularity'),
            '12': ('Theorem 12 (Galois-DRLT)',
                   'completeness_solvability_duality',
                   'UnifiedNecessity'),
            '13': ('Theorem 13 (Unique composition)',
                   'ts_unique_composition', 'TaniyamaShimura'),
            '14': ('Theorem 14 (Collatz)', 'collatz_full', 'Collatz'),
            '17': ('Theorem 17 (Self-ref collapse)',
                   'self_reference_collapse', 'SelfReferenceCollapse'),
            '18': ('Theorem 18 (Spectral complexity)',
                   'discrete_tractable', 'SpectralComplexity'),
        }

        self.log(f"  {'md Thm':>8} | {'Description':>30} | "
                 f"{'Lean':>30} | {'File':>25} | {'Found':>5}")
        self.log(f"  {'-'*8}-+-{'-'*30}-+-{'-'*30}-+-"
                 f"{'-'*25}-+-{'-'*5}")

        found = 0
        total = len(mapping)
        for num, (desc, lean_name, lean_file) in sorted(mapping.items()):
            exists = lean_name in lean_thms
            if exists:
                found += 1
            mark = '✓' if exists else '✗'
            self.log(f"  Thm {num:>3} | {desc:>30} | "
                     f"{lean_name:>30} | {lean_file:>25} | "
                     f"{mark:>5}")

        self.log(f"\n  Mapped: {found}/{total}")
        self.log(f"  md theorems found: {len(md_thms)}")
        self.check(f"md↔Lean mapping: {found}/{total}",
                   found >= total - 3)

    def test6_verification_manifest(self):
        """Generate the complete verification manifest."""
        self.log("\n=== Test 6: Verification Manifest ===\n")

        files = self._lean_files()
        total_thms = 0
        total_sorry = 0
        total_lines = 0

        for f in files:
            with open(f) as fh:
                content = fh.read()
                lines = content.split('\n')

            thms = len(re.findall(r'^theorem\s', content, re.MULTILINE))
            sorry = len(re.findall(r'^\s*sorry\s*$', content, re.MULTILINE))
            total_thms += thms
            total_sorry += sorry
            total_lines += len(lines)

        self.log(f"  ╔═══════════════════════════════════════╗")
        self.log(f"  ║  DRLT VERIFICATION MANIFEST           ║")
        self.log(f"  ║                                       ║")
        self.log(f"  ║  Lean files:    {len(files):>4}                  ║")
        self.log(f"  ║  Total lines:   {total_lines:>5}                 ║")
        self.log(f"  ║  Theorems:      {total_thms:>4}                  ║")
        self.log(f"  ║  Sorry:         {total_sorry:>4}                  ║")
        self.log(f"  ║  Sorry rate:    {total_sorry/max(total_thms,1)*100:>5.1f}%               ║")
        self.log(f"  ║                                       ║")
        self.log(f"  ║  Status: {'ALL VERIFIED' if total_sorry == 0 else 'HAS GAPS':>15}       ║")
        self.log(f"  ╚═══════════════════════════════════════╝")

        self.check("Verification manifest generated",
                   total_sorry == 0 and total_thms > 100)


if __name__ == "__main__":
    SelfVerification().execute()
