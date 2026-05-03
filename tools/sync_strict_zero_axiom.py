#!/usr/bin/env python3
"""sync_strict_zero_axiom.py — sync STRICT_ZERO_AXIOM.md with reality.

G12 T2: runs `tools/scan_all_axioms.py` on the full E213 tree,
parses results, and produces a delta report against the catalog
table in STRICT_ZERO_AXIOM.md.

The catalog itself is hand-curated (with chosen presentation +
narrative).  This tool produces:
  1. A summary of total PURE/DIRTY counts per cluster
  2. A list of theorems IN catalog but NOT verified PURE
  3. A list of theorems verified PURE but NOT in catalog
     (candidates for adding)

Usage:
  python3 tools/sync_strict_zero_axiom.py             # report only
  python3 tools/sync_strict_zero_axiom.py --csv FILE  # write CSV too

Run from repo root.
"""
import subprocess, re, sys, argparse
from pathlib import Path
from collections import defaultdict


REPO = Path(__file__).resolve().parent.parent
CATALOG = REPO / "STRICT_ZERO_AXIOM.md"
SCANNER = REPO / "tools" / "scan_all_axioms.py"


def read_catalog_entries():
    """Parse STRICT_ZERO_AXIOM.md, extract theorem names.
    Heuristic: any backtick-delimited identifier in the catalog
    that looks like a Lean theorem name.
    """
    if not CATALOG.exists():
        return set()
    src = CATALOG.read_text(errors="replace")
    rx = re.compile(r"`([a-zA-Z_][\w.]*)`")
    return set(rx.findall(src))


def run_scanner(csv_out=None):
    cmd = ["python3", str(SCANNER)]
    if csv_out:
        cmd += ["--csv", csv_out]
    result = subprocess.run(cmd, cwd=REPO, capture_output=True,
                            text=True, timeout=3600)
    return result.stdout + result.stderr


def parse_scanner_csv(csv_path):
    """Returns dict {theorem_name: ('PURE'|'DIRTY', axioms)}"""
    out = {}
    line_rx = re.compile(r'^"([^"]+)",([^,]+),([^,]+),"([^"]*)"')
    with open(csv_path) as f:
        next(f)  # header
        for line in f:
            m = line_rx.match(line)
            if m:
                name, _module, status, axioms = m.groups()
                out[name] = (status, axioms)
    return out


def report(catalog_entries, scan_results):
    pure = {n for n, (s, _) in scan_results.items() if s == "PURE"}
    dirty = {n for n, (s, _) in scan_results.items() if s == "DIRTY"}

    print(f"# STRICT_ZERO_AXIOM sync report\n")
    print(f"Total scanned: {len(scan_results)}")
    print(f"  PURE:  {len(pure)}")
    print(f"  DIRTY: {len(dirty)}")
    print(f"Catalog entries (heuristic): {len(catalog_entries)}\n")

    in_catalog_not_pure = []
    for name in catalog_entries:
        if name in scan_results:
            status, axioms = scan_results[name]
            if status != "PURE":
                in_catalog_not_pure.append((name, axioms))

    pure_not_in_catalog = sorted(pure - catalog_entries)

    print(f"## In catalog but not verified PURE: "
          f"{len(in_catalog_not_pure)}")
    for name, axioms in in_catalog_not_pure[:30]:
        print(f"  - {name}  [{axioms}]")
    if len(in_catalog_not_pure) > 30:
        print(f"  ... +{len(in_catalog_not_pure)-30} more")

    print(f"\n## PURE but not in catalog (add candidates): "
          f"{len(pure_not_in_catalog)}")
    by_module = defaultdict(list)
    for name in pure_not_in_catalog:
        mod = ".".join(name.split(".")[:-1])
        by_module[mod].append(name.split(".")[-1])
    for mod, names in sorted(by_module.items())[:30]:
        print(f"  {mod} ({len(names)}): {', '.join(names[:3])}"
              f"{'...' if len(names)>3 else ''}")
    if len(by_module) > 30:
        print(f"  ... +{len(by_module)-30} more modules")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--csv", default="/tmp/scan_for_sync.csv")
    args = ap.parse_args()

    print("# Running scan_all_axioms.py (this may take 30+ min)\n",
          file=sys.stderr)
    out = run_scanner(args.csv)
    print(out[-2000:], file=sys.stderr)

    catalog = read_catalog_entries()
    scan = parse_scanner_csv(args.csv)
    report(catalog, scan)
