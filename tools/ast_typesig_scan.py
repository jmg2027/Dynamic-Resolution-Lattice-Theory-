#!/usr/bin/env python3
"""Type-signature dependency + sort distribution scanner."""
from __future__ import annotations
import sys, subprocess, pathlib, collections, argparse

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "lean"
PROBE = LEAN_DIR / "E213" / "_AstTypeSigProbe.lean"
BODY_TMPL = ROOT / "tools" / "ast_typesig_body.lean"
LOG_PATH = ROOT / "tools" / "_ast_typesig_last.log"
EDGES_PATH = ROOT / "tools" / "_ast_typesig_edges.tsv"
SORTS_PATH = ROOT / "tools" / "_ast_typesig_sorts.tsv"


def cached_modules():
    base = LEAN_DIR / ".lake" / "build" / "lib" / "E213"
    mods = []
    for p in base.rglob("*.olean"):
        rel = p.relative_to(LEAN_DIR / ".lake" / "build" / "lib")
        name = ".".join(rel.with_suffix("").parts)
        if name.endswith(("_AstFoldScanProbe", "_AxiomScanProbe",
                          "_AstCallGraphProbe", "_DepPurityProbe",
                          "_AstShapeProbe", "_AstTypeSigProbe")):
            continue
        mods.append(name)
    return sorted(mods)


def write_probe():
    imports = "\n".join(f"import {m}" for m in cached_modules())
    PROBE.write_text("/- ephemeral -/\nimport Lean\n" + imports + "\n\n"
                     + BODY_TMPL.read_text())


def build():
    r = subprocess.run(["lake", "build", "E213._AstTypeSigProbe"],
                       cwd=LEAN_DIR, capture_output=True, text=True)
    log = r.stdout + r.stderr
    LOG_PATH.write_text(log)
    if "AST-TYPESIG-END" not in log:
        sys.stderr.write(log[-3000:])
        sys.exit("error: probe did not finish")
    return log


def extract(log):
    edges = []
    sorts = {}
    inside = False
    for line in log.splitlines():
        if "AST-TYPESIG-BEGIN" in line: inside = True; continue
        if "AST-TYPESIG-END" in line: inside = False; continue
        if not inside: continue
        if line.startswith("T\t"):
            parts = line.split("\t", 3)
            if len(parts) == 4:
                try: edges.append((parts[1], parts[2], int(parts[3])))
                except ValueError: continue
        elif line.startswith("K\t"):
            parts = line.split("\t", 2)
            if len(parts) == 3:
                sorts[parts[1]] = parts[2]
    return edges, sorts


def report(edges, sorts):
    print(f"# Type-signature edges: {len(edges)}")
    print(f"# Decls with sort info: {len(sorts)}\n")

    # Sort distribution
    sort_count = collections.Counter(sorts.values())
    print("## Sort/universe distribution")
    for s, n in sort_count.most_common():
        pct = 100*n/max(1, len(sorts))
        print(f"  {s:<6} {n:>6}  ({pct:.1f}%)")
    print()

    # Per-callee in type sig
    callees = collections.Counter()
    callees_breadth = collections.defaultdict(set)
    for caller, callee, cnt in edges:
        callees[callee] += cnt
        callees_breadth[callee].add(caller)

    print("## Top 25 E213-internal type-sig callees by breadth")
    int_rank = sorted(
        ((n, cs) for n, cs in callees_breadth.items() if n.startswith('E213.')),
        key=lambda kv: -len(kv[1]))[:25]
    for n, cs in int_rank:
        print(f"  {len(cs):>5} callers  ({callees[n]:>6} total)  {n}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("--report-only", action="store_true")
    args = ap.parse_args()
    if args.report_only:
        edges = []
        for line in EDGES_PATH.read_text().splitlines():
            parts = line.split("\t", 2)
            if len(parts) == 3: edges.append((parts[0], parts[1], int(parts[2])))
        sorts = {}
        for line in SORTS_PATH.read_text().splitlines():
            parts = line.split("\t", 1)
            if len(parts) == 2: sorts[parts[0]] = parts[1]
    else:
        if not args.no_build:
            write_probe()
            log = build()
            PROBE.unlink(missing_ok=True)
        else:
            log = LOG_PATH.read_text()
        edges, sorts = extract(log)
        EDGES_PATH.write_text("\n".join(
            "\t".join((a, b, str(c))) for a, b, c in edges) + "\n")
        SORTS_PATH.write_text("\n".join(
            f"{n}\t{s}" for n, s in sorts.items()) + "\n")
    report(edges, sorts)


if __name__ == "__main__":
    main()
