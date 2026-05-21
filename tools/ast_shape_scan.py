#!/usr/bin/env python3
"""Expr-shape density extractor: per-decl Expr-constructor histogram."""
from __future__ import annotations
import sys, subprocess, pathlib, collections, argparse

ROOT       = pathlib.Path(__file__).resolve().parent.parent
LEAN_DIR   = ROOT / "lean"
PROBE      = LEAN_DIR / "E213" / "_AstShapeProbe.lean"
BODY_TMPL  = ROOT / "tools" / "ast_shape_body.lean"
LOG_PATH   = ROOT / "tools" / "_ast_shape_last.log"
ROWS_PATH  = ROOT / "tools" / "_ast_shape_rows.tsv"

PROBE_HEADER = """\
/- Ephemeral AST shape probe. -/
import Lean
"""

def cached_modules():
    base = LEAN_DIR / ".lake" / "build" / "lib" / "E213"
    mods = []
    for p in base.rglob("*.olean"):
        rel = p.relative_to(LEAN_DIR / ".lake" / "build" / "lib")
        name = ".".join(rel.with_suffix("").parts)
        if name.endswith(("_AstFoldScanProbe", "_AxiomScanProbe",
                          "_AstCallGraphProbe", "_DepPurityProbe",
                          "_AstShapeProbe")):
            continue
        mods.append(name)
    return sorted(mods)


def write_probe():
    imports = "\n".join(f"import {m}" for m in cached_modules())
    PROBE.write_text(PROBE_HEADER + imports + "\n\n" + BODY_TMPL.read_text())


def build():
    r = subprocess.run(["lake", "build", "E213._AstShapeProbe"],
                       cwd=LEAN_DIR, capture_output=True, text=True)
    log = r.stdout + r.stderr
    LOG_PATH.write_text(log)
    if "AST-SHAPE-END" not in log:
        sys.stderr.write(log[-4000:])
        sys.exit("error: probe did not finish")
    return log


def extract(log):
    rows = []
    inside = False
    for line in log.splitlines():
        if "AST-SHAPE-BEGIN" in line: inside = True; continue
        if "AST-SHAPE-END" in line: inside = False; continue
        if not inside or not line.startswith("S\t"): continue
        parts = line.split("\t")
        if len(parts) < 16: continue
        rows.append(parts[1:])
    return rows


def report(rows):
    print(f"# Total decls scanned: {len(rows)}\n")
    if not rows: return
    fields = ['total', 'maxDepth', 'app', 'lam', 'forallE', 'letE',
              'proj', 'mdata', 'bvar', 'fvar', 'mvar', 'const',
              'sort', 'lit']
    cnts = {f: [] for f in fields}
    for r in rows:
        name = r[0]
        for i, f in enumerate(fields):
            cnts[f].append((name, int(r[i+1])))

    print("## Aggregate stats per Expr constructor")
    print(f"{'field':<10} {'sum':>12} {'mean':>8} {'median':>8} {'max':>10}")
    for f in fields:
        vals = [v for _, v in cnts[f]]
        vals.sort()
        s, m = sum(vals), len(vals)
        med = vals[m//2] if m else 0
        mx = vals[-1] if m else 0
        print(f"  {f:<8} {s:>12} {s/m:>8.1f} {med:>8} {mx:>10}")
    print()

    # Top decls by total node count
    print("## Top 15 decls by total Expr-node count")
    for n, v in sorted(cnts['total'], key=lambda x: -x[1])[:15]:
        print(f"  {v:>9}   {n}")
    print()
    print("## Top 15 by maxDepth")
    for n, v in sorted(cnts['maxDepth'], key=lambda x: -x[1])[:15]:
        print(f"  {v:>4}   {n}")
    print()

    # letE / match-proj density — decls with high letE counts
    print("## Top 10 by `letE` count (heavy local-bindings)")
    for n, v in sorted(cnts['letE'], key=lambda x: -x[1])[:10]:
        print(f"  {v:>4}   {n}")
    print()
    print("## Top 10 by `proj` count (heavy structure projections)")
    for n, v in sorted(cnts['proj'], key=lambda x: -x[1])[:10]:
        print(f"  {v:>4}   {n}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("--report-only", action="store_true")
    args = ap.parse_args()
    if args.report_only:
        rows = []
        for line in ROWS_PATH.read_text().splitlines():
            parts = line.split("\t")
            if len(parts) >= 15: rows.append(parts)
    else:
        if not args.no_build:
            write_probe()
            log = build()
            PROBE.unlink(missing_ok=True)
        else:
            log = LOG_PATH.read_text()
        rows = extract(log)
        ROWS_PATH.write_text("\n".join("\t".join(r) for r in rows) + "\n")
    report(rows)


if __name__ == "__main__":
    main()
