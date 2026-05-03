#!/usr/bin/env python3
"""layer_audit.py — derive each Lean file's natural layer from imports.

Insight (Mingu, 2026-05-XX): a file's architectural layer is not a
philosophical question — it is mechanically determined by its import
closure.  F's natural layer >= max(layer of each E213.* it imports).

Corollary (Mingu, same day): EVERY file has a vertical layer.  The
"horizontal" trees (Math/, Physics/, Research/, Infinity/, Tactic/,
Tools/) are topical groupings, NOT separate axes — each file inside
them lives in some Kernel/Firmware/Hypervisor/Meta/App layer
determined by its imports.  This script computes that layer for
every file and reports per-folder distributions.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_ROOT = ROOT / "lean" / "E213"

VERTICAL = {
    "Kernel": 0,
    "Firmware": 1,
    "Hypervisor": 2,
    "Meta": 3,
    "App": 4,
}
HORIZONTAL = {"Math", "Physics"}


def first_segment(path: Path) -> str:
    rel = path.relative_to(LEAN_ROOT)
    return rel.parts[0] if len(rel.parts) > 1 else ""


def parse_imports(path: Path) -> list[str]:
    out = []
    rx = re.compile(r"^\s*import\s+E213\.([A-Za-z0-9_.]+)")
    try:
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
            m = rx.match(line)
            if m:
                out.append(m.group(1))
    except OSError:
        pass
    return out


def classify_provider_consumer(path: Path) -> str:
    """G12 T1 heuristic: a file is *provider* iff it introduces a
    `def`/`structure`/`class` whose namespace matches its directory.
    Otherwise *consumer* (uses level-N abstraction without adding new).

    Returns 'provider', 'consumer', or 'mixed'.
    """
    try:
        src = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return "consumer"
    ns_rx = re.compile(r"^\s*namespace\s+(\S+)", re.MULTILINE)
    decl_rx = re.compile(
        r"^\s*(?:protected\s+|private\s+)?"
        r"(?:def|structure|class|inductive|abbrev)\s+(\S+)",
        re.MULTILINE)
    namespaces = ns_rx.findall(src)
    decls = decl_rx.findall(src)
    if not decls:
        return "consumer"
    expected_dir_ns = ".".join(["E213"] + list(path.relative_to(LEAN_ROOT).parts[:-1]))
    matching = sum(1 for ns in namespaces
                   if ns == expected_dir_ns or ns.startswith(expected_dir_ns + "."))
    if matching >= 1 and len(decls) >= 1:
        return "provider"
    return "consumer"


def import_to_path(imp: str) -> Path:
    return LEAN_ROOT / (imp.replace(".", "/") + ".lean")


def file_layer(path: Path) -> tuple[str, int | None]:
    seg = first_segment(path)
    if seg in VERTICAL:
        return (seg, VERTICAL[seg])
    if seg in HORIZONTAL:
        return (seg, None)
    return (seg or "(root)", None)


def main() -> int:
    files = sorted(LEAN_ROOT.rglob("*.lean"))
    by_path = {p: file_layer(p) for p in files}
    imports = {p: [import_to_path(i) for i in parse_imports(p)] for p in files}

    natural = {}
    for p, imps in imports.items():
        max_rank = -1
        max_label = "Kernel"
        for ip in imps:
            if ip not in by_path:
                continue
            label, rank = by_path[ip]
            if rank is None:
                continue
            if rank > max_rank:
                max_rank = rank
                max_label = label
        natural[p] = (max_label, max_rank if max_rank >= 0 else 0)

    violations = []
    downgrades = []
    horizontal_high = []

    for p, (path_label, path_rank) in by_path.items():
        nat_label, nat_rank = natural[p]
        if path_rank is None:
            if nat_rank >= 3:
                horizontal_high.append((p, path_label, nat_label))
            continue
        if path_rank < nat_rank:
            violations.append((p, path_label, path_rank, nat_label, nat_rank))
        elif path_rank > nat_rank:
            downgrades.append((p, path_label, path_rank, nat_label, nat_rank))

    rc = report(files, violations, downgrades, horizontal_high)
    every_file_layer_report(files, imports, by_path)
    horizontal_depth_report(files, imports)
    return rc


def every_file_layer_report(files, imports, by_path):
    """Compute natural vertical layer for EVERY file (including Math,
    Physics, Research, …) and print per-top-folder distribution."""
    print("\n## Per-file natural vertical layer")
    print("(every file lives in Kernel/Firmware/Hypervisor/Meta/App;")
    print(" computed from import closure)\n")
    natural = {}
    for f in files:
        seg = f.relative_to(LEAN_ROOT).parts[0]
        if seg in VERTICAL:
            natural[f] = VERTICAL[seg]

    def get(f, stack):
        if f in natural:
            return natural[f]
        if f in stack:
            return 0
        stack.add(f)
        deps = [d for d in imports.get(f, []) if d in imports]
        natural[f] = max((get(d, stack) for d in deps), default=0)
        stack.discard(f)
        return natural[f]
    for f in files:
        get(f, set())

    label_of = {v: k for k, v in VERTICAL.items()}
    by_seg = {}
    for f in files:
        seg = f.relative_to(LEAN_ROOT).parts[0]
        by_seg.setdefault(seg, [0, 0, 0, 0, 0])
        by_seg[seg][natural[f]] += 1

    print(f"  {'top-folder':<14} " + "  ".join(f"{label_of[r]:>10}" for r in range(5)) + "   total")
    for seg in sorted(by_seg.keys()):
        row = by_seg[seg]
        print(f"  {seg:<14} " + "  ".join(f"{n:>10}" for n in row) + f"   {sum(row):>5}")

    # G12 T1: provider/consumer split per layer
    print("\n## Per-layer provider/consumer split (G12 T1 heuristic)")
    print("(provider = file introduces def/struct/class in its dir-namespace;")
    print(" consumer = uses level-N abstraction without adding new)\n")
    pc_by_layer = {0: [0, 0], 1: [0, 0], 2: [0, 0], 3: [0, 0], 4: [0, 0]}
    for f in files:
        layer = natural[f]
        kind = classify_provider_consumer(f)
        if kind == "provider":
            pc_by_layer[layer][0] += 1
        else:
            pc_by_layer[layer][1] += 1
    print(f"  {'layer':<14} {'provider':>10}  {'consumer':>10}   total")
    for r in range(5):
        p, c = pc_by_layer[r]
        print(f"  {label_of[r]:<14} {p:>10}  {c:>10}   {p+c:>5}")


def horizontal_depth_report(files, imports):
    """Within each horizontal cluster, report per-file import depth and
    flag sub-folders whose depth span suggests sub-clustering opportunity."""
    print("\n## Horizontal cluster depth (within-cluster imports only)")
    print("(span >= 15 → sub-clustering candidate)\n")
    for cluster in sorted(HORIZONTAL):
        sub_files = [f for f in files
                     if f.relative_to(LEAN_ROOT).parts[0] == cluster]
        if not sub_files:
            continue
        in_set = set(sub_files)
        deps = {f: [ip for ip in imports[f] if ip in in_set] for f in sub_files}
        depth = compute_depth(sub_files, deps)
        print(f"### {cluster}/  ({len(sub_files)} files, max depth {max(depth.values(), default=0)})")
        report_subfolders(sub_files, depth)
        print()


def compute_depth(files, deps):
    """Topological depth of each file: 1 + max(depth of imports), or 0 if leaf."""
    depth = {}
    def dfs(f, stack):
        if f in depth:
            return depth[f]
        if f in stack:
            return 0
        stack.add(f)
        d = 0 if not deps[f] else 1 + max(dfs(x, stack) for x in deps[f])
        stack.discard(f)
        depth[f] = d
        return d
    for f in files:
        dfs(f, set())
    return depth


def report_subfolders(sub_files, depth):
    from statistics import median
    by_sub = {}
    for f in sub_files:
        parts = f.relative_to(LEAN_ROOT).parts
        sub = parts[1] if len(parts) > 2 else "(top)"
        by_sub.setdefault(sub, []).append(depth[f])
    rows = sorted((min(ds), max(ds), int(median(ds)), len(ds), s)
                  for s, ds in by_sub.items())
    print(f"  {'sub':<26} {'n':>4}  min  med  max  flag")
    for mn, mx, md, n, sub in rows:
        flag = "  WIDE" if (mx - mn) >= 15 else ""
        print(f"  {sub:<26} {n:>4}  {mn:>3}  {md:>3}  {mx:>3}{flag}")


def report(files, violations, downgrades, horizontal_high) -> int:
    print(f"# Layer audit — {len(files)} .lean files under lean/E213/\n")
    print(f"Vertical: {VERTICAL}")
    print(f"Horizontal: {sorted(HORIZONTAL)}\n")

    print(f"## Violations: path layer < natural layer  ({len(violations)})")
    print("(file claims to be foundational but imports something higher)\n")
    for p, pl, pr, nl, nr in violations:
        rel = p.relative_to(LEAN_ROOT)
        print(f"  {rel}: at {pl}({pr}) but imports reach {nl}({nr})")

    print(f"\n## Downgrade hints: path layer > natural layer  ({len(downgrades)})")
    print("(file could be moved down — informational, not a violation)\n")
    by_layer = {}
    for p, pl, pr, nl, nr in downgrades:
        by_layer.setdefault((pl, nl), []).append(p)
    for (pl, nl), ps in sorted(by_layer.items()):
        print(f"  {pl} -> could go to {nl}: {len(ps)} files")
        for p in ps[:3]:
            print(f"      {p.relative_to(LEAN_ROOT)}")
        if len(ps) > 3:
            print(f"      ... +{len(ps) - 3} more")

    print(f"\n## Horizontal files reaching Meta/App  ({len(horizontal_high)})")
    by_seg = {}
    for p, pl, nl in horizontal_high:
        by_seg.setdefault((pl, nl), 0)
        by_seg[(pl, nl)] += 1
    for (pl, nl), n in sorted(by_seg.items()):
        print(f"  {pl}/* uses {nl}: {n} files")

    return 1 if violations else 0


if __name__ == "__main__":
    sys.exit(main())
