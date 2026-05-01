#!/usr/bin/env python3
"""layer_audit.py — derive each Lean file's natural layer from imports.

Insight (Mingu, 2026-05-XX): a file's architectural layer is not a
philosophical question — it is mechanically determined by its import
closure.  F's natural layer >= max(layer of each E213.* it imports).
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
HORIZONTAL = {"Math", "Physics", "Research", "Infinity", "Tactic", "Tools"}


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

    return report(files, violations, downgrades, horizontal_high)


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
