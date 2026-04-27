#!/usr/bin/env python3
"""Identify short-proof theorems in lean/E213/ as kernel porting candidates.

Heuristics:
  - body is `rfl`, `by rfl`, `by decide`, `Iff.rfl`, etc.
  - only integer/Bool/Nat arithmetic appears
  - closes within a single line

Such theorems can usually be ported nearly one-to-one as deep-embedded Terms.

Usage: python3 tools/port_candidates.py [--limit 50]
"""
import re, argparse
from pathlib import Path

# theorem/lemma name + body
THEOREM = re.compile(
    r'^(theorem|lemma)\s+(\w+)[^:]*:\s*([^=]+?):=\s*(.+?)\s*$',
    re.MULTILINE
)

EASY = {'rfl', 'by rfl', 'by decide', 'Iff.rfl', 'by trivial', 'trivial'}


def scan_file(path: Path):
    out = []
    text = path.read_text(errors='ignore')
    for m in THEOREM.finditer(text):
        kind, name, type_, body = m.groups()
        body = body.strip().rstrip(',')
        if body in EASY or (len(body) < 20 and body.startswith('by ')):
            out.append((path, name, type_.strip()[:60], body))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--limit', type=int, default=50)
    ap.add_argument('--exclude', default='Kernel,Research')
    args = ap.parse_args()
    excludes = args.exclude.split(',')

    root = Path('lean/E213')
    candidates = []
    for f in root.rglob('*.lean'):
        rel = str(f.relative_to(root))
        if any(e in rel for e in excludes if e):
            continue
        candidates.extend(scan_file(f))

    print(f"== Port candidates (excluding: {excludes}) ==")
    print(f"Total: {len(candidates)}")
    print()
    for path, name, type_, body in candidates[:args.limit]:
        rel = path.relative_to(root)
        print(f"  {rel}::{name}")
        print(f"    type: {type_}")
        print(f"    body: {body}")
        print()


if __name__ == '__main__':
    main()
