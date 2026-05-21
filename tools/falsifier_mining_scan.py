#!/usr/bin/env python3
"""Decide-failure mining: auto-discovered falsifiers.

For every `theorem|lemma|def|instance` whose signature contains a
negation marker (`¬`, `≠`, `Not`, `False`) AND whose body uses
`decide` / `native_decide`, emit a row.  These are
machine-verified impossibility / distinguishability claims —
DRLT's "what cannot be" surface.

Categorisation:
  · `ne`         — `x ≠ y` statements
  · `not_exists` — `¬ ∃ ...` impossibility-of-existence
  · `not_forall` — `¬ ∀ ...` failure-of-universality
  · `not`        — general `¬ P`
  · `arrow_false`/`false`/`Not_token`/`other` — edge cases

Output: report to stdout + TSV at `_falsifier_rows.tsv`.

Usage:
    tools/falsifier_mining_scan.py
    tools/falsifier_mining_scan.py --report-only
"""
from __future__ import annotations
import re, sys, pathlib, collections, argparse

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from lean_syntax_parse import walk_e213_files, strip_comments

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "lean" / "E213"
ROWS_PATH = ROOT / "tools" / "_falsifier_rows.tsv"

DECL_HEAD = re.compile(
    r'^(?:@\[[^\]]*\]\s*|protected\s+|private\s+|noncomputable\s+|partial\s+)*'
    r'(?:theorem|lemma|def|instance|example)\s+([A-Za-z_][\w\'.`]*)',
    re.MULTILINE)
BY_RE = re.compile(r':=\s*by\b')

NEG_MARKERS = re.compile(r'(¬|≠|\bNot\s|\bFalse\b)')
DECIDE_MARKER = re.compile(r'\bdecide\b|\bnative_decide\b')


def classify(sig: str) -> str:
    if '≠' in sig:
        return 'ne'
    if '¬ ∃' in sig or '¬∃' in sig:
        return 'not_exists'
    if '¬ ∀' in sig or '¬∀' in sig:
        return 'not_forall'
    if '¬' in sig:
        return 'not'
    if re.search(r'→\s*False', sig):
        return 'arrow_false'
    if 'False' in sig:
        return 'false'
    if re.search(r'\bNot\s', sig):
        return 'Not_token'
    return 'other'


def scan_all():
    rows = []
    for rel, src in walk_e213_files(LEAN_DIR):
        src = strip_comments(src)
        heads = list(DECL_HEAD.finditer(src))
        for i, h in enumerate(heads):
            start, name = h.start(), h.group(1)
            end = heads[i+1].start() if i+1 < len(heads) else len(src)
            chunk = src[start:end]
            by_m = BY_RE.search(chunk)
            if not by_m:
                continue
            sig = chunk[:by_m.start()]
            body = chunk[by_m.end():]
            if not NEG_MARKERS.search(sig):
                continue
            if not DECIDE_MARKER.search(body[:600]):
                continue
            cat = classify(sig)
            colon_pos = sig.find(':', sig.find(name) + len(name))
            short = (sig[colon_pos:].strip().replace('\n', ' ')[:200]
                     if colon_pos >= 0 else sig[:200])
            rows.append((rel, name, cat, short))
    return rows


def write_tsv(rows):
    lines = ['file\tdecl\tcategory\tsignature']
    for r in rows:
        lines.append('\t'.join(r))
    ROWS_PATH.write_text('\n'.join(lines) + '\n')


def read_tsv():
    rows = []
    for line in ROWS_PATH.read_text().splitlines()[1:]:
        parts = line.split('\t', 3)
        if len(parts) == 4:
            rows.append(tuple(parts))
    return rows


def report(rows):
    print(f"# Total negation+decide decls (auto-discovered falsifiers): {len(rows)}\n")

    cat_count = collections.Counter(r[2] for r in rows)
    print("## Category distribution")
    for c, n in cat_count.most_common():
        print(f"  {n:>4}   {c}")
    print()

    files = collections.Counter(r[0] for r in rows)
    print("## Top files by falsifier count")
    for f, n in files.most_common(20):
        if n < 2:
            break
        relshort = f.replace('lean/E213/', '')
        print(f"  {n:>3}   {relshort}")
    print()

    by_cat = collections.defaultdict(list)
    for r in rows:
        by_cat[r[2]].append(r)
    for cat in sorted(by_cat.keys(), key=lambda c: -len(by_cat[c])):
        print(f"## Category `{cat}` — {len(by_cat[cat])} decls (showing 6)")
        for rel, name, _, sig in by_cat[cat][:6]:
            print(f"  {rel.split('/')[-1]} :: {name}")
            print(f"    {sig[:140]}")
        print()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--report-only", action="store_true")
    args = ap.parse_args()
    if args.report_only:
        rows = read_tsv()
    else:
        rows = scan_all()
        write_tsv(rows)
    report(rows)
    return 0


if __name__ == "__main__":
    sys.exit(main())
