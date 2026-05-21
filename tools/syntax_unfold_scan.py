#!/usr/bin/env python3
"""Tier-1.5+ unfold-argument scanner: operational-chunk discovery.

For every `unfold <name1> <name2> ...` invocation in a tactic body,
records the set of unfolded definitions per decl.  Then:

  (B1) per-definition frequency: which defs are most-unfolded.
  (B2) co-occurrence matrix: definitions unfolded together.
  (B3) "computational chunks": pairs / triples with high Jaccard
       similarity in their per-decl occurrence sets — candidates
       for an *implicit composite lemma* stating their joint
       computation.

Output: report to stdout + TSV `_syntax_unfold_rows.tsv`.

Usage:
    tools/syntax_unfold_scan.py
    tools/syntax_unfold_scan.py --report-only
"""
from __future__ import annotations
import re, sys, pathlib, collections, argparse, itertools

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from lean_syntax_parse import find_decl_bodies, walk_e213_files

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "lean" / "E213"
ROWS_PATH = ROOT / "tools" / "_syntax_unfold_rows.tsv"

# `unfold` takes a space-separated list of names, possibly multi-line.
# We capture from `\bunfold` up to the next newline or semicolon — then
# split by whitespace and filter to identifier-looking tokens.
UNFOLD_RE = re.compile(r'\bunfold\b([^\n;]*)')
NAME_RE = re.compile(r'^[A-Za-z_][\w\'.]*$')


def extract_unfold_args(body: str) -> list[list[str]]:
    """Return list of unfold invocations; each invocation is a list of
    unfolded names (in occurrence order)."""
    out = []
    for m in UNFOLD_RE.finditer(body):
        tail = m.group(1).strip()
        # stop at `at` clause (e.g., `unfold foo at h`)
        if ' at ' in tail:
            tail = tail.split(' at ', 1)[0]
        if ' using ' in tail:
            tail = tail.split(' using ', 1)[0]
        names = [t for t in re.split(r'\s+', tail) if NAME_RE.match(t)]
        if names:
            out.append(names)
    return out


def scan_all():
    """Yield (rel, decl, unfold_set_tuple).  Each decl that uses
    `unfold` at least once."""
    rows = []
    for rel, src in walk_e213_files(LEAN_DIR):
        for name, body in find_decl_bodies(src):
            invocs = extract_unfold_args(body)
            if not invocs:
                continue
            # flatten across all unfold invocations in the decl;
            # keep as a multiset for now.
            flat = [n for inv in invocs for n in inv]
            rows.append((rel, name, tuple(flat)))
    return rows


def report(rows):
    print(f"# Decls using `unfold`: {len(rows)}")

    # (B1) per-definition frequency
    freq = collections.Counter()
    callers = collections.defaultdict(set)
    for rel, decl, defs in rows:
        for d in defs:
            freq[d] += 1
            callers[d].add((rel, decl))
    print(f"# Distinct definitions unfolded: {len(freq)}")
    total_unfold_calls = sum(freq.values())
    print(f"# Total unfold-name occurrences: {total_unfold_calls}\n")

    print("## Top 30 most-unfolded definitions")
    print(f"{'cnt':>5}  {'callers':>7}  name")
    for name, n in freq.most_common(30):
        nc = len(callers[name])
        print(f"  {n:>3}    {nc:>5}    {name}")
    print()

    # (B2) co-occurrence: for each pair of definitions, how many decls
    # unfold BOTH at least once?
    decl_def_sets = {}
    for rel, decl, defs in rows:
        decl_def_sets[(rel, decl)] = set(defs)

    pair_count = collections.Counter()
    for (rel, decl), ds in decl_def_sets.items():
        for a, b in itertools.combinations(sorted(ds), 2):
            pair_count[(a, b)] += 1

    # (B3) Jaccard similarity for pairs that co-occur >= 3 times
    chunks = []
    for (a, b), n in pair_count.items():
        if n < 3:
            continue
        sa, sb = len(callers[a]), len(callers[b])
        union = sa + sb - n
        jacc = n / union if union > 0 else 0
        chunks.append(((a, b), n, sa, sb, jacc))
    chunks.sort(key=lambda x: -x[4])

    print("## Top co-unfolded definition pairs (Jaccard ≥ 0.5, co-occurs ≥ 3)")
    print(f"{'jac':>5}  {'both':>4}  {'A-tot':>5}  {'B-tot':>5}  pair")
    shown = 0
    for (a, b), n, sa, sb, jacc in chunks:
        if jacc < 0.5:
            continue
        shown += 1
        if shown > 20:
            break
        print(f"  {jacc:>4.2f}   {n:>3}   {sa:>4}   {sb:>4}   {a}  ⊕  {b}")
    print()

    # Triples: definitions A, B, C co-unfolded in ≥ 3 decls each
    print("## Top co-unfolded triples (co-occur ≥ 3 decls)")
    triple_count = collections.Counter()
    for (rel, decl), ds in decl_def_sets.items():
        if len(ds) < 3:
            continue
        for trip in itertools.combinations(sorted(ds), 3):
            triple_count[trip] += 1
    shown = 0
    for trip, n in triple_count.most_common():
        if n < 3:
            break
        shown += 1
        if shown > 15:
            break
        print(f"  x{n:<3}  {trip[0]}  ⊕  {trip[1]}  ⊕  {trip[2]}")
    print()

    # Unfold-set-size distribution
    set_sizes = collections.Counter(len(set(defs)) for _, _, defs in rows)
    print("## Per-decl unfold-set-size distribution")
    for s in sorted(set_sizes):
        print(f"  {s:>2} distinct defs   {set_sizes[s]}")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--report-only", action="store_true",
                    help="reuse cached rows file")
    args = ap.parse_args()
    if args.report_only:
        rows = []
        for line in ROWS_PATH.read_text().splitlines():
            parts = line.split('\t')
            if len(parts) >= 3:
                rows.append((parts[0], parts[1], tuple(parts[2:])))
    else:
        rows = scan_all()
        ROWS_PATH.write_text(
            "\n".join("\t".join((f, n) + tuple(d)) for f, n, d in rows) + "\n")
    report(rows)
    return 0


if __name__ == "__main__":
    sys.exit(main())
