#!/usr/bin/env python3
"""Tier-1.5++ rw-cascade analyser: k-gram patterns in ordered rw cites.

Reuses `tools/_syntax_arg_cites.tsv` produced by `syntax_arg_scan.py`.
For each decl, treats its `rw`-kind citations (in body-position order)
as a sequence; mines k-grams to surface "rewrite cascades" — short
chains of lemmas applied in fixed order across many decls.  Top
cascades that already-correspond to a named composite lemma point at
adoption gaps (lemma exists, callers don't use it).

Usage:
    tools/syntax_rw_cascade_scan.py
    tools/syntax_rw_cascade_scan.py --k 3
    tools/syntax_rw_cascade_scan.py --top 30
"""
from __future__ import annotations
import re, sys, pathlib, collections, argparse

ROOT = pathlib.Path(__file__).resolve().parent.parent
CITE_PATH = ROOT / "tools" / "_syntax_arg_cites.tsv"

HYP_RE = re.compile(r'^(h\d*|ih\w*|h[a-z]\w?|this|hyp\w*)$')


def is_hyp(name: str) -> bool:
    return bool(HYP_RE.match(name)) or name in {'rfl', 'trivial'}


def load_decl_rw_seqs():
    seqs = collections.defaultdict(list)
    for line in CITE_PATH.read_text().splitlines():
        parts = line.split('\t', 3)
        if len(parts) != 4:
            continue
        rel, decl, kind, lem = parts
        if kind != 'rw':
            continue
        if is_hyp(lem):
            continue
        seqs[(rel, decl)].append(lem)
    return seqs


def k_grams(seq, k):
    return [tuple(seq[i:i+k]) for i in range(len(seq) - k + 1)]


def report(seqs, k: int, top: int):
    print(f"# Decls with at least one rw cite: {len(seqs)}")
    print(f"# Total rw cite occurrences: {sum(len(s) for s in seqs.values())}")
    print(f"# k = {k}")
    print()
    gram_count = collections.Counter()
    gram_decls = collections.defaultdict(set)
    for key, s in seqs.items():
        for g in k_grams(s, k):
            gram_count[g] += 1
            gram_decls[g].add(key)
    ranked = sorted(gram_count.items(),
                    key=lambda kv: -len(gram_decls[kv[0]]))
    print(f"## Top {top} rw {k}-grams (by distinct-decl count)")
    print(f"{'decls':>5}  {'occ':>4}  cascade")
    for g, n in ranked[:top]:
        nd = len(gram_decls[g])
        cascade = '  →  '.join(g)
        print(f"  {nd:>3}    {n:>4}   {cascade}")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--k", type=int, default=3,
                    help="k-gram length (default 3)")
    ap.add_argument("--top", type=int, default=20)
    args = ap.parse_args()
    if not CITE_PATH.exists():
        sys.exit(f"error: {CITE_PATH} not found; run syntax_arg_scan.py first")
    seqs = load_decl_rw_seqs()
    report(seqs, args.k, args.top)
    return 0


if __name__ == "__main__":
    sys.exit(main())
