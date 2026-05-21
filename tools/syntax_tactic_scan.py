#!/usr/bin/env python3
"""Tier-1 syntax-level tactic-block scanner for E213.

Walks every `.lean` under `lean/E213/`, strips comments, finds each
`theorem|lemma|def|instance|example <name> ... := by <body>` block,
and tokenises the whitelisted tactic names appearing in the body.

Clusters theorems by:
  (a) full tactic sequence (in order)
  (b) tactic multiset
  (c) (first, last) tactic pair
  (d) per-tactic frequency histogram

Outputs a TSV of rows + a top-N report.

Usage:
    tools/syntax_tactic_scan.py
    tools/syntax_tactic_scan.py --report-only
"""
from __future__ import annotations
import re, sys, pathlib, collections, argparse

ROOT      = pathlib.Path(__file__).resolve().parent.parent
LEAN_DIR  = ROOT / "lean" / "E213"
ROWS_PATH = ROOT / "tools" / "_syntax_tactic_rows.tsv"

TACTIC_NAMES = frozenset([
    'intro', 'intros', 'exact', 'refine', 'apply', 'rfl', 'decide',
    'native_decide', 'induction', 'cases', 'rcases', 'obtain',
    'constructor', 'rw', 'rewrite', 'simp', 'simp_all', 'simp_rw',
    'simpa', 'unfold', 'have', 'show', 'let', 'omega', 'ring',
    'linarith', 'nlinarith', 'polyrith', 'exact_mod_cast', 'push_cast',
    'contradiction', 'exfalso', 'funext', 'ext', 'congr', 'generalize',
    'specialize', 'trivial', 'assumption', 'revert', 'clear',
    'fin_cases', 'use', 'left', 'right', 'split', 'sorry', 'change',
    'subst', 'norm_num', 'norm_cast', 'symm', 'trans', 'by_contra',
    'pick_goal', 'all_goals', 'any_goals', 'first', 'try', 'repeat',
    'fail', 'match', 'nofun', 'abel', 'tauto', 'aesop',
])


def strip_comments(src: str) -> str:
    """Strip /- ... -/ (one level of nesting) and -- line comments."""
    out = []
    i, depth = 0, 0
    n = len(src)
    while i < n:
        c2 = src[i:i+2]
        if depth == 0 and c2 == '/-':
            depth = 1; i += 2
        elif depth > 0 and c2 == '/-':
            depth += 1; i += 2
        elif depth > 0 and c2 == '-/':
            depth -= 1; i += 2
        elif depth == 0 and c2 == '--':
            j = src.find('\n', i)
            i = n if j == -1 else j
        elif depth == 0:
            out.append(src[i]); i += 1
        else:
            i += 1
    return ''.join(out)


DECL_KW = r'(?:theorem|lemma|def|example|instance)'
DECL_HEAD_RE = re.compile(
    r'^(?:@\[[^\]]*\]\s*|protected\s+|private\s+|noncomputable\s+|partial\s+|unsafe\s+|abbrev\s+)*'
    + DECL_KW + r'\s+(?P<name>[A-Za-z_][\w\'.`]*)?',
    re.MULTILINE
)

# Top-level boundaries that end a decl block
BOUNDARY_RE = re.compile(
    r'^(?:@\[[^\]]*\]\s*|protected\s+|private\s+|noncomputable\s+|partial\s+|unsafe\s+|abbrev\s+)*'
    r'(?:' + DECL_KW + r'|namespace|end|section|open|variable|axiom|inductive|structure|class|export|attribute|import|#\w+)\b',
    re.MULTILINE
)

BY_RE = re.compile(r':=\s*by\b')

TACTIC_TOKEN_RE = re.compile(
    r'(?:(?<=\s)|(?<=;)|(?<=\|)|(?<=·)|(?<=>)|(?<==>)|^)'
    r'([a-z][a-z_]*)'
    r"(?:'|\b)"
)


def find_decl_bodies(src: str):
    """Yield (name, body_after_by) for each `<kw> name ... := by <body>`
    at top level.  Body terminates at next top-level boundary."""
    src = strip_comments(src)
    decl_positions = [(m.start(), m.group('name') or '_anon_')
                      for m in DECL_HEAD_RE.finditer(src)]
    boundaries = [m.start() for m in BOUNDARY_RE.finditer(src)]
    boundaries.append(len(src))
    for idx, (start, name) in enumerate(decl_positions):
        # End = first boundary strictly after start (skipping start itself)
        end = next((b for b in boundaries if b > start), len(src))
        chunk = src[start:end]
        by_match = BY_RE.search(chunk)
        if not by_match:
            continue
        body = chunk[by_match.end():]
        yield name, body


def extract_tactic_seq(body: str) -> tuple[str, ...]:
    out = []
    for m in TACTIC_TOKEN_RE.finditer(body):
        t = m.group(1)
        if t in TACTIC_NAMES:
            out.append(t)
    return tuple(out)


def scan_all() -> list[tuple[str, str, tuple[str, ...]]]:
    rows = []
    for p in sorted(LEAN_DIR.rglob("*.lean")):
        if p.name.startswith("_"):
            continue
        try:
            src = p.read_text()
        except UnicodeDecodeError:
            continue
        rel = p.relative_to(LEAN_DIR).as_posix()
        for name, body in find_decl_bodies(src):
            seq = extract_tactic_seq(body)
            if not seq:
                continue
            rows.append((rel, name, seq))
    return rows


def report(rows):
    print(f"# Files scanned: {len({r[0] for r in rows})}")
    print(f"# Decls with tactic bodies: {len(rows)}")
    print()

    # (A) frequency histogram
    freq = collections.Counter()
    for _, _, seq in rows:
        freq.update(seq)
    total_tok = sum(freq.values())
    print(f"## Tactic frequency (total tokens = {total_tok})")
    for t, n in freq.most_common(30):
        pct = 100 * n / total_tok
        print(f"  {t:<16} {n:>6}   {pct:>5.1f}%")
    print()

    # (B) full-sequence clusters
    seqs = collections.Counter(seq for _, _, seq in rows)
    print(f"## Top tactic-sequence clusters (exact match)")
    # Filter trivial/short sequences for signal
    seqs_filtered = [(s, c) for s, c in seqs.items() if 1 <= len(s) <= 12]
    for s, c in sorted(seqs_filtered, key=lambda kv: -kv[1])[:20]:
        if c < 2:
            break
        sample_names = [n for f, n, sq in rows if sq == s][:3]
        print(f"  x{c:<4} [{', '.join(s)}]")
        for nm in sample_names:
            print(f"        · {nm}")
    print()

    # (C) (first, last) pairs
    pairs = collections.Counter()
    for _, _, seq in rows:
        if seq:
            pairs[(seq[0], seq[-1])] += 1
    print(f"## Top (first, last) tactic pairs")
    for (a, b), c in pairs.most_common(15):
        print(f"  {a:<14} ⇒ {b:<14}  x{c}")
    print()

    # (D) seq-length distribution
    lengths = collections.Counter(len(s) for _, _, s in rows)
    print(f"## Tactic-sequence length distribution")
    for L in sorted(lengths):
        bar = '#' * (lengths[L] * 50 // max(lengths.values()))
        print(f"  len={L:<3} {lengths[L]:>5}  {bar}")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--report-only", action="store_true",
                    help="reuse cached rows file")
    args = ap.parse_args()
    if args.report_only:
        rows = []
        for line in ROWS_PATH.read_text().splitlines():
            parts = line.split("\t")
            if len(parts) >= 3:
                rows.append((parts[0], parts[1], tuple(parts[2:])))
    else:
        rows = scan_all()
        ROWS_PATH.write_text(
            "\n".join("\t".join((f, n) + tuple(s)) for f, n, s in rows) + "\n")
    report(rows)
    return 0


if __name__ == "__main__":
    sys.exit(main())
