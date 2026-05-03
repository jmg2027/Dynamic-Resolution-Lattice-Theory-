#!/usr/bin/env python3
"""theorem_inspect.py — extract bodies for chosen fingerprint clusters.

Usage:
  python3 tools/theorem_inspect.py --cluster {existential,capstone,equality_rfl,equality_decide,equality_rw,equality_other}
  python3 tools/theorem_inspect.py --cluster equality_decide --limit 80

Pure-equality clusters are stratified by proof-method so the
distinct *shapes* of equality reasoning can be inspected side by side.
"""
import csv
import re
import sys
import pathlib

CSV_PATH = pathlib.Path('research-notes/G17_audit_raw.csv')
LEAN_ROOT = pathlib.Path('lean')


def extract_body(file_rel, name):
    path = LEAN_ROOT / file_rel
    if not path.exists():
        return None
    src = path.read_text(encoding='utf-8')
    pattern = re.compile(
        rf'((?:protected\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance)\s+'
        rf'{re.escape(name)}\b.*?)'
        rf'(?=\n(?:(?:protected\s+)?(?:noncomputable\s+)?'
        rf'(?:theorem|lemma|def|abbrev|instance)\b|end\s|/-!|namespace\s|\Z))',
        re.DOTALL,
    )
    m = pattern.search(src)
    if m:
        body = m.group(1).strip()
        if len(body) > 600:
            body = body[:600] + '\n... [truncated]'
        return body
    return None


def i(r, k): return int(r.get(k, 0))


def is_pure_equality(r):
    return i(r, 'stmt:=') > 0 and not any(
        i(r, f'stmt:{t}') > 0 for t in ['∃', '∀', '∧', '∨', '¬', '↔'])


def is_theorem(r):
    return r['kind'].startswith('theorem')


CLUSTER_FILTERS = {
    'existential':   lambda r: i(r, 'stmt:∃') > 0,
    'capstone':      lambda r: i(r, 'proof:<;>') > 0 and i(r, 'proof:decide') > 0
                                 and i(r, 'proof:refine') > 0,
    # Pure-equality strata (theorems only, partition by primary proof method):
    'equality_rfl': lambda r:
        is_theorem(r) and is_pure_equality(r)
        and i(r, 'proof:rfl') > 0
        and i(r, 'proof:decide') == 0,
    'equality_decide': lambda r:
        is_theorem(r) and is_pure_equality(r)
        and i(r, 'proof:decide') > 0
        and i(r, 'proof:rfl') == 0
        and i(r, 'proof:rw ') == 0,
    'equality_rw': lambda r:
        is_theorem(r) and is_pure_equality(r)
        and i(r, 'proof:rw ') > 0,
    'equality_match': lambda r:
        is_theorem(r) and is_pure_equality(r)
        and i(r, 'proof:match') > 0,
    'equality_cases': lambda r:
        is_theorem(r) and is_pure_equality(r)
        and i(r, 'proof:cases') > 0,
    'omega_users': lambda r: i(r, 'proof:omega') > 0,
    'simp_users':  lambda r: i(r, 'proof:simp') > 0,
}


def main():
    cluster = sys.argv[2] if len(sys.argv) > 2 and sys.argv[1] == '--cluster' else 'existential'
    limit = int(sys.argv[4]) if len(sys.argv) > 4 and sys.argv[3] == '--limit' else 100

    if cluster not in CLUSTER_FILTERS:
        print(f'Unknown cluster: {cluster}', file=sys.stderr)
        print(f'Available: {", ".join(CLUSTER_FILTERS)}')
        sys.exit(1)

    with CSV_PATH.open() as f:
        rows = list(csv.DictReader(f))

    decls = [r for r in rows if CLUSTER_FILTERS[cluster](r)]
    out_path = pathlib.Path(f'research-notes/G17_inspect_{cluster}.md')

    title = f'Cluster `{cluster}` — {len(decls)} decls (sample limited to {limit})'
    lines = [f'# {title}\n', f'(Auto-extracted by `tools/theorem_inspect.py`.)\n']
    seen = set()
    sampled = 0
    # Spread across files for diversity
    seen_files: dict[str, int] = {}
    for r in decls:
        key = (r['file'], r['name'])
        if key in seen:
            continue
        # Per-file cap to ensure spread
        if seen_files.get(r['file'], 0) >= 5:
            continue
        seen_files[r['file']] = seen_files.get(r['file'], 0) + 1
        seen.add(key)
        body = extract_body(r['file'], r['name'])
        lines.append(f'## `{r["name"]}` ({r["file"]})\n')
        if body:
            lines.append('```lean\n' + body + '\n```\n')
        else:
            lines.append('(body extraction failed)\n')
        sampled += 1
        if sampled >= limit:
            break

    out_path.write_text('\n'.join(lines), encoding='utf-8')
    print(f'Cluster {cluster}: total={len(decls)}, sampled={sampled} → {out_path}')


if __name__ == '__main__':
    main()
