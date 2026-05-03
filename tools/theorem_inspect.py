#!/usr/bin/env python3
"""theorem_inspect.py — extract full bodies for chosen fingerprint clusters.

Usage:
  python3 tools/theorem_inspect.py --cluster existential
  python3 tools/theorem_inspect.py --cluster capstone

Pulls full theorem bodies (type + proof) for the selected cluster,
formatted as markdown for visual inspection.  Intended as input to
an empirical "what does this cluster EXPRESS?" pass — no automated
classification.
"""
import csv
import re
import sys
import pathlib

CSV_PATH = pathlib.Path('research-notes/G17_audit_raw.csv')
LEAN_ROOT = pathlib.Path('lean')

DECL_HEAD_RX = re.compile(
    r'(?:protected\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance)\s+'
)


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
        # Cap at 600 chars for inspection
        if len(body) > 600:
            body = body[:600] + '\n... [truncated]'
        return body
    return None


def filter_existential(rows):
    return [r for r in rows if int(r.get('stmt:∃', 0)) > 0]


def filter_capstone(rows):
    return [r for r in rows
            if int(r.get('proof:<;>', 0)) > 0
            and int(r.get('proof:decide', 0)) > 0
            and int(r.get('proof:refine', 0)) > 0]


def main():
    cluster = 'existential'
    if len(sys.argv) > 2 and sys.argv[1] == '--cluster':
        cluster = sys.argv[2]

    with CSV_PATH.open() as f:
        rows = list(csv.DictReader(f))

    if cluster == 'existential':
        decls = filter_existential(rows)
        out_path = pathlib.Path('research-notes/G17_inspect_existential.md')
        title = 'Existential theorems (∃) — 170 decls'
    elif cluster == 'capstone':
        decls = filter_capstone(rows)
        out_path = pathlib.Path('research-notes/G17_inspect_capstone.md')
        title = 'Capstone pattern (refine ⟨..⟩ <;> decide) — 105 decls'
    else:
        print(f'Unknown cluster: {cluster}')
        sys.exit(1)

    lines = [f'# {title}\n', f'(Auto-extracted by `tools/theorem_inspect.py`.)\n']
    seen = set()
    for r in decls:
        key = (r['file'], r['name'])
        if key in seen:
            continue
        seen.add(key)
        body = extract_body(r['file'], r['name'])
        lines.append(f'## `{r["name"]}` ({r["file"]})\n')
        if body:
            lines.append('```lean\n' + body + '\n```\n')
        else:
            lines.append('(body extraction failed)\n')

    out_path.write_text('\n'.join(lines), encoding='utf-8')
    print(f'Wrote {len(seen)} unique decls to {out_path}')


if __name__ == '__main__':
    main()
