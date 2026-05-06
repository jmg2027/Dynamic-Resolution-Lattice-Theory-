#!/usr/bin/env python3
"""theorem_audit.py — empirical fingerprint extraction.

Walks lean/E213 and extracts per-declaration raw data:
  · name, namespace, kind (theorem/lemma/def/noncomputable def)
  · body length (chars + lines)
  · proof method tokens (rfl/decide/refine/cases/match/Classical/omega/…)
  · statement structure tokens (=/∃/∀/∧/¬/<…)
  · used primitives (Cochain, delta0, spinAt, mkSpin, foldl, …)

NO classification.  Just fingerprint.  Output: CSV + JSON.
Subsequent inspection (sorting, clustering) is a separate step.
"""
import re
import csv
import json
import pathlib

LEAN_ROOT = pathlib.Path('lean/E213')
OUT_CSV = pathlib.Path('research-notes/G17_audit_raw.csv')
OUT_JSON = pathlib.Path('research-notes/G17_audit_summary.json')

# Per-declaration extraction.  Captures name + everything until next
# top-level decl or `end <ns>` line.  Imperfect on heavy macros / sections
# but fine for the ∅-axiom decide-heavy decls of this codebase.
DECL_RX = re.compile(
    r'^(?P<kind>(?:protected\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance))\s+'
    r'(?P<name>[A-Za-zα-ωΑ-Ωσδ_₀₁₂₃₄₅₆₇₈₉][\wα-ωΑ-Ωσδ\'₀₁₂₃₄₅₆₇₈₉]*)',
    re.MULTILINE,
)

NS_RX = re.compile(r'^namespace\s+(\S+)', re.MULTILINE)

# Tokens to count in body.
PROOF_TOKENS = [
    'rfl', 'decide', 'by decide', 'refine', 'cases', 'rcases', 'match',
    'omega', 'simp', 'rw ', 'unfold', 'exact ', '⟨',
    'Classical.choose', 'Classical.byContradiction', 'Classical.em',
    'Classical.choose_spec', 'noncomputable',
    'fun ', '<;>', 'intro', 'apply', 'constructor', 'left', 'right',
    'absurd', 'Or.inl', 'Or.inr', 'And.intro',
]

STMT_TOKENS = [
    '=', '≠', '<', '≤', '≥', '>',
    '∃', '∀', '∧', '∨', '¬', '↔', '→',
    'Prop', 'Bool', 'Nat', 'Fin', 'List', 'Option', 'Type',
]

INFRA_TOKENS = [
    'Cochain', 'delta0', 'delta1', 'spinAt', 'mkSpin', 'binom',
    'frustrationCount', 'cocycleObstruction', 'energy',
    'List.finRange', 'List.range', 'foldl', 'foldr',
    'List.all', 'List.any', 'List.map',
    'parity', 'half', 'bitOf', 'Nat.beq', 'Nat.ble',
    'σ', 'group', 'orbit', 'fixed',
    'Hodge', 'Galois', 'Frobenius', 'Beilinson',
    'cup', 'wedge', 'hodgeStar',
]


def get_namespace(text, decl_pos):
    """Return the innermost namespace at decl_pos."""
    last_ns = None
    for m in NS_RX.finditer(text):
        if m.start() > decl_pos:
            break
        last_ns = m.group(1)
    return last_ns


def split_decls(text):
    """Yield (kind, name, ns, body) tuples."""
    matches = list(DECL_RX.finditer(text))
    for i, m in enumerate(matches):
        kind = re.sub(r'\s+', ' ', m.group('kind')).strip()
        name = m.group('name')
        ns = get_namespace(text, m.start()) or ''
        end_pos = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        body = text[m.end():end_pos]
        # Trim at end-of-namespace or section
        eom = re.search(r'^(?:end\s|\Z)', body, re.MULTILINE)
        if eom:
            body = body[:eom.start()]
        yield kind, name, ns, body


def fingerprint(kind, name, ns, body):
    fp = {
        'name': name,
        'namespace': ns,
        'kind': kind,
        'body_chars': len(body),
        'body_lines': body.count('\n') + 1,
    }
    # Split body at first ':=' to separate type from proof.
    type_part, _, proof_part = body.partition(':=')
    if not proof_part:
        # Could be an instance with no `:=`, or unusual; record raw
        type_part = body
        proof_part = ''
    # Statement tokens (in type)
    for tok in STMT_TOKENS:
        fp[f'stmt:{tok}'] = type_part.count(tok)
    # Proof tokens (in proof_part)
    for tok in PROOF_TOKENS:
        fp[f'proof:{tok}'] = proof_part.count(tok)
    # Infrastructure tokens (in entire body)
    for tok in INFRA_TOKENS:
        fp[f'infra:{tok}'] = body.count(tok)
    return fp


def audit_file(path):
    try:
        text = path.read_text(encoding='utf-8')
    except Exception:
        return []
    out = []
    for kind, name, ns, body in split_decls(text):
        fp = fingerprint(kind, name, ns, body)
        fp['file'] = str(path.relative_to(pathlib.Path('lean')))
        out.append(fp)
    return out


def main():
    all_decls = []
    files = sorted(LEAN_ROOT.rglob('*.lean'))
    for f in files:
        if '_AxiomScanProbe' in f.name or '_Probe' in f.name:
            continue
        all_decls.extend(audit_file(f))

    # Write CSV
    if all_decls:
        keys = sorted({k for d in all_decls for k in d.keys()})
        # Order: file, namespace, name, kind, body_*, then stmt:, proof:, infra:
        priority = ['file', 'namespace', 'name', 'kind', 'body_chars', 'body_lines']
        keys = priority + [k for k in keys if k not in priority]
        with OUT_CSV.open('w', newline='', encoding='utf-8') as fp:
            w = csv.DictWriter(fp, fieldnames=keys)
            w.writeheader()
            w.writerows(all_decls)

    # Summary
    summary = {
        'total_decls': len(all_decls),
        'total_files': len(files),
        'kind_counts': {},
        'namespace_counts': {},
        'proof_token_totals': {},
        'stmt_token_totals': {},
        'infra_token_totals': {},
    }
    for d in all_decls:
        summary['kind_counts'][d['kind']] = summary['kind_counts'].get(d['kind'], 0) + 1
        ns = d.get('namespace', '')
        # Aggregate by top-level component (first 2 segments)
        ns_top = '.'.join(ns.split('.')[:3])
        summary['namespace_counts'][ns_top] = summary['namespace_counts'].get(ns_top, 0) + 1
        for k, v in d.items():
            if k.startswith('proof:') and v:
                summary['proof_token_totals'][k] = summary['proof_token_totals'].get(k, 0) + v
            if k.startswith('stmt:') and v:
                summary['stmt_token_totals'][k] = summary['stmt_token_totals'].get(k, 0) + v
            if k.startswith('infra:') and v:
                summary['infra_token_totals'][k] = summary['infra_token_totals'].get(k, 0) + v

    OUT_JSON.write_text(json.dumps(summary, indent=2, ensure_ascii=False, sort_keys=True))
    print(f'Wrote {len(all_decls)} declarations from {len(files)} files.')
    print(f'  CSV  → {OUT_CSV}')
    print(f'  JSON → {OUT_JSON}')


if __name__ == '__main__':
    main()
