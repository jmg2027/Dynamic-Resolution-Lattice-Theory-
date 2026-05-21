#!/usr/bin/env python3
"""Tier-1.5 tactic-argument scanner for E213.

Extracts argument patterns from tactic bodies:
  (B) `rw [a, b, c]` / `simp only [...]` / `rewrite [...]` /
      `simp_rw [...]`  — lemma citations (dependency-graph hint).
      Also captures `apply <name>` and `exact <name>` heads.
  (C) `induction <x> (with | ... =>)?` — induction target + case
      tags.
      `cases <h> (with | ... =>)?` — same.
      `obtain ⟨...⟩ := ...` — destructuring shape (token count +
      pattern).

Emits a citation TSV (`rel\tdecl\tkind\tname`) and a shape TSV
(`rel\tdecl\tconstruct\tdetail`), then prints:
  · top cited lemmas (frequency + by distinct caller)
  · top citations missing from E213 (probably Lean / std)
  · induction-variable popularity + case-count distribution
  · top obtain destructuring shapes

Usage:
    tools/syntax_arg_scan.py
    tools/syntax_arg_scan.py --report-only
"""
from __future__ import annotations
import re, sys, pathlib, collections, argparse

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from lean_syntax_parse import find_decl_bodies, walk_e213_files  # noqa: E402

ROOT      = pathlib.Path(__file__).resolve().parent.parent
LEAN_DIR  = ROOT / "lean" / "E213"
CITE_PATH = ROOT / "tools" / "_syntax_arg_cites.tsv"
SHAPE_PATH = ROOT / "tools" / "_syntax_arg_shapes.tsv"


# ---------- (B) citation extraction ----------

# Header keywords whose arg list is a lemma-bracket: `rw [..]`,
# `rewrite [..]`, `simp only [..]`, `simp_rw [..]`, `simp_all only
# [..]`.  We require the `[` immediately after the (possibly
# multi-word) header.
BRACKET_HDR_RE = re.compile(
    r'\b(rw|rewrite|simp_rw|simp_all_rw)\s*\['
    r'|\b(simp)(?:_all)?\s+only\s*\['
    r'|\b(simp_all|simp)\s*\['
)

# Apply / exact heads (just the leading identifier, dotted path OK).
APPLY_HEAD_RE = re.compile(r'\bapply\s+([A-Za-z_][\w\'.]*)')
EXACT_HEAD_RE = re.compile(r'\bexact\s+([A-Za-z_][\w\'.]*)')
REFINE_HEAD_RE = re.compile(r'\brefine\s+([A-Za-z_][\w\'.]*)')


def balance_brackets(src: str, start: int) -> int:
    """Given src[start] == '[', return idx of the matching ']'."""
    depth = 1; j = start + 1
    n = len(src)
    while j < n and depth > 0:
        c = src[j]
        if c == '[': depth += 1
        elif c == ']': depth -= 1
        j += 1
    return j  # one past the ']'


def split_top_level(content: str, sep: str = ',') -> list[str]:
    items, cur = [], []
    dp = db = dc = da = 0  # paren / brack / brace / angle (⟨⟩)
    for c in content:
        if c == '(': dp += 1
        elif c == ')': dp -= 1
        elif c == '[': db += 1
        elif c == ']': db -= 1
        elif c == '{': dc += 1
        elif c == '}': dc -= 1
        elif c == '⟨': da += 1
        elif c == '⟩': da -= 1
        if c == sep and dp == db == dc == da == 0:
            items.append(''.join(cur).strip()); cur = []
        else:
            cur.append(c)
    if cur:
        items.append(''.join(cur).strip())
    return items


HEAD_NAME_RE = re.compile(r'([A-Za-z_][\w\'.]*)')


def parse_lemma_head(item: str) -> str | None:
    s = item.lstrip()
    # Skip `← ` (backward) and `show ... from ...` prefixes
    while s and s[0] in '←↑':
        s = s[1:].lstrip()
    if s.startswith('show '):
        # `show <T> from <name>` — head identifier after `from`
        m = re.search(r'\bfrom\s+([A-Za-z_][\w\'.]*)', s)
        return m.group(1) if m else None
    m = HEAD_NAME_RE.match(s)
    return m.group(1) if m else None


def extract_citations(rel: str, name: str, body: str):
    """Yield (kind, lemma_head) tuples for every citation."""
    # Bracket-list tactics: rw, rewrite, simp_rw, simp only, simp_all only
    i = 0
    while i < len(body):
        m = BRACKET_HDR_RE.search(body, i)
        if not m:
            break
        # find `[` start (at m.end() - 1 since regex includes the `[`)
        lb = body.find('[', m.start())
        if lb == -1 or lb >= len(body):
            i = m.end(); continue
        rb = balance_brackets(body, lb)
        content = body[lb+1:rb-1]
        kind = next(g for g in m.groups() if g)
        for item in split_top_level(content):
            head = parse_lemma_head(item)
            if head:
                yield (kind, head)
        i = rb

    # Single-name tactics: apply / exact / refine
    for m in APPLY_HEAD_RE.finditer(body):
        yield ('apply', m.group(1))
    for m in EXACT_HEAD_RE.finditer(body):
        yield ('exact', m.group(1))
    for m in REFINE_HEAD_RE.finditer(body):
        yield ('refine', m.group(1))


# ---------- (C) construct shape extraction ----------

INDUCTION_RE = re.compile(r'\binduction\s+([A-Za-z_][\w\'.]*)')
CASES_RE     = re.compile(r'\bcases\s+([A-Za-z_][\w\'.]*)')
OBTAIN_RE    = re.compile(r'\bobtain\s+(⟨)')


def find_with_block(body: str, idx: int) -> list[str]:
    """If `with` follows at position idx (after stripping whitespace),
    parse the immediately-following case-tag block.  Returns list of
    case tags after `|`."""
    tail = body[idx:]
    m = re.match(r'\s+with\b', tail)
    if not m:
        return []
    after = tail[m.end():]
    # Heuristic: collect tags `| Foo =>` until either next top-level
    # tactic keyword on a fresh-bullet line or end of immediate block.
    tags = []
    for cm in re.finditer(r'\|\s*([A-Za-z_][\w\'.]*)', after):
        tags.append(cm.group(1))
        # bail out at 200 chars or after 12 cases for safety
        if cm.end() > 4000 or len(tags) >= 12:
            break
    return tags


def extract_obtain_pattern(body: str, start_angle: int) -> str:
    """Balance ⟨ ⟩ starting at start_angle.  Return the literal pattern."""
    depth = 0; j = start_angle
    while j < len(body):
        c = body[j]
        if c == '⟨': depth += 1
        elif c == '⟩':
            depth -= 1
            if depth == 0:
                return body[start_angle:j+1]
        j += 1
    return ''


def classify_obtain(pat: str) -> str:
    """Normalise an obtain pattern to a shape string: e.g.
    `⟨a, b⟩` -> `⟨_,_⟩`, `⟨a, ⟨b, c⟩⟩` -> `⟨_,⟨_,_⟩⟩`."""
    out = []
    for c in pat:
        if c in '⟨⟩,':
            out.append(c)
    return ''.join(out).replace('', '').replace(' ', '')


def extract_shapes(rel: str, name: str, body: str):
    """Yield (construct, detail) tuples."""
    for m in INDUCTION_RE.finditer(body):
        var = m.group(1)
        tags = find_with_block(body, m.end())
        yield ('induction', f'{var}\t{len(tags)}\t{",".join(tags)}')
    for m in CASES_RE.finditer(body):
        var = m.group(1)
        tags = find_with_block(body, m.end())
        yield ('cases', f'{var}\t{len(tags)}\t{",".join(tags)}')
    for m in OBTAIN_RE.finditer(body):
        pat = extract_obtain_pattern(body, m.start(1))
        if pat:
            shape = classify_obtain(pat)
            yield ('obtain', f'{len(shape)}\t{shape}')


# ---------- scan loop + reporting ----------

def scan_all():
    cites, shapes = [], []
    for rel, src in walk_e213_files(LEAN_DIR):
        for name, body in find_decl_bodies(src):
            for kind, lemma in extract_citations(rel, name, body):
                cites.append((rel, name, kind, lemma))
            for ctype, detail in extract_shapes(rel, name, body):
                shapes.append((rel, name, ctype, detail))
    return cites, shapes


def write_tsv(rows, path):
    path.write_text("\n".join("\t".join(r) for r in rows) + "\n")


def read_cites(path):
    rows = []
    for line in path.read_text().splitlines():
        parts = line.split('\t', 3)
        if len(parts) == 4:
            rows.append(tuple(parts))
    return rows


def read_shapes(path):
    rows = []
    for line in path.read_text().splitlines():
        parts = line.split('\t', 3)
        if len(parts) == 4:
            rows.append(tuple(parts))
    return rows


def report(cites, shapes):
    # ---- (B) citation summary ----
    print(f"# Citations extracted: {len(cites)}")
    print(f"# Distinct cited names: {len({c[3] for c in cites})}")
    print()

    by_kind = collections.Counter(c[2] for c in cites)
    print("## Citations by tactic kind")
    for k, n in by_kind.most_common():
        print(f"  {k:<14} {n}")
    print()

    freq = collections.Counter(c[3] for c in cites)
    callers = collections.defaultdict(set)
    for rel, decl, _, lemma in cites:
        callers[lemma].add((rel, decl))

    print("## Top 30 cited lemmas (by total occurrences)")
    for lem, n in freq.most_common(30):
        nc = len(callers[lem])
        print(f"  {n:>5}  ({nc:>4} callers)  {lem}")
    print()

    print("## Top 20 cited lemmas (by distinct callers)")
    rank = sorted(callers.items(), key=lambda kv: -len(kv[1]))[:20]
    for lem, cs in rank:
        print(f"  {len(cs):>4} callers   total {freq[lem]:>5}   {lem}")
    print()

    # External vs internal
    e213 = sum(1 for l in freq if l.startswith('E213') or '.' in l and l.split('.')[0] == 'E213')
    print(f"## E213-internal vs external citations")
    is_e213 = lambda l: l.startswith('E213.')
    internal = sum(c for l, c in freq.items() if is_e213(l))
    external = sum(c for l, c in freq.items() if not is_e213(l))
    print(f"  E213.* names cited:   {internal:>6}  ({100*internal/(internal+external):.1f}%)")
    print(f"  External (Nat/List/Lean core): {external:>6}  ({100*external/(internal+external):.1f}%)")
    print()

    # ---- (C) construct shapes ----
    print(f"# Construct shape rows: {len(shapes)}")
    ctypes = collections.Counter(s[2] for s in shapes)
    for k, n in ctypes.most_common():
        print(f"  {k:<14} {n}")
    print()

    # induction targets
    ind_rows = [s for s in shapes if s[2] == 'induction']
    ind_vars = collections.Counter()
    ind_cases = collections.Counter()
    ind_tagsets = collections.Counter()
    for _, _, _, detail in ind_rows:
        parts = detail.split('\t', 2)
        if len(parts) == 3:
            var, ncases, tags = parts
            ind_vars[var] += 1
            ind_cases[int(ncases)] += 1
            if tags:
                ind_tagsets[tags] += 1
    print("## Top induction target variables")
    for v, n in ind_vars.most_common(15):
        print(f"  {n:>4}   induction {v}")
    print()
    print("## Induction `with` block case-count distribution")
    for nc in sorted(ind_cases):
        print(f"  with-{nc:<2} cases: {ind_cases[nc]}")
    print()
    print("## Top induction case-tag sets")
    for tags, n in ind_tagsets.most_common(10):
        print(f"  x{n:<3}   with | {' | '.join(tags.split(','))}")
    print()

    # cases targets
    cas_rows = [s for s in shapes if s[2] == 'cases']
    cas_tagsets = collections.Counter()
    cas_vars = collections.Counter()
    for _, _, _, detail in cas_rows:
        parts = detail.split('\t', 2)
        if len(parts) == 3:
            v, _, tags = parts
            cas_vars[v] += 1
            if tags:
                cas_tagsets[tags] += 1
    print("## Top `cases` target variables")
    for v, n in cas_vars.most_common(15):
        print(f"  {n:>4}   cases {v}")
    print()
    print("## Top `cases ... with` tag sets")
    for tags, n in cas_tagsets.most_common(10):
        print(f"  x{n:<3}   with | {' | '.join(tags.split(','))}")
    print()

    # obtain patterns
    obt_rows = [s for s in shapes if s[2] == 'obtain']
    obt_shapes = collections.Counter()
    for _, _, _, detail in obt_rows:
        parts = detail.split('\t', 1)
        if len(parts) == 2:
            obt_shapes[parts[1]] += 1
    print("## Top `obtain` destructuring shapes")
    for s, n in obt_shapes.most_common(15):
        print(f"  x{n:<4}  {s}")


# ---------- target-context dump (C3 from G93) ----------

# Reuse the tactic whitelist from the sibling scanner.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from syntax_tactic_scan import TACTIC_NAMES  # noqa: E402

CTX_TOKEN_RE = re.compile(
    r'(?:(?<=\s)|(?<=;)|(?<=\|)|(?<=·)|(?<=>)|(?<==>)|^)'
    r'([a-z][a-z_]*)'
    r"(?:'|\b)"
)


def extract_apply_contexts(body: str, targets: set[str], window: int = 5):
    """For each `apply <name>` (or `rw [<name>, ...]`, `exact <name>`)
    with name in `targets`, yield (tokens_before, tokens_after) — the
    surrounding ±window whitelisted tactic-name tokens, EXCLUDING the
    `apply`/`rw`/`exact` itself."""
    # Build sorted (pos, tac) stream of all whitelisted tactic tokens.
    tokens = []
    for m in CTX_TOKEN_RE.finditer(body):
        if m.group(1) in TACTIC_NAMES:
            tokens.append((m.start(1), m.group(1)))

    # Build a list of citation-event positions: (pos, kind, name)
    events = []
    for m in APPLY_HEAD_RE.finditer(body):
        if m.group(1) in targets:
            events.append((m.start(), 'apply', m.group(1)))
    for m in EXACT_HEAD_RE.finditer(body):
        if m.group(1) in targets:
            events.append((m.start(), 'exact', m.group(1)))
    # Also bracket-list cites of the targets
    i = 0
    while i < len(body):
        m = BRACKET_HDR_RE.search(body, i)
        if not m:
            break
        lb = body.find('[', m.start())
        if lb == -1:
            i = m.end(); continue
        rb = balance_brackets(body, lb)
        content = body[lb+1:rb-1]
        kind = next(g for g in m.groups() if g)
        for item in split_top_level(content):
            head = parse_lemma_head(item)
            if head in targets:
                events.append((lb, kind, head))
        i = rb

    events.sort(key=lambda e: e[0])

    for pos, kind, lemma in events:
        # Find idx in `tokens` where token pos == pos (the tactic
        # before/at this citation).  The kind itself is a tactic
        # name; find its index.
        # Identify the index of the *kind* token closest to pos.
        idx = None
        for k, (tp, tn) in enumerate(tokens):
            if tp == pos and tn == kind:
                idx = k; break
        if idx is None:
            # Fallback: nearest tactic token starting at/before pos
            for k, (tp, _) in enumerate(tokens):
                if tp > pos:
                    idx = max(0, k - 1); break
            else:
                idx = len(tokens) - 1
        lo = max(0, idx - window)
        hi = min(len(tokens), idx + window + 1)
        before = tuple(t for _, t in tokens[lo:idx])
        after  = tuple(t for _, t in tokens[idx+1:hi])
        yield (kind, lemma, before, after)


def _line_no(src: str, pos: int) -> int:
    """Approximate line number (1-indexed) for a position in src."""
    return src.count('\n', 0, pos) + 1


# Heuristic granularity hint for `Raw.fold_slash` (and similar Raw-axiom
# direct invocations).  The hint is inferred from the surrounding body
# text within ± 400 characters of the cite — looks for marker tokens
# that suggest either atomic-Raw or count-Lens-group level.
GROUP_MARKERS = ('Decomp', 'count', 'Atomicity', 'partition', 'IsAlive',
                 'Clause4', 'pair_forcing', 'kSubset', 'binom', 'NS·NT',
                 'NS * NT')
ATOMIC_MARKERS = ('Tree.', 'Raw.a', 'Raw.b', 'Raw.slash', 'a/b',
                  'binaryProj', 'booleanProj', 'isBool')


def _granularity_hint(body: str, pos: int) -> str:
    """Inspect ± 400 chars around `pos` and decide 'atomic' vs 'group'."""
    lo, hi = max(0, pos - 400), min(len(body), pos + 400)
    window = body[lo:hi]
    g_hits = sum(1 for m in GROUP_MARKERS if m in window)
    a_hits = sum(1 for m in ATOMIC_MARKERS if m in window)
    if g_hits > a_hits:
        return 'group'
    if a_hits > g_hits:
        return 'atomic'
    return 'ambiguous'


def scan_contexts(targets: set[str], window: int = 5):
    rows = []  # (rel, decl, line, kind, lemma, before_tuple, after_tuple, hint)
    for rel, src in walk_e213_files(LEAN_DIR):
        for name, body in find_decl_bodies(src):
            # Compute body offset to translate body-pos → src-pos.  body
            # is a suffix of src; find its start.
            body_off = src.find(body)
            if body_off < 0:
                body_off = 0
            # Extract with positions for line-number + granularity hint:
            for kind, lemma, before, after, pos in extract_apply_contexts_pos(
                    body, targets, window):
                line = _line_no(src, body_off + pos)
                hint = _granularity_hint(body, pos)
                rows.append((rel, name, line, kind, lemma, before, after, hint))
    return rows


def extract_apply_contexts_pos(body: str, targets: set[str], window: int = 5):
    """Same as extract_apply_contexts but also yields the body-relative
    position of the citation event."""
    tokens = []
    for m in CTX_TOKEN_RE.finditer(body):
        if m.group(1) in TACTIC_NAMES:
            tokens.append((m.start(1), m.group(1)))
    events = []
    for m in APPLY_HEAD_RE.finditer(body):
        if m.group(1) in targets:
            events.append((m.start(), 'apply', m.group(1)))
    for m in EXACT_HEAD_RE.finditer(body):
        if m.group(1) in targets:
            events.append((m.start(), 'exact', m.group(1)))
    i = 0
    while i < len(body):
        m = BRACKET_HDR_RE.search(body, i)
        if not m:
            break
        lb = body.find('[', m.start())
        if lb == -1:
            i = m.end(); continue
        rb = balance_brackets(body, lb)
        content = body[lb+1:rb-1]
        kind = next(g for g in m.groups() if g)
        for item in split_top_level(content):
            head = parse_lemma_head(item)
            if head in targets:
                events.append((lb, kind, head))
        i = rb
    events.sort(key=lambda e: e[0])
    for pos, kind, lemma in events:
        idx = None
        for k, (tp, tn) in enumerate(tokens):
            if tp == pos and tn == kind:
                idx = k; break
        if idx is None:
            for k, (tp, _) in enumerate(tokens):
                if tp > pos:
                    idx = max(0, k - 1); break
            else:
                idx = len(tokens) - 1
        lo = max(0, idx - window)
        hi = min(len(tokens), idx + window + 1)
        before = tuple(t for _, t in tokens[lo:idx])
        after  = tuple(t for _, t in tokens[idx+1:hi])
        yield (kind, lemma, before, after, pos)


def report_contexts(rows, window: int):
    print(f"# Context-extracted citation rows: {len(rows)}")
    by_decl = collections.Counter(r[0] + '::' + r[1] for r in rows)
    print(f"# Distinct (file, decl) hosting a target citation: {len(by_decl)}")
    print()
    # Cluster by (kind, before-tuple, after-tuple)
    cluster = collections.defaultdict(list)
    for r in rows:
        rel, decl, line, kind, lemma, before, after, hint = r
        cluster[(kind, before, after)].append((rel, decl, line, lemma, hint))
    print(f"# Distinct ±{window} context skeletons: {len(cluster)}\n")
    print(f"## Top context skeletons around target citation")
    ranked = sorted(cluster.items(), key=lambda kv: -len(kv[1]))
    for (kind, b, a), occs in ranked[:15]:
        decls = sorted({(r, d) for r, d, _, _, _ in occs})
        hints = collections.Counter(h for _, _, _, _, h in occs)
        hint_summary = ', '.join(f'{h}={n}' for h, n in hints.most_common())
        print(f"  x{len(occs)}   {len(decls)} distinct (file, decl)   [{hint_summary}]")
        print(f"    BEFORE: [{', '.join(b) if b else '(start of proof)'}]")
        print(f"    KIND:   {kind}  <target>")
        print(f"    AFTER:  [{', '.join(a) if a else '(end of proof)'}]")
        for r, d, _, _, _ in occs[:3]:
            print(f"    · {r} :: {d}")
        if len(occs) > 3:
            print(f"    · ... +{len(occs)-3}")
        print()

    # by lemma if multiple targets
    by_lemma = collections.Counter(r[4] for r in rows)
    if len(by_lemma) > 1:
        print("## Hits per target")
        for lem, n in by_lemma.most_common():
            print(f"  {n:>4}  {lem}")
    # granularity summary
    by_hint = collections.Counter(r[7] for r in rows)
    print()
    print("## Granularity-hint distribution")
    for h, n in by_hint.most_common():
        print(f"  {h:<10} {n}")


def write_context_tsv(rows, path):
    """Write a TSV deliverable: file, line, decl, kind, lemma,
    before-tactics, after-tactics, granularity-hint."""
    lines = ['file\tline\tdecl\tkind\tlemma\tbefore\tafter\thint']
    for rel, decl, line, kind, lemma, before, after, hint in rows:
        lines.append('\t'.join([
            rel, str(line), decl, kind, lemma,
            ','.join(before), ','.join(after), hint
        ]))
    path.write_text('\n'.join(lines) + '\n')


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--report-only", action="store_true",
                    help="reuse cached TSV files")
    ap.add_argument("--context-target",
                    help="comma-separated lemma names; dump ±W tactic "
                         "context around every citation site")
    ap.add_argument("--context-window", type=int, default=5,
                    help="window size in tactic tokens (default 5)")
    ap.add_argument("--context-tsv",
                    help="also write a TSV (file/line/decl/kind/lemma/"
                         "before/after/hint) to the given path")
    args = ap.parse_args()
    if args.context_target:
        targets = {t.strip() for t in args.context_target.split(',')}
        rows = scan_contexts(targets, args.context_window)
        report_contexts(rows, args.context_window)
        if args.context_tsv:
            write_context_tsv(rows, pathlib.Path(args.context_tsv))
            print(f"\n# TSV written to {args.context_tsv}  ({len(rows)} rows)")
        return 0
    if args.report_only:
        cites = read_cites(CITE_PATH)
        shapes = read_shapes(SHAPE_PATH)
    else:
        cites, shapes = scan_all()
        write_tsv(cites, CITE_PATH)
        write_tsv(shapes, SHAPE_PATH)
    report(cites, shapes)
    return 0


if __name__ == "__main__":
    sys.exit(main())
