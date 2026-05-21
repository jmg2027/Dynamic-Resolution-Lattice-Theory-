"""Shared Lean-source surface parsing helpers.

Used by `tools/syntax_tactic_scan.py` and `tools/syntax_arg_scan.py`
to walk `.lean` files, strip comments, locate decl boundaries, and
extract tactic bodies — without any Lean / lake build dependency.
"""
from __future__ import annotations
import re, pathlib


DECL_KW = r'(?:theorem|lemma|def|example|instance)'

DECL_HEAD_RE = re.compile(
    r'^(?:@\[[^\]]*\]\s*|protected\s+|private\s+|noncomputable\s+|'
    r'partial\s+|unsafe\s+|abbrev\s+)*'
    + DECL_KW + r'\s+(?P<name>[A-Za-z_][\w\'.`]*)?',
    re.MULTILINE,
)

BOUNDARY_RE = re.compile(
    r'^(?:@\[[^\]]*\]\s*|protected\s+|private\s+|noncomputable\s+|'
    r'partial\s+|unsafe\s+|abbrev\s+)*'
    r'(?:' + DECL_KW + r'|namespace|end|section|open|variable|axiom|'
    r'inductive|structure|class|export|attribute|import|#\w+)\b',
    re.MULTILINE,
)

BY_RE = re.compile(r':=\s*by\b')


def strip_comments(src: str) -> str:
    """Strip `/- ... -/` (one level of nesting) and `--` line comments."""
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


def find_decl_bodies(src: str):
    """Yield (name, body_after_by) for each `<kw> name ... := by <body>`
    at top level.  Body terminates at next top-level boundary."""
    src = strip_comments(src)
    decls = [(m.start(), m.group('name') or '_anon_')
             for m in DECL_HEAD_RE.finditer(src)]
    bounds = [m.start() for m in BOUNDARY_RE.finditer(src)]
    bounds.append(len(src))
    for start, name in decls:
        end = next((b for b in bounds if b > start), len(src))
        chunk = src[start:end]
        by_m = BY_RE.search(chunk)
        if not by_m:
            continue
        yield name, chunk[by_m.end():]


def walk_e213_files(lean_dir: pathlib.Path):
    """Yield (relpath, source) for each non-probe `.lean` under lean_dir."""
    for p in sorted(lean_dir.rglob("*.lean")):
        if p.name.startswith("_"):
            continue
        try:
            yield p.relative_to(lean_dir).as_posix(), p.read_text()
        except UnicodeDecodeError:
            continue
