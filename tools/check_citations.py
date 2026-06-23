#!/usr/bin/env python3
"""check_citations.py — mechanical immune system against fabricated Lean citations.

Scans permanent-tier prose (theory/, seed/, papers/, catalogs/, books/) for
backticked citations of Lean artifacts and reports any that DO NOT resolve in
lean/E213. This is the mechanical form of the Phase-8 lesson: a "PROVED
∅-axiom" claim must point at a real theorem; a `.lean` path must exist.

Two checks, both conservative (designed to minimise false positives):

  1. PATH citations — any backticked token ending in `.lean`. The file must
     exist under lean/ (accepting both `E213/...` and `lean/E213/...` forms,
     and bare `Foo/Bar.lean` resolved anywhere in the tree).

  2. QUALIFIED-NAME citations — backticked `A.B.c`-shaped tokens that look like
     Lean qualified identifiers (Lean-ish, no math/markup). The FINAL segment
     must appear as a declaration name somewhere in lean/E213. A final segment
     found nowhere is a probable phantom (the Phase-8 failure class).

Exit code 1 if any PATH citation is unresolved (hard error) — qualified-name
misses are reported as warnings (heuristic, may have false positives).

Usage:  python3 tools/check_citations.py [--strict] [dir ...]
        --strict : also exit 1 on unresolved qualified-name citations.
"""
import os, re, sys, subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN_ROOT = os.path.join(ROOT, "lean")
DEFAULT_DIRS = ["theory", "seed", "papers", "catalogs", "books"]

# --- build the universe of declaration names in lean/E213 (last-segment set) ---
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+([A-Za-z_][A-Za-z0-9_'!?]*)"
)
def build_decl_index():
    names = set()
    files = set()
    for dirpath, _, fns in os.walk(os.path.join(LEAN_ROOT, "E213")):
        for fn in fns:
            if fn.endswith(".lean"):
                p = os.path.join(dirpath, fn)
                rel = os.path.relpath(p, LEAN_ROOT)          # E213/.../X.lean
                files.add(rel.replace("\\", "/"))
                files.add(fn)                                 # bare basename
                try:
                    for line in open(p, encoding="utf-8", errors="ignore"):
                        m = DECL_RE.match(line)
                        if m:
                            names.add(m.group(1))
                except OSError:
                    pass
    return names, files

# --- token classification ---
BACKTICK = re.compile(r"`([^`]+)`")
# a Lean-ish qualified name: segments of identifier chars joined by dots,
# at least one dot, starts with a letter.
QUAL = re.compile(r"^[A-Za-z][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)+$")
MATH_CHARS = set("αβγδεζηθικλμνξοπρστυφχψωΛΩΣΠΦΨΔΘ√⊕⊗→↔⇒≤≥∈∉∅∞·×∘⌣²³⁰¹⁴ℝℕℤℚℂπφ")

# Lean *core*/stdlib namespaces — citations into these are external-by-design,
# not phantoms (the E213 corpus legitimately names core lemmas).
CORE_NS = {"Nat", "Bool", "List", "Fin", "Option", "Int", "Array", "Char",
           "String", "Prod", "Sum", "Sigma", "Subtype", "Function", "Eq", "Or",
           "And", "Iff", "Exists", "Classical", "Decidable", "Std", "Lean",
           "Quot", "Setoid", "Subsingleton", "WellFounded", "Acc", "Ne", "Not",
           "Empty", "Unit", "PUnit", "PProd", "ULift", "Ordering"}
GLOB_CHARS = set("{}*<>[]")

def is_path_token(tok):
    return tok.endswith(".lean") and not (any(c in GLOB_CHARS for c in tok)
                                          or "," in tok or "..." in tok)

DOC_EXT = (".md", ".py", ".sh", ".txt", ".json", ".toml", ".lean", ".rs")
def is_lean_qual(tok):
    if not QUAL.match(tok) or any(c in MATH_CHARS for c in tok):
        return False
    if tok.endswith(DOC_EXT):        # file refs, not declarations
        return False
    segs = tok.split(".")
    if segs[-1][:1].isdigit() or tok.lower() in ("e.g", "i.e", "et.al", "vs.the"):
        return False
    if segs[0] in CORE_NS:           # core/stdlib reference, not a phantom
        return False
    has_ns = any(s[:1].isupper() for s in segs[:-1])
    snake_final = ("_" in segs[-1]) or segs[-1].islower()
    return has_ns and (snake_final or segs[-1][:1].isupper())

def is_module_path(tok, files):
    """`A.B.C` that resolves to a file `E213/A/B/C.lean` is a module ref, not a
    declaration phantom."""
    cand = "E213/" + tok.replace(".", "/") + ".lean"
    if cand in files:
        return True
    # also the dotted form may be a namespace prefix of a real module file
    return (tok.replace(".", "/") + ".lean") in {f for f in files}

def resolve_path(tok, files):
    t = tok.lstrip("./")
    if t.startswith("lean/"):
        t = t[len("lean/"):]
    if t in files:
        return True
    base = t.split("/")[-1]
    return base in files

def main():
    args = [a for a in sys.argv[1:] if a != "--strict"]
    strict = "--strict" in sys.argv
    dirs = args or DEFAULT_DIRS
    names, files = build_decl_index()

    path_miss = []   # (file, line, token)
    qual_miss = []
    for d in dirs:
        base = os.path.join(ROOT, d)
        for dirpath, _, fns in os.walk(base):
            for fn in fns:
                if not fn.endswith(".md"):
                    continue
                p = os.path.join(dirpath, fn)
                rel = os.path.relpath(p, ROOT)
                for i, line in enumerate(open(p, encoding="utf-8", errors="ignore"), 1):
                    for tok in BACKTICK.findall(line):
                        tok = tok.strip()
                        if is_path_token(tok):
                            if not resolve_path(tok, files):
                                path_miss.append((rel, i, tok))
                        elif is_lean_qual(tok):
                            if (tok.split(".")[-1] not in names
                                    and not is_module_path(tok, files)):
                                qual_miss.append((rel, i, tok))

    print(f"# scanned dirs: {', '.join(dirs)}")
    print(f"# lean decls indexed: {len(names)};  lean files: {len(files)//2}")
    print(f"\n## PATH citations unresolved (hard errors): {len(path_miss)}")
    for f, ln, t in path_miss:
        print(f"  {f}:{ln}  `{t}`")
    print(f"\n## QUALIFIED-NAME citations whose final id resolves nowhere "
          f"(probable phantoms, heuristic): {len(qual_miss)}")
    for f, ln, t in sorted(set(qual_miss)):
        print(f"  {f}:{ln}  `{t}`")

    bad = len(path_miss) + (len(qual_miss) if strict else 0)
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main()
