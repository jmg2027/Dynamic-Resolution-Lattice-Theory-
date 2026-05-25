#!/usr/bin/env python3
"""Generate a per-file summary of the Lean source tree.

For each `.lean` file under `lean/E213/`, emits:

  · Module path
  · Module-level `/-! ... -/` docstring (first one only)
  · Top-level declarations (`theorem`, `def`, `inductive`, `structure`,
    `instance`, `abbrev`, `class`)
  · Imports

The source-of-truth content is the Lean docstrings; this script
is a derivation, not a duplication.  Run it on demand instead of
maintaining a parallel markdown digest.

Usage:
  tools/lean_summary.py                # full tree → stdout
  tools/lean_summary.py <subdir>       # restricted to one subdir
  tools/lean_summary.py --decls-only   # skip docstrings
"""

import argparse
import re
import sys
from pathlib import Path


DOCSTRING_RE = re.compile(r"/-!\s*(.*?)\s*-/", re.DOTALL)
DECL_RE = re.compile(
    r"^(?:private\s+|protected\s+|noncomputable\s+|@\[[^\]]*\]\s*)*"
    r"(theorem|def|inductive|structure|instance|abbrev|class)\s+"
    r"([A-Za-z_][\w'.]*)",
    re.MULTILINE,
)
IMPORT_RE = re.compile(r"^import\s+(\S+)", re.MULTILINE)


def summarise(path: Path, decls_only: bool) -> str:
    text = path.read_text(errors="replace")
    out = [f"### `{path}`"]

    if not decls_only:
        doc = DOCSTRING_RE.search(text)
        if doc:
            # Take the first non-empty line as the role summary.
            for line in doc.group(1).splitlines():
                line = line.strip("# ").strip()
                if line:
                    out.append(f"- **role**: {line}")
                    break

    decls = DECL_RE.findall(text)
    if decls:
        names = sorted({name for _, name in decls})
        # Truncate long lists to keep the summary compact.
        if len(names) > 12:
            shown = names[:12]
            out.append(
                f"- **decls** ({len(names)} total): "
                + ", ".join(shown)
                + f", … (+{len(names) - 12})"
            )
        else:
            out.append("- **decls**: " + ", ".join(names))

    imports = IMPORT_RE.findall(text)
    if imports:
        # Drop the `E213.` prefix for readability.
        short = sorted({i.removeprefix("E213.") for i in imports})
        if len(short) > 8:
            short = short[:8] + [f"… (+{len(imports) - 8})"]
        out.append("- **imports**: " + ", ".join(short))

    return "\n".join(out)


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("subdir", nargs="?", default="lean/E213")
    p.add_argument("--decls-only", action="store_true")
    args = p.parse_args()

    root = Path(args.subdir)
    if not root.exists():
        print(f"not found: {root}", file=sys.stderr)
        return 1

    files = sorted(root.rglob("*.lean"))
    print(f"# Lean summary — {root} ({len(files)} files)\n")
    for f in files:
        print(summarise(f, args.decls_only))
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
