#!/usr/bin/env python3
"""sync_namespaces.py — Auto namespace ↔ path alignment for E213 Lean tree."""
from __future__ import annotations
import argparse
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LEAN_ROOT = REPO / "lean"
E213 = LEAN_ROOT / "E213"

# Directories where files share a namespace by design (don't auto-align).
# Per ARCHITECTURE.md §6.1: tactic-bearing files use `namespace E213.Tactic`
# short-form so users `open E213.Tactic` to access the omega213 macro etc.
# Their *path* (Kernel/Tactic/, Math/Tactic/, Meta/Tactic/) reflects the
# import-derived layer, but the *namespace* is intentionally short.
DEFAULT_SKIP = {
    # Raw umbrella — multiple flat files share `E213.Theory`
    "lean/E213/Theory/Raw",
    "lean/E213/Theory/Raw.lean",
    "lean/E213/Theory/RawLevels.lean",
    "lean/E213/Theory/RawSwap.lean",
    # Hypervisor/Lens.lean uses `E213.Lens` umbrella
    "lean/E213/Lens/Lens.lean",
    # Kernel layer umbrella (101 thms in `namespace E213.Term`)
    "lean/E213/Term",
    "lean/E213/Prelude.lean",
    # Tactic short-namespace umbrellas (post-2026-05-XX reorg).
    # Files at these paths declare `namespace E213.Tactic` for ergonomic
    # `open E213.Tactic` macro access.  Path is path-aligned-to-layer;
    # namespace is intentionally short.
    "lean/E213/Term/Tactic",
    "lean/E213/Lib/Math/Tactic",
    "lean/E213/Meta/Tactic",
    # Math/Infinity/ files share `namespace E213.Infinity` umbrella by
    # design — they ALSO use `namespace E213.Theory.Internal` for
    # helper access (multi-namespace files), which the auto-aligner
    # mis-handles.  Keep the umbrella stable.
    "lean/E213/Lib/Math/Infinity",
    # Math/Polynomial213/ — namespace `E213.Polynomial213` is the
    # canonical reflection AST (top-level, like E213.Tactic).  Path
    # is under Math/ for layer-classification, namespace is short.
    "lean/E213/Lib/Math/Polynomial213.lean",
    "lean/E213/Lib/Math/Polynomial213",
    # Math/AxiomSystems/*AsLens.lean — file names use the "X AS LENS"
    # description; namespaces use the bare X (e.g.,
    # ZFCExtensionalityAsLens.lean → namespace E213.Lib.Math.AxiomSystems
    # .ZFCExtensionality).  Intentional: file = exposition, namespace
    # = subject matter.
    "lean/E213/Lib/Math/AxiomSystems",
    # ArithFSM/V2to3.lean — namespace ArithFSMto3 reflects the
    # cross-FSM bridge concept (V2 → V3); the file path encodes
    # the V2to3 sub-cluster.
    "lean/E213/Lib/Math/Cohomology/Dyadic/ArithFSM/V2to3.lean",
}


@dataclass
class FileInfo:
    path: Path
    expected_ns: str
    actual_ns: str | None


def expected_namespace(path: Path) -> str:
    rel = path.relative_to(LEAN_ROOT).with_suffix("")
    return ".".join(rel.parts)


def first_namespace(path: Path) -> str | None:
    pat = re.compile(r"^namespace\s+(\S+)\s*$", re.M)
    try:
        text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return None
    m = pat.search(text)
    return m.group(1) if m else None


def is_skipped(path: Path, skip_dirs: set[str]) -> bool:
    p = str(path.relative_to(REPO))
    return any(p == d or p.startswith(d + "/") for d in skip_dirs)


def collect(root: Path, skip_dirs: set[str]) -> list[FileInfo]:
    out = []
    for f in sorted(root.rglob("*.lean")):
        if is_skipped(f, skip_dirs):
            continue
        actual = first_namespace(f)
        if actual is None:
            continue
        out.append(FileInfo(f, expected_namespace(f), actual))
    return out


def mismatches(infos: list[FileInfo]) -> list[FileInfo]:
    return [i for i in infos if i.actual_ns != i.expected_ns]


def update_ns_decl(path: Path, old: str, new: str) -> bool:
    text = path.read_text(encoding="utf-8")
    ns_pat = re.compile(rf"^namespace\s+{re.escape(old)}\s*$", re.M)
    end_pat = re.compile(rf"^end\s+{re.escape(old)}\s*$", re.M)
    new_text = ns_pat.sub(f"namespace {new}", text)
    new_text = end_pat.sub(f"end {new}", new_text)
    if new_text != text:
        path.write_text(new_text, encoding="utf-8")
        return True
    return False


def apply_global_renames(roots: list[Path], renames: list[tuple[str, str]]) -> int:
    """Sentinel-protected single-pass rewrite.  Each old\\b is replaced with
    a unique \\x00<idx>\\x00 marker first, then markers are resolved.  This
    avoids cascade errors where rename A's output looks like rename B's input.
    """
    sentinel_for = lambda i: f"\x00{i}\x00"
    files_changed = 0
    for root in roots:
        for f in root.rglob("*"):
            if not f.is_file():
                continue
            if f.suffix not in (".lean", ".rs", ".md"):
                continue
            try:
                text = f.read_text(encoding="utf-8")
            except UnicodeDecodeError:
                continue
            new_text = text
            for i, (old, _) in enumerate(renames):
                pat = re.compile(rf"\b{re.escape(old)}\b")
                new_text = pat.sub(sentinel_for(i), new_text)
            for i, (_, new) in enumerate(renames):
                new_text = new_text.replace(sentinel_for(i), new)
            if new_text != text:
                f.write_text(new_text, encoding="utf-8")
                files_changed += 1
    return files_changed


def lake_build() -> tuple[bool, str]:
    env = os.environ.copy()
    env["PATH"] = "/root/.elan/bin:" + env.get("PATH", "")
    proc = subprocess.run(
        ["lake", "build"],
        cwd=str(LEAN_ROOT), env=env,
        capture_output=True, text=True, timeout=900,
    )
    return proc.returncode == 0, proc.stdout + proc.stderr


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--apply", action="store_true",
                    help="write changes (default: dry-run)")
    ap.add_argument("--root", type=str, default="lean/E213",
                    help="restrict scan to this root (rel to repo)")
    ap.add_argument("--include-rust", action="store_true",
                    help="also rewrite *.rs files in rust-engine/")
    ap.add_argument("--skip-list", type=str, default="",
                    help="comma-separated extra dirs to skip")
    ap.add_argument("--no-build", action="store_true",
                    help="skip post-apply lake build")
    args = ap.parse_args()

    root = (REPO / args.root).resolve()
    skip = set(DEFAULT_SKIP)
    if args.skip_list:
        skip.update(x.strip() for x in args.skip_list.split(",") if x.strip())

    infos = collect(root, skip)
    bad = mismatches(infos)
    print(f"scanned: {len(infos)} files, mismatches: {len(bad)}")
    if not bad:
        return 0

    for info in bad[:30]:
        print(f"  {info.path.relative_to(REPO)}")
        print(f"    actual:   {info.actual_ns}")
        print(f"    expected: {info.expected_ns}")
    if len(bad) > 30:
        print(f"  ... and {len(bad) - 30} more")

    if not args.apply:
        print("\n(dry-run; pass --apply to write changes)")
        return 0

    print("\nupdating namespace declarations...")
    for info in bad:
        update_ns_decl(info.path, info.actual_ns, info.expected_ns)

    print("rewriting global references...")
    renames = sorted({(i.actual_ns, i.expected_ns) for i in bad},
                     key=lambda p: -len(p[0]))
    roots = [E213]
    if args.include_rust:
        rust = REPO / "rust-engine"
        if rust.is_dir():
            roots.append(rust)
    n = apply_global_renames(roots, renames)
    print(f"  {n} files modified")

    if args.no_build:
        return 0

    print("\nverifying lake build...")
    ok, out = lake_build()
    if ok:
        print("✓ lake build clean")
        infos2 = collect(root, skip)
        bad2 = mismatches(infos2)
        if bad2:
            print(f"⚠ {len(bad2)} mismatches remain")
            return 1
        return 0
    else:
        print("✗ lake build FAILED:")
        print(out[-2000:])
        return 2


if __name__ == "__main__":
    sys.exit(main())
