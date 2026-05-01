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
# Vertical-layer dirs use umbrella-shared namespaces (e.g., multiple
# Tactic/X.lean files all live under `namespace E213.Tactic`).  Per
# CLAUDE.md "vertical layer takes precedence", leave these alone.
DEFAULT_SKIP = {
    # Raw umbrella — multiple flat files share `E213.Firmware`
    "lean/E213/Firmware/Raw",
    "lean/E213/Firmware/Raw.lean",
    "lean/E213/Firmware/RawLevels.lean",
    "lean/E213/Firmware/RawSwap.lean",
    # Other vertical-layer umbrellas
    "lean/E213/Hypervisor",
    "lean/E213/Infinity",
    "lean/E213/Tactic",
    "lean/E213/Kernel",
    "lean/E213/Prelude.lean",
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
