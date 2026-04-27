#!/usr/bin/env python3
"""기존 .lean 파일에서 bracket 패턴 자동 포팅.

지원 패턴:
  1. `theorem N : LO < M ∧ M < HI := by decide`
     → `Nat.ble (LO+1) M = true ∧ Nat.ble (M+1) HI = true := ⟨rfl, rfl⟩`

  2. `theorem N : K = V := rfl`  (정수 등식)
     → 변경 없음 (이미 axiom-free 가능성 높음)

Usage: python3 tools/auto_port.py <input.lean>
출력: stdout 에 ported 코드.

수동 검수 후 lean/E213/Kernel/Cap_*.lean 으로 합쳐 넣기.
"""
import re, sys
from pathlib import Path

BRACKET_LT = re.compile(
    r'theorem\s+(\w+)\s*:\s*'
    r'(\d+)\s*<\s*(\d+)\s*∧\s*(\d+)\s*<\s*(\d+)\s*'
    r':=\s*by\s+decide'
)


def port_bracket(text: str) -> list[str]:
    out = []
    for m in BRACKET_LT.finditer(text):
        name, lo, n1, n2, hi = m.groups()
        if n1 != n2:
            continue
        out.append(
            f"theorem {name} :\n"
            f"    Nat.ble {int(lo)+1} {n1} = true ∧ "
            f"Nat.ble {int(n2)+1} {hi} = true := ⟨rfl, rfl⟩"
        )
    return out


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    path = Path(sys.argv[1])
    text = path.read_text()
    ported = port_bracket(text)
    print(f"-- Auto-ported from {path}")
    print(f"-- {len(ported)} bracket theorem(s) detected")
    print()
    for p in ported:
        print(p)
        print()


if __name__ == '__main__':
    main()
