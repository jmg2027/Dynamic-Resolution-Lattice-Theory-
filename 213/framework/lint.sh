#!/bin/bash
# 213 Layer Lint: import 경로로 레이어 위반 검출.
echo "=== 213 Layer Lint ==="

violations=0

layer_of() {
  case "$1" in
    *Firmware*) echo "fw";;
    *Translation*) echo "trans";;
    *Hypervisor*) echo "hv";;
    *OS*|*Goldbach*|*Pigeonhole*|*Primality*) echo "os";;
    *Meta*|*Test*) echo "meta";;
    *) echo "hw";;
  esac
}

# FW가 상위를 import하면 위반.
for f in E213/Firmware/*.lean; do
  grep "import E213\.\(OS\|Hypervisor\|Meta\|Translation\)" "$f" 2>/dev/null && {
    echo "VIOLATION: $f imports upper layer"
    violations=$((violations+1))
  }
done

# HV가 OS/Meta를 import하면 위반.
for f in E213/Hypervisor/*.lean; do
  grep "import E213\.\(OS\|Meta\)" "$f" 2>/dev/null && {
    echo "VIOLATION: $f imports upper layer"
    violations=$((violations+1))
  }
done

# Translation이 OS/Meta/HV를 import하면 위반.
for f in E213/Translation/*.lean; do
  grep "import E213\.\(OS\|Meta\|Hypervisor\)" "$f" 2>/dev/null && {
    echo "VIOLATION: $f imports upper layer"
    violations=$((violations+1))
  }
done

echo "---"
echo "Violations: $violations"
[ $violations -eq 0 ] && echo "PASS: No layer violations."
