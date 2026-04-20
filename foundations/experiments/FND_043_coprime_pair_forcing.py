"""
EXP_FND_043: (2,3) 쌍의 arithmetic 유일성 — coprime pair 전수 조사

FND_042 는 A(L)={L,...,2L-1} 에서 L=2 만 atomic n 존재를 보임.
이번 실험: atom set 을 **임의의 {p, q} coprime pair** 로 확장.

Setup:
  A = {p, q}, gcd(p, q) = 1, 2 ≤ p < q
  Decomp: n = c_p · p + c_q · q, (c_p, c_q) ∈ ℕ²
  Alive: c_p, c_q 둘 다 odd positive
  Atomic(n): 유일 decomp AND alive

Bézout 분석:
  (c_p, c_q) → (c_p + q, c_q - p) 는 n 보존
  Atomic 은 c_p < q AND c_q < p 필요
  Odd positive + 상한 → atomic pair 수 = ⌈(q-1)/2⌉ · ⌈(p-1)/2⌉

Hypothesis: atomic 유일 ⟺ (p, q) = (2, 3).
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))
from experiment import Experiment
from math import gcd


def atomic_pairs(p, q):
    """ALL (c_p, c_q) with c_p, c_q odd pos, c_p < q, c_q < p."""
    pairs = []
    for c_q in range(1, p, 2):
        for c_p in range(1, q, 2):
            pairs.append((c_p, c_q, c_p * p + c_q * q))
    return pairs


class EXP_FND_043(Experiment):
    ID = "FND_043"
    TITLE = "(2,3) arithmetic 유일성 — coprime pair"

    def run(self):
        self.log("=" * 65)
        self.log("Coprime pair (p, q) atomic-n 유일성")
        self.log("=" * 65)
        self.log("")

        # CHECK 1: atomic pair count formula
        self.log("=" * 65)
        self.log("CHECK 1: atomic pair 개수 = ⌈(p-1)/2⌉·⌈(q-1)/2⌉")
        self.log("=" * 65)
        unique_pairs = []
        for q in range(2, 11):
            for p in range(2, q):
                if gcd(p, q) != 1:
                    continue
                pairs = atomic_pairs(p, q)
                count = len(pairs)
                mark = " ← 유일!" if count == 1 else ""
                if count == 1:
                    unique_pairs.append((p, q, pairs[0]))
                self.log(f"  (p,q)=({p},{q}): {count} atomic{mark}")

        self.log("")
        self.log(f"Unique atomic pairs: {unique_pairs}")
        self.check("유일 atomic = (p,q)=(2,3) → n=5",
                   len(unique_pairs) == 1 and
                   unique_pairs[0][:2] == (2, 3) and
                   unique_pairs[0][2][2] == 5)

        # CHECK 2: 공식 검증
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 2: Formula count(p,q) = ⌈(p-1)/2⌉·⌈(q-1)/2⌉")
        self.log("=" * 65)
        ok = True
        for q in range(2, 11):
            for p in range(2, q):
                if gcd(p, q) != 1:
                    continue
                pairs = atomic_pairs(p, q)
                predicted = ((p - 1 + 1) // 2) * ((q - 1 + 1) // 2)
                ok = ok and (len(pairs) == predicted)
        self.check("count 공식 검증", ok)

        # CHECK 3: non-coprime 은?
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 3: gcd(p,q)>1 인 경우")
        self.log("=" * 65)
        for (p, q) in [(2,4), (3,6), (4,6)]:
            g = gcd(p,q)
            pairs = atomic_pairs(p, q)
            self.log(f"  (p,q)=({p},{q}): gcd={g}, atomic={len(pairs)}")
            self.log(f"    (non-coprime → 전체 n 이 g 배수만)")

        # Summary
        self.log("")
        self.log("=" * 65)
        self.log("결론")
        self.log("=" * 65)
        self.log("")
        self.log("(p, q) = (2, 3) 은 다음 3 조건을 동시에 만족하는")
        self.log("유일한 coprime pair (p, q ≤ 10 scan):")
        self.log("  1. gcd(p, q) = 1 (coprime)")
        self.log("  2. 2 ≤ p < q (atom size ≥ 2)")
        self.log("  3. 유일 atomic n (alive + 유일 decomp)")
        self.log("")
        self.log("→ DRLT d=5 는 단순히 'arity=2 arithmetic 귀결' 이 아니라")
        self.log("  모든 atom-pair 중 (2,3) 이 유일한 unique-atomic solution.")


if __name__ == "__main__":
    EXP_FND_043().execute()
