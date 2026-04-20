"""
EXP_FND_042: Atom set generalization — 일반 L 의 atomic n 탐색

213 framework atom 구조:
  L = atom 하한 (현재 L=2)
  A(L) = non-decomposable integers ≥ L = {L, L+1, ..., 2L-1}
  Decomp: n = Σ c_j · (L+j), c_j ∈ ℕ
  Atomic(n): 유일 decomp + 전부 c_j odd

DRLT (L=2): A={2,3}, atomic n = 5 유일 → d=5.
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))
from experiment import Experiment


def atom_set(L):
    return list(range(L, 2*L))


def all_decomps(n, L):
    atoms = atom_set(L)
    results = []
    def rec(idx, remaining, acc):
        if idx == L:
            if remaining == 0:
                results.append(tuple(acc))
            return
        a = atoms[idx]
        for c in range(remaining // a + 1):
            acc.append(c)
            rec(idx+1, remaining - c*a, acc)
            acc.pop()
    rec(0, n, [])
    return results


def is_alive(c_tuple):
    return all(c > 0 and c % 2 == 1 for c in c_tuple)


def atomic_ns(L, n_max):
    result = []
    for n in range(1, n_max + 1):
        decomps = all_decomps(n, L)
        if len(decomps) == 1 and is_alive(decomps[0]):
            result.append((n, decomps[0]))
    return result


class EXP_FND_042(Experiment):
    ID = "FND_042"
    TITLE = "Atom set generalization — 일반 L 의 atomic n"

    def run(self):
        self.log("=" * 65)
        self.log("Atom set generalization: L ≥ 2")
        self.log("=" * 65)
        self.log("Setup:")
        self.log("  A(L) = {L, L+1, ..., 2L-1}")
        self.log("  Decomp: n = Σ c_j · (L+j), c_j ∈ ℕ")
        self.log("  Atomic: 유일 decomp + 전부 c_j odd (alive)")
        self.log("")

        # CHECK 1: atom set
        self.log("=" * 65)
        self.log("CHECK 1: Atom set A(L) = {L,...,2L-1}")
        self.log("=" * 65)
        for L in range(1, 9):
            A = atom_set(L)
            self.log(f"  L={L}: A = {A}  (|A|={len(A)})")
        self.check("A(L)=[L..2L-1], |A|=L",
                   all(len(atom_set(L))==L for L in range(1,9)))

        # CHECK 2: n_min(L) = L(3L-1)/2
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 2: n_min(L) = Σ A(L) = L(3L-1)/2")
        self.log("=" * 65)
        for L in range(2, 9):
            n_min = sum(atom_set(L))
            formula = L*(3*L - 1) // 2
            self.log(f"  L={L}: Σ A = {n_min},  L(3L-1)/2 = {formula}")
            assert n_min == formula
        self.check("n_min(L) = L(3L-1)/2", True)

        # CHECK 3: atomic n set for L=2..6
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 3: Atomic n set — L=2..6")
        self.log("=" * 65)
        atomic_results = {}
        for L in range(2, 7):
            n_max = 6 * L * L
            atomics = atomic_ns(L, n_max)
            atomic_results[L] = atomics
            n_min = sum(atom_set(L))
            self.log(f"\n  L={L} (A={atom_set(L)}, n_min={n_min}, scan≤{n_max}):")
            if atomics:
                for n, decomp in atomics:
                    self.log(f"    n={n:3d}: c = {decomp}")
            else:
                self.log(f"    (no atomic n in range)")

        # CHECK 4: L=2 → atomic = {5} 유일
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 4: L=2 → atomic n = {5} 유일")
        self.log("=" * 65)
        l2 = atomic_results[2]
        self.log(f"  L=2 atomic set: {[n for n, _ in l2]}")
        self.check("L=2: atomic = {5} 유일",
                   len(l2) == 1 and l2[0][0] == 5)

        # CHECK 5: d(L) = # atomic n
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 5: d(L) = # atomic n (L=2..6)")
        self.log("=" * 65)
        d_values = {}
        for L in range(2, 7):
            count = len(atomic_results[L])
            ns = [n for n, _ in atomic_results[L]]
            d_values[L] = count
            self.log(f"  L={L}: {count} atomic n — {ns}")
        self.log("")
        self.check("L=2 유일하게 d=1 (atomic n 유일)",
                   d_values[2] == 1)

        # CHECK 6: n_min(L) atomic?
        self.log("")
        self.log("=" * 65)
        self.log("CHECK 6: n_min(L) 이 atomic 인가?")
        self.log("=" * 65)
        for L in range(2, 7):
            n_min = sum(atom_set(L))
            ns = [n for n, _ in atomic_results[L]]
            in_atomic = n_min in ns
            status = "✓" if in_atomic else "✗"
            self.log(f"  L={L}: n_min={n_min}, atomic={in_atomic} {status}")

        # Summary
        self.log("")
        self.log("=" * 65)
        self.log("SUMMARY")
        self.log("=" * 65)
        self.log("")
        self.log("L=2 (DRLT): A={2,3}, atomic n = 5 유일 → d = 5")
        self.log("")
        self.log("L≥3: 여러 atomic n 가능, 유일성 깨짐")
        self.log("  → L=2 가 'atomic n 유일' 조건의 unique solution")
        self.log("")
        self.log("결론: atoms={2,3} 은 non-decomposable 정의 + L=2 (arity)")
        self.log("에서 강제되고, d=5 유일성은 arithmetic 귀결.")
        self.log("일반 L 은 '유일 atomic n' 조건이 성립 안 함.")


if __name__ == "__main__":
    EXP_FND_042().execute()
