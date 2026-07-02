"""The c-increment collapsing laws — the extension-language finding (2026-07-02).

The harmonic-kernel coefficient of the zeta(3) numerator Apery number,
    c(n,k) = H3(n) + kappa(n,k),
    H3(n)      = sum_{j<=n} 1/j^3,
    kappa(n,k) = sum_{m=1}^k (-1)^(m-1) / (2 m^3 C(n,m) C(n+m,m)),
has BOTH increments collapsing to a single rational multiple of the half-weight
carrier  w(n,k) = 1/(C(n,k) C(n+k,k))  (so b*w = C(n,k)C(n+k,k) = sqrt(b), an
integer, b(n,k) = C(n,k)^2 C(n+k,k)^2):

    (1)  c(n,k) - c(n-1,k) = (-1)^k     * w(n,k) / (n^2 (n-k))      [0 <= k <= n-1]
    (2)  c(n,k) - c(n,k-1) = (-1)^(k-1) * w(n,k) / (2 k^3)          [1 <= k <= n]

(2) is definitional; (1) is the collapsing lemma (van der Poorten / Beukers,
re-found by the extension protocol's P3 probe).  Note k=0 in (1) gives 1/n^3:
one increment law covers the harmonic AND kernel parts together -- the
H3/K split of numerator_plan.md is a presentation, not a necessity.

Consequence (the wall re-read): the KEY FINDING "no clean WZ certificate"
(numerator_plan.md) is a CAP for the b-only certificate language
{rational(j,k) * b(j,k)} -- not a wall for the problem.  In the extended
language over the carrier pair (b, sqrt(b)) with c-as-data, every
Delta-computation on b*c is rational; the A/K-recurrence certificate search
belongs there.

Run: python3 verify_c_increments.py   (exact Fractions, no CAS)
"""
from fractions import Fraction as Fr
from math import comb

def H3(n):
    return sum(Fr(1, j**3) for j in range(1, n+1))

def kappa(n, k):
    return sum(Fr((-1)**(m-1), 2*m**3*comb(n,m)*comb(n+m,m)) for m in range(1, k+1))

def c(n, k):
    return H3(n) + kappa(n, k)

def w(n, k):
    return Fr(1, comb(n,k)*comb(n+k,k))

def b(n, k):
    return (comb(n,k)*comb(n+k,k))**2

N = 20
bad1 = [(n,k) for n in range(2, N) for k in range(0, n)
        if c(n,k)-c(n-1,k) != Fr((-1)**k, 1) * w(n,k) / (n**2*(n-k))]
bad2 = [(n,k) for n in range(1, N) for k in range(1, n+1)
        if c(n,k)-c(n,k-1) != Fr((-1)**(k-1), 1) * w(n,k) / (2*k**3)]
bad3 = [(n,k) for n in range(1, N) for k in range(0, n+1)
        if b(n,k)*w(n,k) != comb(n,k)*comb(n+k,k)]

print("(1) cross-n collapse:", "HOLDS" if not bad1 else f"FAILS {bad1[:3]}")
print("(2) cross-k collapse:", "HOLDS" if not bad2 else f"FAILS {bad2[:3]}")
print("(3) b*w = sqrt(b) integer:", "HOLDS" if not bad3 else f"FAILS {bad3[:3]}")
assert not (bad1 or bad2 or bad3)
print(f"all exact up to n < {N}")
