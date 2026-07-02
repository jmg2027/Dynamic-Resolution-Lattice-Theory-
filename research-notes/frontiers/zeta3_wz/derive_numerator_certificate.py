"""THE NUMERATOR CERTIFICATE — found + verified (2026-07-02, extension-protocol V1 round 3).

The zeta(3) NUMERATOR Apery recurrence  Sum_k F_A(j,k) = 0,
  F_A(j,k) = (j+2)^3 b(j+2,k)c(j+2,k) + (j+1)^3 b(j,k)c(j,k) - aL(j) b(j+1,k)c(j+1,k),
  b(n,k) = C(n,k)^2 C(n+k,k)^2,  c(n,k) = H3(n)+kappa(n,k),  aL(j)=34j^3+153j^2+231j+117,
telescopes COMPLETELY in the extended language over (b, sqrt(b), c) — overturning the
"no clean WZ certificate / hand-derived kernel telescoping needed" verdict
(numerator_plan.md KEY FINDING, now re-read as a cap for the b-only language).

The chain (all verified EXACTLY below, j <= 25):

 (0) collapsing laws (verify_c_increments.py):
       Dn(n,k) := c(n,k)-c(n-1,k) = (-1)^k  w(n,k)/(n^2(n-k)),   w = 1/sqrt(b)
       dk(n,k) := c(n,k)-c(n,k-1) = (-1)^(k-1) w(n,k)/(2k^3)
 (1) express c at the TOP row:  F_A = F_B(j,k)*c(j+2,k)
       - (j+1)^3 b(j,k)[Dn(j+1,k)+Dn(j+2,k)] + aL(j) b(j+1,k) Dn(j+2,k)
 (2) Abel on Sum_k F_B*c(j+2,k) with the KNOWN denominator certificate G_B
       (F_B = G_B(j,k+1)-G_B(j,k)):  Sum F_B c = -Sum_k G_B(j,k+1)*dk(j+2,k+1)
 (3) residual  U(j,k) := -(j+1)^3 b(j,k)(Dn(j+1,k)+Dn(j+2,k)) + aL b(j+1,k)Dn(j+2,k)
                          - G_B(j,k+1) dk(j+2,k+1)
     satisfies  U(j,k) = (-1)^k sqrt(b)(j,k) * u(j,k)  for 0<=k<=j, u EXPLICIT RATIONAL:
       u = -(j+1)/(j+1+k) - (j+1)^3(j+1-k)/((j+2)^2(j+1+k)(j+2+k))
           + aL(j)(j+1+k)/((j+2)^2(j+1-k)(j+2+k))
           + 2(2j+3)Q(j,k+1)(j+k+1)/((k+1)(j+1-k)(j+k+2)(j+k+3)),
       Q(j,k) = 4j^2+12j-2k^2+3k+8
 (4) GOSPER CERTIFICATE (found by sympy gosper_sum on (3), then verified exactly):
       psi(j,k) = -(-1)^k * k*(2j+3)*P4(j,k)*sqrt(b)(j,k)
                   / ((j+1)(j+2)^2 (j-k+1)(j+k+1)(j+k+2))
       P4 = 8j^4 + 24j^3 k + 48j^3 + 31j^2 k^2 + 107j^2 k + 104j^2
            + 13j k^3 + 86j k^2 + 153j k + 96j + 18k^3 + 60k^2 + 70k + 32
     with  U(j,k) = psi(j,k+1) - psi(j,k)   for 0 <= k <= j-1,  psi(j,0) = 0
 (5) BOUNDARY identity (the k=j edge, where the certificate's (j-k+1)-pole
     compensates the vanishing binomial — same phenomenon as the denominator
     README's k in {j+1,j+2} boundary):
       psi(j,j) + U(j,j) + U(j,j+1) + U(j,j+2) = 0
 => Sum_k F_A(j,k) = 0.  QED-shape: per-k polynomial identities + telescoping +
    one boundary identity — the SAME mechanical shape as the denominator
    (AperyRecurrence reduced_wz_identity route).  Lean targets:
    AperyCollapsing bricks (landed) + cleared forms of (0),(3),(4),(5).

Run: python3 derive_numerator_certificate.py   (exact Fractions; ~1 min)
"""
from fractions import Fraction as Fr
from math import comb

def C(n, k): return comb(n, k) if 0 <= k <= n else 0
def b(n, k): return (C(n,k)*C(n+k,k))**2
def sqw(n, k): return C(n,k)*C(n+k,k)
def w(n, k): return Fr(1, C(n,k)*C(n+k,k))
def aL(j): return 34*j**3 + 153*j**2 + 231*j + 117
def Q(j, k): return 4*j**2 + 12*j - 2*k**2 + 3*k + 8
def Ghat(j, k): return -4*k**4*(2*j+3)*Q(j,k)*(C(j+2,k)*C(j+k,k))**2
def GB(j, k): return Fr(Ghat(j,k), (j+1)**2*(j+2)**2)

def H3(n): return sum(Fr(1, i**3) for i in range(1, n+1))
def kappa(n, k):
    return sum(Fr((-1)**(m-1), 2*m**3*comb(n,m)*comb(n+m,m)) for m in range(1, k+1))
def c(n, k): return H3(n) + kappa(n, k)

def Dn(n, k):
    if k > n-1: return None
    return Fr((-1)**k,1) * w(n,k) / (n**2*(n-k))
def dk(n, k):
    if not (1 <= k <= n): return None
    return Fr((-1)**(k-1),1) * w(n,k) / (2*k**3)

def U(j, k):
    total = Fr(0)
    if b(j,k) != 0:
        total += -Fr((j+1)**3,1) * b(j,k) * (Dn(j+1,k) + Dn(j+2,k))
    if b(j+1,k) != 0:
        total += Fr(aL(j),1) * b(j+1,k) * Dn(j+2,k)
    g = GB(j, k+1)
    if g != 0 and (1 <= k+1 <= j+2):
        total += -g * dk(j+2, k+1)
    return total

def u_closed(j, k):
    return (Fr(-(j+1), 1)/(j+1+k)
            - Fr((j+1)**3,1)*(j+1-k)/Fr((j+2)**2*(j+1+k)*(j+2+k),1)
            + Fr(aL(j),1)*(j+1+k)/Fr((j+2)**2*(j+1-k)*(j+2+k),1)
            + Fr(2*(2*j+3)*Q(j,k+1)*(j+k+1),1)/Fr((k+1)*(j+1-k)*(j+k+2)*(j+k+3),1))

def P4(j, k):
    return (8*j**4 + 24*j**3*k + 48*j**3 + 31*j**2*k**2 + 107*j**2*k + 104*j**2
            + 13*j*k**3 + 86*j*k**2 + 153*j*k + 96*j + 18*k**3 + 60*k**2 + 70*k + 32)

def psi(j, k):
    s = sqw(j, k)
    if s == 0: return Fr(0)
    return Fr(-((-1)**k) * k * (2*j+3) * P4(j,k) * s,
              (j+1) * (j+2)**2 * (j-k+1) * (j+k+1) * (j+k+2))

JMAX = 26
ok = {name: True for name in
      ("(1) decomposition", "(3) closed u", "(4) telescoping", "(5) boundary",
       "sumU=0", "recurrence")}

for j in range(1, JMAX):
    # (1)+(2) combined check: sum U == sum F_A  == 0  (F_A needs actual c-values)
    def term(n, k): return Fr(b(n,k),1)*c(n,k) if 0 <= k <= n else Fr(0)
    FAsum = sum(Fr((j+2)**3,1)*term(j+2,k) + Fr((j+1)**3,1)*term(j,k)
                - Fr(aL(j),1)*term(j+1,k) for k in range(0, j+3))
    if FAsum != 0: ok["recurrence"] = False
    if sum(U(j,k) for k in range(0, j+3)) != 0: ok["sumU=0"] = False
    # (1) per-k decomposition identity
    for k in range(0, j+3):
        FA = (Fr((j+2)**3,1)*term(j+2,k) + Fr((j+1)**3,1)*term(j,k)
              - Fr(aL(j),1)*term(j+1,k))
        FB = Fr((j+2)**3*b(j+2,k) + (j+1)**3*b(j,k) - aL(j)*b(j+1,k), 1)
        rhs = FB * c(j+2,k)
        if b(j,k) != 0:
            rhs += -Fr((j+1)**3,1)*b(j,k)*(Dn(j+1,k)+Dn(j+2,k))
        if b(j+1,k) != 0:
            rhs += Fr(aL(j),1)*b(j+1,k)*Dn(j+2,k)
        if FA != rhs: ok["(1) decomposition"] = False
    # (3) closed u
    for k in range(0, j+1):
        if sqw(j,k) == 0: continue
        if U(j,k) != Fr((-1)**k,1)*sqw(j,k)*u_closed(j,k):
            ok["(3) closed u"] = False
    # (4) telescoping below the edge
    for k in range(0, j):
        if U(j,k) != psi(j,k+1) - psi(j,k): ok["(4) telescoping"] = False
    # (5) boundary
    if psi(j,j) + U(j,j) + U(j,j+1) + U(j,j+2) != 0: ok["(5) boundary"] = False

for name, v in ok.items():
    print(f"{name}: {'HOLDS' if v else 'FAILS'}")
assert all(ok.values())
print(f"\nALL EXACT for j < {JMAX}: the numerator recurrence telescopes with the")
print("explicit certificate psi in the extended (b, sqrt(b), c) language.")

# ----------------------------------------------------------------------------
# THE REDUCED IDENTITIES (round-4 blueprint; each verified symbolically == 0
# with sympy, and numerically above).  Dividing everything by (-1)^k sqw(j,k):
#
#   phi(j,k) := -k(2j+3) P4(j,k) / ((j+1)(j+2)^2 (j-k+1)(j+k+1)(j+k+2))
#   rho(j,k) := sqw(j,k+1)/sqw(j,k) = (j-k)(j+k+1)/(k+1)^2      [sqw_shift_k]
#
#   R-NUM :  u(j,k) + rho(j,k)*phi(j,k+1) + phi(j,k)  ==  0
#            (common denominator (j+1)(j+2)^2(k+1)(j-k+1)(j+k+1)(j+k+2)(j+k+3);
#             the cleared numerator is IDENTICALLY the zero polynomial)
#   R-BND :  phi(j,j) + u(j,j) - T1(j)  ==  0
#            T1(j)     = 2(2j+1)(19j^2+58j+45)/((j+1)(j+2)^2)
#              [= U(j,j+1)*(-1)^(j+1)/sqw(j,j); piecewise:
#               aL-piece  = 2(2j+1)(17j^2+51j+39)/((j+1)(j+2)^2),
#               Ghat-piece = 2(2j+1)(2j+3)/((j+1)(j+2)) ]
#   R-NIL :  U(j,j+2) == 0 identically (C(j+2,j+3)=0 kills Ghat; b's vanish)
#
# Lean plan (mirror of AperyRecurrence's REDID route): clear denominators,
# substitute j = k+d (additive Nat form), prove by ring_nat on the
# AperyCollapsing bricks (sqw_shift_n/k for the contiguity reductions of u and
# T1's pieces); then sumTo telescoping + R-BND + R-NIL close Sum U = 0; with
# the collapsing laws (cleared) and the Abel step this closes Sum F_A = 0.
# ----------------------------------------------------------------------------
