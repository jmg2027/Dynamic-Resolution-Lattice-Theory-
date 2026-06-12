from fractions import Fraction as Fr
from math import comb
def b(n,k): return comb(n,k)**2*comb(n+k,k)**2 if 0<=k<=n else 0
def kap(n,k): return sum(Fr((-1)**(m-1), 2*m**3*comb(n,m)*comb(n+m,m)) for m in range(1,k+1)) if k>=0 else Fr(0)
def tK(n,k): return Fr(b(n,k))*kap(n,k) if 0<=k<=n else Fr(0)
def aL(j): return 34*j**3+153*j**2+231*j+117
def LtK(j,k): return (j+2)**3*tK(j+2,k)+(j+1)**3*tK(j,k)-aL(j)*tK(j+1,k)
def rhs(j,k): return Fr(b(j,k)-b(j+2,k))   # the inhomogeneous density (sums to B(j)-B(j+2))
# F_K(j,k) := LtK(j,k) - rhs(j,k) telescopes (sums to 0); cert_K = G_K/b(j,k)
for j in [4,5,6]:
    print(f"--- j={j} ---")
    G=Fr(0)
    for k in range(0,j+4):
        cert = G/Fr(b(j,k)) if b(j,k)!=0 else None
        print(f"  k={k}: cert_K = {cert}")
        G += LtK(j,k)-rhs(j,k)
    print(f"  final G={G}")
