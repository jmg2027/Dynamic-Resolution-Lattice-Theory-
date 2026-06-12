from fractions import Fraction as Fr
from math import comb
def b(n,k): return comb(n,k)**2*comb(n+k,k)**2 if 0<=k<=n else 0
def kappa(n,k): return sum(Fr((-1)**(m-1), 2*m**3*comb(n,m)*comb(n+m,m)) for m in range(1,k+1)) if k>=0 else Fr(0)
def H3(n): return sum(Fr(1,j**3) for j in range(1,n+1))
def c(n,k): return H3(n)+kappa(n,k)         # the harmonic coefficient
def tA(n,k): return Fr(b(n,k))*c(n,k) if 0<=k<=n else Fr(0)   # numerator summand
def aL(j): return 34*j**3+153*j**2+231*j+117
# L[tA](j,k) = (j+2)^3 tA(j+2,k)+(j+1)^3 tA(j,k) - aL(j) tA(j+1,k)
def LtA(j,k): return (j+2)**3*tA(j+2,k)+(j+1)**3*tA(j,k)-aL(j)*tA(j+1,k)
# antidifference G_A(j,k) = sum_{i<k} LtA(j,i) ; cert_A = G_A / b(j,k)
for j in [4,5,6]:
    print(f"--- j={j} ---")
    G=Fr(0)
    for k in range(0,j+4):
        cert = G/Fr(b(j,k)) if b(j,k)!=0 else None
        print(f"  k={k}: cert_A=G/b = {cert}")
        G+=LtA(j,k)
    print(f"  final G={G} (should be 0)")
