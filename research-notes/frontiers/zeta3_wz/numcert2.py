from fractions import Fraction as Fr
from math import comb
def b(n,k): return comb(n,k)**2*comb(n+k,k)**2 if 0<=k<=n else 0
def H3(n): return sum(Fr(1,j**3) for j in range(1,n+1))
def kap(n,k): return sum(Fr((-1)**(m-1), 2*m**3*comb(n,m)*comb(n+m,m)) for m in range(1,k+1)) if k>=0 else Fr(0)
def c(n,k): return H3(n)+kap(n,k)
def tA(n,k): return Fr(b(n,k))*c(n,k) if 0<=k<=n else Fr(0)
def aL(j): return 34*j**3+153*j**2+231*j+117
def LtA(j,k): return (j+2)**3*tA(j+2,k)+(j+1)**3*tA(j,k)-aL(j)*tA(j+1,k)
# scaled antidifference S_A(j,k) = sum_{i<k} (j+1)^2(j+2)^2 LtA(j,i)
# denominator certificate cert_B(j,k) (= G_B/b, found earlier)
def cert_B(j,k):
    return Fr(-4*k**4*(2*j+3)*(4*j*j+12*j-2*k*k+3*k+8), (j-k+1)**2*(j-k+2)**2) if (j-k+1)!=0 and (j-k+2)!=0 else None
for j in [4,5,6]:
    print(f"--- j={j} ---")
    S=Fr(0)
    for k in range(0,j+1):
        cb=cert_B(j,k)
        certA = S/Fr(b(j,k)) if b(j,k)!=0 else None
        diff = (certA - cb*c(j,k)) if (certA is not None and cb is not None) else None
        print(f"  k={k}: cert_A - cert_B*c = {diff}")
        S += (j+1)**2*(j+2)**2*LtA(j,k)
