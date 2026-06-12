import sympy as sp
from sympy import binomial, simplify, factor, expand
j,k=sp.symbols('j k', integer=True)
def C(n,m): return binomial(n,m)
def a(n,m): return C(n,m)**2*C(n+m,m)**2
aL=34*j**3+153*j**2+231*j+117
F=(j+2)**3*a(j+2,k)+(j+1)**3*a(j,k)-aL*a(j+1,k)
# cleared certificate Ghat(j,k) = -4 k^4 (2j+3)(4j^2+12j-2k^2+3k+8) C(j+2,k)^2 C(j+k,k)^2
def Ghat(kk):
    return -4*kk**4*(2*j+3)*(4*j**2+12*j-2*kk**2+3*kk+8)*C(j+2,kk)**2*C(j+kk,kk)**2
# claim: (j+1)^2 (j+2)^2 * F(j,k) = Ghat(k) - Ghat(k-1)
lhs=(j+1)**2*(j+2)**2*F
rhs=Ghat(k+1)-Ghat(k)
# numeric check over many (J,K)
import random
ok=True; bad=None
for _ in range(400):
    J=random.randint(0,14); K=random.randint(0,J+4)
    L=lhs.subs({j:J,k:K}); R=rhs.subs({j:J,k:K})
    if sp.simplify(L-R)!=0:
        ok=False; bad=(J,K,L,R); break
print("cleared telescoping identity holds (400 random pts):", ok, bad)
# boundary: Ghat(j,0)=0 and Ghat(j,k)=0 for k>j+2
b0=all(Ghat(0).subs(j,J)==0 for J in range(0,8))
btop=all(Ghat(K).subs(j,J)==0 for J in range(0,6) for K in range(J+3,J+6))
print("Ghat(j,0)=0:",b0,"  Ghat(j,k>j+2)=0:",btop)
