import sympy as sp
from sympy import symbols, cancel, factor, fraction, together
from math import comb
j,k=symbols('j k')
# 1) recurrence holds on B-values
def b(N,K): return comb(N,K)**2*comb(N+K,K)**2 if 0<=K<=N else 0
B=[sum(b(N,K) for K in range(0,N+1)) for N in range(0,8)]
aL=lambda j:34*j**3+153*j**2+231*j+117
rec=all((j2+2)**3*B[j2+2]+(j2+1)**3*B[j2]==aL(j2)*B[j2+1] for j2 in range(0,6))
print("B =",B[:6])
print("recurrence (j+2)^3 B(j+2)+(j+1)^3 B(j) = aperyLead(j) B(j+1):",rec)
# 2) WZ combination sums to 0
sumF=[sum((j2+2)**3*b(j2+2,K)+(j2+1)**3*b(j2,K)-aL(j2)*b(j2+1,K) for K in range(0,j2+3)) for j2 in range(0,7)]
print("sum_k F(j,k) for j=0..6:",sumF)
# 3) R_F = F/a(j,k) as rational function (exact)
R_F=cancel((j+2)**3*((j+k+1)*(j+k+2))**2/((j+1-k)*(j+2-k))**2 + (j+1)**3
           -(34*j**3+153*j**2+231*j+117)*(j+k+1)**2/(j+1-k)**2)
num,den=fraction(together(R_F))
print("R_F numerator factored:",factor(num))
print("R_F denominator:",factor(den))
