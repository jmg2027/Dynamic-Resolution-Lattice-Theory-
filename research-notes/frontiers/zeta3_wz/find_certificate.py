from fractions import Fraction as Fr
from math import comb
import sympy as sp
j=sp.symbols('j')
def a(n,kk): return (comb(n,kk)*comb(n+kk,kk))**2 if 0<=kk<=n else 0
def aL(jj): return 34*jj**3+153*jj**2+231*jj+117
def F(jj,kk): return (jj+2)**3*a(jj+2,kk)+(jj+1)**3*a(jj,kk)-aL(jj)*a(jj+1,kk)
def cert(jj,kk):
    G=sum(F(jj,i) for i in range(0,kk)); ajk=a(jj,kk)
    return Fr(G,ajk) if ajk!=0 else None
from sympy import Rational, simplify, factor, interpolate
for K in [1,2,3,4]:
    xs=[]; ys=[]
    for J in range(K, K+14):
        c=cert(J,K)
        if c is None: continue
        xs.append(J); ys.append(Rational(c.numerator, c.denominator))
    # rational interpolation: try denominators of increasing degree
    found=None
    from sympy import symbols, solve, Poly
    for dn in range(1,7):
        for dd in range(1,7):
            if len(xs) < dn+dd+2: continue
            ncoef=symbols(f'n0:{dn+1}'); dcoef=symbols(f'd0:{dd+1}')
            num=lambda x: sum(ncoef[i]*x**i for i in range(dn+1))
            den=lambda x: sum(dcoef[i]*x**i for i in range(dd+1))+x**(dd+1)  # monic
            eqs=[num(X)-Y*den(X) for X,Y in zip(xs,ys)]
            sol=solve(eqs, list(ncoef)+list(dcoef), dict=True)
            if sol:
                s=sol[0]
                N=sum(s.get(ncoef[i],ncoef[i])*j**i for i in range(dn+1)).subs({c:0 for c in ncoef if c not in s})
                D=sum(s.get(dcoef[i],dcoef[i])*j**i for i in range(dd+1)).subs({c:0 for c in dcoef if c not in s})+j**(dd+1)
                # verify on held-out
                expr=N/D
                ok=all(simplify(expr.subs(j,X)-Y)==0 for X,Y in zip(xs,ys))
                if ok and N!=0:
                    found=(factor(N),factor(D)); break
        if found: break
    print(f"k={K}: cert(j,{K}) = ({found[0]}) / ({found[1]})" if found else f"k={K}: not found")
