# Numerator Apery numbers a_n (harmonic): verify recurrence, integrality, orbit bridge.
from fractions import Fraction as Fr
from math import comb, factorial, gcd
def H3(n): return sum(Fr(1,j**3) for j in range(1,n+1))
def cnk(n,k):
    s=H3(n)
    for m in range(1,k+1):
        s += Fr((-1)**(m-1), 2*m**3*comb(n,m)*comb(n+m,m))
    return s
def a(n): return sum(comb(n,k)**2*comb(n+k,k)**2*cnk(n,k) for k in range(0,n+1))
def lcm_to(n):
    l=1
    for i in range(1,n+1): l=l*i//gcd(l,i)
    return l
av=[a(n) for n in range(0,7)]
def L(n): return 34*n**3-51*n**2+27*n-5
print('a_n:', av)
print('recurrence n^3 a_n=(34n^3-51n^2+27n-5)a_{n-1}-(n-1)^3 a_{n-2}:',
      all(n**3*av[n]==L(n)*av[n-1]-(n-1)**3*av[n-2] for n in range(2,7)))
print('2 lcm^3 a_n integral:', all((2*lcm_to(n)**3*av[n]).denominator==1 for n in range(1,7)))
print('zeta3Num=(n!)^3 a_n:', [int(factorial(n)**3*av[n]) for n in range(0,6)])
