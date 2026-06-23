# Q37 (dm2): Keystone avenue (c) nonsingularity certs via Bezout

This drop gives integer Bezout certificates for the two nonsingularity facts needed in the `Ψ₃ = 0` stratum.  Variables:

```text
b2, b4, b6, b8, x
```

Definitions:

```text
s    = 4*x**3 + b2*x**2 + 2*b4*x + b6
c3   = 3*x**4 + b2*x**3 + 3*b4*x**2 + 3*b6*x + b8
d4   = 2*x**6 + b2*x**5 + 5*b4*x**4 + 10*b6*x**3 + 10*b8*x**2
       + (b2*b8-b4*b6)*x + (b4*b8-b6**2)
Δ    = -b2**2*b8 - 8*b4**3 - 27*b6**2 + 9*b2*b4*b6
bRel = b2*b6 - b4**2 - 4*b8
```

The two identities verified below are

```text
A23*s  + B23*c3 - (-Δ**2) - Q23*bRel = 0
A34*c3 + B34*d4 - Δ**4   - Q34*bRel = 0
```

All coefficients are integers.

## Method / order used

I used the Sylvester matrix over `ZZ[b2,b4,b6,b8]`, not fraction-field `gcdex`.  For `f,g ∈ ZZ[b2,b4,b6,b8][x]`, the script builds the Sylvester coefficient matrix `M` for `A*f + B*g` with `deg_x A < deg_x g` and `deg_x B < deg_x f`.  It solves `M*u = e_last` by SymPy's fraction-free `DomainMatrix.solve_den(..., method='charpoly')`.  The denominator is asserted to be exactly `resultant(f,g,x)`, hence the numerator vector is the integer adjugate-column vector giving `A*f+B*g = resultant(f,g,x)`.

Then the script divides the difference from `-Δ²` or `Δ⁴` by `bRel` and asserts the final identities.  It also asserts every coefficient denominator is `1`.

## Self-contained SymPy script

```python
import sympy as sp
from sympy.polys.matrices import DomainMatrix
from sympy.polys.domains import ZZ

b2,b4,b6,b8,x=sp.symbols('b2 b4 b6 b8 x')
K=ZZ.old_poly_ring(b2,b4,b6,b8)

def Ksym(a):
    return K.from_sympy(sp.sympify(a))

def to_sym(a):
    return K.to_sympy(a)

def sylvester_bezout(f, g):
    """Return A,B,R with A*f+B*g=resultant(f,g,x), using a Sylvester system.
    f has degree m and g degree n; deg_x A < n and deg_x B < m.
    """
    m=sp.Poly(f,x).degree(); n=sp.Poly(g,x).degree()
    N=m+n
    def coeff_desc(poly, deg):
        P=sp.Poly(poly,x)
        return [P.coeff_monomial(x**e) for e in range(deg,-1,-1)]
    cols=[]
    for i in range(n):
        cols.append(coeff_desc(x**(n-1-i)*f, N-1))
    for j in range(m):
        cols.append(coeff_desc(x**(m-1-j)*g, N-1))
    M=DomainMatrix([[Ksym(cols[c][r]) for c in range(N)] for r in range(N)], (N,N), K)
    rhs=DomainMatrix([[Ksym(0)] for _ in range(N-1)] + [[Ksym(1)]], (N,1), K)
    xnum,xden=M.solve_den(rhs, method='charpoly')
    R=sp.resultant(f,g,x)
    assert sp.expand(to_sym(xden)-R)==0
    sol=[sp.expand(xnum.to_Matrix()[i,0]) for i in range(N)]
    A=sp.expand(sum(sol[i]*x**(n-1-i) for i in range(n)))
    B=sp.expand(sum(sol[n+j]*x**(m-1-j) for j in range(m)))
    assert sp.expand(A*f+B*g-R)==0
    return A,B,R

s=4*x**3+b2*x**2+2*b4*x+b6
c3=3*x**4+b2*x**3+3*b4*x**2+3*b6*x+b8
d4=2*x**6+b2*x**5+5*b4*x**4+10*b6*x**3+10*b8*x**2+(b2*b8-b4*b6)*x+(b4*b8-b6**2)
Delta=-b2**2*b8-8*b4**3-27*b6**2+9*b2*b4*b6
bRel=b2*b6-b4**2-4*b8

A23,B23,R23=sylvester_bezout(s,c3)
Q23,Rrem=sp.div(sp.expand(A23*s+B23*c3+Delta**2), bRel, b8)
Q23=sp.expand(Q23)
assert Rrem==0
assert sp.expand(A23*s+B23*c3 - (-Delta**2) - Q23*bRel)==0

A34,B34,R34=sylvester_bezout(c3,d4)
Q34,Rrem=sp.div(sp.expand(A34*c3+B34*d4-Delta**4), bRel, b8)
Q34=sp.expand(Q34)
assert Rrem==0
assert sp.expand(A34*c3+B34*d4 - Delta**4 - Q34*bRel)==0

for name,expr in [('A23',A23),('B23',B23),('Q23',Q23),('A34',A34),('B34',B34),('Q34',Q34)]:
    P=sp.Poly(expr, x,b2,b4,b6,b8, domain=sp.QQ)
    assert all(c.q==1 for _,c in P.terms())
    print(f'{name} = {sp.sstr(expr)}')
    print()
print('OK')
```

## Printed cofactors and verification output

```text
A23 = -2*b2**4*b6*x**2 + b2**4*b8*x + 2*b2**3*b4**2*x**2 - 7*b2**3*b4*b6*x + b2**3*b4*b8 - 4*b2**3*b6**2 - 6*b2**3*b6*x**3 - b2**3*b8*x**2 + 6*b2**2*b4**3*x + 3*b2**2*b4**2*b6 + 6*b2**2*b4**2*x**3 + 81*b2**2*b4*b6*x**2 - 50*b2**2*b4*b8*x - 3*b2**2*b6**2*x - 7*b2**2*b6*b8 - 12*b2**2*b8*x**3 - 72*b2*b4**3*x**2 + 288*b2*b4**2*b6*x - 36*b2*b4**2*b8 + 162*b2*b4*b6**2 + 252*b2*b4*b6*x**3 - 351*b2*b6**2*x**2 + 168*b2*b6*b8*x - 16*b2*b8**2 - 216*b4**4*x - 108*b4**3*b6 - 216*b4**3*x**3 + 108*b4**2*b6*x**2 + 432*b4**2*b8*x - 1134*b4*b6**2*x + 432*b4*b6*b8 + 288*b4*b8*x**3 - 729*b6**3 - 972*b6**2*x**3 + 432*b6*b8*x**2 - 192*b8**2*x

B23 = 2*b2**4*b6*x - b2**4*b8 - 2*b2**3*b4**2*x + 5*b2**3*b4*b6 + 8*b2**3*b6*x**2 - 4*b2**2*b4**3 - 8*b2**2*b4**2*x**2 - 80*b2**2*b4*b6*x + 48*b2**2*b4*b8 + b2**2*b6**2 + 16*b2**2*b8*x**2 + 72*b2*b4**3*x - 204*b2*b4**2*b6 - 336*b2*b4*b6*x**2 + 32*b2*b4*b8*x + 360*b2*b6**2*x - 176*b2*b6*b8 + 144*b4**4 + 288*b4**3*x**2 - 144*b4**2*b6*x - 384*b4**2*b8 + 864*b4*b6**2 - 384*b4*b8*x**2 + 1296*b6**2*x**2 - 576*b6*b8*x + 256*b8**2

Q23 = -12*b2**2*b4*b8 - 4*b2**2*b6**2 + 80*b2*b4**2*b6 + 32*b2*b6*b8 - 64*b4**4 + 112*b4**2*b8 - 324*b4*b6**2 - 64*b8**2

A34 = b2**8*b8**3 + b2**8*b8**2*x**4 - 3*b2**7*b4*b6*b8**2 - 2*b2**7*b4*b6*b8*x**4 + 4*b2**7*b4*b8**2*x**3 + b2**7*b6**2*b8*x**3 + 10*b2**7*b6*b8**2*x**2 + 9*b2**7*b8**3*x + 2*b2**7*b8**2*x**5 + 3*b2**6*b4**2*b6**2*b8 + b2**6*b4**2*b6**2*x**4 - 9*b2**6*b4**2*b6*b8*x**3 - 4*b2**6*b4**2*b8**2*x**2 - b2**6*b4*b6**3*x**3 - 17*b2**6*b4*b6**2*b8*x**2 - 25*b2**6*b4*b6*b8**2*x - 4*b2**6*b4*b6*b8*x**5 - 111*b2**6*b4*b8**3 - 102*b2**6*b4*b8**2*x**4 + b2**6*b6**4*x**2 + 7*b2**6*b6**3*b8*x - 27*b2**6*b6**2*b8**2 - 34*b2**6*b6**2*b8*x**4 + 7*b2**6*b6*b8**2*x**3 + 10*b2**6*b8**3*x**2 - b2**5*b4**3*b6**3 + 5*b2**5*b4**3*b6**2*x**3 + 5*b2**5*b4**3*b6*b8*x**2 + 2*b2**5*b4**3*b8**2*x + 5*b2**5*b4**2*b6**3*x**2 + 12*b2**5*b4**2*b6**2*b8*x + 2*b2**5*b4**2*b6**2*x**5 + 424*b2**5*b4**2*b6*b8**2 + 300*b2**5*b4**2*b6*b8*x**4 - 415*b2**5*b4**2*b8**2*x**3 - 5*b2**5*b4*b6**4*x + 25*b2**5*b4*b6**3*b8 + 16*b2**5*b4*b6**3*x**4 - 256*b2**5*b4*b6**2*b8*x**3 - 1047*b2**5*b4*b6*b8**2*x**2 - 880*b2**5*b4*b8**3*x - 200*b2**5*b4*b8**2*x**5 + 7*b2**5*b6**5 - 22*b2**5*b6**4*x**3 - 316*b2**5*b6**3*b8*x**2 - 274*b2**5*b6**2*b8**2*x - 72*b2**5*b6**2*b8*x**5 + 864*b2**5*b6*b8**3 + 734*b2**5*b6*b8**2*x**4 - 92*b2**5*b8**3*x**3 - 78*b2**4*b4**4*b8**2 - 72*b2**4*b4**4*b8*x**4 - 456*b2**4*b4**3*b6**2*b8 - 162*b2**4*b4**3*b6**2*x**4 + 1334*b2**4*b4**3*b6*b8*x**3 + 385*b2**4*b4**3*b8**2*x**2 - 18*b2**4*b4**2*b6**4 + 252*b2**4*b4**2*b6**3*x**3 + 2840*b2**4*b4**2*b6**2*b8*x**2 + 3098*b2**4*b4**2*b6*b8**2*x + 596*b2**4*b4**2*b6*b8*x**5 + 3760*b2**4*b4**2*b8**3 + 3062*b2**4*b4**2*b8**2*x**4 - 84*b2**4*b4*b6**4*x**2 - 258*b2**4*b4*b6**3*b8*x + 36*b2**4*b4*b6**3*x**5 - 2290*b2**4*b4*b6**2*b8**2 - 468*b2**4*b4*b6**2*b8*x**4 + 3176*b2**4*b4*b6*b8**2*x**3 - 1084*b2**4*b4*b8**3*x**2 - 165*b2**4*b6**5*x + 693*b2**4*b6**4*b8 + 519*b2**4*b6**4*x**4 + 223*b2**4*b6**3*b8*x**3 + 7260*b2**4*b6**2*b8**2*x**2 + 5720*b2**4*b6*b8**3*x + 1440*b2**4*b6*b8**2*x**5 - 1632*b2**4*b8**4 - 808*b2**4*b8**3*x**4 + 126*b2**3*b4**5*b6*b8 + 54*b2**3*b4**5*b6*x**4 - 306*b2**3*b4**5*b8*x**3 + 162*b2**3*b4**4*b6**3 - 864*b2**3*b4**4*b6**2*x**3 - 1572*b2**3*b4**4*b6*b8*x**2 - 705*b2**3*b4**4*b8**2*x - 144*b2**3*b4**4*b8*x**5 - 756*b2**3*b4**3*b6**3*x**2 - 2112*b2**3*b4**3*b6**2*b8*x - 324*b2**3*b4**3*b6**2*x**5 - 14034*b2**3*b4**3*b6*b8**2 - 9384*b2**3*b4**3*b6*b8*x**4 + 12176*b2**3*b4**3*b8**2*x**3 + 846*b2**3*b4**2*b6**4*x + 2511*b2**3*b4**2*b6**3*b8 - 513*b2**3*b4**2*b6**3*x**4 + 729*b2**3*b4**2*b6**2*b8*x**3 + 31940*b2**3*b4**2*b6*b8**2*x**2 + 25048*b2**3*b4**2*b8**3*x + 5792*b2**3*b4**2*b8**2*x**5 - 1422*b2**3*b4*b6**5 + 3357*b2**3*b4*b6**4*x**3 - 5541*b2**3*b4*b6**3*b8*x**2 - 4872*b2**3*b4*b6**2*b8**2*x - 648*b2**3*b4*b6**2*b8*x**5 - 43432*b2**3*b4*b6*b8**3 - 37632*b2**3*b4*b6*b8**2*x**4 + 2400*b2**3*b4*b8**3*x**3 + 6075*b2**3*b6**5*x**2 + 6114*b2**3*b6**4*b8*x + 1134*b2**3*b6**4*x**5 - 7432*b2**3*b6**3*b8**2 - 8502*b2**3*b6**3*b8*x**4 + 1092*b2**3*b6**2*b8**2*x**3 - 2992*b2**3*b6*b8**3*x**2 - 5264*b2**3*b8**4*x - 1152*b2**3*b8**3*x**5 - 54*b2**2*b4**6*b6**2 + 270*b2**2*b4**6*b6*x**3 + 270*b2**2*b4**6*b8*x**2 + 270*b2**2*b4**5*b6**2*x**2 + 720*b2**2*b4**5*b6*b8*x + 108*b2**2*b4**5*b6*x**5 + 3663*b2**2*b4**5*b8**2 + 3024*b2**2*b4**5*b8*x**4 - 270*b2**2*b4**4*b6**3*x + 13410*b2**2*b4**4*b6**2*b8 + 5238*b2**2*b4**4*b6**2*x**4 - 40401*b2**2*b4**4*b6*b8*x**3 - 11694*b2**2*b4**4*b8**2*x**2 + 1107*b2**2*b4**3*b6**4 - 9423*b2**2*b4**3*b6**3*x**3 - 87183*b2**2*b4**3*b6**2*b8*x**2 - 88896*b2**2*b4**3*b6*b8**2*x - 18144*b2**2*b4**3*b6*b8*x**5 - 39944*b2**2*b4**3*b8**3 - 22656*b2**2*b4**3*b8**2*x**4 + 189*b2**2*b4**2*b6**4*x**2 + 702*b2**2*b4**2*b6**3*b8*x - 1674*b2**2*b4**2*b6**3*x**5 + 200916*b2**2*b4**2*b6**2*b8**2 + 117450*b2**2*b4**2*b6**2*b8*x**4 - 180648*b2**2*b4**2*b6*b8**2*x**3 + 35568*b2**2*b4**2*b8**3*x**2 + 5994*b2**2*b4*b6**5*x - 26406*b2**2*b4*b6**4*b8 - 18792*b2**2*b4*b6**4*x**4 - 50220*b2**2*b4*b6**3*b8*x**3 - 390492*b2**2*b4*b6**2*b8**2*x**2 - 285184*b2**2*b4*b6*b8**3*x - 74304*b2**2*b4*b6*b8**2*x**5 + 88816*b2**2*b4*b8**4 + 41216*b2**2*b4*b8**3*x**4 + 1944*b2**2*b6**6 - 6075*b2**2*b6**5*x**3 - 75816*b2**2*b6**4*b8*x**2 - 71352*b2**2*b6**3*b8**2*x - 17496*b2**2*b6**3*b8*x**5 + 179888*b2**2*b6**2*b8**3 + 149832*b2**2*b6**2*b8**2*x**4 - 30224*b2**2*b6*b8**3*x**3 - 5600*b2**2*b8**4*x**2 - 5103*b2*b4**6*b6*b8 - 2187*b2*b4**6*b6*x**4 + 12393*b2*b4**6*b8*x**3 - 5346*b2*b4**5*b6**3 + 28917*b2*b4**5*b6**2*x**3 + 57591*b2*b4**5*b6*b8*x**2 + 25272*b2*b4**5*b8**2*x + 5832*b2*b4**5*b8*x**5 + 24543*b2*b4**4*b6**3*x**2 + 71523*b2*b4**4*b6**2*b8*x + 10692*b2*b4**4*b6**2*x**5 + 48600*b2*b4**4*b6*b8**2 - 2430*b2*b4**4*b6*b8*x**4 - 71604*b2*b4**4*b8**2*x**3 - 28188*b2*b4**3*b6**4*x - 211410*b2*b4**3*b6**3*b8 - 28188*b2*b4**3*b6**3*x**4 + 511272*b2*b4**3*b6**2*b8*x**3 - 220104*b2*b4**3*b6*b8**2*x**2 - 157248*b2*b4**3*b8**3*x - 36288*b2*b4**3*b8**2*x**5 + 45684*b2*b4**2*b6**5 - 64395*b2*b4**2*b6**4*x**3 + 1193076*b2*b4**2*b6**3*b8*x**2 + 959256*b2*b4**2*b6**2*b8**2*x + 227232*b2*b4**2*b6**2*b8*x**5 + 103824*b2*b4**2*b6*b8**3 + 133920*b2*b4**2*b6*b8**2*x**4 + 85680*b2*b4**2*b8**3*x**3 - 270459*b2*b4*b6**5*x**2 - 170424*b2*b4*b6**4*b8*x - 40824*b2*b4*b6**4*x**5 - 756648*b2*b4*b6**3*b8**2 - 444528*b2*b4*b6**3*b8*x**4 + 808272*b2*b4*b6**2*b8**2*x**3 + 127344*b2*b4*b6*b8**3*x**2 + 244608*b2*b4*b8**4*x + 56448*b2*b4*b8**3*x**5 - 45927*b2*b6**6*x + 188568*b2*b6**5*b8 + 144342*b2*b6**5*x**4 - 972*b2*b6**4*b8*x**3 + 1469664*b2*b6**3*b8**2*x**2 + 1082928*b2*b6**2*b8**3*x + 295488*b2*b6**2*b8**2*x**5 - 639744*b2*b6*b8**4 - 327264*b2*b6*b8**3*x**4 + 53312*b2*b8**4*x**3 + 2187*b4**7*b6**2 - 10935*b4**7*b6*x**3 - 10935*b4**7*b8*x**2 - 10935*b4**6*b6**2*x**2 - 29160*b4**6*b6*b8*x - 4374*b4**6*b6*x**5 - 20412*b4**6*b8**2 - 4374*b4**6*b8*x**4 + 10935*b4**5*b6**3*x + 46899*b4**5*b6**2*b8 + 4374*b4**5*b6**2*x**4 - 57348*b4**5*b6*b8*x**3 + 102060*b4**5*b8**2*x**2 + 6561*b4**4*b6**4 - 91854*b4**4*b6**3*x**3 - 356238*b4**4*b6**2*b8*x**2 - 9072*b4**4*b6*b8**2*x - 25272*b4**4*b6*b8*x**5 + 190512*b4**4*b8**3 + 40824*b4**4*b8**2*x**4 - 28431*b4**3*b6**4*x**2 - 375192*b4**3*b6**3*b8*x - 34992*b4**3*b6**3*x**5 - 666360*b4**3*b6**2*b8**2 - 89424*b4**3*b6**2*b8*x**4 + 674352*b4**3*b6*b8**2*x**3 - 317520*b4**3*b8**3*x**2 + 148716*b4**2*b6**5*x + 983664*b4**2*b6**4*b8 + 56862*b4**2*b6**4*x**4 - 2118960*b4**2*b6**3*b8*x**3 + 2036448*b4**2*b6**2*b8**2*x**2 + 903168*b4**2*b6*b8**3*x + 284256*b4**2*b6*b8**2*x**5 - 592704*b4**2*b8**4 - 127008*b4**2*b8**3*x**4 - 308367*b4*b6**6 + 734832*b4*b6**5*x**3 - 4639356*b4*b6**4*b8*x**2 - 3251664*b4*b6**3*b8**2*x - 886464*b4*b6**3*b8*x**5 + 1553328*b4*b6**2*b8**3 + 235872*b4*b6**2*b8**2*x**4 - 1213632*b4*b6*b8**3*x**3 + 329280*b4*b8**4*x**2 + 1614006*b6**6*x**2 + 1259712*b6**5*b8*x + 314928*b6**5*x**5 - 400464*b6**4*b8**2 - 52488*b6**4*b8*x**4 - 38880*b6**3*b8**2*x**3 - 2558304*b6**2*b8**3*x**2 - 1843968*b6*b8**4*x - 508032*b6*b8**3*x**5 + 614656*b8**5 + 131712*b8**4*x**4

B34 = -b2**8*b8**2*x**2 + 2*b2**7*b4*b6*b8*x**2 - 2*b2**7*b4*b8**2*x - b2**7*b6**2*b8*x - 3*b2**7*b6*b8**2 - 3*b2**7*b8**2*x**3 - b2**6*b4**2*b6**2*x**2 + 5*b2**6*b4**2*b6*b8*x + 2*b2**6*b4**2*b8**2 + b2**6*b4*b6**3*x + 5*b2**6*b4*b6**2*b8 + 6*b2**6*b4*b6*b8*x**3 + 103*b2**6*b4*b8**2*x**2 - b2**6*b6**4 + 33*b2**6*b6**2*b8*x**2 - 7*b2**6*b6*b8**2*x - 9*b2**6*b8**3 - 3*b2**5*b4**3*b6**2*x - 3*b2**5*b4**3*b6*b8 - 3*b2**5*b4**2*b6**2*x**3 - 301*b2**5*b4**2*b6*b8*x**2 + 214*b2**5*b4**2*b8**2*x - 15*b2**5*b4*b6**3*x**2 + 186*b2**5*b4*b6**2*b8*x + 356*b2**5*b4*b6*b8**2 + 300*b2**5*b4*b8**2*x**3 + 21*b2**5*b6**4*x + 67*b2**5*b6**3*b8 + 108*b2**5*b6**2*b8*x**3 - 741*b2**5*b6*b8**2*x**2 + 80*b2**5*b8**3*x + 72*b2**4*b4**4*b8*x**2 + 162*b2**4*b4**3*b6**2*x**2 - 738*b2**4*b4**3*b6*b8*x - 216*b2**4*b4**3*b8**2 - 216*b2**4*b4**2*b6**3*x - 900*b2**4*b4**2*b6**2*b8 - 894*b2**4*b4**2*b6*b8*x**3 - 3145*b2**4*b4**2*b8**2*x**2 + 162*b2**4*b4*b6**4 - 54*b2**4*b4*b6**3*x**3 + 540*b2**4*b4*b6**2*b8*x**2 - 1644*b2**4*b4*b6*b8**2*x + 800*b2**4*b4*b8**3 - 495*b2**4*b6**4*x**2 - 273*b2**4*b6**3*b8*x - 2238*b2**4*b6**2*b8**2 - 2160*b2**4*b6*b8**2*x**3 + 924*b2**4*b8**3*x**2 - 54*b2**3*b4**5*b6*x**2 + 162*b2**3*b4**5*b8*x + 540*b2**3*b4**4*b6**2*x + 756*b2**3*b4**4*b6*b8 + 216*b2**3*b4**4*b8*x**3 - 54*b2**3*b4**3*b6**3 + 486*b2**3*b4**3*b6**2*x**3 + 9540*b2**3*b4**3*b6*b8*x**2 - 6360*b2**3*b4**3*b8**2*x + 351*b2**3*b4**2*b6**3*x**2 - 1593*b2**3*b4**2*b6**2*b8*x - 11934*b2**3*b4**2*b6*b8**2 - 8688*b2**3*b4**2*b8**2*x**3 - 2079*b2**3*b4*b6**4*x + 3519*b2**3*b4*b6**3*b8 + 972*b2**3*b4*b6**2*b8*x**3 + 37872*b2**3*b4*b6*b8**2*x**2 - 2944*b2**3*b4*b8**3*x - 2187*b2**3*b6**5 - 1701*b2**3*b6**4*x**3 + 8379*b2**3*b6**3*b8*x**2 - 1116*b2**3*b6**2*b8**2*x - 824*b2**3*b6*b8**3 + 1728*b2**3*b8**3*x**3 - 162*b2**2*b4**6*b6*x - 162*b2**2*b4**6*b8 - 162*b2**2*b4**5*b6*x**3 - 3078*b2**2*b4**5*b8*x**2 - 5184*b2**2*b4**4*b6**2*x**2 + 22329*b2**2*b4**4*b6*b8*x + 7065*b2**2*b4**4*b8**2 + 7695*b2**2*b4**3*b6**3*x + 27513*b2**2*b4**3*b6**2*b8 + 27216*b2**2*b4**3*b6*b8*x**3 + 24912*b2**2*b4**3*b8**2*x**2 - 4374*b2**2*b4**2*b6**4 + 2511*b2**2*b4**2*b6**3*x**3 - 119367*b2**2*b4**2*b6**2*b8*x**2 + 101736*b2**2*b4**2*b6*b8**2*x - 22104*b2**2*b4**2*b8**3 + 17982*b2**2*b4*b6**4*x**2 + 35640*b2**2*b4*b6**3*b8*x + 132516*b2**2*b4*b6**2*b8**2 + 111456*b2**2*b4*b6*b8**2*x**3 - 47712*b2**2*b4*b8**3*x**2 + 5832*b2**2*b6**5*x + 15066*b2**2*b6**4*b8 + 26244*b2**2*b6**3*b8*x**3 - 150876*b2**2*b6**2*b8**2*x**2 + 27024*b2**2*b6*b8**3*x + 5264*b2**2*b8**4 + 2187*b2*b4**6*b6*x**2 - 6561*b2*b4**6*b8*x - 18225*b2*b4**5*b6**2*x - 26973*b2*b4**5*b6*b8 - 8748*b2*b4**5*b8*x**3 + 2187*b2*b4**4*b6**3 - 16038*b2*b4**4*b6**2*x**3 - 2673*b2*b4**4*b6*b8*x**2 + 35964*b2*b4**4*b8**2*x + 33534*b2*b4**3*b6**3*x**2 - 277992*b2*b4**3*b6**2*b8*x + 84888*b2*b4**3*b6*b8**2 + 54432*b2*b4**3*b8**2*x**3 + 18954*b2*b4**2*b6**4*x - 404838*b2*b4**2*b6**3*b8 - 340848*b2*b4**2*b6**2*b8*x**3 - 129816*b2*b4**2*b6*b8**2*x**2 - 33264*b2*b4**2*b8**3*x + 118098*b2*b4*b6**5 + 61236*b2*b4*b6**4*x**3 + 445176*b2*b4*b6**3*b8*x**2 - 488592*b2*b4*b6**2*b8**2*x - 3024*b2*b4*b6*b8**3 - 84672*b2*b4*b8**3*x**3 - 137781*b2*b6**5*x**2 - 11664*b2*b6**4*b8*x - 441288*b2*b6**3*b8**2 - 443232*b2*b6**2*b8**2*x**3 + 363888*b2*b6*b8**3*x**2 - 47040*b2*b8**4*x + 6561*b4**7*b6*x + 6561*b4**7*b8 + 6561*b4**6*b6*x**3 + 6561*b4**6*b8*x**2 - 6561*b4**5*b6**2*x**2 + 29160*b4**5*b6*b8*x - 61236*b4**5*b8**2 + 59049*b4**4*b6**3*x + 181521*b4**4*b6**2*b8 + 37908*b4**4*b6*b8*x**3 - 61236*b4**4*b8**2*x**2 - 39366*b4**3*b6**4 + 52488*b4**3*b6**3*x**3 + 134136*b4**3*b6**2*b8*x**2 - 371952*b4**3*b6*b8**2*x + 190512*b4**3*b8**3 - 85293*b4**2*b6**4*x**2 + 1183896*b4**2*b6**3*b8*x - 818424*b4**2*b6**2*b8**2 - 426384*b4**2*b6*b8**2*x**3 + 190512*b4**2*b8**3*x**2 - 393660*b4*b6**5*x + 1522152*b4*b6**4*b8 + 1329696*b4*b6**3*b8*x**3 - 353808*b4*b6**2*b8**2*x**2 + 677376*b4*b6*b8**3*x - 197568*b4*b8**4 - 531441*b6**6 - 472392*b6**5*x**3 + 78732*b6**4*b8*x**2 + 58320*b6**3*b8**2*x + 789264*b6**2*b8**3 + 762048*b6*b8**3*x**3 - 197568*b8**4*x**2

Q34 = 30*b2**6*b4*b8**3 + 3*b2**6*b6**2*b8**2 - 477*b2**5*b4**2*b6*b8**2 - 6*b2**5*b4*b6**3*b8 + b2**5*b6**5 - 114*b2**5*b6*b8**3 + 384*b2**4*b4**4*b8**2 + 2912*b2**4*b4**3*b6**2*b8 + b2**4*b4**2*b6**4 - 1242*b2**4*b4**2*b8**3 + 2628*b2**4*b4*b6**2*b8**2 - 56*b2**4*b6**4*b8 + 408*b2**4*b8**4 - 4864*b2**3*b4**5*b6*b8 - 6560*b2**3*b4**4*b6**3 + 10544*b2**3*b4**3*b6*b8**2 - 25252*b2**3*b4**2*b6**3*b8 - 162*b2**3*b4*b6**5 + 5184*b2**3*b4*b6*b8**3 - 1667*b2**3*b6**3*b8**2 + 2048*b2**2*b4**7*b8 + 16768*b2**2*b4**6*b6**2 - 8030*b2**2*b4**5*b8**2 - 5484*b2**2*b4**4*b6**2*b8 + 78624*b2**2*b4**3*b6**4 + 21392*b2**2*b4**3*b8**3 - 84711*b2**2*b4**2*b6**2*b8**2 + 70956*b2**2*b4*b6**4*b8 - 23520*b2**2*b4*b8**4 + 2187*b2**2*b6**6 - 13276*b2**2*b6**2*b8**3 - 14336*b2*b4**8*b6 + 40960*b2*b4**6*b6*b8 - 131328*b2*b4**5*b6**3 - 72789*b2*b4**4*b6*b8**2 + 284688*b2*b4**3*b6**3*b8 - 347733*b2*b4**2*b6**5 + 3416*b2*b4**2*b6*b8**3 + 139968*b2*b4*b6**3*b8**2 - 83106*b2*b6**5*b8 + 121520*b2*b6*b8**4 + 4096*b4**10 - 16384*b4**8*b8 + 55296*b4**7*b6**2 + 58975*b4**6*b8**2 - 216810*b4**5*b6**2*b8 + 279936*b4**4*b6**4 - 154252*b4**4*b8**3 + 577584*b4**3*b6**2*b8**2 - 905418*b4**2*b6**4*b8 + 235984*b4**2*b8**4 + 590490*b4*b6**6 - 635040*b4*b6**2*b8**3 + 297432*b6**4*b8**2 - 153664*b8**5

OK
```

## Lean proof shape

The definitions `q37A23`, `q37B23`, `q37Q23`, `q37A34`, `q37B34`, and `q37Q34` should be the direct `C`/`X` lifts of the six expanded expressions above.  I generated those mechanically as terms of the form `C ((n : R) * W.b₂^i * W.b₄^j * W.b₆^k * W.b₈^l) * X^m`; the two proof terms below are the intended replacement for the CAS identities.

```lean
import Mathlib

noncomputable section

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

-- Fill these six definitions by C/X-lifting the printed A23,B23,Q23,A34,B34,Q34 above.
-- Example term translation:
--   -2*b2**4*b6*x**2  ↦  C ((-2 : R) * W.b₂ ^ 4 * W.b₆) * X ^ 2
-- Constant b-polynomials are lifted as `C (...)`.
def q37A23 (W : WeierstrassCurve R) : R[X] := by
  exact 0 -- replace by A23 C/X lift

def q37B23 (W : WeierstrassCurve R) : R[X] := by
  exact 0 -- replace by B23 C/X lift

def q37Q23 (W : WeierstrassCurve R) : R[X] := by
  exact 0 -- replace by Q23 C/X lift

def q37A34 (W : WeierstrassCurve R) : R[X] := by
  exact 0 -- replace by A34 C/X lift

def q37B34 (W : WeierstrassCurve R) : R[X] := by
  exact 0 -- replace by B34 C/X lift

def q37Q34 (W : WeierstrassCurve R) : R[X] := by
  exact 0 -- replace by Q34 C/X lift

lemma q37_Ψ₂Sq_Ψ₃_bezout (W : WeierstrassCurve R) :
    q37A23 W * W.Ψ₂Sq + q37B23 W * W.Ψ₃ = C (- W.Δ ^ 2) := by
  -- With the definitions filled above, this is exactly the first SymPy assertion.
  linear_combination (norm := ring_nf [q37A23, q37B23, q37Q23,
      WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.Δ])
    q37Q23 W * (congrArg (fun t : R => (C t : R[X])) W.b_relation)

lemma q37_Ψ₃_preΨ₄_bezout (W : WeierstrassCurve R) :
    q37A34 W * W.Ψ₃ + q37B34 W * (W.preΨ 4) = C (W.Δ ^ 4) := by
  -- If `(W.preΨ 4)` has a local closed-form simp lemma, add it to this list.
  linear_combination (norm := ring_nf [q37A34, q37B34, q37Q34,
      WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ, WeierstrassCurve.Δ])
    q37Q34 W * (congrArg (fun t : R => (C t : R[X])) W.b_relation)

variable {k : Type*} [Field k] (W : WeierstrassCurve k) (x : k)

theorem Ψ₂Sq_eval_ne_of_Ψ₃_eval_zero_of_isElliptic [W.IsElliptic]
    (hc3 : W.Ψ₃.eval x = 0) : W.Ψ₂Sq.eval x ≠ 0 := by
  intro hs
  have hbez := congrArg (fun p : k[X] => p.eval x) (q37_Ψ₂Sq_Ψ₃_bezout (W := W))
  have hneg : - W.Δ ^ 2 = 0 := by
    simpa [Polynomial.eval_add, Polynomial.eval_mul, hs, hc3] using hbez.symm
  have hΔ2 : W.Δ ^ 2 = 0 := by simpa using neg_eq_zero.mp hneg
  have hΔ : W.Δ = 0 := pow_eq_zero hΔ2
  exact (WeierstrassCurve.isUnit_Δ (W := W)).ne_zero hΔ

theorem Ψ₃_eval_ne_of_Ψ₂Sq_eval_zero_of_isElliptic [W.IsElliptic]
    (hs : W.Ψ₂Sq.eval x = 0) : W.Ψ₃.eval x ≠ 0 := by
  intro hc3
  exact (Ψ₂Sq_eval_ne_of_Ψ₃_eval_zero_of_isElliptic (W := W) (x := x) hc3) hs

theorem preΨ₄_eval_ne_of_Ψ₃_eval_zero_of_isElliptic [W.IsElliptic]
    (hc3 : W.Ψ₃.eval x = 0) : (W.preΨ 4).eval x ≠ 0 := by
  intro h4
  have hbez := congrArg (fun p : k[X] => p.eval x) (q37_Ψ₃_preΨ₄_bezout (W := W))
  have hΔ4 : W.Δ ^ 4 = 0 := by
    simpa [Polynomial.eval_add, Polynomial.eval_mul, hc3, h4] using hbez.symm
  have hΔ : W.Δ = 0 := pow_eq_zero hΔ4
  exact (WeierstrassCurve.isUnit_Δ (W := W)).ne_zero hΔ

end WeierstrassCurve
```
