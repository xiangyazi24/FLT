# Q237 (dm1): complete short-Weierstrass `addX`/`addY` and doubling cofactors

## Result

For the short Weierstrass curve

```text
F_W = Y**2 - X**3 - A*X - B
```

with standard short-Weierstrass division polynomials and

```text
ω_m = (ψ_{m+2}*ψ_{m-1}**2 - ψ_{m-2}*ψ_{m+1}**2) / (4*Y),
```

I computed exact cofactors for

```text
addX([X,Y,1], [φ_m,ω_m,ψ_m]) - ψ_{m-1}**2 * φ_{m+1} = Q_m * F_W
addY([X,Y,1], [φ_m,ω_m,ψ_m]) - ψ_{m-1}**3 * ω_{m+1} = R_m * F_W
```

for `m = 2..8`, and exact doubling cofactors for

```text
dblX([φ_m,ω_m,ψ_m]) - φ_{2m} = S_m * F_W
dblY([φ_m,ω_m,ψ_m]) - ω_{2m} = T_m * F_W
```

for `m = 1..4`.

The script below uses a sparse polynomial-in-`Y` representation over `QQ[X,A,B]` and a custom exact quotient by the monic polynomial `Y² - (X³ + A X + B)`. This was needed because the `addY` cases `m = 7,8` are heavy in plain SymPy `ring(..., Y,X,A,B)` division.

---

## Term counts and verification table

### Addition identities

```text
m  Q_m verified?  #terms(Q_m)  deg_Y(Q_m)  R_m verified?  #terms(R_m)  deg_Y(R_m)
2  yes            3            2           yes            14           5
3  yes            58           4           yes            188          9
4  yes            217          8           yes            940          15
5  yes            1047         14          yes            3430         23
6  yes            2670         20          yes            9740         31
7  yes            6841         24          yes            23792        41
8  yes            15160        36          yes            53491        55
```

### Doubling identities

```text
m  S_m verified?  #terms(S_m)  deg_Y(S_m)  T_m verified?  #terms(T_m)  deg_Y(T_m)
1  yes            1            0           yes            4            2
2  yes            45           6           yes            143          10
3  yes            385          10          yes            1382         18
4  yes            2099         18          yes            7295         30
```

---

## Explicit `Q_m` for `m ≤ 4`

### `Q_2`

```text
32*A*X*Y**2 + 32*B*Y**2 + 32*X**3*Y**2
```

Equivalently:

```text
32*Y**2*(X**3 + A*X + B)
```

### `Q_3`

```text
-2*A**8 + 48*A**7*X**2 + 96*A**6*B*X - 408*A**6*X**4 + 64*A**6*X*Y**2 - 1728*A**5*B*X**3 + 64*A**5*B*Y**2 + 1296*A**5*X**6 + 64*A**5*Y**4 - 1728*A**4*B**2*X**2 + 9504*A**4*B*X**5 - 576*A**4*B*X**2*Y**2 - 108*A**4*X**8 - 2496*A**4*X**5*Y**2 - 64*A**4*X**2*Y**4 + 20736*A**3*B**2*X**4 - 10368*A**3*B*X**7 - 9600*A**3*B*X**4*Y**2 - 512*A**3*B*X*Y**4 - 3888*A**3*X**10 - 1536*A**3*X**7*Y**2 - 2432*A**3*X**4*Y**4 + 13824*A**2*B**3*X**3 + 512*A**2*B**3*Y**2 - 51840*A**2*B**2*X**6 - 12288*A**2*B**2*X**3*Y**2 + 512*A**2*B**2*Y**4 - 28512*A**2*B*X**9 + 4992*A**2*B*X**6*Y**2 - 6656*A**2*B*X**3*Y**4 - 3672*A**2*X**12 + 2240*A**2*X**9*Y**2 + 896*A**2*X**6*Y**4 - 82944*A*B**3*X**5 - 12288*A*B**3*X**2*Y**2 - 62208*A*B**2*X**8 + 18432*A*B**2*X**5*Y**2 - 6144*A*B**2*X**2*Y**4 - 15552*A*B*X**11 + 16704*A*B*X**8*Y**2 + 10752*A*B*X**5*Y**4 - 1296*A*X**14 + 1536*A*X**11*Y**2 + 1344*A*X**8*Y**4 - 41472*B**4*X**4 - 6144*B**4*X*Y**2 - 41472*B**3*X**7 + 7680*B**3*X**4*Y**2 - 6144*B**3*X*Y**4 - 15552*B**2*X**10 + 18432*B**2*X**7*Y**2 + 13824*B**2*X**4*Y**4 - 2592*B*X**13 + 4800*B*X**10*Y**2 + 4608*B*X**7*Y**4 - 162*X**16 + 192*X**13*Y**2 + 192*X**10*Y**4
```

### `Q_4`

```text
128*A**13*X*Y**2 + 128*A**12*B*Y**2 - 896*A**12*X**3*Y**2 - 384*A**12*Y**4 - 4608*A**11*B*X**2*Y**2 - 9472*A**11*X**5*Y**2 - 11264*A**11*X**2*Y**4 - 1536*A**10*B**2*X*Y**2 - 21248*A**10*B*X**4*Y**2 - 11776*A**10*B*X*Y**4 + 63232*A**10*X**7*Y**2 - 75008*A**10*X**4*Y**4 - 4096*A**10*X*Y**6 + 2048*A**9*B**3*Y**2 - 13312*A**9*B**2*X**3*Y**2 - 14336*A**9*B**2*Y**4 + 478720*A**9*B*X**6*Y**2 - 91136*A**9*B*X**3*Y**4 - 4096*A**9*B*Y**6 + 207232*A**9*X**9*Y**2 - 28672*A**9*X**6*Y**4 - 65536*A**9*X**3*Y**6 - 4096*A**9*Y**8 - 71680*A**8*B**3*X**2*Y**2 + 1024512*A**8*B**2*X**5*Y**2 - 301056*A**8*B**2*X**2*Y**4 + 539520*A**8*B*X**8*Y**2 + 539136*A**8*B*X**5*Y**4 - 110592*A**8*B*X**2*Y**6 - 1164928*A**8*X**11*Y**2 + 537472*A**8*X**8*Y**4 - 307200*A**8*X**5*Y**6 - 61440*A**8*X**2*Y**8 - 57344*A**7*B**4*X*Y**2 + 1024000*A**7*B**3*X**4*Y**2 - 262144*A**7*B**3*X*Y**4 - 454656*A**7*B**2*X**7*Y**2 - 368640*A**7*B**2*X**4*Y**4 - 147456*A**7*B**2*X*Y**6 - 11813888*A**7*B*X**10*Y**2 + 2674688*A**7*B*X**7*Y**4 - 540672*A**7*B*X**4*Y**6 - 49152*A**7*B*X*Y**8 - 1195520*A**7*X**13*Y**2 - 665600*A**7*X**10*Y**4 - 131072*A**7*X**7*Y**6 - 245760*A**7*X**4*Y**8 + 8192*A**6*B**5*Y**2 + 925696*A**6*B**4*X**3*Y**2 - 188416*A**6*B**4*Y**4 + 303104*A**6*B**3*X**6*Y**2 - 638976*A**6*B**3*X**3*Y**4 - 98304*A**6*B**3*Y**6 - 42413056*A**6*B**2*X**9*Y**2 + 2351104*A**6*B**2*X**6*Y**4 - 1523712*A**6*B**2*X**3*Y**6 - 98304*A**6*B**2*Y**8 + 165376*A**6*B*X**12*Y**2 - 8944640*A**6*B*X**9*Y**4 + 1589248*A**6*B*X**6*Y**6 - 245760*A**6*B*X**3*Y**8 + 1653248*A**6*X**15*Y**2 - 1613312*A**6*X**12*Y**4 + 1466368*A**6*X**9*Y**6 + 114688*A**6*X**6*Y**8 + 147456*A**5*B**5*X**2*Y**2 + 5382144*A**5*B**4*X**5*Y**2 - 2310144*A**5*B**4*X**2*Y**4 - 83791872*A**5*B**3*X**8*Y**2 + 9076736*A**5*B**3*X**5*Y**4 - 1966080*A**5*B**3*X**2*Y**6 + 42780672*A**5*B**2*X**11*Y**2 - 27807744*A**5*B**2*X**8*Y**4 + 49152*A**5*B**2*X**5*Y**6 - 1179648*A**5*B**2*X**2*Y**8 + 25537536*A**5*B*X**14*Y**2 - 5658624*A**5*B*X**11*Y**4 + 9314304*A**5*B*X**8*Y**6 + 1720320*A**5*B*X**5*Y**8 + 1878912*A**5*X**17*Y**2 + 2183168*A**5*X**14*Y**4 + 1351680*A**5*X**8*Y**8 - 294912*A**4*B**6*X*Y**2 + 7299072*A**4*B**5*X**4*Y**2 - 1867776*A**4*B**5*X*Y**4 - 124968960*A**4*B**4*X**7*Y**2 + 4907008*A**4*B**4*X**4*Y**4 - 1572864*A**4*B**4*X*Y**6 + 150810624*A**4*B**3*X**10*Y**2 - 28196864*A**4*B**3*X**7*Y**4 - 1540096*A**4*B**3*X**4*Y**6 - 786432*A**4*B**3*X*Y**8 + 97956864*A**4*B**2*X**13*Y**2 + 12939264*A**4*B**2*X**10*Y**4 + 16760832*A**4*B**2*X**7*Y**6 - 491520*A**4*B**2*X**4*Y**8 + 9224064*A**4*B*X**16*Y**2 + 26715136*A**4*B*X**13*Y**4 - 8626176*A**4*B*X**10*Y**6 + 6242304*A**4*B*X**7*Y**8 - 194688*A**4*X**19*Y**2 + 732544*A**4*X**16*Y**4 - 1466368*A**4*X**13*Y**6 - 1351680*A**4*X**10*Y**8 + 7077888*A**3*B**6*X**3*Y**2 - 1048576*A**3*B**6*Y**4 - 140673024*A**3*B**5*X**6*Y**2 + 2490368*A**3*B**5*X**3*Y**4 - 786432*A**3*B**5*Y**6 + 235560960*A**3*B**4*X**9*Y**2 - 38764544*A**3*B**4*X**6*Y**4 - 6553600*A**3*B**4*X**3*Y**6 - 786432*A**3*B**4*Y**8 + 131604480*A**3*B**3*X**12*Y**2 + 45023232*A**3*B**3*X**9*Y**4 + 38273024*A**3*B**3*X**6*Y**6 - 262144*A**3*B**3*X**3*Y**8 - 26210304*A**3*B**2*X**15*Y**2 + 91774976*A**3*B**2*X**12*Y**4 - 38191104*A**3*B**2*X**9*Y**6 + 11010048*A**3*B**2*X**6*Y**8 - 12151296*A**3*B*X**18*Y**2 - 2895872*A**3*B*X**15*Y**4 - 10436608*A**3*B*X**12*Y**6 - 13516800*A**3*B*X**9*Y**8 - 822528*A**3*X**21*Y**2 - 625664*A**3*X**18*Y**4 + 131072*A**3*X**15*Y**6 - 114688*A**3*X**12*Y**8 + 3538944*A**2*B**7*X**2*Y**2 - 100859904*A**2*B**6*X**5*Y**2 - 4849664*A**2*B**6*X**2*Y**4 + 238215168*A**2*B**5*X**8*Y**2 - 6094848*A**2*B**5*X**5*Y**4 - 8650752*A**2*B**5*X**2*Y**6 + 56844288*A**2*B**4*X**11*Y**2 + 9756672*A**2*B**4*X**8*Y**4 + 41680896*A**2*B**4*X**5*Y**6 - 5505024*A**2*B**4*X**2*Y**8 - 169205760*A**2*B**3*X**14*Y**2 + 110477312*A**2*B**3*X**11*Y**4 - 46694400*A**2*B**3*X**8*Y**6 + 27525120*A**2*B**3*X**5*Y**8 - 73944576*A**2*B**2*X**17*Y**2 - 55713792*A**2*B**2*X**14*Y**4 - 10862592*A**2*B**2*X**11*Y**6 - 35684352*A**2*B**2*X**8*Y**8 - 9462528*A**2*B*X**20*Y**2 - 9426432*A**2*B*X**17*Y**4 + 5849088*A**2*B*X**14*Y**6 + 3194880*A**2*B*X**11*Y**8 - 352512*A**2*X**23*Y**2 - 363776*A**2*X**20*Y**4 + 307200*A**2*X**17*Y**6 + 245760*A**2*X**14*Y**8 - 49545216*A*B**7*X**4*Y**2 - 4194304*A*B**7*X*Y**4 + 162791424*A*B**6*X**7*Y**2 + 1310720*A*B**6*X**4*Y**4 - 5242880*A*B**6*X*Y**6 + 22560768*A*B**5*X**10*Y**2 + 21626880*A*B**5*X**7*Y**4 + 32243712*A*B**5*X**4*Y**6 - 3145728*A*B**5*X*Y**8 - 235118592*A*B**4*X**13*Y**2 + 73056256*A*B**4*X**10*Y**4 - 57409536*A*B**4*X**7*Y**6 + 19660800*A*B**4*X**4*Y**8 - 140064768*A*B**3*X**16*Y**2 - 157122560*A*B**3*X**13*Y**4 + 11927552*A*B**3*X**10*Y**6 - 38535168*A*B**3*X**7*Y**8 - 28947456*A*B**2*X**19*Y**2 - 35272704*A*B**2*X**16*Y**4 + 28852224*A*B**2*X**13*Y**6 + 21626880*A*B**2*X**10*Y**8 - 2308608*A*B*X**22*Y**2 - 2679808*A*B*X**19*Y**4 + 2715648*A*B*X**16*Y**6 + 2408448*A*B*X**13*Y**8 - 58752*A*X**25*Y**2 - 65536*A*X**22*Y**4 + 65536*A*X**19*Y**6 + 61440*A*X**16*Y**8 - 14155776*B**8*X**3*Y**2 - 2097152*B**8*Y**4 + 46006272*B**7*X**6*Y**2 + 6815744*B**7*X**3*Y**4 - 2097152*B**7*Y**6 + 25657344*B**6*X**9*Y**2 - 17432576*B**6*X**6*Y**4 + 13631488*B**6*X**3*Y**6 - 2097152*B**6*Y**8 - 94003200*B**5*X**12*Y**2 + 88702976*B**5*X**9*Y**4 - 22806528*B**5*X**6*Y**6 + 15728640*B**5*X**3*Y**8 - 81174528*B**4*X**15*Y**2 - 121954304*B**4*X**12*Y**4 - 9699328*B**4*X**9*Y**6 - 38535168*B**4*X**6*Y**8 - 24827904*B**3*X**18*Y**2 - 37076992*B**3*X**15*Y**4 + 33652736*B**3*X**12*Y**6 + 28835840*B**3*X**9*Y**8 - 3331584*B**2*X**21*Y**2 - 4364288*B**2*X**18*Y**4 + 5062656*B**2*X**15*Y**6 + 4816896*B**2*X**12*Y**8 - 183168*B*X**24*Y**2 - 220672*B*X**21*Y**4 + 249856*B*X**18*Y**6 + 245760*B*X**15*Y**8 - 3456*X**27*Y**2 - 3968*X**24*Y**4 + 4096*X**21*Y**6 + 4096*X**18*Y**8
```

---

## Complete runnable script

```python
from sympy.polys.rings import ring
from sympy import QQ
import time
import gc

R0, X, A, B = ring('X,A,B', QQ, order='lex')
f = X**3 + A*X + B
zero, one = R0.zero, R0.one

class YP:
    """Sparse polynomial in Y with coefficients in QQ[X,A,B]."""
    __slots__ = ('d',)
    def __init__(self, d=None):
        self.d = {k: v for k, v in (d or {}).items() if v}
    @staticmethod
    def c(c):
        return YP({0: c}) if c else YP()
    @staticmethod
    def y():
        return YP({1: one})
    def __add__(self, other):
        other = toYP(other); d = self.d.copy()
        for k, v in other.d.items():
            d[k] = d.get(k, zero) + v
        return YP(d)
    __radd__ = __add__
    def __neg__(self):
        return YP({k: -v for k, v in self.d.items()})
    def __sub__(self, other):
        return self + (-toYP(other))
    def __rsub__(self, other):
        return toYP(other) + (-self)
    def __mul__(self, other):
        other = toYP(other); d = {}
        for i, a in self.d.items():
            for j, b in other.d.items():
                k = i + j
                d[k] = d.get(k, zero) + a*b
        return YP(d)
    __rmul__ = __mul__
    def __pow__(self, n):
        n = int(n); res = YP.c(one); base = self
        while n:
            if n & 1:
                res = res * base
            n >>= 1
            if n:
                base = base * base
        return res
    def div_y_scalar(self, q, label=''):
        d = {}
        for k, v in self.d.items():
            if k < 1:
                raise AssertionError(f'{label}: not divisible by Y; term Y^{k} has coeff {v}')
            d[k-1] = d.get(k-1, zero) + v.quo_ground(q)
        return YP(d)
    def quotient_F(self, label=''):
        """Exact quotient by F = Y^2 - (X^3 + A X + B), requiring zero remainder."""
        coeff = self.d.copy(); q = {}
        maxk = max(coeff.keys()) if coeff else -1
        for k in range(maxk, 1, -1):
            c = coeff.get(k, zero)
            if c:
                q[k-2] = q.get(k-2, zero) + c
                coeff[k] = zero
                coeff[k-2] = coeff.get(k-2, zero) + c*f
        rem0, rem1 = coeff.get(0, zero), coeff.get(1, zero)
        if rem0 or rem1:
            raise AssertionError(f'{label}: nonzero remainder rem0={rem0}, rem1={rem1}')
        return YP(q)
    def terms(self):
        return sum(len(v.terms()) for v in self.d.values())
    def degY(self):
        return max(self.d.keys()) if self.d else -1
    def to_str(self):
        import sympy as sp
        Ys = sp.Symbol('Y')
        expr = 0
        for k, v in self.d.items():
            expr += v.as_expr() * Ys**k
        return str(sp.expand(expr))

def toYP(x):
    if isinstance(x, YP):
        return x
    if isinstance(x, int):
        return YP.c(one*x)
    return YP.c(x)

Y = YP.y()
C = lambda c: YP.c(c)

psi = {0: YP(), 1: C(one), 2: 2*Y}
psi[3] = C(3*X**4 + 6*A*X**2 + 12*B*X - A**2)
psi[4] = 4*Y*C(X**6 + 5*A*X**4 + 20*B*X**3 - 5*A**2*X**2 - 4*A*B*X - 8*B**2 - A**3)

def getpsi(n):
    n = int(n)
    if n in psi:
        return psi[n]
    if n < 0:
        return -getpsi(-n)
    if n % 2:
        m = (n - 1)//2
        ans = getpsi(m+2)*getpsi(m)**3 - getpsi(m-1)*getpsi(m+1)**3
    else:
        m = n//2
        ans = (getpsi(m)*(getpsi(m+2)*getpsi(m-1)**2 - getpsi(m-2)*getpsi(m+1)**2)).div_y_scalar(2, f'psi{n}')
    psi[n] = ans
    return ans

phi_cache = {}
def phi(n):
    n = int(n)
    if n not in phi_cache:
        phi_cache[n] = C(X)*getpsi(n)**2 - getpsi(n+1)*getpsi(n-1)
    return phi_cache[n]

omega_cache = {}
def omega(n):
    n = int(n)
    if n not in omega_cache:
        omega_cache[n] = (getpsi(n+2)*getpsi(n-1)**2 - getpsi(n-2)*getpsi(n+1)**2).div_y_scalar(4, f'omega{n}')
    return omega_cache[n]

def addX(P, Q):
    XP, YP0, ZP = P; XQ, YQ, ZQ = Q
    return (XP*XQ**2*ZP**2 - 2*YP0*YQ*ZP*ZQ + XP**2*XQ*ZQ**2
            + C(A)*XQ*ZP**4*ZQ**2 + C(A)*XP*ZP**2*ZQ**4 + C(2*B)*ZP**4*ZQ**4)

def negAddY(P, Q):
    XP, YP0, ZP = P; XQ, YQ, ZQ = Q
    return (-YP0*XQ**3*ZP**3 + 2*YP0*YQ**2*ZP**3 - 3*XP**2*XQ*YQ*ZP**2*ZQ
            + 3*XP*YP0*XQ**2*ZP*ZQ**2 + XP**3*YQ*ZQ**3 - 2*YP0**2*YQ*ZQ**3
            - C(A)*XQ*YQ*ZP**6*ZQ - C(A)*XP*YQ*ZP**4*ZQ**3
            + C(A)*YP0*XQ*ZP**3*ZQ**4 + C(A)*XP*YP0*ZP*ZQ**6
            - C(2*B)*YQ*ZP**6*ZQ**3 + C(2*B)*YP0*ZP**3*ZQ**6)

def addY(P, Q):
    return -negAddY(P, Q)

def negY(P):
    return -P[1]

def dblU(P):
    return -(C(3)*P[0]**2 + C(A)*P[2]**4)

def dblX(P):
    U = dblU(P); D = P[1] - negY(P)
    return U**2 - 2*P[0]*D**2

def negDblY(P):
    U = dblU(P); D = P[1] - negY(P); XX = dblX(P)
    return -U*(XX - P[0]*D**2) + P[1]*D**3

def dblY(P):
    return -negDblY(P)

def Rm(m):
    return (phi(m), omega(m), getpsi(m))

# addY for m=8 needs omega(9), hence psi through 11.
for n in range(12):
    getpsi(n)
for n in range(1, 10):
    omega(n)

print('precomputed psi through 11 and omega through 9')
print('psi_terms', {n: getpsi(n).terms() for n in range(12)})
print('omega_terms', {n: omega(n).terms() for n in range(1, 10)})

P = (C(X), Y, C(one))
results = {}
t0 = time.time()

for m in range(2, 9):
    expr = addX(P, Rm(m)) - getpsi(m-1)**2 * phi(m+1)
    q = expr.quotient_F(f'Q{m}')
    results[('Q', m)] = q
    print(f'ADD-X m={m}: verified, terms={q.terms()}, degY={q.degY()}, elapsed={time.time()-t0:.2f}')
    del expr; gc.collect()

for m in range(2, 9):
    expr = addY(P, Rm(m)) - getpsi(m-1)**3 * omega(m+1)
    q = expr.quotient_F(f'R{m}')
    results[('R', m)] = q
    print(f'ADD-Y m={m}: verified, terms={q.terms()}, degY={q.degY()}, elapsed={time.time()-t0:.2f}')
    del expr; gc.collect()

for m in range(1, 5):
    S = (dblX(Rm(m)) - phi(2*m)).quotient_F(f'S{m}')
    T = (dblY(Rm(m)) - omega(2*m)).quotient_F(f'T{m}')
    results[('S', m)] = S; results[('T', m)] = T
    print(f'DBL m={m}: verified, S_terms={S.terms()}, S_degY={S.degY()}, T_terms={T.terms()}, T_degY={T.degY()}')

for m in (2, 3, 4):
    print(f'Q{m} = {results[("Q", m)].to_str()}')

print('OK')
```

## Run output summary

```text
precomputed psi through 11 and omega through 9
psi_terms {0: 0, 1: 1, 2: 1, 3: 4, 4: 7, 5: 23, 6: 44, 7: 86, 8: 183, 9: 365, 10: 577, 11: 1031}
omega_terms {1: 1, 2: 7, 3: 26, 4: 110, 5: 272, 6: 817, 7: 1814, 8: 3953, 9: 7311}
ADD-X m=2: verified, terms=3, degY=2
ADD-X m=3: verified, terms=58, degY=4
ADD-X m=4: verified, terms=217, degY=8
ADD-X m=5: verified, terms=1047, degY=14
ADD-X m=6: verified, terms=2670, degY=20
ADD-X m=7: verified, terms=6841, degY=24
ADD-X m=8: verified, terms=15160, degY=36
ADD-Y m=2: verified, terms=14, degY=5
ADD-Y m=3: verified, terms=188, degY=9
ADD-Y m=4: verified, terms=940, degY=15
ADD-Y m=5: verified, terms=3430, degY=23
ADD-Y m=6: verified, terms=9740, degY=31
ADD-Y m=7: verified, terms=23792, degY=41
ADD-Y m=8: verified, terms=53491, degY=55
DBL m=1: verified, S_terms=1, S_degY=0, T_terms=4, T_degY=2
DBL m=2: verified, S_terms=45, S_degY=6, T_terms=143, T_degY=10
DBL m=3: verified, S_terms=385, S_degY=10, T_terms=1382, T_degY=18
DBL m=4: verified, S_terms=2099, S_degY=18, T_terms=7295, T_degY=30
OK
```
