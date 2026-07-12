from sage.all import *

print('Q4399_VERIFY_BEGIN')
R0.<Avar> = PolynomialRing(QQ)
L.<a> = NumberField(Avar^3 - 3*Avar - 1)
A0=-a-1
q0=a^2-1
rp=a^2-a-2
rm=-a^2-a
c0=84*a^2-132*a-48
c2=420*a^2+780*a+240
c3=1800*a^2+3384*a+960
dplus=15185664*a^2+28539648*a+8080128
d4minus=2880*a^2-3600*a-1440
d6minus=17280*a^2-24192*a-10368

# Constant identities and inverses.
assert q0^2 == A0^2-a
assert q0^3 == 3*a^2+3*a
assert q0*(2*a^2-a-4) == 3
assert c0*(2*a^2+5*a+3) == 12
assert c3*(6*a^2-15*a+7) == 24
assert c0*c3^2 == dplus
assert c0*c2 == d4minus
assert c3*c0^2 == d6minus
assert (7*a^2+13*a+4)*(-2*a^2-a+9) == 3
assert (17*a^2+32*a+9)*(4*a^2+a-16) == 1
assert (a^2-a)*(-2*a^2+a+7) == 3
assert (a^2-2*a-1)*(2*a^2-a-6) == 1
print('CONSTANT_IDENTITIES_PASS')

# Exact function field of C.
Kx.<x> = FunctionField(L)
Py.<T> = PolynomialRing(Kx)
f = x^6+4*x^5+10*x^4+10*x^3+5*x^2+2*x+1
KC.<y> = Kx.extension(T^2-f)
assert y^2 == f
z=(x-rp)/(x-rm)
u=z^2
v=(z-1)^3*y
w=z*v

# Involution checks as rational functions.
sx=(A0*x-a)/(x-A0)
sy=q0^3*y/(x-A0)^3
zsig=(sx-rp)/(sx-rm)
assert zsig == -z
# Substitute z-coordinate formula for the multiplier.
assert q0^3/(x-A0)^3 == -(z-1)^3/(z+1)^3
print('INVOLUTION_IDENTITIES_PASS')

# Raw quotient equations.
assert v^2 == c3*u^3+c2*u^2+c0
assert w^2 == u*(c3*u^3+c2*u^2+c0)
print('RAW_QUOTIENT_EQUATIONS_PASS')

# Monic Weierstrass quotient maps.
Xp=c3*u
Yp=c3*v
Xm=c0/u
Ym=c0*w/u^2
assert Yp^2 == Xp^3+c2*Xp^2+dplus
assert Ym^2 == Xm^3+d4minus*Xm+d6minus
print('WEIERSTRASS_QUOTIENT_EQUATIONS_PASS')

# Isomorphism E+ -> E0=162b1.
ap=(-2*a^2-a+9)/48
bp=(2*a^2+a-9)/96
gp=(4*a^2+a-16)/192
x0=ap*Xp+3/2
y0=bp*Xp+gp*Yp-5/4
assert y0^2+x0*y0+y0 == x0^3-x0^2-5*x0+5
Ap=112*a^2+208*a+64
Bp=1632*a^2+3072*a+864
assert Xp == Ap*x0-(168*a^2+312*a+96)
assert Yp == Bp*x0+2*Bp*y0+Bp
print('PLUS_ISOMORPHISM_PASS')

# Isomorphism E- -> Ehat0=162b2.
am=(-2*a^2+a+7)/16
bm=(2*a^2-a-7)/32
gm=(6*a^2-3*a-18)/64
xh=am*Xm+1/4
yh=bm*Xm+gm*Ym-5/8
assert yh^2+xh*yh+yh == xh^3-xh^2+25*xh+1
Am=16*(a^2-a)/3
Bm=32*(a^2-2*a-1)/3
assert Xm == Am*(xh-1/4)
assert Ym == Bm*(xh+2*yh+1)
print('MINUS_ISOMORPHISM_PASS')

# Direct invariant-coordinate formulas.
assert x0 == ((4*a^2+8*a+3)*u+3)/2
assert y0 == ((a^2+a-1)*v-(8*a^2+16*a+6)*u-10)/8
assert xh == (u+12*a^2-24*a+3)/(4*u)
assert yh == ((27*a^2-27*a-45)*w+(-24*a^2+48*a-6)*u-10*u^2)/(16*u^2)
print('DIRECT_FORMULAS_PASS')
print('Q4399_VERIFY_END')
