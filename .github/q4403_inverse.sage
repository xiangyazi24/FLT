from sage.all import *
print('Q4403_INVERSE_BEGIN')
# Lex order intended to eliminate y then x and expose linear formulas over QQ(r,s).
R.<y,x,r,s> = PolynomialRing(QQ, order='lex')
h=x^3-2*x^2+3*x+1
C=y^2+h*y+2*x
nr=x^2-x*y-3*x+1
dr=(x-1)^2*(x*y+1)
ns=x^2-2*x-y
ds=x^2-x*y-3*x-y^2-2*y
I=R.ideal([C, r*dr-nr, s*ds-ns])
G=I.groebner_basis()
print('GB_LEN',len(G))
for i,g in enumerate(G):
    print('GB',i,factor(g))
# Recompute over fraction field QQ(r,s), solve zero-dimensional ideal in x,y.
A.<rr,ss> = PolynomialRing(QQ)
F=A.fraction_field()
S.<yy,xx> = PolynomialRing(F, order='lex')
hh=xx^3-2*xx^2+3*xx+1
CC=yy^2+hh*yy+2*xx
nrr=xx^2-xx*yy-3*xx+1
drr=(xx-1)^2*(xx*yy+1)
nss=xx^2-2*xx-yy
dss=xx^2-xx*yy-3*xx-yy^2-2*yy
J=S.ideal([CC, F(rr)*drr-nrr, F(ss)*dss-nss])
GG=J.groebner_basis()
print('FF_GB_LEN',len(GG))
for i,g in enumerate(GG):
    print('FF_GB',i,g)
print('Q4403_INVERSE_END')
