from sage.all import *

print('Q4403_INVERSE_BEGIN')

# Sutherland's optimized N=18 model and map to the raw (r,s)-model.
A.<rr,ss> = PolynomialRing(QQ)
F = A.fraction_field()
S.<yy,xx> = PolynomialRing(F, order='lex')

h = xx^3 - 2*xx^2 + 3*xx + 1
C = yy^2 + h*yy + 2*xx
nr = xx^2 - xx*yy - 3*xx + 1
dr = (xx-1)^2 * (xx*yy + 1)
ns = xx^2 - 2*xx - yy
ds = xx^2 - xx*yy - 3*xx - yy^2 - 2*yy

J = S.ideal([C, F(rr)*dr - nr, F(ss)*ds - ns])
GG = J.groebner_basis()
print('FF_GB_LEN', len(GG))
for i,g in enumerate(GG):
    print('FF_GB', i, g)

# Print numerator/denominator separately for any linear solution formulas.
for i,g in enumerate(GG):
    py = g.polynomial(yy)
    if py.degree() == 1:
        print('LINEAR_Y', i, 'LC', py[1], 'CONST', py[0])
    px = g.polynomial(xx)
    if px.degree() == 1:
        print('LINEAR_X', i, 'LC', px[1], 'CONST', px[0])

print('Q4403_INVERSE_END')
