from sage.all import *
print('Q4403_INVERSE_BEGIN')

Fr.<r0> = FunctionField(QQ)
Ps.<S> = PolynomialRing(Fr)
F18 = (
    r0^4*S^3 - 6*r0^4*S^2 + 9*r0^4*S - r0^4
  + r0^3*S^5 - 7*r0^3*S^4 + 20*r0^3*S^3 - 19*r0^3*S^2 - 8*r0^3*S + r0^3
  + r0^2*S^4 - 11*r0^2*S^3 + 28*r0^2*S^2
  + r0*S^4 - 5*r0*S^3 - 8*r0*S^2
  + S^4 + S^3 + S^2)
K.<s> = Fr.extension(F18)
r=K(r0)

# Add z with z*dr*ds=1; lex eliminates z and removes denominator components.
R.<z,y,x> = PolynomialRing(K, order='lex')
h=x^3-2*x^2+3*x+1
C=y^2+h*y+2*x
nr=x^2-x*y-3*x+1
dr=(x-1)^2*(x*y+1)
ns=x^2-2*x-y
ds=x^2-x*y-3*x-y^2-2*y
I=R.ideal([C, r*dr-nr, s*ds-ns, z*dr*ds-1])
G=I.groebner_basis()
print('GB_LEN',len(G))
for i,g in enumerate(G):
    if g.degree(z)==0:
        print('ELIM',i,g)
print('Q4403_INVERSE_END')
