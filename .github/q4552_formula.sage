print('Q4552_FORMULA_BEGIN')
# Dual-side cube root: solve ((mX+n)+q Z)^3 = c3 * X^3*w in Q(X,Z)/(Z^2-F).
R.<X> = PolynomialRing(QQ)
F = X^3 - QQ(27)/4*X^2 + QQ(81)/2*X - QQ(243)/4
U = X^3-9*X^2+81*X-243
V = X^3-81*X+486
Aw = U*X/6 - X^3
Bw = V/27
S.<m,n,q,k> = PolynomialRing(QQ)
p = m*X+n
Aroot = p^3 + 3*p*q^2*F
Broot = 3*p^2*q + q^3*F
polys=[]
for coeff in (Aroot-k*Aw).coefficients(sparse=False): polys.append(S(coeff))
for coeff in (Broot-k*Bw).coefficients(sparse=False): polys.append(S(coeff))
I=S.ideal(polys)
print('DUAL_GB',I.groebner_basis())
# Try normalized q=1 and q=2.
for qv in [1,2,-1,-2,3,-3,QQ(1)/3,QQ(2)/3]:
  J=I+S.ideal(q-qv)
  try:
    sols=J.variety(QQ)
    if sols: print('DUAL_SOL_Q',qv,sols)
  except Exception as ex: pass

# Forward side. Work over Q(zeta), zeta^2+zeta+1=0.
Qt.<zz> = PolynomialRing(QQ)
M.<zeta> = NumberField(zz^2+zz+1)
Ru.<u> = PolynomialRing(M)
# quotient algebra in w: w^2 = (3u-2)w+u^3
# ansatz root = (w + p*u + q0)/u, p,q0 in M.
# Compute cube of N=w+p*u+q0 as A+B*w.
Spq.<p0,p1,q0,q1> = PolynomialRing(QQ)
pM = M['u'](0) if False else None
# Solve by brute symbolic over QQ basis 1,zeta using polynomial ring with zeta relation and unknowns.
T.<u,w,z,m0,m1,n0,n1,h> = PolynomialRing(QQ)
pz=m0+m1*z; nz=n0+n1*z
N=w+pz*u+nz
# reduce N^3 modulo w^2-(3u-2)w-u^3 and z^2+z+1 via groebner normal form.
relw=w^2-(3*u-2)*w-u^3
relz=z^2+z+1
G=T.ideal([relw,relz]).groebner_basis()
def red(expr): return T.ideal([relw,relz]).reduce(expr)
N3=red(N^3)
C=u^3-6*u+4; A=u^3+6*u-8; B=-18*u^2+24*u-8
# g numerator over u^3: A*w+B+u^3+3*z*C*u
Gnum=red(A*w+B+u^3+3*z*C*u)
diff=red(N3-h*Gnum)
coeffs=[]
# gather coefficients in u,w,z
for mon,co in diff.dict().items(): coeffs.append(co)
J=QQ[m0,m1,n0,n1,h].ideal(coeffs)
print('FORWARD_GB',J.groebner_basis())
try:
  sols=J.variety(QQ)
  print('FORWARD_SOLS',sols)
except Exception as ex: print('FORWARD_SOL_ERR',repr(ex))
print('Q4552_FORMULA_END')
