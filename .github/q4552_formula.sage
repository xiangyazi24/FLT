print('Q4552_FORMULA_BEGIN')
# Dual-side cube root by a coefficient ansatz.
S.<m,n,q,k> = PolynomialRing(QQ)
R.<X> = PolynomialRing(S)
F = X^3 - QQ(27)/4*X^2 + QQ(81)/2*X - QQ(243)/4
U = X^3-9*X^2+81*X-243
V = X^3-81*X+486
Aw = U*X/6 - X^3
Bw = V/27
p = m*X+n
Aroot = p^3 + 3*p*q^2*F
Broot = 3*p^2*q + q^3*F
polys=list((Aroot-k*Aw).coefficients(sparse=False))+list((Broot-k*Bw).coefficients(sparse=False))
I=S.ideal(polys)
print('DUAL_GB',I.groebner_basis())
for qv in [1,2,-1,-2,3,-3,QQ(1)/3,QQ(2)/3,QQ(1)/2]:
  J=I+S.ideal(q-qv)
  try:
    sols=J.variety(QQ)
    if sols: print('DUAL_SOL_Q',qv,sols)
  except Exception: pass

# Ask the genus-one function fields directly for cube roots.
QX.<x> = FunctionField(QQ)
PZ.<zz> = PolynomialRing(QX)
Fq=x^3-QQ(27)/4*x^2+QQ(81)/2*x-QQ(243)/4
Kd.<z> = QX.extension(zz^2-Fq)
Uq=x^3-9*x^2+81*x-243
Vq=x^3-81*x+486
wd = Vq*z/(27*x^3)+Uq/(6*x^2)-1
print('DUAL_METHODS',[s for s in dir(wd) if 'power' in s.lower() or 'root' in s.lower()][:100])
for meth in ['is_nth_power','nth_root','sqrt','is_square']:
  if hasattr(wd,meth):
    try:
      if meth in ['is_nth_power','nth_root']: out=getattr(wd,meth)(3)
      else: out=getattr(wd,meth)()
      print('DUAL',meth,out)
    except Exception as ex: print('DUAL_ERR',meth,repr(ex))

Qt.<tt> = PolynomialRing(QQ)
M.<zeta> = NumberField(tt^2+tt+1)
Fu.<u> = FunctionField(M)
Pw.<ww> = PolynomialRing(Fu)
Kf.<w> = Fu.extension(ww^2-(3*u-2)*ww-u^3)
C=u^3-6*u+4; A=u^3+6*u-8; B=-18*u^2+24*u-8
gf=(A*w+B+u^3+3*zeta*C*u)/u^3
print('FORWARD_METHODS',[s for s in dir(gf) if 'power' in s.lower() or 'root' in s.lower()][:100])
for meth in ['is_nth_power','nth_root','sqrt','is_square']:
  if hasattr(gf,meth):
    try:
      if meth in ['is_nth_power','nth_root']: out=getattr(gf,meth)(3)
      else: out=getattr(gf,meth)()
      print('FORWARD',meth,out)
    except Exception as ex: print('FORWARD_ERR',meth,repr(ex))
print('Q4552_FORMULA_END')
