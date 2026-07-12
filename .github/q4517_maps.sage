print('MAPS_BEGIN')
R.<u,Y> = PolynomialRing(QQ)
F=R.fraction_field()
u=F(u); Y=F(Y)
C=u^3-6*u+4
A=u^3+6*u-8
P=u^3+3*u^2-6*u+4
X=P/u^2
U=lambda x: x^3-9*x^2+81*x-243
V=lambda x: x^3-81*x+486
ucomp=(U(X)/(9*X^2)).factor()
Ycomp=(V(X)*(A*Y/u^3)/(27*X^3)).factor()
print('COMP_U',ucomp)
print('COMP_Y',Ycomp)
print('COMP_U_NUM',ucomp.numerator().factor())
print('COMP_U_DEN',ucomp.denominator().factor())
print('COMP_Y_NUM',Ycomp.numerator().factor())
print('COMP_Y_DEN',Ycomp.denominator().factor())
Ec=EllipticCurve(QQ,[0,QQ(9)/4,0,-3,1])
Epc=EllipticCurve(QQ,[0,-QQ(27)/4,0,QQ(81)/2,-QQ(243)/4])
for name,E in [('EC',Ec),('EPC',Epc)]:
    print(name,'METHODS',[s for s in dir(E) if 'multip' in s.lower() or 'morphism' in s.lower()][:80])
    for meth in ['multiplication_by_m','multiplication_by_n','scalar_multiplication']:
        if hasattr(E,meth):
            try:
                m=getattr(E,meth)(3)
                print(name,meth,m)
                if hasattr(m,'rational_maps'): print(name,'MUL3_MAPS',m.rational_maps())
            except Exception as ex: print(name,meth,'ERR',repr(ex))
print('MAPS_END')