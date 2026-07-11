R.<a,h> = PolynomialRing(QQ)
F = h*(a^2+13*a+49)*(a^2+5*a+1)^3 - a*(h^2+10*h+5)^3
print('factor=', factor(F))
P2.<A,H,Z> = ProjectiveSpace(QQ,2)
Fp = H*(A^2+13*A*Z+49*Z^2)*(A^2+5*A*Z+Z^2)^3 - A*(H^2+10*H*Z+5*Z^2)^3
C = Curve(P2,Fp)
print('curve=',C)
print('curve methods=', [m for m in dir(C) if any(k in m.lower() for k in ['normal','function','canonical','hyperell','genus','riemann','model'])])
try:
    print('genus=',C.genus())
except Exception as e: print('genus error',repr(e))
try:
    K=C.function_field()
    print('K=',K)
    print('K methods=',[m for m in dir(K) if any(k in m.lower() for k in ['normal','canonical','hyperell','genus','riemann','model','curve'])])
    try: print('K genus=',K.genus())
    except Exception as e: print('K genus error',repr(e))
except Exception as e: print('function field error',repr(e))
