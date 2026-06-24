import sympy as sp
b2,b4,b6,b8,X = sp.symbols('b2 b4 b6 b8 X')
Psi3 = 3*X**4 + b2*X**3 + 3*b4*X**2 + 3*b6*X + b8
prePsi4 = 2*X**6 + b2*X**5 + 5*b4*X**4 + 10*b6*X**3 + 10*b8*X**2 + (b2*b8-b4*b6)*X + (b4*b8-b6**2)
Psi2Sq = 4*X**3 + b2*X**2 + 2*b4*X + b6
bRel = b2*b6 - b4**2 - 4*b8   # = 0
expr = sp.expand(prePsi4**2 + 4*Psi3**3)
# reduce mod Psi2Sq (in X) then mod bRel (in b8)
Q1, r1 = sp.div(expr, Psi2Sq, X)
print("deg expr in X:", sp.degree(expr,X), "| after /Psi2Sq remainder deg:", sp.degree(r1,X) if r1!=0 else "0")
# remainder r1 should be expressible via bRel: r1 = Q2*bRel
Q2, r2 = sp.div(sp.expand(r1), bRel, b8)
print("prePsi4^2 + 4*Psi3^3 = Q1*Psi2Sq + Q2*bRel + r2 ;  r2 == 0:", sp.expand(r2)==0)
if sp.expand(r2)==0:
    print("=> prePsi4^2 + 4*Psi3^3 = 0 mod (Psi2Sq, b_relation). hCD CONFIRMED.")
    print("Q1 terms:", len(sp.Add.make_args(sp.expand(Q1))), "| Q2 terms:", len(sp.Add.make_args(sp.expand(Q2))))

import pickle
pickle.dump({'Q1': sp.expand(Q1), 'Q2': sp.expand(Q2)}, open('/tmp/hcd_cert.pkl','wb'))
print("saved /tmp/hcd_cert.pkl")
