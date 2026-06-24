import sympy as sp, pickle, sys
b2,b4,b6,b8,X = sp.symbols("b2 b4 b6 b8 X")
f = 2*X**6 + b2*X**5 + 5*b4*X**4 + 10*b6*X**3 + 10*b8*X**2 + (b2*b8 - b4*b6)*X + (b4*b8 - b6**2)
g = sp.diff(f, X)
Delta = -b2**2*b8 - 8*b4**3 - 27*b6**2 + 9*b2*b4*b6
bRel  = b2*b6 - b4**2 - 4*b8
print("deg f,g:", sp.degree(f,X), sp.degree(g,X)); sys.stdout.flush()
Res_full = sp.resultant(f, g, X)
print("Res_full computed, #terms:", len(sp.Add.make_args(sp.expand(Res_full)))); sys.stdout.flush()
# determine target c*Delta^e by eliminating b8 via b_relation (b8 = (b2*b6-b4^2)/4)
sub = {b8: (b2*b6 - b4**2)/4}
Rr = sp.expand(Res_full.subs(sub)); Dr = sp.expand(Delta.subs(sub))
# find e = totaldeg(Rr)/totaldeg(Dr)
def tdeg(p):
    p=sp.Poly(sp.expand(p), b2,b4,b6); return p.total_degree()
e = tdeg(Rr)//tdeg(Dr)
print("tdeg Rr,Dr:", tdeg(Rr), tdeg(Dr), "=> e =", e); sys.stdout.flush()
ratio = sp.simplify(Rr / Dr**e)
print("Rr / Dr^e =", ratio, "(should be constant c)"); sys.stdout.flush()
c = sp.nsimplify(ratio)
target = c * Delta**e
# Q = (Res_full - target)/bRel
Q, r = sp.div(sp.expand(Res_full - target), bRel, b8)
print("target = (%s)*Delta^%d ; remainder 0:" % (c, e), sp.expand(r)==0); sys.stdout.flush()
# Bezout A*f+B*g = Res_full, deg A<=4 (5 unk), deg B<=5 (6 unk)
a = sp.symbols("a0:5"); cc = sp.symbols("c0:6")
A = sum(a[i]*X**i for i in range(5)); B = sum(cc[i]*X**i for i in range(6))
P = sp.Poly(sp.expand(A*f + B*g - Res_full), X)
sol = list(sp.linsolve(P.all_coeffs(), list(a)+list(cc)))[0]
subs = dict(zip(list(a)+list(cc), sol))
A0 = sp.expand(A.subs(subs)); B0 = sp.expand(B.subs(subs))
print("verify A*f+B*g=Res_full:", sp.expand(A0*f+B0*g-Res_full)==0); sys.stdout.flush()
def intp(p): return all(v==int(v) for v in sp.Poly(p,X,b2,b4,b6,b8).coeffs())
print("A,B integer:", intp(A0), intp(B0))
print("deg A,B:", sp.Poly(A0,X).degree(), sp.Poly(B0,X).degree(),
      "| terms A,B,Q:", len(sp.Add.make_args(A0)), len(sp.Add.make_args(B0)), len(sp.Add.make_args(sp.expand(Q))))
pickle.dump({"A":A0,"B":B0,"Q":sp.expand(Q),"c":int(c),"e":int(e)}, open("/tmp/sep_n4_cert.pkl","wb"))
print("saved /tmp/sep_n4_cert.pkl  c=%s e=%d" % (c,e))
