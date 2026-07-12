from sage.all import *

print('Q4518_COMPACT_BEGIN')
R.<T> = PolynomialRing(QQ)
L.<a> = NumberField(T^3-3*T-1)
E = EllipticCurve(L,[1,-1,1,-5,5])
T3 = E(1,0)
A=-a-1; q=a^2-1; rp=a^2-a-2; rm=-a^2-a
ku=4*a^2+8*a+3; kv=a^2+a-1; lu=8*a^2+16*a+6
f=lambda x:x^6+4*x^5+10*x^4+10*x^3+5*x^2+2*x+1
pts=E.torsion_points()
G=sorted([P for P in pts if P.order()==21 and 7*P==T3],key=str)[0]
print('G=',G,'; 3G=',3*G,'; 7G=',7*G)

def qs(x): return str(L(x))
def isQ(x): return L(x).polynomial().degree()<=0
def mark(x,y):
    if isQ(x) and isQ(y):
        xx=QQ(L(x)); yy=QQ(L(y))
        if (xx,yy)==(0,1): return 'Q-CUSP(0,1)'
        if (xx,yy)==(0,-1): return 'Q-CUSP(0,-1)'
        if (xx,yy)==(-1,1): return 'Q-CUSP(-1,1)'
        if (xx,yy)==(-1,-1): return 'Q-CUSP(-1,-1)'
        return 'Q-NONCUSP'
    return 'L-NONQ'

def fibline(k):
    P=k*G
    if P.is_zero():
        fr=f(rm)
        return f"{k}|O|1|O-FIBER|x={qs(rm)}; y^2={qs(fr)}|nonsquare-in-L|2 quadratic-over-L"
    X0,Y0=P[0],P[1]
    u=(2*X0-3)/ku
    v=(8*Y0+lu*u+10)/kv
    base=f"{k}|({qs(X0)},{qs(Y0)})|{P.order()}|u={qs(u)}|v={qs(v)}|"
    if u==0:
        x=rp; y=-v
        return base+f"RAMIFIED|({qs(x)},{qs(y)})[{mark(x,y)}], multiplicity2"
    if u==1:
        x=A; y=-v/8
        inf='inf+' if v==-8*q^3 else ('inf-' if v==8*q^3 else 'inf?')
        return base+f"U1|({qs(x)},{qs(y)})[{mark(x,y)}] ; {inf}[Q-CUSP]"
    if not u.is_square():
        return base+"NONSQUARE|z^2=u; x=(z*rm-rp)/(z-1); y=v/(z-1)^3; two quadratic-over-L"
    s=L(u.sqrt())
    out=[]
    for sg,z in [('+',s),('-',-s)]:
        x=(z*rm-rp)/(z-1); y=v/(z-1)^3
        out.append(f"{sg}:z={qs(z)},x={qs(x)},y={qs(y)}[{mark(x,y)}]")
    return base+"SQUARE|"+' ; '.join(out)

for k in range(21): print('ROW|'+fibline(k))

# Summary and exact Q points.
qentries=[]; lr=0; nlr=0; ram=[]; distinct=0
for k in range(21):
    P=k*G
    if P.is_zero(): nlr+=2; distinct+=2; continue
    X0,Y0=P[0],P[1]; u=(2*X0-3)/ku; v=(8*Y0+lu*u+10)/kv
    if u==0:
        ram.append(k); lr+=1; distinct+=1
        x=rp;y=-v
        if mark(x,y).startswith('Q-'):qentries.append((k,mark(x,y),x,y))
    elif u==1:
        lr+=2;distinct+=2
        x=A;y=-v/8
        if mark(x,y).startswith('Q-'):qentries.append((k,mark(x,y),x,y))
        qentries.append((k,'Q-CUSP(infinity+' if v==-8*q^3 else 'Q-CUSP(infinity-',None,None))
    elif u.is_square():
        lr+=2;distinct+=2
        s=L(u.sqrt())
        for z in [s,-s]:
            x=(z*rm-rp)/(z-1);y=v/(z-1)^3
            if mark(x,y).startswith('Q-'):qentries.append((k,mark(x,y),x,y))
    else:
        nlr+=2;distinct+=2
print('SUMMARY|distinct=',distinct,'|ramified=',ram,'|L-rational=',lr,'|quadratic-over-L=',nlr,'|Q-count=',len(qentries))
for k,m,x,y in qentries: print('QPOINT|',k,'|',m,'|', '' if x is None else qs(x),'|','' if y is None else qs(y))
print('Q4518_COMPACT_END')
