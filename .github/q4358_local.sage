from sage.all import *
from itertools import product

F3 = GF(3)

def cube_class(a, basis):
    if a == 0:
        raise ValueError("zero has no multiplicative cube class")
    for exps in product(range(3), repeat=len(basis)):
        b = prod(basis[i]**exps[i] for i in range(len(basis)))
        q = a / b
        try:
            ok = q.is_nth_power(3)
        except (AttributeError, NotImplementedError):
            try:
                q.nth_root(3)
                ok = True
            except (ValueError, ArithmeticError):
                ok = False
        if ok:
            return tuple(ZZ(e) for e in exps)
    raise RuntimeError("cube class not found for %s" % a)

def span_basis(vectors, ncols):
    B=[]
    r=0
    for v in vectors:
        nr=matrix(F3, B+[list(v)], ncols=ncols).rank()
        if nr>r:
            B.append(tuple(F3(x) for x in v)); r=nr
    return B

def full_span(B):
    if not B:
        return [tuple()]
    n=len(B[0]); out=set()
    for cc in product(range(3), repeat=len(B)):
        v=[F3(0)]*n
        for c,b in zip(cc,B):
            for j in range(n): v[j]+=F3(c)*b[j]
        out.add(tuple(ZZ(x) for x in v))
    return sorted(out)

def setup_local(p, prec=80):
    Q=Qp(p, prec=prec, type='capped-rel')
    R=PolynomialRing(Q,'X'); X=R.gen()
    K=Q.extension(X**2+X+1, names='z')
    z=K.gen()
    s=1+2*z
    g1=(3+2*s)/7; g2=s; g3=(3-2*s)/7; g4=-s
    A=1+3*z; Bb=1+3*z**2
    c=-A*Bb**2
    def rhs(m): return c*(m-g1)*(m-g2)*(m-g3)**2*(m-g4)**2
    m0=K(1)
    h10=(m0-g1)/(m0-g4); h20=(m0-g2)/(m0-g4)
    if p==2:
        cbasis=[K(2),z]
        uniformizer=K(2)
    else:
        uniformizer=1-z
        cbasis=[uniformizer,z,1+uniformizer**2,1+uniformizer**3]
    return K,z,s,(g1,g2,g3,g4),c,rhs,m0,h10,h20,uniformizer,cbasis

def point_vector(m, data):
    K,z,s,gg,c,rhs,m0,h10,h20,pi,cbasis=data
    g1,g2,g3,g4=gg
    if m==g4 or m==g1 or m==g2 or m==g3:
        return None
    rr=rhs(m)
    if rr==0: return None
    try:
        if not rr.is_nth_power(3): return None
    except (AttributeError, NotImplementedError):
        try: rr.nth_root(3)
        except (ValueError, ArithmeticError): return None
    aa=((m-g1)/(m-g4))/h10
    bb=((m-g2)/(m-g4))/h20
    return cube_class(aa,cbasis)+cube_class(bb,cbasis)

def enum_p2(depth=5):
    data=setup_local(2)
    K,z,*rest=data
    digits=[K(0),K(1),z,1+z]
    vecs=[]; witnesses={}
    for ds in product(digits, repeat=depth):
        r=sum(ds[i]*K(2)**i for i in range(depth))
        m=1+2*r
        v=point_vector(m,data)
        if v is not None:
            vecs.append(v); witnesses.setdefault(v,m)
    B=span_basis(vecs,4)
    print("P2_POINT_CLASS_COUNT",len(set(vecs)))
    print("P2_BASIS",[tuple(ZZ(x) for x in b) for b in B])
    print("P2_FULL_TABLE",full_span(B))
    for b in B: print("P2_WITNESS",tuple(ZZ(x) for x in b),witnesses.get(tuple(ZZ(x) for x in b),witnesses.get(b)))
    return data,B

def enum_p3(depth=7):
    data=setup_local(3,prec=100)
    K,z,s,gg,c,rhs,m0,h10,h20,pi,cbasis=data
    digits=[K(0),K(1),K(2)]
    vecs=[]; witnesses={}
    # integral m modulo pi^depth
    for ds in product(digits, repeat=depth):
        m=sum(ds[i]*pi**i for i in range(depth))
        v=point_vector(m,data)
        if v is not None:
            vecs.append(v); witnesses.setdefault(v,m)
    # a small search at negative valuations
    for k in [1,2,3]:
      for ds in product(digits, repeat=4):
        if ds[0]==0: continue
        u=sum(ds[i]*pi**i for i in range(4))
        m=u/pi**k
        v=point_vector(m,data)
        if v is not None:
            vecs.append(v); witnesses.setdefault(v,m)
    B=span_basis(vecs,8)
    print("P3_POINT_CLASS_COUNT",len(set(vecs)))
    print("P3_BASIS",[tuple(ZZ(x) for x in b) for b in B])
    print("P3_FULL_TABLE",full_span(B))
    for b in B: print("P3_WITNESS",tuple(ZZ(x) for x in b),witnesses.get(tuple(ZZ(x) for x in b),witnesses.get(b)))
    return data,B

def in_span(v,B):
    if not B: return all(F3(x)==0 for x in v)
    r=matrix(F3,[list(b) for b in B]).rank()
    return matrix(F3,[list(b) for b in B]+[list(v)]).rank()==r

def invariant_candidates(data2,B2,data3,B3):
    out2=[]; out3=[]; both=[]
    for a,b,c in product(range(3),repeat=3):
        # alpha = 2^b * s^c, beta = z^a
        v2=cube_class(data2[0](2)**b*data2[2]**c,data2[-1])+cube_class(data2[1]**a,data2[-1])
        v3=cube_class(data3[0](2)**b*data3[2]**c,data3[-1])+cube_class(data3[1]**a,data3[-1])
        ok2=in_span(v2,B2); ok3=in_span(v3,B3)
        if ok2: out2.append((a,b,c,v2))
        if ok3: out3.append((a,b,c,v3))
        if ok2 and ok3: both.append((a,b,c,v2,v3))
    print("GLOBAL_QINV_P2_SURVIVORS",out2)
    print("GLOBAL_QINV_P3_SURVIVORS",out3)
    print("GLOBAL_QINV_BOTH",both)

print("Q4358_SAGE_BEGIN")
d2,B2=enum_p2(6)
d3,B3=enum_p3(7)
invariant_candidates(d2,B2,d3,B3)
print("Q4358_SAGE_END")
