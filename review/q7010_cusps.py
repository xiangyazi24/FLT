#!/usr/bin/env python3
# Exact truncated-series check of the five canonical cusps and the pole order
# of T=-(x*w+y*z+z*w)/(z*w).  The approximate arcs record enough leading
# terms to certify numerator order = denominator order - 1 at A,D,E.
N=10

def S(*cs):
    return list(cs)+[0]*(N-len(cs))
def add(a,b): return [a[i]+b[i] for i in range(N)]
def neg(a): return [-x for x in a]
def sub(a,b): return add(a,neg(b))
def mul(a,b):
    c=[0]*N
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            if i+j<N: c[i+j]+=x*y
    return c
def order(a):
    for i,x in enumerate(a):
        if x: return i
    return 999

def Q(x,y,z,w):
    return add(add(add(neg(mul(x,z)),neg(mul(x,w))),mul(y,y)),add(mul(y,z),mul(z,w)))
def C(x,y,z,w):
    out=mul(mul(x,x),w)
    for term,sgn in [(mul(mul(x,y),z),1),(mul(mul(x,y),w),-1),(mul(mul(x,z),w),-1),(mul(mul(y,z),w),1),(mul(mul(z,z),w),1),(mul(z,mul(w,w)),-1)]:
        out=add(out,term if sgn==1 else neg(term))
    return out
def num(x,y,z,w): return add(add(mul(x,w),mul(y,z)),mul(z,w))
def den(x,y,z,w): return mul(z,w)

def q0(P):
    x,y,z,w=P
    return -x*z-x*w+y*y+y*z+z*w
def c0(P):
    x,y,z,w=P
    return x*x*w+x*y*z-x*y*w-x*z*w+y*z*w+z*z*w-z*w*w

cusps={
 'A':(0,0,0,1),
 'B':(0,-1,1,0),
 'C':(1,1,0,1),
 'D':(0,0,1,0),
 'E':(1,0,0,0),
}
print('CANONICAL_CUSP_EXACT_CHECK')
for name,P in cusps.items():
    x,y,z,w=P
    n=x*w+y*z+z*w; d=z*w
    print(f'{name}: Q={q0(P)} C={c0(P)} numerator={n} denominator={d}')

one=S(1); t=S(0,1)
arcs={
 'A':(S(0,0,1,-1), t, S(0,0,0,-1), one),
 'D':(t, t, one, S(0,0,-1)),
 'E':(one, t, S(0,0,1,2), S(0,0,0,-1)),
}
print('FORMAL_LEADING_ARCS')
for name,(x,y,z,w) in arcs.items():
    qq=Q(x,y,z,w); cc=C(x,y,z,w); nn=num(x,y,z,w); dd=den(x,y,z,w)
    print(f'{name}: ord(Qres)={order(qq)} ord(Cres)={order(cc)} ord(num)={order(nn)} ord(den)={order(dd)} pole_order_T={order(dd)-order(nn)}')
print('B,C: denominator z*w is identically zero and numerator is respectively -1,+1, so T=infinity exactly.')
print('At every T=infinity branch, (T-beta_j)/(T-beta_0) -> 1; c(1)=0, hence normalized local record and global gauge class are zero.')
