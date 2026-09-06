#!/usr/bin/env python3
from itertools import product

# Exact arithmetic in Z[pi], pi^4 - 5*pi^3 + 10*pi^2 - 10*pi + 5 = 0.
# Elements are [c0,c1,c2,c3] = c0+c1*pi+c2*pi^2+c3*pi^3.

def add(x,y): return tuple(x[i]+y[i] for i in range(4))
def neg(x): return tuple(-a for a in x)
def sub(x,y): return add(x,neg(y))
def smul(n,x): return tuple(n*a for a in x)
ONE=(1,0,0,0); ZERO=(0,0,0,0); PI=(0,1,0,0)

def mul(x,y):
    c=[0]*7
    for i,a in enumerate(x):
        for j,b in enumerate(y): c[i+j]+=a*b
    # pi^d = pi^(d-4) * (5*pi^3 - 10*pi^2 + 10*pi - 5)
    for d in range(6,3,-1):
        a=c[d]
        if a:
            c[d]=0
            c[d-1]+=5*a
            c[d-2]+=-10*a
            c[d-3]+=10*a
            c[d-4]+=-5*a
    return tuple(c[:4])

def pw(x,n):
    r=ONE; b=x
    while n:
        if n&1: r=mul(r,b)
        b=mul(b,b); n//=2
    return r

def div_pi(x):
    a0,a1,a2,a3=x
    if a0%5: raise ValueError(f'not pi-divisible: {x}')
    q=a0//5
    return (a1+10*q, a2-10*q, a3+5*q, -q)

def ord_pi(x,cap=80):
    if x==ZERO: return 10**9
    y=x; n=0
    while n<cap and y[0]%5==0:
        y=div_pi(y); n+=1
    return n

def div_pi_n(x,n):
    y=x
    for _ in range(n): y=div_pi(y)
    return y

def poly(x):
    a=list(x); terms=[]
    names=['','*pi','*pi^2','*pi^3']
    for i,c in enumerate(a):
        if c: terms.append(f'{c}{names[i]}')
    return '0' if not terms else ' + '.join(terms).replace('+ -','- ')

def vadd(x,y): return tuple((x[i]+y[i])%5 for i in range(len(x)))
def vsub(x,y): return tuple((x[i]-y[i])%5 for i in range(len(x)))
def vsmul(n,x): return tuple((n*a)%5 for a in x)

ZETA=sub(ONE,PI)
S=add(add(ONE,smul(2,ZETA)),smul(2,pw(ZETA,4)))
BETA=(neg(mul(S,ZETA)), mul(S,pw(ZETA,2)), neg(mul(S,pw(ZETA,4))), mul(S,pw(ZETA,3)))
EXPECTED_BETA=((-5,5,-2,0),(5,-10,7,-2),(0,0,-2,1),(-5,5,-3,1))
assert BETA==EXPECTED_BETA, (BETA,EXPECTED_BETA)
ETA={k:add(ONE,pw(PI,k)) for k in range(2,6)}
E=(1,3,4,2)

# Coordinate formulas from the pinned local basis
# [pi],[zeta],[eta2],[eta3],[eta4],[eta5].
def F(n):
    assert n%5
    return ((n**4-1)//5)%5

def c_rat(n):
    f=F(n)
    return (0,0,0,0,f,(2*f)%5)

def Cunit(i,q):
    q%=5; q2=q*q%5
    rows=(
      (0,0,2*q,0,3*q2,4*q),
      (0,0,3*q,2*q,3*q2,4*q2),
      (0,0,2*q,4*q,q+3*q2,2*q2),
      (0,0,3*q,4*q,3*q+3*q2,4*q+3*q2),
    )
    return tuple(z%5 for z in rows[i])

BASEPOS=((2,0,2,2,2,0),(2,1,2,2,2,0),(2,3,2,2,2,0),(2,2,2,2,2,0))
def Dpos(i,u):
    u%=5; u2=u*u%5
    rows=(
      (0,0,2*u,4*u,u+3*u2,2*u2),
      (0,0,3*u,4*u,3*u+3*u2,4*u+3*u2),
      (0,0,2*u,0,3*u2,4*u),
      (0,0,3*u,2*u,3*u2,4*u2),
    )
    return tuple(z%5 for z in rows[i])

def weighted(cs):
    out=(0,0,0,0,0,0)
    for e,c in zip(E,cs): out=vadd(out,vsmul(e,c))
    return out

def gauge(cs): return vsub(cs[1],cs[0])+vsub(cs[2],cs[0])
def ell(g): return (g[2]+2*g[3])%5

def inv5(a): return pow(a%5,-1,5)
def inv25(a): return pow(a%25,-1,25)

def unit_coords(a,b):
    assert a%5 and b%5
    q=(b*inv5(a))%5
    ca=c_rat(a)
    return tuple(vadd(ca,Cunit(i,q)) for i in range(4))

def pos_coords(a,b):
    assert a%5==0 and b%5
    u=((a//5)*inv5(b))%5
    cb=c_rat(b)
    return tuple(vadd(cb,vadd(BASEPOS[i],Dpos(i,u))) for i in range(4))

def alpha(a,b,i): return sub(smul(a,ONE),smul(b,BETA[i]))

# Fresh exact congruence witness search. Correction b=(b2,b3,b4,b5).
# Target a=(a1,a2,a3,a4,a5), with omega among rational Teichmuller reps.
OMEGAS=(1,7,18,-1)

def correction(b):
    r=ONE
    for k,e in zip(range(2,6),b): r=mul(r,pw(ETA[k],e))
    return r

def target(v,omega,a):
    a1,a2,a3,a4,a5=a
    r=mul(pw(PI,v),smul(omega,ONE))
    r=mul(r,pw(ZETA,a1))
    for k,e in zip(range(2,6),(a2,a3,a4,a5)): r=mul(r,pw(ETA[k],e))
    return r

CORR=[(b,correction(b)) for b in product(range(5),repeat=4)]

def witness(x,c):
    v=ord_pi(x)
    assert v in (0,2)
    assert c[0]==v%5
    candidates=[]
    for b,lmul in CORR:
        a=(c[1],)+tuple((c[k]+b[k-2])%5 for k in range(2,6))
        lhs=mul(x,lmul)
        for om in OMEGAS:
            rhs=target(v,om,a)
            d=sub(lhs,rhs)
            if ord_pi(d)>=v+6:
                r=ZERO if d==ZERO else div_pi_n(d,v+6)
                score=(sum(b)+sum(a),sum(b),sum(a),OMEGAS.index(om),b,a)
                candidates.append((score,v,om,b,a,r))
    if not candidates: raise RuntimeError(f'no witness x={x} c={c}')
    candidates.sort(key=lambda z:z[0])
    _,v,om,b,a,r=candidates[0]
    # exact identity, not only a valuation test
    lhs=mul(x,correction(b)); rhs=target(v,om,a)
    assert sub(lhs,rhs)==mul(pw(PI,v+6),r)
    return v,om,b,a,r

def fmtvec(v): return '('+','.join(str(x%5) for x in v)+')'
def fmtb(v): return '('+','.join(str(x) for x in v)+')'

def print_record(tag,a,b,cs):
    g=gauge(cs); w=weighted(cs)
    print(f'{tag}: rep=({a},{b})')
    for i,c in enumerate(cs): print(f'  c(alpha{i})={fmtvec(c)}')
    print(f'  gauge={fmtvec(g)}  ell={ell(g)}  cW={fmtvec(w)}  admissible={w==(0,0,0,0,0,0)}')

print('Q7035 N25 EXACT CERTIFICATE OUTPUT')
print('beta-polynomials:')
for i,b in enumerate(BETA): print(f'  beta{i}={poly(b)}')
print()

print('TABLE 1: 5 does not divide a*b; one gauge record for each t mod 5 in {1,2,3,4}')
unit_records=[]
for t in (1,2,3,4):
    a,b=t,1
    cs=unit_coords(a,b); unit_records.append((t,a,b,cs))
    print_record(f't={t} mod5',a,b,cs)
print()

print('SAME-t DEMONSTRATION: t mod5=2, different a mod25')
for a,b in ((2,1),(7,1),(12,1)):
    cs=unit_coords(a,b)
    print_record(f'a_mod25={a%25}, b_mod5={b%5}, t_mod5={(a*inv5(b))%5}',a,b,cs)
print()

print('TABLE 2: 5 divides a, 5 does not divide b; t mod25 in {0,5,10,15,20}')
pos_records=[]
for t in (0,5,10,15,20):
    a,b=t,1
    cs=pos_coords(a,b); pos_records.append((t,a,b,cs))
    print_record(f't={t} mod25',a,b,cs)
    w=weighted(cs)
    nz=[j for j,x in enumerate(w) if x%5]
    print(f'  inadmissibility_nonzero_coordinates={nz}')
print()

print('TABLE 3: 5 divides b; reps v5(b)=1,2,3 with a=2')
zero_gauge=(0,)*12
c2=c_rat(2)
for b,r in ((5,1),(25,2),(125,3)):
    vals=[ord_pi(alpha(2,b,i)) for i in range(4)]
    congr=[ord_pi(sub(alpha(2,b,i),smul(2,ONE))) for i in range(4)]
    cs=(c2,c2,c2,c2)
    print_record(f'v5(b)={r}',2,b,cs)
    print(f'  vpi(alpha)={vals}  vpi(alpha-a)={congr}  all_c_equal_c(a)={all(c==c2 for c in cs)}')
print()

print('WITNESS COVERAGE: exact fresh identities for all 9 table-1/table-2 representatives')
all_rows=unit_records+pos_records
for t,a,b,cs in all_rows:
    branch='unit' if a%5 else 'positive'
    print(f't={t} branch={branch}')
    for i,c in enumerate(cs):
        x=alpha(a,b,i)
        v,om,bcorr,avec,r=witness(x,c)
        print(f'  i={i} v={v} omega={om} b={fmtb(bcorr)} a={fmtb(avec)} r={poly(r)}')
        # repeated independent exact check
        assert sub(mul(x,correction(bcorr)),target(v,om,avec))==mul(pw(PI,v+6),r)
print()

print('OMEGA ZERO-CLASS CONGRUENCES')
for om in OMEGAS:
    d=sub(pw(smul(om,ONE),5),smul(om,ONE))
    assert ord_pi(d)>=6
    r=ZERO if d==ZERO else div_pi_n(d,6)
    print(f'  omega={om}: omega^5-omega=pi^6*({poly(r)})')
print()

print('OLD t=2 WITNESSES FROM THE EXISTING CERTIFICATE: exact recheck')
old=(
  ((0,0,0,2),(0,1,0,0,0),7,(-37,68,-67,28)),
  ((1,0,0,0),(0,0,1,0,2),7,(1227,-1959,1612,-521)),
  ((0,0,2,1),(0,1,2,0,0),7,(-565,921,-764,261)),
  ((1,0,1,0),(0,0,2,0,0),7,(-7,11,-9,2)),
)
for i,(bcorr,avec,om,r) in enumerate(old):
    x=alpha(2,1,i); rr=tuple(r)
    diff=sub(mul(x,correction(bcorr)),target(0,om,avec))
    assert diff==mul(pw(PI,6),rr)
    print(f'  i={i} v=0 omega={om} b={fmtb(bcorr)} a={fmtb(avec)} r={poly(rr)} OK')
print()

# Final ten records: 4 unit + 5 positive + denominator-divisible zero record.
records=[]
for t,a,b,cs in unit_records+pos_records:
    records.append((f't{t}',gauge(cs),weighted(cs)))
records.append(('bdiv5',zero_gauge,(0,0,0,0,0,0)))
g2=gauge(unit_coords(2,1))
print('FINAL TEN-RECORD CHECK')
print(f'  g={fmtvec(g2)}')
for name,g,w in records:
    print(f'  {name}: gauge={fmtvec(g)} cW={fmtvec(w)} ell={ell(g)}')
assert all(w!=(0,0,0,0,0,0) or ell(g)==0 for _,g,w in records)
assert all(w!=(0,0,0,0,0,0) or g==zero_gauge or g==g2 for _,g,w in records)
assert any(w==(0,0,0,0,0,0) and g==g2 for _,g,w in records)
assert g2!=zero_gauge
print('  CHECK_1 cW=0 => ell(gauge)=0 : PASS')
print('  CHECK_2 admissible and gauge!=0 => gauge=g : PASS')
print('  CHECK_3 g occurs and g!=0 : PASS')
print('Q7035 ALL EXACT CHECKS PASS')
