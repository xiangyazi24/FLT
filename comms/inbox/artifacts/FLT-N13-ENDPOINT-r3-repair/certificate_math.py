import json
from pathlib import Path
OUT=Path(__file__).parent

def mul(a,b):
 r=0
 while b:
  if b&1:r^=a
  a<<=1;b>>=1
 return r

def powp(a,n):
 r=1
 for _ in range(n):r=mul(r,a)
 return r

def divmodp(a,b):
 if not b:raise ZeroDivisionError
 q=0
 while a.bit_length()>=b.bit_length():
  k=a.bit_length()-b.bit_length();q^=1<<k;a^=b<<k
 return q,a

def comp(a,b):
 r=0
 for i in range(a.bit_length()):
  if a>>i&1:r^=powp(b,i)
 return r

def poly(a):
 return ' + '.join('1' if i==0 else 'X' if i==1 else f'X ^ {i}' for i in range(a.bit_length()) if a>>i&1) or '0'

def order(a):
 return next((i for i in range(9) if a>>i&1),9)
H=0b1011;R=(1<<5)|(1<<4);HI=0b1101;RI=0b110
jets=[(1<<4)|(1<<7),1|(1<<1)|(1<<3)|(1<<4)|(1<<7),sum(1<<i for i in [1,2,3,4,5,6,8]),sum(1<<i for i in [0,1,4,5,6,8]),sum(1<<i for i in [1,3,4,5,6,8]),sum(1<<i for i in [0,1,2,4,5,6,8])]
res=[]
for i,s in enumerate(jets):
 h,r=(H,R) if i<2 else (comp(H,3),comp(R,3)) if i<4 else (HI,RI)
 residual=powp(s,2)^mul(h,s)^r
 q,rem=divmodp(residual,1<<9)
 assert rem==0
 res.append({'index':i,'cofactor':q,'cofactor_polynomial':poly(q)})
T=mul(1<<16,powp(3,16))
rows=[]
for a in range(32):
 for b in range(4):
  n=powp(a,2)^mul(mul(a,b),H)^mul(powp(b,2),R)
  good=n!=0 and divmodp(T,n)[1]==0
  ai=sum(((a>>i)&1)<<(4-i) for i in range(5));bi=((b&1)<<1)|((b>>1)&1)
  js=[a^mul(b,jets[0]),a^mul(b,jets[1]),comp(a,3)^mul(comp(b,3),jets[2]),comp(a,3)^mul(comp(b,3),jets[3]),ai^mul(bi,jets[4]),ai^mul(bi,jets[5])]
  orders=[order(p) for p in js]
  code=sum(w*k for w,k in zip([1,-1,7,-7,8,-8],orders))%19
  if good:assert max(orders)<9 and code==0,(a,b,n,orders,code)
  row={'a':a,'b':b,'norm':n,'supported':good,'jets':js,'orders':orders,'code':code}
  if not good and n:
   f=n;q=1
   for p in [2,3]:
    while divmodp(f,p)[1]==0:
     f=divmodp(f,p)[0];q=mul(q,p)
   assert f>1 and mul(f,q)==n
   v0,r0=divmodp(f^1,2);v1,r1=divmodp(f^1,3)
   assert r0==r1==0
   row.update(factor=f,cofactor=q,bezout_x=v0,bezout_x1=v1)
  rows.append(row)
(OUT/'certificate_math.json').write_text(json.dumps({'residual_cofactors':res,'rows':rows},indent=2)+'\n')
print('Residual cofactors:',res)
print('Supported:',sum(r['supported'] for r in rows),'invalid nonzero:',sum(not r['supported'] and bool(r['norm']) for r in rows),'zero norm:',sum(not r['norm'] for r in rows))
print('Distinct obstruction factors:',sorted(set(r['factor'] for r in rows if 'factor' in r)))
print('All 128 coefficient pairs checked with exact GF(2) bit-polynomial arithmetic')
