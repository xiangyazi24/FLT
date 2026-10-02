"""Independent exact F2 coefficient-list arithmetic; no Lean or project code executed."""
from itertools import product
from pathlib import Path
import json
P=Path(__file__).parent

def trim(p):
 p=list(p)
 while p and p[-1]==0:p.pop()
 return tuple(p)
def add(p,q):
 return trim([(p[i] if i<len(p) else 0)^(q[i] if i<len(q) else 0) for i in range(max(len(p),len(q)))])
def mul(p,q):
 out=[0]*(len(p)+len(q))
 for i,a in enumerate(p):
  for j,b in enumerate(q):out[i+j]^=a*b
 return trim(out)
def pw(p,n):
 out=(1,)
 for _ in range(n):out=mul(out,p)
 return out
def comp(p,q):
 out=()
 for a in reversed(p):out=add(mul(out,q),(a,))
 return out
def divide(p,q):
 assert q
 p=trim(p);out=[0]*max(0,len(p)-len(q)+1)
 while len(p)>=len(q):
  k=len(p)-len(q);out[k]^=1;p=add(p,(0,)*k+q)
 return trim(out),p
def at(p,i):return p[i] if i<len(p) else 0
def order(p):return next((i for i in range(9) if at(p,i)),9)
def exps(xs):return trim([int(i in xs) for i in range(max(xs)+1)])
def bits(p):return sum(v*2**i for i,v in enumerate(p))
def terms(p):return [i for i,v in enumerate(p) if v]
X=(0,1);xp1=(1,1);h=exps([0,1,3]);rhs=exps([4,5]);hi=exps([0,2,3]);ri=exps([1,2])
jets=[exps(xs) for xs in [[4,7],[0,1,3,4,7],[1,2,3,4,5,6,8],[0,1,4,5,6,8],[1,3,4,5,6,8],[0,1,2,4,5,6,8]]]
residuals=[]
for i,s in enumerate(jets):
 H,R=(h,rhs) if i<2 else (comp(h,xp1),comp(rhs,xp1)) if i<4 else (hi,ri)
 r=add(add(pw(s,2),mul(H,s)),R);q,rem=divide(r,pw(X,9))
 assert not rem
 residuals.append({'index':i,'cofactor_exponents':terms(q),'cofactor_bits':bits(q)})
T=mul(pw(X,16),pw(xp1,16));rows=[]
for ac in product(range(2),repeat=5):
 for bc in product(range(2),repeat=2):
  a=trim(ac);b=trim(bc);n=add(add(pw(a,2),mul(mul(a,b),h)),mul(pw(b,2),rhs))
  supported=bool(n) and not divide(T,n)[1]
  ai=trim(ac[::-1]);bi=trim(bc[::-1])
  js=[add(a,mul(b,jets[0])),add(a,mul(b,jets[1])),add(comp(a,xp1),mul(comp(b,xp1),jets[2])),add(comp(a,xp1),mul(comp(b,xp1),jets[3])),add(ai,mul(bi,jets[4])),add(ai,mul(bi,jets[5]))]
  orders=[order(j) for j in js];weighted=sum(w*v for w,v in zip([1,-1,7,-7,8,-8],orders))
  if supported:
   assert all(v<9 and at(j,v)==1 and all(at(j,k)==0 for k in range(v)) for j,v in zip(js,orders))
   assert weighted%19==0
  rest=n
  if n:
   for f in [X,xp1]:
    while True:
     q,r=divide(rest,f)
     if r:break
     rest=q
   assert (rest==(1,))==supported
  rows.append({'a':bits(a),'b':bits(b),'norm':bits(n),'supported':supported,'jets':[bits(j) for j in js],'orders':orders,'code':weighted%19,'weighted_integer':weighted,'remaining_factor':bits(rest)})
rows.sort(key=lambda r:(r['a'],r['b']))
other=json.loads((P/'certificate_math.json').read_text())
for own,theirs in zip(rows,other['rows']):
 for key in ['a','b','norm','supported','jets','orders','code']:assert own[key]==theirs[key],(key,own,theirs)
result={'method':'Independent coefficient-list convolution and Euclidean division over F2, not Lean or project code','residual_cofactors':residuals,'counts':{'supported':sum(r['supported'] for r in rows),'unsupported_nonzero':sum(bool(r['norm']) and not r['supported'] for r in rows),'zero_norm':sum(not r['norm'] for r in rows)},'supported_max_jet_order':max(max(r['orders']) for r in rows if r['supported']),'supported_weighted_integer_values':sorted(set(r['weighted_integer'] for r in rows if r['supported'])),'matches_other_artifact_all_128_rows':True,'rows':rows}
(P/'independent_certificate_math.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2))
