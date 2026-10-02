"""Parse and audit generated Lean polynomial literals; does not run Lean or project code."""
from pathlib import Path
from itertools import product
import ast,re,json,hashlib
P=Path(__file__).parent
s=(P/'REGENERATED_N13SpecialSmallFunctionCertificate.lean').read_text(); source=(P/'INPUT_N13SpecialSmallFunctionCertificate.lean').read_text()
def trim(p):
 p=list(p)
 while p and not p[-1]:p.pop()
 return tuple(p)
def add(p,q):return trim([(p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0) for i in range(max(len(p),len(q)))])
def neg(p):return tuple(-x for x in p)
def sub(p,q):return add(p,neg(q))
def mul(p,q):
 z=[0]*(len(p)+len(q))
 for i,a in enumerate(p):
  for j,b in enumerate(q):z[i+j]+=a*b
 return trim(z)
def pw(p,n):
 z=(1,)
 for _ in range(n):z=mul(z,p)
 return z
def comp(p,q):
 z=()
 for a in reversed(p):z=add(mul(z,q),(a,))
 return z
def parse(e):
 def go(a):
  if isinstance(a,ast.Constant) and isinstance(a.value,int):return (a.value,)
  if isinstance(a,ast.Name) and a.id=='X':return (0,1)
  if isinstance(a,ast.UnaryOp) and isinstance(a.op,ast.USub):return neg(go(a.operand))
  if isinstance(a,ast.BinOp):
   if isinstance(a.op,ast.Add):return add(go(a.left),go(a.right))
   if isinstance(a.op,ast.Sub):return sub(go(a.left),go(a.right))
   if isinstance(a.op,ast.Mult):return mul(go(a.left),go(a.right))
   if isinstance(a.op,ast.Pow):return pw(go(a.left),a.right.value)
  raise ValueError(ast.dump(a))
 return trim(go(ast.parse(e.strip().replace('^','**'),mode='eval').body))
def bits(p):return sum((v%2)*2**i for i,v in enumerate(p))
def polybits(v):return tuple((v>>i)&1 for i in range(v.bit_length()))
def certs(t):
 return [parse(m.group(1)) if m.group(1) is not None else () for m in re.finditer(r'linear_combination \(([^\n]*)\) \* two_poly|^\s*ring\s*$',t,re.M)]
def check_lc(lhs,rhs,c):assert sub(lhs,rhs)==mul((2,),c),(lhs,rhs,c)
rows=json.loads((P/'independent_certificate_math.json').read_text())['rows']; byid={(r['a'],r['b']):r for r in rows}
js=[parse(x) for x in ['X^4+X^7','1+X+X^3+X^4+X^7','X+X^2+X^3+X^4+X^5+X^6+X^8','1+X+X^4+X^5+X^6+X^8','X+X^3+X^4+X^5+X^6+X^8','1+X+X^2+X^4+X^5+X^6+X^8']]
h=parse('1+X+X^3');rhs=parse('X^4+X^5');hi=parse('1+X^2+X^3');ri=parse('X+X^2');X=(0,1);xp1=(1,1)
blocks=list(re.finditer(r'private theorem row_(\d+)_(\d+) : PairCertificate !\[([^\]]+)\] !\[([^\]]+)\] := by\n(.*?)(?=\n-- Coefficient|\nprivate theorem binary)',s,re.S));assert len(blocks)==128
supported=excluded=0
for m in blocks:
 a,b=map(int,m.group(1,2));ac=tuple(map(int,m.group(3).split(',')));bc=tuple(map(int,m.group(4).split(',')));body=m.group(5);row=byid[a,b]
 assert bits(ac)==a and bits(bc)==b
 if row['supported']:
  supported+=1
  pol=re.search(r'have hp :.*?=\s*!\[(.*?)\] := by',body,re.S);assert pol
  normal=[parse(x) for x in pol.group(1).split(',')];assert [bits(p) for p in normal]==row['jets']
  orders=list(map(int,re.search(r'apply goodJets_of_coefficients _ !\[([^\]]+)\]',body).group(1).split(',')));assert orders==row['orders']
  direct=[add(ac,mul(bc,js[0])),add(ac,mul(bc,js[1])),add(comp(ac,xp1),mul(comp(bc,xp1),js[2])),add(comp(ac,xp1),mul(comp(bc,xp1),js[3])),add(ac[::-1],mul(bc[::-1],js[4])),add(ac[::-1],mul(bc[::-1],js[5]))]
  c=certs(body);assert len(c)==6
  for lhs,right,k in zip(direct,normal,c):check_lc(lhs,right,k)
 elif row['norm']:
  excluded+=1
  factor=parse(re.search(r'have hf : \((.*?) : K\[X\]\) ∣',body).group(1));cofactor=parse(re.search(r'refine ⟨(.*?), \?_⟩',body).group(1));idx=int(re.search(r'False.elim \(obstruction_(\d+)',body).group(1));assert idx==bits(factor)
  norm=sub(sub(pw(ac,2),mul(mul(ac,bc),h)),mul(pw(bc,2),rhs))
  c=certs(body);assert len(c)==1;check_lc(norm,mul(factor,cofactor),c[0]);assert bits(norm)==row['norm']
 else:assert (a,b)==(0,0)
obs=list(re.finditer(r'private theorem obstruction_(\d+) :\n    ¬ \((.*?) : K\[X\]\).*? := by\n(.*?)(?=\nprivate theorem obstruction_|\n-- Coefficient)',s,re.S));assert len(obs)==17
for m in obs:
 f=parse(m.group(2));assert bits(f)==int(m.group(1));u,v=map(parse,re.search(r'apply obstruction _ \((.*?)\) \((.*?)\)',m.group(3)).groups());c=certs(m.group(3));assert len(c)==2
 check_lc(add(f,mul(u,X)),(1,),c[0]);check_lc(add(f,mul(v,(-1,1))),(1,),c[1])
 eqco=int(re.search(r'p.coeff (\d+)',m.group(3)).group(1));assert eqco==len(f)-1 and f[-1]==1 and eqco>0
first=s[s.index('theorem jet_polynomials_satisfy_equations :'):s.index('/-- First nonzero')]
cofs=[parse(x) for x in re.findall(r'refine ⟨([^?]*?), \?_⟩',first)];cs=certs(first);assert len(cofs)==len(cs)==6
for i,(j,cof,c) in enumerate(zip(js,cofs,cs)):
 H,R=(h,rhs) if i<2 else (comp(h,xp1),comp(rhs,xp1)) if i<4 else (hi,ri)
 check_lc(sub(add(pw(j,2),mul(H,j)),R),mul(pw(X,9),cof),c)
last=s[s.index('theorem supported_small_function_certificate :'):]
used=[tuple(map(int,p)) for p in re.findall(r'using row_(\d+)_(\d+)',last)]
expected=[(sum(v*2**i for i,v in enumerate(xs[:5])),sum(v*2**i for i,v in enumerate(xs[5:]))) for xs in product([0,1],repeat=7)]
assert used==expected
pat=r'(?m)^(?:@\[[^\n]*\]\s*)?(?:theorem|def|abbrev)\s+(\w+)([\s\S]*?)(?::=|\bwhere\b)'
def sigs(t):return {m.group(1):re.sub(r'\s+',' ',m.group(2)).strip() for m in re.finditer(pat,t)}
assert sigs(source)==sigs(s)
for m in re.finditer(r'(?m)^(?:def|abbrev)\s+(\w+)[^\n]*',source):
 name=m.group(1);old=m.group(0);assert old in s
result={'candidate_sha256':hashlib.sha256(s.encode()).hexdigest(),'public_signatures_count':len(sigs(s)),'public_signatures_equal':True,'public_definition_lines_equal':True,'source_supported_rows_verified':supported,'source_excluded_rows_verified':excluded,'source_zero_norm_rows_verified':1,'source_obstruction_factor_certificates_verified':len(obs),'source_integer_linear_combination_certificates_verified':6+69*6+58+17*2,'source_case_dispatch_order_verified':True,'method':'Independent parser of Lean polynomial literal expressions and coefficient-list arithmetic over integers; no Lean or project code executed'}
(P/'independent_source_literal_audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
