#!/usr/bin/env python3
import math, subprocess, time
import numpy as np

B = 10_000
Avals = np.arange(-B, B + 1, dtype=np.int64)
maxN = 71 * B**4
maxroot = int(maxN ** 0.2) + 10
while (maxroot + 1) ** 5 <= maxN:
    maxroot += 1
while maxroot ** 5 > maxN:
    maxroot -= 1
fifths = np.array([n**5 for n in range(maxroot + 1)], dtype=np.int64)
fifths25 = 25 * fifths[fifths <= maxN // 25]

def member_sorted(vals, arr):
    idx = np.searchsorted(arr, vals)
    ok = idx < len(arr)
    out = np.zeros(vals.shape, dtype=bool)
    ii = np.nonzero(ok)[0]
    out[ii] = arr[idx[ii]] == vals[ii]
    return out

def norm_array(a, b):
    # a^4+5a^3b+15a^2b^2+25ab^3+25b^4, Horner form.
    return ((((a + 5*b) * a + 15*b*b) * a + 25*b**3) * a + 25*b**4)

t0 = time.time()
all_candidates = []
neg_candidates = []
for b in range(1, B + 1):
    N = norm_array(Avals, np.int64(b))
    m1 = member_sorted(N, fifths)
    m25 = member_sorted(N, fifths25)
    idxs = np.nonzero(m1 | m25)[0]
    for idx in idxs.tolist():
        a = int(Avals[idx]); n = int(N[idx])
        if math.gcd(a, b) != 1:
            continue
        # Primitive local pi valuation is 2 iff 5|a and 5∤b, otherwise 0.
        expected = m25[idx] if (a % 5 == 0 and b % 5 != 0) else m1[idx]
        if not expected:
            continue
        row = (a, b, n)
        all_candidates.append(row)
        if b % 5 == 0:
            neg_candidates.append(row)

elapsed = time.time() - t0
print(f"NUMPY_VERSION={np.__version__}")
print(f"BOUND={B}")
print(f"PAIR_DOMAIN=b=1..{B}, a=-{B}..{B}; sign-normalized b>0")
print(f"RAW_PAIRS={B*(2*B+1)}")
print(f"NORM_FILTER_SECONDS={elapsed:.3f}")
print(f"ALL_NORM_CANDIDATES={len(all_candidates)}")
print(f"NEGATIVE_BRANCH_NORM_CANDIDATES={len(neg_candidates)}")
print("NEGATIVE_BRANCH_NORM_CANDIDATE_LIST=", neg_candidates[:100])
print("ALL_NORM_CANDIDATE_HEAD=", all_candidates[:100])

# Classify every necessary norm candidate exactly in PARI/GP.  W fifth-power
# candidates are the only possible rational t with a global K-point on the
# weighted cover.  For those, recover all four S-unit Kummer classes by
# testing the 125 [zeta]^r [eps]^s [pi]^p classes.
pairs_gp = ";".join(f"[{a},{b}]" for a,b,_ in all_candidates)
gp = r'''
default(parisizemax, 1200000000);
P = y^4+y^3+y^2+y+1; nf=nfinit(P); z=Mod(y,P); pi5=1-z;
s=1+2*z+2*z^4; eps=1+z;
beta=[-s*z,s*z^2,-s*z^4,s*z^3]; e=[1,3,4,2];
global5(u)=#nfroots(nf,x^5-u)>0;
Wab(a,b)=prod(i=1,4,(a-b*beta[i])^e[i]);
sub5(u,v)=vector(#u,i,lift(Mod(u[i]-v[i],5)));
suclass(u)={
  for(p=0,4,for(r=0,4,for(q=0,4,
    if(global5(u/(z^r*eps^q*pi5^p)),return([r,q,p]));
  )));
  return([]);
};
C=[%PAIRS%];
countW=0; countA=0; countWneg=0;
print("PARI_SEARCH_CANDIDATES=",#C);
for(k=1,#C,
  a=C[k][1]; b=C[k][2]; al=vector(4,i,a-b*beta[i]);
  ga=global5(al[1]); if(ga,countA++);
  gw=global5(Wab(a,b));
  if(gw,
    countW++; if(b%5==0,countWneg++);
    v=vector(4,i,suclass(al[i]));
    A=sub5(v[2],v[1]); Bv=sub5(v[3],v[1]); C3=sub5(v[4],v[1]);
    fixed=(Bv==[0,0,0] && A[3]==0 && A[1]==2*A[2]%5);
    cf=if(fixed,A[2],-1);
    print("W_PASS a=",a," b=",b," alpha0_fifth=",ga,
      " v=",v," gaugeA=",A," gaugeB=",Bv," gaugeC3=",C3,
      " fixed=",fixed," coeff=",cf);
  );
);
print("GLOBAL_W_PASS_COUNT=",countW);
print("GLOBAL_W_PASS_NEGATIVE_BRANCH_COUNT=",countWneg);
print("GLOBAL_ALPHA0_FIFTH_COUNT=",countA);
'''.replace('%PAIRS%', pairs_gp)
res = subprocess.run(['gp','-q'], input=gp, text=True, capture_output=True, timeout=1200)
print("--- PARI CLASSIFICATION STDOUT ---")
print(res.stdout, end='')
print("--- PARI CLASSIFICATION STDERR ---")
print(res.stderr, end='')
print(f"PARI_RETURN_CODE={res.returncode}")
if res.returncode != 0:
    raise SystemExit(res.returncode)
