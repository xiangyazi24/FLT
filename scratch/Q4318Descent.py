import math
Ds=[1,2,4,7,14,28,49,98,196]
primes=[2,3,5,7,11,13,17,19,23,29,31,37,41,43]

def data(d):
 i=0;j=0;q=d
 while q%2==0:i+=1;q//=2
 while q%7==0:j+=1;q//=7
 istar=(-i)%3;jstar=(-j)%3
 ds=2**istar*7**jstar
 c=2**((i+istar)//3)*7**((j+jstar)//3)
 return ds,c

def C(d,a,b,n):
 ds,c=data(d)
 return ds*b**3-d*a**3-8*c*a*b*n-56*n**3

for d in Ds:
 ds,c=data(d)
 bad=[]
 for p in primes:
  ok=False
  for a in range(p):
   for b in range(p):
    for n in range(p):
     if (a,b,n)!=(0,0,0) and C(d,a,b,n)%p==0:
      ok=True;break
    if ok:break
   if ok:break
  if not ok:bad.append(p)
 sols=[]
 B=70
 for n in range(1,B+1):
  for a in range(-B,B+1):
   for b in range(-B,B+1):
    if math.gcd(math.gcd(abs(a),abs(b)),n)!=1:continue
    if C(d,a,b,n)==0:sols.append((a,b,n))
 print('d',d,'dstar',ds,'c',c,'badmod',bad,'sols',sols[:20],'nsol',len(sols))
