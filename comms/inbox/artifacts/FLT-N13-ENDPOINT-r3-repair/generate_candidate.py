from certificate_math import *
import re

def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a

def iz(a):return [(a>>i)&1 for i in range(max(a.bit_length(),1))]
def ia(a,b):return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def neg(a):return [-x for x in a]
def sub(a,b):return ia(a,neg(b))
def im(a,b):
 r=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):r[i+j]+=x*y
 return trim(r)
def ip(a,n):
 r=[1]
 for _ in range(n):r=im(r,a)
 return r

def ic(a,b):
 r=[0]
 for i,x in enumerate(a):r=ia(r,[x*y for y in ip(b,i)])
 return r

def term(c,i):
 x='1' if i==0 else 'X' if i==1 else f'X ^ {i}'
 if i==0:return str(abs(c))
 return x if abs(c)==1 else f'{abs(c)} * {x}'
def integer_poly(a):
 terms=[]
 for i,c in enumerate(a):
  if c:
   t=term(c,i)
   if not terms:terms.append(('-' if c<0 else '')+t)
   else:terms.append((' - ' if c<0 else ' + ')+t)
 return ''.join(terms) or '0'
def lc(lhs,rhs):
 diff=sub(lhs,rhs)
 assert all(x%2==0 for x in diff),(lhs,rhs,diff)
 h=[x//2 for x in diff]
 return f'linear_combination ({integer_poly(h)}) * two_poly' if any(h) else 'ring'

def vec(bits,n):return '!['+', '.join(str((bits>>i)&1) for i in range(n))+']'
def plist(polys):return '!['+',\n      '.join(poly(p) for p in polys)+']'

src=(Path(__file__).parent / 'INPUT_N13SpecialSmallFunctionCertificate.lean').read_text()
start=src.index('abbrev K :=')
pre=src[start:src.index('/-- The displayed')]
post=src[src.index('/-- First nonzero'):src.index('/-- The norm-support')]
statement=src[src.index('theorem supported_small_function_certificate :'):src.index(' := by\n  decide',src.index('theorem supported_small_function_certificate :'))]
firststat=src[src.index('theorem jet_polynomials_satisfy_equations :'):src.index(' := by\n  decide',src.index('theorem jet_polynomials_satisfy_equations :'))]
head='''import FLT.Assumptions.MazurProof.N13SpecialSmallNumerator
import Mathlib.RingTheory.Coprime.Lemmas

/-!
Source pin: b07243d72093bec5686e15b1208cb50d000f3e8d.
Source-only repair of the certificate candidate from
4109ba77745784c1a9f8c4c7b304df4124bf5ac4. Lean and axiom checks NOT RUN.

Finite polynomial certificates for all 32 * 4 coefficient pairs in the
GOOD F2 model. Polynomial divisibility is never passed to a decision
procedure. The six local equations have explicit cofactors. Each of the
58 unsupported nonzero norms has an explicit factor coprime to both X
and X - 1; its two Bezout identities rule out support. The zero norm is
excluded separately. The 69 supported rows have explicit six-polynomial
normal forms and first-nonzero-coefficient certificates.

All public definition values and theorem statements are unchanged.
The link between these nine-jet orders and the six geometric local
orders is a separate theorem.
-/

namespace MazurProof.N13SpecialSmallFunctionCertificate

noncomputable section
open Polynomial

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

'''
text=head+pre+'''private theorem two_poly : (2 : K[X]) = 0 :=
  CharP.cast_eq_zero (K[X]) 2

/-- The displayed polynomials really satisfy all six local equations to
nine-jet precision. The divisibility witnesses are explicit polynomials. -/
'''+firststat+' := by\n  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩\n'
for i,s in enumerate(jets):
 hi,ri=(iz(H),iz(R)) if i<2 else (ic(iz(H),[1,1]),ic(iz(R),[1,1])) if i<4 else (iz(HI),iz(RI))
 lhs=sub(ia(ip(iz(s),2),im(hi,iz(s))),ri)
 rhs=im(ip([0,1],9),iz(res[i]['cofactor']))
 # Dvd constructor uses residual = X^9 * quotient.
 text+='  · refine ⟨'+poly(res[i]['cofactor'])+', ?_⟩\n'
 text+='    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,\n      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,\n      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,\n      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,\n      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,\n      Polynomial.pow_comp] <;>\n      '+lc(lhs,rhs)+'\n'
text+='\n'+post
text+='''
/-- A first nonzero coefficient below nine determines `jetOrder`.
This is a proved bridge from finite coefficient data to `List.findIdx`. -/
private theorem jetOrder_of_coefficients (p : K[X]) (n : ℕ) (hn : n < 9)
    (hne : p.coeff n ≠ 0)
    (hzero : ∀ j : Fin 9, (j : ℕ) < n → p.coeff j = 0) :
    jetOrder p = n := by
  unfold jetOrder
  apply (List.findIdx_eq (xs := List.range 9) (i := n) (by simpa using hn)).2
  constructor
  · simpa using hne
  · intro j hj
    have hz := hzero ⟨j, hj.trans hn⟩ hj
    simpa using hz

private def GoodJets (p : Fin 6 → K[X]) : Prop :=
  (∀ i : Fin 6, jetOrder (p i) < 9 ∧
    (p i).coeff (jetOrder (p i)) ≠ 0 ∧
    ∀ j : Fin 9, (j : ℕ) < jetOrder (p i) → (p i).coeff j = 0) ∧
  (jetOrder (p 0) : ZMod 19) - jetOrder (p 1) +
    7 * (jetOrder (p 2) : ZMod 19) - 7 * jetOrder (p 3) +
    8 * (jetOrder (p 4) : ZMod 19) - 8 * jetOrder (p 5) = 0

private theorem goodJets_of_coefficients (p : Fin 6 → K[X]) (n : Fin 6 → ℕ)
    (hlt : ∀ i, n i < 9)
    (hne : ∀ i, (p i).coeff (n i) ≠ 0)
    (hzero : ∀ i, ∀ j : Fin 9, (j : ℕ) < n i → (p i).coeff j = 0)
    (hcode : (n 0 : ZMod 19) - n 1 + 7 * (n 2 : ZMod 19) - 7 * n 3 +
      8 * (n 4 : ZMod 19) - 8 * n 5 = 0) : GoodJets p := by
  have ho (i : Fin 6) : jetOrder (p i) = n i :=
    jetOrder_of_coefficients (p i) (n i) (hlt i) (hne i) (hzero i)
  constructor
  · intro i
    rw [ho i]
    exact ⟨hlt i, hne i, hzero i⟩
  · simpa only [ho] using hcode

private def PairCertificate (a : Fin 5 → K) (b : Fin 2 → K) : Prop :=
  N13SpecialAffineNorm.normPolynomial (numerator a) (ordinate b) ∣
    (X : K[X]) ^ 16 * (X - 1) ^ 16 → GoodJets (sixJetPolynomials a b)

/-- Two explicit Bezout identities exclude a monic nonconstant factor. -/
private theorem obstruction (f u v : K[X]) (hm : f.Monic) (hne : f ≠ 1)
    (hx : f + u * X = 1) (hx1 : f + v * (X - 1) = 1) :
    ¬ f ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  have h0 : IsCoprime f X := ⟨1, u, by simpa only [one_mul] using hx⟩
  have h1 : IsCoprime f (X - 1) := ⟨1, v, by simpa only [one_mul] using hx1⟩
  have hc : IsCoprime f ((X : K[X]) ^ 16 * (X - 1) ^ 16) :=
    h0.pow_right.mul_right h1.pow_right
  intro hd
  exact hne (hm.eq_one_of_isUnit (hc.isUnit_of_dvd hd))

'''
factors=sorted(set(r['factor'] for r in rows if 'factor' in r))
for f in factors:
 row=next(r for r in rows if r.get('factor')==f)
 u,v=row['bezout_x'],row['bezout_x1']
 text+=f'private theorem obstruction_{f} :\n    ¬ ({poly(f)} : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by\n'
 text+=f'  apply obstruction _ ({poly(u)}) ({poly(v)})\n'
 text+='  · monicity <;> norm_num\n'
 text+=f'  · intro h\n    have hc := congrArg (fun p : K[X] => p.coeff {f.bit_length()-1}) h\n    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc\n'
 text+='  · '+lc(ia(iz(f),im(iz(u),[0,1])),[1])+'\n'
 text+='  · '+lc(ia(iz(f),im(iz(v),[-1,1])),[1])+'\n\n'

simp_defs='''sixJetPolynomials, numerator, ordinate, infinityNumerator,
      infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
      jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
      Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp'''
for row in rows:
 a,b=row['a'],row['b'];aa,bb=vec(a,5),vec(b,2)
 text+=f'-- Coefficient bit codes (a, b) = ({a}, {b}).\n'
 text+=f'private theorem row_{a}_{b} : PairCertificate {aa} {bb} := by\n'
 if row['supported']:
  text+='  intro _\n'
  text+=f'  have hp : sixJetPolynomials {aa} {bb} =\n    {plist(row["jets"])} := by\n'
  text+='    funext i\n    fin_cases i\n'
  ai=[((a>>(4-i))&1) for i in range(5)];bi=[((b>>1)&1),b&1]
  for i in range(6):
   raw=ia(iz(a),im(iz(b),iz(jets[i]))) if i<2 else ia(ic(iz(a),[1,1]),im(ic(iz(b),[1,1]),iz(jets[i]))) if i<4 else ia(ai,im(bi,iz(jets[i])))
   text+='    · norm_num ['+simp_defs.replace('\n      ','\n        ')+'] <;>\n        '+lc(raw,iz(row['jets'][i]))+'\n'
  text+='  rw [hp]\n'
  text+='  apply goodJets_of_coefficients _ !['+', '.join(map(str,row['orders']))+']\n'
  text+='  · decide\n'
  text+='  · intro i\n    fin_cases i <;>\n      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]\n'
  text+='  · intro i j hj\n    fin_cases i <;> fin_cases j <;>\n      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *\n'
  text+='  · decide\n\n'
 elif row['norm']==0:
  text+='''  intro h
  have hn : N13SpecialAffineNorm.normPolynomial
      (numerator ![0, 0, 0, 0, 0]) (ordinate ![0, 0]) = 0 := by
    simp [N13SpecialAffineNorm.normPolynomial, numerator, ordinate, Fin.sum_univ_succ]
  rw [hn, zero_dvd_iff] at h
  have hx1 : (X : K[X]) - 1 ≠ 0 := by
    simpa using (Polynomial.X_sub_C_ne_zero (1 : K))
  exact False.elim ((mul_ne_zero (pow_ne_zero 16 Polynomial.X_ne_zero)
    (pow_ne_zero 16 hx1)) h)

'''
 else:
  f,q=row['factor'],row['cofactor']
  text+='  intro h\n'
  text+=f'  have hf : ({poly(f)} : K[X]) ∣\n      N13SpecialAffineNorm.normPolynomial (numerator {aa}) (ordinate {bb}) := by\n'
  text+=f'    refine ⟨{poly(q)}, ?_⟩\n'
  text+='    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,\n      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,\n      Fin.sum_univ_succ] <;>\n'
  raw=sub(sub(ip(iz(a),2),im(im(iz(a),iz(b)),iz(H))),im(ip(iz(b),2),iz(R)))
  text+='      '+lc(raw,im(iz(f),iz(q)))+'\n'
  text+=f'  exact False.elim (obstruction_{f} (hf.trans h))\n\n'
text+='''private theorem binary (x : K) : x = 0 ∨ x = 1 := by
  fin_cases x <;> decide

/-- The norm-support restriction leaves only genuine nonzero nine-jets,
and every surviving pair has zero weighted code. The common infinity
shift -4 cancels between the last two coefficients, whose weights sum to 0. -/
'''+statement+' := by\n'
text+='''  intro a b
  change PairCertificate a b
  have ha : a = ![a 0, a 1, a 2, a 3, a 4] := by
    funext i
    fin_cases i <;> rfl
  have hb : b = ![b 0, b 1] := by
    funext i
    fin_cases i <;> rfl
  rw [ha, hb]
  rcases binary (a 0) with h0 | h0 <;>
    rcases binary (a 1) with h1 | h1 <;>
    rcases binary (a 2) with h2 | h2 <;>
    rcases binary (a 3) with h3 | h3 <;>
    rcases binary (a 4) with h4 | h4 <;>
    rcases binary (b 0) with k0 | k0 <;>
    rcases binary (b 1) with k1 | k1
'''
from itertools import product
for bits in product(range(2),repeat=7):
 a=sum(bits[i]<<i for i in range(5));b=bits[5]|(bits[6]<<1)
 text+=f'  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_{a}_{b}\n'
text+='\nend\nend MazurProof.N13SpecialSmallFunctionCertificate\n'
path=(Path(__file__).parent / 'REGENERATED_N13SpecialSmallFunctionCertificate.lean')
path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
print('Wrote',path,len(text.encode()),'bytes',len(text.splitlines()),'lines')
