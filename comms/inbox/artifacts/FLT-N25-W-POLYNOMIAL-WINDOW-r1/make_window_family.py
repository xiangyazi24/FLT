from pathlib import Path
import re
r=Path(__file__).parent
base=(r/'SectionFinitenessFamilyInput.lean').read_text()
base=base[:base.index('#print axioms MazurProof.CurveZetaEffectiveDivisors.')]
base+='end MazurProof.N25F_SectionFiniteness\n'
poly=(r/'PolynomialBasisWindowCheck.lean').read_text()
poly=poly[:poly.index('#print axioms')]
imports=[]
for s in [base,poly]:
 for line in s.splitlines():
  if line.startswith('import ') and line not in imports:imports.append(line)
imports+=['import Mathlib.LinearAlgebra.FiniteDimensional.Basic','import Mathlib.RingTheory.Localization.FractionRing','import Mathlib.Algebra.Polynomial.AlgebraMap']
base='\n'.join(imports)+'\n'+''.join('\n'.join(x for x in s.splitlines() if not x.startswith('import '))+'\n' for s in [base,poly])
head='''
namespace MazurProof.N25F_WPolynomialWindow
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_SectionFiniteness N25F_PolynomialBasisWindow
variable (C : ClosedPointGrading)
variable (A : Type*) [CommRing A] [IsDomain A]
  [Algebra (ZMod 2) A] [Algebra (Polynomial (ZMod 2)) A]
variable (principal : Additive ((FractionRing A)ˣ) →+ C.Divisor)
variable (hmin : ∀ f g h : Additive ((FractionRing A)ˣ),
  (h.toMul : FractionRing A) = (f.toMul : FractionRing A) + (g.toMul : FractionRing A) → ∀ a,
    min (principal f a) (principal g a) ≤ principal h a)
variable (hzero : ∀ f : Additive ((FractionRing A)ˣ), C.divisorDegree (principal f) = 0)
variable (hinj : Function.Injective principal)
variable (basis : Module.Basis (Fin 4) (Polynomial (ZMod 2)) A)
variable (B : ℕ) (H : C.Divisor) (qz : A)
variable (hqz : algebraMap (Polynomial (ZMod 2)) A Polynomial.X = qz)
variable (hH : 0 ≤ H)
variable (hPower : ∀ n : ℕ, (algebraMap A (FractionRing A) qz) ^ n ∈
  fullRiemannRochSpace25Two C principal hmin ((n : ℤ) • H))
variable (hBasis : ∀ i : Fin 4, algebraMap A (FractionRing A) (basis i) ∈
  fullRiemannRochSpace25Two C principal hmin ((B : ℤ) • H))
include hqz in
theorem basePolynomial_inFunctionField (p : Polynomial (ZMod 2)) :
    algebraMap A (FractionRing A) (algebraMap (Polynomial (ZMod 2)) A p) =
      p.aeval (algebraMap A (FractionRing A) qz) := by
  have h : (algebraMap A (FractionRing A)).comp (algebraMap (Polynomial (ZMod 2)) A) =
      (Polynomial.aeval (algebraMap A (FractionRing A) qz)).toRingHom := by
    apply Polynomial.ringHom_ext'
    · exact RingHom.ext_zmod _ _
    · change algebraMap A (FractionRing A) (algebraMap (Polynomial (ZMod 2)) A Polynomial.X) =
        (Polynomial.aeval (algebraMap A (FractionRing A) qz)) Polynomial.X
      rw [Polynomial.aeval_X, hqz]
  exact congrArg (fun h : Polynomial (ZMod 2) →+* FractionRing A => h p) h
'''
mult=(r/'N25F_SectionMultiplication.lean').read_text()
mult=mult[mult.index('theorem fullRiemannRochSpace25Two_mono'):mult.index('end MazurProof.N25F_SectionMultiplication')]
src=(r/'N25F_WPolynomialWindow.lean').read_text()
body=src[src.index('/-- The actual four polynomial'):src.index('end MazurProof.N25F_WPolynomialWindow')]
args={'fullRiemannRochSpace25Two':'C principal hmin','fullRiemannRochSpace25Two_mono':'C A principal hmin','mul_mem_fullRiemannRochSpace25Two':'C A principal hmin','wPolynomialWindow25Two':'A basis','wPolynomialWindow25Two_linearIndependent':'A basis','wPolynomialWindow25Two_mem':'C A principal hmin basis B H qz hqz hH hPower hBasis','four_mul_succ_le_finrank_basePole_space':'C A principal hmin hzero hinj basis B H qz hqz hH hPower hBasis'}
args['four_mul_le_finrank_basePole_add_constant']=args['four_mul_succ_le_finrank_basePole_space']
def transform(s):
 for a,b in [('wPolynomialBasis_mem_uniform_section_space','hBasis'),('wPolynomialBasis25Two','basis'),('wPolynomialBasisPoleBound25Two','B'),('basePoleDivisor25Two_nonneg','hH'),('basePoleDivisor25Two','H'),('qz_pow_mem_basePole_section_space','hPower'),('ProjectiveDivisor25Two','C.Divisor'),('projectivePrincipalDivisor','principal')]:s=s.replace(a,b)
 s=re.sub(r'\bW\b','A',s).replace('Kˣ','((FractionRing A)ˣ)')
 s=re.sub(r'\bK\b','(FractionRing A)',s)
 s=re.sub(r'\bP\b','(Polynomial (ZMod 2))',s)
 for n,a in args.items():
  s=re.sub(r'\b'+n+r'\b',n+' '+a,s)
  for kind in ['def','theorem']:s=s.replace(kind+' '+n+' '+a,kind+' '+n)
 return s
mult=transform(mult);body=transform(body)
mult=mult.replace('theorem fullRiemannRochSpace25Two_mono','omit [Algebra (Polynomial (ZMod 2)) A] in\ntheorem fullRiemannRochSpace25Two_mono')
mult=mult.replace('/-- Orders add under','omit [Algebra (Polynomial (ZMod 2)) A] in\n/-- Orders add under')
body=body.replace('basePolynomial_inFunctionField]','basePolynomial_inFunctionField A qz hqz]')
body=body.replace('/-- Every member obeys','include hqz hH hPower hBasis in\n/-- Every member obeys')
body=body.replace('/-- A genuine linear lower bound','include hzero hinj hqz hH hPower hBasis in\n/-- A genuine linear lower bound')
body=body.replace('/-- The same actual spaces','include hzero hinj hqz hH hPower hBasis in\n/-- The same actual spaces')
body=body.replace('  let v :','  letI := fullRiemannRochSpace25Two_moduleFinite C principal hmin hzero hinj (((B + n : ℕ) : ℤ) • H)\n  let v :')
out=base+head+mult+body
for n in ['wPolynomialWindow25Two','wPolynomialWindow25Two_linearIndependent','wPolynomialWindow25Two_mem','four_mul_succ_le_finrank_basePole_space','four_mul_le_finrank_basePole_add_constant']:
 out+='#print axioms '+n+'\n'
out+='end MazurProof.N25F_WPolynomialWindow\n'
(r/'WPolynomialWindowFamilyCheck.lean').write_text(out)
