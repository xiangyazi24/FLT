from pathlib import Path
import re
r=Path(__file__).parent
base=(r/'WBasisPoleSectionsFamilyInput.lean').read_text()
base=base[:base.index('#print axioms basePoleDivisor25Two')]
m=(r/'N25F_SectionMultiplication.lean').read_text()
m=m[m.index('theorem fullRiemannRochSpace25Two_mono'):m.index('end MazurProof.N25F_SectionMultiplication')]
p=(r/'N25F_BasePolePowers.lean').read_text()
p=p[p.index('theorem basePoleDivisor25Two_nonneg'):p.index('end MazurProof.N25F_BasePolePowers')]
one='''
omit [Algebra (Polynomial (ZMod 2)) A] in
theorem one_mem_zero : (1 : FractionRing A) ∈ fullRiemannRochSpace25Two C principal hmin 0 := by
  refine Or.inr ⟨one_ne_zero, ?_⟩
  intro a
  have hu : Additive.ofMul (Units.mk0 (1 : FractionRing A) one_ne_zero) = 0 := by
    apply Additive.toMul.injective
    exact Units.ext rfl
  rw [hu, map_zero]
  simp
variable (qz : A) (hfq : algebraMap A (FractionRing A) qz ≠ 0)
variable (hxq : xOrder (Additive.ofMul (Units.mk0 (algebraMap A (FractionRing A) qz) hfq)) = -1)
variable (hyzq : yzOrder (Additive.ofMul (Units.mk0 (algebraMap A (FractionRing A) qz) hfq)) = -1)
variable (hzq : zOrder (Additive.ofMul (Units.mk0 (algebraMap A (FractionRing A) qz) hfq)) = -2)
'''
args={'fullRiemannRochSpace25Two':'C principal hmin','fullRiemannRochSpace25Two_mono':'C A principal hmin','mul_mem_fullRiemannRochSpace25Two':'C A principal hmin','basePoleDivisor25Two':'C boundaryAtom','basePoleDivisor25Two_nonneg':'C boundaryAtom','regular_function_mem_basePole_space':'C A principal hmin boundaryAtom hbinj xOrder yzOrder zOrder hxcoeff hyzcoeff hzcoeff prime haff','qz_mem_basePole_section_space':'C A principal hmin boundaryAtom hbinj xOrder yzOrder zOrder hxcoeff hyzcoeff hzcoeff prime haff qz hfq hxq hyzq hzq','qz_pow_mem_basePole_section_space':'C A principal hmin boundaryAtom hbinj xOrder yzOrder zOrder hxcoeff hyzcoeff hzcoeff prime haff qz hfq hxq hyzq hzq'}
def transform(body):
 for a,b in [('ProjectiveDivisor25Two','C.Divisor'),('projectivePrincipalDivisor','principal'),('fraction_qz_ne_zero','hfq'),('xBoundaryOrder_qz','hxq'),('yzBoundaryOrder_qz','hyzq'),('zBoundaryOrder_qz','hzq'),('one_mem_fullRiemannRochSpace25Two_zero','one_mem_zero C A principal hmin')]:body=body.replace(a,b)
 body=re.sub(r'\bW\b','A',body).replace('Kˣ','((FractionRing A)ˣ)')
 body=re.sub(r'\bK\b','(FractionRing A)',body)
 for n,a in args.items():
  body=re.sub(r'\b'+n+r'\b',n+' '+a,body)
  body=body.replace('theorem '+n+' '+a,'theorem '+n)
 return body
m=transform(m);p=transform(p)
for n in ['fullRiemannRochSpace25Two_mono','mul_mem_fullRiemannRochSpace25Two']:
 m=m.replace('theorem '+n,'omit [Algebra (Polynomial (ZMod 2)) A] in\ntheorem '+n)
m=m.replace('/-- Orders add under multiplication of actual rational functions. -/\nomit [Algebra (Polynomial (ZMod 2)) A] in','omit [Algebra (Polynomial (ZMod 2)) A] in\n/-- Orders add under multiplication of actual rational functions. -/')
p=p.replace('basePoleDivisor25Two C boundaryAtom','(basePoleDivisor25Two C boundaryAtom)')
p=p.replace('ih qz_mem_basePole_section_space '+args['qz_mem_basePole_section_space'],
  'ih (qz_mem_basePole_section_space '+args['qz_mem_basePole_section_space']+')')
inc='include hbinj hxcoeff hyzcoeff hzcoeff haff hxq hyzq hzq in\nomit [Algebra (Polynomial (ZMod 2)) A] in\n'
p=p.replace('theorem qz_mem_basePole_section_space',inc+'theorem qz_mem_basePole_section_space')
p=p.replace('/-- Powers of the actual base coordinate',inc+'/-- Powers of the actual base coordinate')
out=base+m+one+p
for n in ['fullRiemannRochSpace25Two_mono','mul_mem_fullRiemannRochSpace25Two','basePoleDivisor25Two_nonneg','qz_mem_basePole_section_space','qz_pow_mem_basePole_section_space']:
 out+='#print axioms '+n+'\n'
out+='end MazurProof.N25F_WBasisPoleSections\n'
(r/'ProductBasePowersFamilyCheck.lean').write_text(out)
