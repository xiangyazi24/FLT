from pathlib import Path
import re
r=Path(__file__).parent
base=(r/'XSectionFiltrationFamilyInput.lean').read_text()
base=base[:base.index('#print axioms fullRiemannRochSpace25Two_sub_X_le')]
base+='end MazurProof.N25F_XSectionFiltration\n'
integral=(r/'N25F_DVRIntegralLift.lean').read_text()
base+='\n'.join(x for x in integral.splitlines() if not x.startswith('import '))+'\n'
src=(r/'N25F_XSectionResidue.lean').read_text()
body=src[src.index('private def xSectionScale'):src.index('end MazurProof.N25F_XSectionResidue')]
body=body.replace('    letI : Algebra XLocalRing CurveField := xLocalToFraction.toRingHom.toAlgebra\n','').replace('    letI : IsFractionRing XLocalRing CurveField := xLocalToFraction_isFractionRing\n','')
body=body.replace('  letI : Algebra XLocalRing CurveField := xLocalToFraction.toRingHom.toAlgebra\n','').replace('  letI : IsFractionRing XLocalRing CurveField := xLocalToFraction_isFractionRing\n','')
for a,b in [('projectivePrincipalDivisor_apply_X','hcoeff'),('ProjectiveDivisor25Two','C.Divisor'),('CurveField','L'),('XLocalRing','R'),('xLocalToFraction_injective','(IsFractionRing.injective R L)'),('xInverseZGerm_ne_zero','htaune'),('xInverseZGerm_ord_eq_one','htauorder'),('xLocalResidueRingEquivF2','e')]:body=body.replace(a,b)
for a,b in [('xLocalToFraction','(algebraMap R L)'),('xLocalFractionOrder','(Ring.ordFrac R)'),('xInverseZGerm','tau')]:body=re.sub(r'\b'+a+r'\b',b,body)
g='C principal hmin R XPoint hcoeff tau htaune htauorder'
f='C principal hmin R XPoint hcoeff e tau htaune htauorder'
args={'fullRiemannRochSpace25Two':'C principal hmin','mem_fullRiemannRochSpace25Two_sub_X_iff':'C principal hmin R XPoint hcoeff','xSectionScale':'C (L := L) R XPoint tau','xSectionScale_ne_zero':'C (L := L) R XPoint tau htaune','xSectionScale_order':'C (L := L) R XPoint tau htaune htauorder','scaled_section_nonneg':g,'xScaledSection_has_germ':g,'xScaledSectionGerm25Two':g,'xLocalToFraction_xScaledSectionGerm25Two':g,'xScaledSectionGerm_zero':g,'xScaledSectionGerm25Two_add':g,'xLeadingResidue25Two':f,'xLeadingResidue25Two_eq_zero_iff':f,'ker_xLeadingResidue25Two':f}
for n,a in args.items():
 body=re.sub(r'\b'+n+r'\b',n+' '+a,body)
 for kind in ['def','theorem']:body=body.replace(kind+' '+n+' '+a,kind+' '+n)
body=body.replace('private theorem xSectionScale_ne_zero','include htaune in\nomit [Algebra (ZMod 2) L] [IsDomain R] [IsDiscreteValuationRing R] in\nprivate theorem xSectionScale_ne_zero')
body=body.replace('private theorem xSectionScale_order','include htaune htauorder in\nomit [Algebra (ZMod 2) L] in\nprivate theorem xSectionScale_order')
body=body.replace('private theorem scaled_section_nonneg','include hcoeff htaune htauorder in\nprivate theorem scaled_section_nonneg')
body=body.replace('private theorem xScaledSection_has_germ','include hcoeff htaune htauorder in\nprivate theorem xScaledSection_has_germ')
head='''
namespace MazurProof.N25F_XSectionResidue
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_XSectionFiltration N25F_DVRIntegralLift
variable (C : ClosedPointGrading) {L : Type*} [Field L] [Algebra (ZMod 2) L]
variable (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ,
  (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
    min (principal f A) (principal g A) ≤ principal h A)
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R L] [IsFractionRing R L]
variable (XPoint : C.Atom)
variable (hcoeff : ∀ f : Additive Lˣ, principal f XPoint = boundaryOrder R f)
variable (e : IsLocalRing.ResidueField R ≃+* ZMod 2)
variable (tau : R) (htaune : tau ≠ 0) (htauorder : Ring.ord R tau = 1)
'''
out=base+head+body
for n in ['xScaledSectionGerm25Two','xLocalToFraction_xScaledSectionGerm25Two','xScaledSectionGerm25Two_add','xLeadingResidue25Two','xLeadingResidue25Two_eq_zero_iff','ker_xLeadingResidue25Two']:
 out+='#print axioms '+n+'\n'
out+='end MazurProof.N25F_XSectionResidue\n'
(r/'XSectionResidueFamilyCheck.lean').write_text(out)
