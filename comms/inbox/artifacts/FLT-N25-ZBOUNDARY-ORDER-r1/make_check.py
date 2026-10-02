from pathlib import Path
import hashlib,re
r=Path('/workspace/shared/flt-n25-zboundary-order')
s='''import ZChartFractionEquivCheck
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.OrderOfVanishing.Basic
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace N25ZLocalFamilyCheck
open MazurProof.RationalPointsN25QuotientTwoWBoundaryZLocal

local instance (f : ZChartRing →ₐ[ZMod 2] ZMod 2) :
    (RingHom.ker f.toRingHom).IsPrime := RingHom.ker_isPrime f.toRingHom

abbrev LocalRing (f : ZChartRing →ₐ[ZMod 2] ZMod 2) :=
  Localization.AtPrime (RingHom.ker f.toRingHom)

def germ (f : ZChartRing →ₐ[ZMod 2] ZMod 2) : LocalRing f :=
  algebraMap ZChartRing (LocalRing f) zW

theorem pointPrime_isMaximal (f : ZChartRing →ₐ[ZMod 2] ZMod 2) :
    (RingHom.ker f.toRingHom).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  exact ⟨algebraMap (ZMod 2) ZChartRing c, f.commutes c⟩

@[simp] theorem pointEval_zW (f : ZChartRing →ₐ[ZMod 2] ZMod 2)
    [Fact (f zW = 0)] : f zW = 0 := Fact.out

theorem germ_ord_two (f : ZChartRing →ₐ[ZMod 2] ZMod 2)
    [Fact (Ring.ord (LocalRing f) (germ f) = 2)] :
    Ring.ord (LocalRing f) (germ f) = 2 := Fact.out

end N25ZLocalFamilyCheck
'''
p=(r/'N25F_ZBoundaryOrder.lean').read_text();body=p[p.index('namespace MazurProof.'):]
body=body.replace('local notation "K" => FractionRing W','''local notation "K" => FractionRing W
variable [Module.IsTorsionFree (Polynomial (ZMod 2)) W] [IsDedekindDomain W]
variable {pointEval : ZChartRing →ₐ[ZMod 2] ZMod 2} [Fact (pointEval zW = 0)]
local notation "zPointEval" => pointEval
local notation "zPrime" => RingHom.ker pointEval.toRingHom
local notation "zPrime_isMaximal" => N25ZLocalFamilyCheck.pointPrime_isMaximal pointEval
local notation "ZLocalRing" => N25ZLocalFamilyCheck.LocalRing pointEval
local notation "zWGerm" => N25ZLocalFamilyCheck.germ pointEval
local notation "zWGerm_ord_eq_two" => N25ZLocalFamilyCheck.germ_ord_two pointEval''')
body=body.replace('rw [zWGerm, zLocalToFraction_algebraMap, zChartToFraction_zW]','rw [N25ZLocalFamilyCheck.germ, zLocalToFraction_algebraMap, zChartToFraction_zW]')
body=body.replace('/-- The common-field image of the actual boundary germ', '''variable [Fact (Ring.ord (N25ZLocalFamilyCheck.LocalRing pointEval) (N25ZLocalFamilyCheck.germ pointEval) = 2)]

/-- The common-field image of the actual boundary germ''')
body=body.replace('zPrime.', '(zPrime).').replace('zPrime_isMaximal.', '(zPrime_isMaximal).')
refs=['zW_mem_zPrime','zPrime_ne_bot','zWGerm_ne_zero','zChartToFraction_isUnit_of_primeCompl','zLocalToFraction','zLocalToFraction_algebraMap','zLocalToFraction_injective','zLocalToFraction_zWGerm','zLocalToFraction_isFractionRing','zLocalFractionOrder','zBoundaryOrder','zLocalFractionOrder_zWGerm']
for n in refs:
    declaration_spans=[(m.start(1),m.end(1)) for m in re.finditer(r'^(?:private )?(?:def|theorem|instance) ('+n+r')\b',body,re.M)]
    matches=list(re.finditer(r'\b'+n+r'\b',body))
    for m in reversed(matches):
        if any(m.start()==a for a,b in declaration_spans): continue
        body=body[:m.start()]+'('+n+' (pointEval := pointEval))'+body[m.end():]
s+='\n'+body+'\n'
for n in ['zW_ne_zero','zW_mem_zPrime','zPrime_ne_bot','zLocalRing_isDiscreteValuationRing','zWGerm_ne_zero','zLocalToFraction','zLocalToFraction_injective','zLocalToFraction_xWGerm','zLocalToFraction_zWGerm','zLocalToFraction_isFractionRing','zLocalFractionOrder','zBoundaryOrder','zLocalFractionOrder_zWGerm','zBoundaryOrder_qz']:
 if n=='zLocalToFraction_xWGerm':continue
 s+=f'#check @MazurProof.N25F_ZBoundaryOrder.{n}\n#print axioms MazurProof.N25F_ZBoundaryOrder.{n}\n'
(r/'GenericZBoundaryOrderCheck.lean').write_text(s);print(len(s),hashlib.sha256(s.encode()).hexdigest())
