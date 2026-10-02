from pathlib import Path
import re
r=Path('/workspace/shared/flt-n25-polynomial-boundary-orders')
g=(r/'GenericPolynomialPole.lean').read_text();g=g[g.index('theorem ordFrac_aeval_at_pole'):g.index('#print axioms')]
g=re.sub(r'\bK\b', 'L', g).replace('(L := L)', '(K := L)')
header='''import FLT.Assumptions.MazurProof.N25F_XBoundaryZOrder
import FLT.Assumptions.MazurProof.N25F_YZBoundaryOrder
import FLT.Assumptions.MazurProof.N25F_ZBoundaryOrder
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Valuation.IsTrivialOn

/-! Exact boundary orders of every nonzero binary polynomial in the actual
function qz=Z/W. This is a proved subcase, not the general product formula. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_PolynomialBoundaryOrders
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal
open N25F_XLocalFractionEmbedding N25F_XBoundaryOrder N25F_XBoundaryZOrder
open N25F_YZLocalFractionEmbedding N25F_YZBoundaryOrder N25F_ZBoundaryOrder
open N25F_ZChartFractionMap
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "K" => FractionRing W

'''
parts=[]
for tag,ring,n in [('x','XLocalRing',1),('yz','YZLocalRing',1),('z','ZLocalRing',2)]:
 s=f'''/-- The actual {tag.upper()} boundary order of p(Z/W) is minus {n} times its degree. -/
theorem {tag}LocalFractionOrder_aeval_qz (p : Polynomial (ZMod 2)) (hp : p ≠ 0) :
    {tag}LocalFractionOrder (p.aeval (algebraMap W K qz)) =
      WithZero.exp (-({n} * p.natDegree : ℤ)) := by
  letI : Algebra {ring} K := {tag}LocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing {ring} K := {tag}LocalToFraction_isFractionRing
  letI : IsScalarTower (ZMod 2) {ring} K :=
    IsScalarTower.of_algebraMap_eq fun a => ({tag}LocalToFraction.commutes a).symm
  have hzlog : WithZero.log ({tag}LocalFractionOrder (algebraMap W K qz)) = -{n} :=
    {tag}BoundaryOrder_qz
  have hz : {tag}LocalFractionOrder (algebraMap W K qz) = WithZero.exp (-({n} : ℤ)) :=
    (WithZero.exp_log (((isUnit_iff_ne_zero.mpr fraction_qz_ne_zero).map
      {tag}LocalFractionOrder).ne_zero)).symm.trans (congrArg WithZero.exp hzlog)
  exact ordFrac_aeval_at_pole (R := {ring}) (algebraMap W K qz) {n}
    (by decide) hz p hp

'''
 parts.append(s)
(r/'N25F_PolynomialBoundaryOrders.lean').write_text(header+'private '+g+'\n'+''.join(parts)+'end MazurProof.N25F_PolynomialBoundaryOrders\n')
# X slice uses the exact existing X-point harness and the newly proved coordinate/pole calculations.
a=Path('/workspace/shared/flt-n25-xqz-order/XBoundaryZOrderCheck.lean').read_text()
a=a.replace('import XChartFractionEquivCheck','import XChartFractionEquivCheck\nimport Mathlib.RingTheory.Valuation.IsTrivialOn')
xheader=header[header.index('namespace MazurProof.N25F_PolynomialBoundaryOrders'):]
xheader=xheader.replace('open RationalPointsN25QuotientTwoWBoundaryYZLocal\n','').replace('open RationalPointsN25QuotientTwoWBoundaryZLocal\n','').replace('open N25F_YZLocalFractionEmbedding N25F_YZBoundaryOrder N25F_ZBoundaryOrder\n','').replace('open N25F_ZChartFractionMap\n','')
xheader += '''variable [IsDedekindDomain W]
variable (hord : Ring.ord XLocalRing xWGerm = 3)
variable (fraction_qz_ne_zero : algebraMap W K qz ≠ 0)
'''
part=parts[0].replace('/-- The actual','include hord fraction_qz_ne_zero in\n/-- The actual').replace('    xBoundaryOrder_qz','    xBoundaryOrder_qz hord fraction_qz_ne_zero')
(r/'XPolynomialBoundaryCheck.lean').write_text(a+'\n'+xheader+'private '+g+'\n'+part+'''#check @xLocalFractionOrder_aeval_qz
#print axioms xLocalFractionOrder_aeval_qz
end MazurProof.N25F_PolynomialBoundaryOrders
''')
