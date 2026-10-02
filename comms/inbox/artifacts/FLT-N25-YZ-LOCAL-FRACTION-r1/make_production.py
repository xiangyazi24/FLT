from pathlib import Path
import re
root=Path('/workspace/shared/flt-n25-yz-fraction-embedding')
generic=(root/'GenericFractionExtension.lean').read_text().split('theorem exists_atPrime_fraction_map',1)[1].split('#print axioms',1)[0]
generic='private theorem exists_atPrime_fraction_map'+generic
point=(root/'CurvePointFractionCheck.lean').read_text().split('private theorem yZ_not_mem',1)[1].split('#print axioms yzLocalToFraction_yX',1)[0]
point='private theorem yZ_not_mem'+point
left,right=point.split('private theorem exists_yzLocalToFraction',1)
right='private theorem exists_yzLocalToFraction'+right
away=(root/'AwayFractionCheck.lean').read_text().split('private theorem zY_powers_nonZeroDivisors',1)[1].split('#print axioms',1)[0]
away='private theorem zY_powers_nonZeroDivisors'+away
names=['zY_powers_nonZeroDivisors','zY_powers_map_units','zYOpenToFraction','zYOpenToFraction_algebraMap','zYOpenToFraction_isFractionRing','zYOpenToFraction_injective','zYOpenToFraction_invSelf','yZOpenToFraction','yZOpenToFraction_injective','yZOpenToFraction_isFractionRing']
for name in names:
    away=away.replace(name+' hs',name)
    right=right.replace(name+' (zY_ne_zero f hf)',name)
away=re.sub(r'\bhs\b','zY_ne_zero',away)
s=left+away+right
s=s.replace('N25FractionExtensionCheck.exists_atPrime_fraction_map','exists_atPrime_fraction_map')
s=s.replace('Localization.AtPrime (RingHom.ker f.toRingHom)','YZLocalRing')
s=s.replace('RingHom.ker f.toRingHom','yzPrime')
s=s.replace(' f hf','').replace('rw [hf]','rw [yzPointEval_yZ]')
s=re.sub(r'\bf yZ\b', 'yzPointEval yZ', s)
s=s.replace('The coordinate-rigid embedding of the prime-local Y chart into the common field.', 'The coordinate-rigid embedding of the existing YZ local ring into the common W-chart function field.')
header='''import FLT.Assumptions.MazurProof.N25F_YZAffineOverlapEquiv
import FLT.Assumptions.MazurProof.N25F_ZChartFractionEquiv
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! The actual YZ local ring embeds coordinate-rigidly into the fixed W-chart
function field, which is its fraction field. The construction uses the proved
Y/Z affine-overlap equivalence and the canonical localization at the actual
point. No Y-chart domain, local-ring isomorphism, or field-map premise is added. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace MazurProof.N25F_YZLocalFractionEmbedding

open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryZLocal
open RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open N25F_ZChartWChartEquiv N25F_ZChartFractionMap N25F_ZChartFractionInjective
open N25F_ZChartFractionEquiv N25F_YZLocalZUnit N25F_YZOverlapMap
open N25F_YZAffineOverlapEquiv
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local instance : yzPrime.IsPrime := yzPrime_isMaximal.isPrime

'''
footer='''
/-- The existing Z/Y germ has its prescribed homogeneous-coordinate image. -/
@[simp] theorem yzLocalToFraction_yzZGerm :
    yzLocalToFraction yzZGerm =
      algebraMap W (FractionRing W) qz / algebraMap W (FractionRing W) qy :=
  yzLocalToFraction_yZ

/-- The existing W/Y germ has its prescribed homogeneous-coordinate image. -/
@[simp] theorem yzLocalToFraction_yzWGerm :
    yzLocalToFraction yzWGerm = 1 / algebraMap W (FractionRing W) qy :=
  yzLocalToFraction_yzW

end MazurProof.N25F_YZLocalFractionEmbedding
'''
(root/'N25F_YZLocalFractionEmbedding.lean').write_text(header+generic+s+footer)
