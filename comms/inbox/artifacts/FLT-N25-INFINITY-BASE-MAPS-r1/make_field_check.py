from pathlib import Path
r=Path('/workspace/shared/flt-n25-infinity-base');s=(r/'N25F_InfinityBaseMaps.lean').read_text()
g=s[s.index('private theorem inverse_aeval_injective'):s.index('open RationalPointsN25')]
a=Path('/workspace/shared/flt-n25-base-polynomial-product/accepted-r19/N25F_ProjectivePrincipalDivisor.lean').read_text();a=a[a.index('theorem basePolynomial_inFunctionField'):a.index('/-- The genuine projective principal divisor has degree zero')]
f=s[s.index('def infinityBaseToField'):s.index('/-- The actual reciprocal base maps to the X-boundary')]
header='''import ZChartFractionEquivCheck
import Mathlib.RingTheory.Algebraic.Basic
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_ProjectivePrincipalDivisor
open RationalPointsN25QuotientTwoWOpenPrimeSurjective N25F_ZChartFractionMap
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "K" => FractionRing W
variable [Module.IsTorsionFree (Polynomial (ZMod 2)) W] [IsDedekindDomain W]
'''
tail='''end MazurProof.N25F_ProjectivePrincipalDivisor
namespace MazurProof.N25F_InfinityBaseMaps
'''+g+'''open RationalPointsN25QuotientTwoWOpenPrimeSurjective N25F_ZChartFractionMap
open N25F_ProjectivePrincipalDivisor
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "K" => FractionRing W
variable [Module.IsTorsionFree (Polynomial (ZMod 2)) W] [IsDedekindDomain W]
'''+f+'''#check @infinityBaseToField_injective
#print axioms infinityBaseToField
#print axioms infinityBaseToField_injective
end MazurProof.N25F_InfinityBaseMaps
'''
(r/'InfinityFieldCheck.lean').write_text(header+a+tail)
