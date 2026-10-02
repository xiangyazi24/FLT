from pathlib import Path
r=Path('/workspace/shared/flt-n25-infinity-separable');s=(r/'N25F_InfinitySeparable.lean').read_text();s=s.replace('import FLT.Assumptions.MazurProof.N25F_InfinityFunctionField','import InfinityFunctionFieldCheck')
s=s.replace('local notation "CurveField" => FractionRing W','''local notation "CurveField" => FractionRing W
variable [Module.IsTorsionFree BasePolynomial W] [IsDedekindDomain W]
variable [Module.Finite BasePolynomial W]
variable (hCanonical :
  letI : Algebra BaseField CurveField := FractionRing.liftAlgebra (R := BasePolynomial) (K := CurveField)
  Algebra.IsSeparable BaseField CurveField)
''')
s=s.replace('/-- The existing actual canonical separability','include hCanonical in\n/-- The existing actual canonical separability').replace('/-- The actual reciprocal rational-base extension','include hCanonical in\n/-- The actual reciprocal rational-base extension')
s=s.replace('exact RationalPointsN25QuotientTwoWChartNormalization.canonicalWChart_fractionRing_isSeparable','exact hCanonical').replace(':= affineRationalBaseToField_isSeparable',':= affineRationalBaseToField_isSeparable hCanonical')
s=s.replace('end MazurProof.N25F_InfinitySeparable','''#check @affineRationalBaseToField_eq_canonicalLift
#check @infinityRationalBaseToField_isSeparable
#print axioms affineRationalBaseToField_eq_canonicalLift
#print axioms affineRationalBaseToField_isSeparable
#print axioms infinityRationalBaseToField_isSeparable
end MazurProof.N25F_InfinitySeparable''')
(r/'InfinitySeparableCheck.lean').write_text(s)
