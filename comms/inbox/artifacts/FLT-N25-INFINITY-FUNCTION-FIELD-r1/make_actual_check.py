from pathlib import Path
import re
r=Path('/workspace/shared/flt-n25-infinity-field')
s=(r/'N25F_InfinityFunctionField.lean').read_text()
c=s.replace('import FLT.Assumptions.MazurProof.N25F_InfinityBaseMaps','import InfinityFieldCheck').replace('import FLT.Assumptions.MazurProof.N25F_RationalBaseInversion','import N25F_RationalBaseInversion')
c=c.replace('local notation "CurveField" => FractionRing W','''local notation "CurveField" => FractionRing W
variable [Module.IsTorsionFree BasePolynomial W] [IsDedekindDomain W]
variable [Module.Finite BasePolynomial W]
variable (hWrank : Module.finrank BasePolynomial W = 4)
''')
c=c.replace('/-- The existing actual affine quartic degree','include hWrank in\n/-- The existing actual affine quartic degree')
c=c.replace('exact N25F_NonBoundaryPrincipalDivisor.wChart_finrank_polynomial_eq_four','exact hWrank')
c=c.replace('/-- The same actual curve function field','include hWrank in\n/-- The same actual curve function field')
c=c.replace('rw [affineRationalBaseToField_finrank]','rw [affineRationalBaseToField_finrank hWrank]').replace('h.2.trans affineRationalBaseToField_finrank','h.2.trans (affineRationalBaseToField_finrank hWrank)')
names=re.findall(r'^(?:def|theorem)\s+(\w+)',s,re.M)
c=c.replace('end MazurProof.N25F_InfinityFunctionField','\n'+''.join('#check @'+n+'\n#print axioms '+n+'\n' for n in names)+'end MazurProof.N25F_InfinityFunctionField')
(r/'InfinityFunctionFieldCheck.lean').write_text(c)
print('Public declarations',len(names))
