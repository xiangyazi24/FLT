from pathlib import Path
import re,json,hashlib,shutil
root=Path('/workspace/shared/flt-n25-zfraction-map')
for old in ['flt-n25-xchart-map','flt-n25-zchart-equiv']:
    for f in (Path('/workspace/shared')/old/'sources').glob('*.lean'):
        dest=root/'sources'/f.name
        if dest.exists(): assert dest.read_bytes()==f.read_bytes(),str(f)
        else: shutil.copyfile(f,dest)
shutil.copyfile('/workspace/shared/flt-n25-zchart-equiv/N25F_ZChartWChartEquiv.lean',root/'sources'/'N25F_ZChartWChartEquiv.lean')
plan=[
('RationalPointsN25QuotientF2',['Coordinates4']),
('RationalPointsN25QuotientSmoothF2',['canonicalQuadric25CharTwo','canonicalCubic25CharTwo']),
('RationalPointsN25QuotientTwoConormal',['BinaryHomogeneousRing','canonicalQuadricPolynomial25Two','canonicalCubicPolynomial25Two','coordinates4ToFun']),
('RationalPointsN25QuotientTwoGradedKoszul',['k','S']),
('RationalPointsN25QuotientTwoAffineCharts',['OtherCoordinate','AffineChart','dehomogenizedVariable','ambientDehomogenize','ambientDehomogenize_X_self','chartAffineQuadric','chartAffineCubic','chartAffineRelation','chartAffineRelation_zero','chartAffineRelation_one','chartAffineRelation_range','chartAffineEquationIdeal']),
('RationalPointsN25QuotientTwoStructuralJacobian',['mappedAmbientPoint','coordinates4ToFun_mappedAmbientPoint','mapCoordinates4','map_canonicalQuadric_coordinates','map_canonicalCubic_coordinates','map_canonicalQuadric','map_canonicalCubic']),
('RationalPointsN25QuotientTwoAffineChartsSmooth',['ChartQuotient','chartMap','chartQuotient_relation_zero','chartMap_quadric_zero','chartMap_cubic_zero','chartQuotientPoint','chartMap_X_pivot','chartQuotientPoint_pivot','chartQuotientPoint_quadric','chartQuotientPoint_cubic']),
('RationalPointsN25QuotientTwoWOpenEvaluation',['WChartQuotient','scaleCoordinates4','canonicalQuadric25CharTwo_scale','canonicalCubic25CharTwo_scale']),
('RationalPointsN25QuotientTwoWOpenPrimeSurjective',['W','qx','qy','qz']),
('RationalPointsN25QuotientTwoWBoundaryZLocal',['ZChartRing','zW']),
('N25F_NonBoundaryPrincipalDivisor',['W']),
('N25F_ZChartWChartEquiv',['zX','zY']),
('RationalPointsN25QuotientTwoPlaneFunctionField',['k','zRing','planeSexticPolynomial','PlaneCoordinateRing','planeZ','wChartPoint','projectionDenominator','projectionNumerator','planeSexticValue','planeSexticPolynomial_eval','planeSextic_elimination_identity','planeSexticPolynomial_eval_eq_zero_of_canonical']),
('RationalPointsN25QuotientTwoPlaneChartBridge',['k','wChartOriginEvaluation','wChartOriginEvaluation_relation','wChartAffineEquationIdeal_le_originKernel','wChartAffineEquationIdeal_ne_top','canonicalWChart_nontrivial','canonicalWChart_charP','canonicalWChartPoint','canonicalWChartX','canonicalWChartY','canonicalWChartZ','canonicalWChartPoint_w','coordinates4_ext','wChartPoint_eq_canonicalWChartPoint','zPolynomialToCanonicalWChart','planeSexticPolynomial_eval_canonicalWChart','planeCoordinateRingToCanonicalWChart','planeCoordinateRingToCanonicalWChart_planeZ']),
('RationalPointsN25QuotientTwoWChartNormalization',['planeAlgebraW','rzAlgebraW']),
]
s='''import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
'''
opened=[];copied=[]
for file,names in plan:
    txt=(root/'sources'/f'{file}.lean').read_text()
    s+=f'\nnamespace MazurProof.{file}\n\n'
    s+=''.join('open MazurProof.'+n+'\n' for n in opened)
    if file=='RationalPointsN25QuotientTwoPlaneFunctionField': s+='open Polynomial\n'
    if file=='RationalPointsN25QuotientTwoPlaneChartBridge': s+='open Polynomial\n'
    if file=='RationalPointsN25QuotientTwoWChartNormalization':
        s+='local notation "Rz" => Polynomial (ZMod 2)\nlocal notation "A" => PlaneCoordinateRing\nlocal notation "W" => ChartQuotient 3\n'
    s+='\n'
    for name in names:
        m=re.search(r'^(?:private )?(?:noncomputable )?(?:def|abbrev|theorem|structure|instance) '+re.escape(name)+r'(?=[\s:{])',txt,re.M)
        assert m,(file,name)
        start=m.start()
        if txt[max(0,start-8):start]=='@[simp]\n':start-=8
        end=txt.find('\n\n',m.start())
        if end<0:end=len(txt)
        nextdecl=re.search(r'^/--|^(?:private )?(?:noncomputable )?(?:def|abbrev|theorem|structure|instance) ',txt[m.end():end],re.M)
        if nextdecl:end=m.end()+nextdecl.start()
        raw=txt[start:end]
        s+=raw+'\n\n'
        copied.append(dict(file=file+'.lean',declaration=name,start_line=txt[:start].count('\n')+1,end_line=txt[:end].count('\n')+1,sha256=hashlib.sha256(raw.encode()).hexdigest()))
    s+=f'end MazurProof.{file}\n'
    opened.append(file)
prod=(root/'N25F_ZChartFractionMap.lean').read_text()
body=prod[prod.index('namespace MazurProof.N25F_ZChartFractionMap'):]
body=body.replace('/-- The genuine nonvanishing', 'variable [Module.IsTorsionFree (Polynomial (ZMod 2)) W]\n\n/-- The genuine nonvanishing')
body=body.replace('/-- The universal W-chart point, mapped', 'variable [IsDomain W]\n\n/-- The universal W-chart point, mapped')
s+='\n'+body+'\n'
for name in ['algebraMap_Rz_X','qz_ne_zero','fraction_qz_ne_zero','zFractionPoint_z','zChartToFraction','zChartToFraction_zX','zChartToFraction_zY','zChartToFraction_zW']:
    s+=f'#check @MazurProof.N25F_ZChartFractionMap.{name}\n#print axioms MazurProof.N25F_ZChartFractionMap.{name}\n'
(root/'ZChartFractionMapCheck.lean').write_text(s)
(root/'copied-declarations.json').write_text(json.dumps(copied,indent=2)+'\n')
print('Check file',len(s),'bytes;',len(copied),'exact copied declarations')
