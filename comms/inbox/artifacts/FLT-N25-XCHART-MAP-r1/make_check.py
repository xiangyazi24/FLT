from pathlib import Path
import re,json,hashlib
root=Path('/workspace/shared/flt-n25-xchart-map')
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
('RationalPointsN25QuotientTwoWBoundaryChartArtin',['XChartRing','xY','xZ','xW']),
('N25F_NonBoundaryPrincipalDivisor',['W']),
]
s='''import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
'''
opened=[]; copied=[]
for file,names in plan:
    txt=(root/'sources'/f'{file}.lean').read_text()
    s+=f'\nnamespace MazurProof.{file}\n\n'
    s+=''.join('open MazurProof.'+n+'\n' for n in opened)
    s+='\n'
    for name in names:
        m=re.search(r'^(?:noncomputable )?(?:def|abbrev|theorem|structure) '+re.escape(name)+r'(?=[\s:{])',txt,re.M)
        assert m,(file,name)
        start=m.start()
        if txt[max(0,start-8):start]=='@[simp]\n': start-=8
        end=txt.find('\n\n',m.start())
        if end<0:end=len(txt)
        nextdecl=re.search(r'^/--|^(?:noncomputable )?(?:def|abbrev|theorem|structure) ',txt[m.end():end],re.M)
        if nextdecl: end=m.end()+nextdecl.start()
        raw=txt[start:end]
        s+=raw+'\n\n'
        copied.append(dict(file=file+'.lean',declaration=name,start_line=txt[:start].count('\n')+1,end_line=txt[:end].count('\n')+1,sha256=hashlib.sha256(raw.encode()).hexdigest()))
    s+=f'end MazurProof.{file}\n'
    opened.append(file)
prod=(root/'N25F_XChartFractionMap.lean').read_text()
body=prod[prod.index('namespace MazurProof.N25F_XChartFractionMap'):]
body=body.replace('/-- The universal W-chart point, mapped', 'variable [IsDomain W]\n\n/-- The universal W-chart point, mapped')
s+='\n'+body+'\n'
s+='''#print axioms MazurProof.N25F_XChartFractionMap.qx_ne_zero
#check @MazurProof.N25F_XChartFractionMap.qx_ne_zero
#check @MazurProof.N25F_XChartFractionMap.xChartToFraction
#print axioms MazurProof.N25F_XChartFractionMap.xChartToFraction
#print axioms MazurProof.N25F_XChartFractionMap.xChartToFraction_xY
#print axioms MazurProof.N25F_XChartFractionMap.xChartToFraction_xZ
#print axioms MazurProof.N25F_XChartFractionMap.xChartToFraction_xW
'''
(root/'XChartMapCheck.lean').write_text(s)
(root/'copied-declarations.json').write_text(json.dumps(copied,indent=2)+'\n')
print('Check file',len(s),'bytes;',len(copied),'exact copied declarations')
