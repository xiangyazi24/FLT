from pathlib import Path
import re,json,hashlib
root=Path('/workspace/shared/flt-n25-xboundary-order')
source=Path('/workspace/shared/flt-n25-xlocal-fraction/RationalPointsN25QuotientTwoWBoundaryXLocal.lean')
src=source.read_text()
s='''import XChartFractionEquivCheck
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.OrderOfVanishing.Basic
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoWBoundaryChartArtin
local notation "k₂" => ZMod 2
'''
names=['XAffineRing','xAffineEval','xAffineEvalAlg','xAffineEval_quadric','xAffineEval_cubic','xEquationIdeal_le_ker','xChartEval','xChartEval_surjective','xPrime','xPrime_isMaximal','xChartEval_xW','XLocalRing','xWGerm']
records=[]
for name in names:
    m=re.search(r'^(?:@\[simp\] )?(?:private )?(?:noncomputable )?(?:def|abbrev|theorem) '+re.escape(name)+r'(?=[\s:{])',src,re.M)
    assert m,name
    a=m.start();b=src.find('\n\n',m.end());b=len(src) if b<0 else b;raw=src[a:b]
    s+='\n'+raw+'\n';records.append({'declaration':name,'first_line':src[:a].count('\n')+1,'sha256':hashlib.sha256(raw.encode()).hexdigest()})
    if name=='xPrime_isMaximal':s+='\nlocal instance : xPrime.IsPrime := xPrime_isMaximal.isPrime\n'
s+='\nend MazurProof.RationalPointsN25QuotientTwoWBoundaryXLocal\n'
for path in [Path('/workspace/shared/flt-n25-xlocal-dvr/N25F_XLocalDVR.lean'),Path('/workspace/shared/flt-n25-xlocal-fraction/N25F_XLocalFractionEmbedding.lean'),root/'N25F_XBoundaryOrder.lean']:
    p=path.read_text();body=p[p.index('namespace MazurProof.'):]
    body=body.replace('local notation "W" => N25F_NonBoundaryPrincipalDivisor.W','local notation "W" => N25F_NonBoundaryPrincipalDivisor.W\nvariable [IsDedekindDomain W]')
    if path.name=='N25F_XBoundaryOrder.lean':
        body=body.replace('/-- The common-field image of the actual boundary germ', '''variable (xWGerm_ord_eq_three : Ring.ord XLocalRing xWGerm = 3)
include xWGerm_ord_eq_three

/-- The common-field image of the actual boundary germ''')
        body=body.replace('WithZero.log_inv, xLocalFractionOrder_xWGerm,','WithZero.log_inv, xLocalFractionOrder_xWGerm xWGerm_ord_eq_three,')
    s+='\n'+body+'\n'
for n in ['xLocalToFraction_isFractionRing','xLocalFractionOrder','xBoundaryOrder','xLocalFractionOrder_xWGerm','xBoundaryOrder_qx']:
    s+=f'#check @MazurProof.N25F_XBoundaryOrder.{n}\n#print axioms MazurProof.N25F_XBoundaryOrder.{n}\n'
(root/'XBoundaryOrderCheck.lean').write_text(s);(root/'copied-local-declarations.json').write_text(json.dumps(records,indent=2)+'\n');print(len(s),hashlib.sha256(s.encode()).hexdigest())
