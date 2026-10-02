from pathlib import Path
import re,json,hashlib
root=Path('/workspace/shared/flt-n25-xlocal-fraction')
base=Path('/workspace/shared/flt-n25-xchart-injective/XChartInjectiveCheck.lean').read_text()
s='import Mathlib.RingTheory.Localization.AtPrime.Basic\n'+base
src=(root/'RationalPointsN25QuotientTwoWBoundaryXLocal.lean').read_text()
names=['XAffineRing','xAffineEval','xAffineEvalAlg','xAffineEval_quadric','xAffineEval_cubic','xEquationIdeal_le_ker','xChartEval','xChartEval_surjective','xPrime','xPrime_isMaximal','XLocalRing','xWGerm']
s+='\nnamespace MazurProof.RationalPointsN25QuotientTwoWBoundaryXLocal\nopen RationalPointsN25QuotientTwoAffineCharts\nopen RationalPointsN25QuotientTwoAffineChartsSmooth\nopen RationalPointsN25QuotientTwoConormal\nopen RationalPointsN25QuotientTwoWBoundaryChartArtin\nlocal notation "k₂" => ZMod 2\n'
records=[]
for name in names:
    m=re.search(r'^(?:private )?(?:noncomputable )?(?:def|abbrev|theorem) '+re.escape(name)+r'(?=[\s:{])',src,re.M)
    assert m,name
    start=m.start();end=src.find('\n\n',m.end());end=len(src) if end<0 else end
    body=src[start:end]
    s+='\n'+body+'\n'
    records.append({'declaration':name,'first_line':src[:start].count('\n')+1,'sha256':hashlib.sha256(body.encode()).hexdigest()})
    if name=='xPrime_isMaximal':s+='\nlocal instance : xPrime.IsPrime := xPrime_isMaximal.isPrime\n'
s+='\nend MazurProof.RationalPointsN25QuotientTwoWBoundaryXLocal\n'
prod=(root/'N25F_XLocalFractionEmbedding.lean').read_text()
body=prod[prod.index('namespace MazurProof.N25F_XLocalFractionEmbedding'):]
body=body.replace('local notation "W" => N25F_NonBoundaryPrincipalDivisor.W','local notation "W" => N25F_NonBoundaryPrincipalDivisor.W\nvariable [IsDedekindDomain W]')
s+='\n'+body+'\n'
for n in ['xLocalToFraction','xLocalToFraction_algebraMap','xLocalToFraction_injective','xLocalToFraction_xWGerm']:
    s+=f'#check @MazurProof.N25F_XLocalFractionEmbedding.{n}\n#print axioms MazurProof.N25F_XLocalFractionEmbedding.{n}\n'
(root/'XLocalFractionCheck.lean').write_text(s)
(root/'copied-local-declarations.json').write_text(json.dumps(records,indent=2)+'\n')
print(len(s),hashlib.sha256(s.encode()).hexdigest())
