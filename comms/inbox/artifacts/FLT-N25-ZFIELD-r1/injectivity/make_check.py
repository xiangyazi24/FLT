from pathlib import Path
import hashlib,re,json
r=Path('/workspace/shared/flt-n25-zfraction-injective')
s=Path('/workspace/shared/flt-n25-zfraction-map/ZChartFractionMapCheck.lean').read_text()
s='''import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.DedekindDomain.Basic
'''+s
p=Path('/workspace/shared/flt-n25-zchart-equiv/N25F_ZChartWChartEquiv.lean').read_text();body=p[p.index('namespace MazurProof.'):]
for n in ['zX','zY']:
 body=re.sub(r'/-- The `'+('X/Z' if n=='zX' else 'Y/Z')+r'` coordinate\.[^\n]*\n'+r'def '+n+r' : ZChartRing :=[^\n]*\n','',body)
body=body.replace('/-- The actual Z-chart ring is a domain','variable [IsDedekindDomain W]\n\n/-- The actual Z-chart ring is a domain')
s+='\n'+body+'\n'
p=(r/'N25F_ZChartFractionInjective.lean').read_text();body=p[p.index('namespace MazurProof.'):]
body=body.replace('/-- No positive power','variable [Module.IsTorsionFree (Polynomial (ZMod 2)) W]\n\n/-- No positive power')
body=body.replace('/-- The actual Z-chart transition','variable [IsDedekindDomain W]\n\n/-- The actual Z-chart transition')
s+='\n'+body+'\n'
for n in ['qz_pow_ne_one','zChartToFraction_injective']:
 s+=f'#check @MazurProof.N25F_ZChartFractionInjective.{n}\n#print axioms MazurProof.N25F_ZChartFractionInjective.{n}\n'
(r/'ZChartInjectiveCheck.lean').write_text(s);print(len(s),hashlib.sha256(s.encode()).hexdigest())
