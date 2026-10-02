from pathlib import Path
import hashlib
r=Path('/workspace/shared/flt-n25-zfield-equivalence')
p=(r/'N25F_ZChartFractionEquiv.lean').read_text();body=p[p.index('namespace MazurProof.'):]
body=body.replace('local notation "W" => N25F_NonBoundaryPrincipalDivisor.W','local notation "W" => N25F_NonBoundaryPrincipalDivisor.W\nvariable [Module.IsTorsionFree (Polynomial (ZMod 2)) W] [IsDedekindDomain W]')
s='''import ZChartInjectiveCheck
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
'''+body+'\n'
for n in ['zFractionToFraction','zFractionToFraction_algebraMap','fraction_qz_mem_range','fraction_qx_mem_range','fraction_qy_mem_range','wChart_algebraMap_mem_range','zFractionToFraction_surjective','zFractionToFraction_injective','zChartFractionAlgEquiv','zChartFractionAlgEquiv_algebraMap','zChartToFraction_isFractionRing']:
 s+=f'#check @MazurProof.N25F_ZChartFractionEquiv.{n}\n#print axioms MazurProof.N25F_ZChartFractionEquiv.{n}\n'
(r/'ZChartFractionEquivCheck.lean').write_text(s);print(len(s),hashlib.sha256(s.encode()).hexdigest())
