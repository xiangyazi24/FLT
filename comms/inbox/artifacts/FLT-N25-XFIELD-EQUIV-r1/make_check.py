from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
prereq=root/'prerequisites'
base=(prereq/'XChartInjectiveCheck.lean').read_text()
base=base[:base.index('#check @MazurProof.N25F_XChartFractionInjective.')]
p=root/'N25F_XChartFractionEquiv.lean'
body=p.read_text(); body=body[body.index('namespace MazurProof.'):]
body=body.replace('/-- The coordinate-rigid extension', 'variable [IsDedekindDomain W]\n\n/-- The coordinate-rigid extension',1)
s=base+'\n'+body+'\n'
for name in ['xFractionToFraction','xFractionToFraction_algebraMap','fraction_qx_mem_range','fraction_qy_mem_range','fraction_qz_mem_range','wChart_algebraMap_mem_range','xFractionToFraction_surjective','xFractionToFraction_injective','xChartFractionAlgEquiv','xChartFractionAlgEquiv_algebraMap','xChartToFraction_isFractionRing']:
    s+=f'#check @MazurProof.N25F_XChartFractionEquiv.{name}\n#print axioms MazurProof.N25F_XChartFractionEquiv.{name}\n'
(root/'XChartFractionEquivCheck.lean').write_text(s)
print(len(s),'bytes')
meta={'prerequisite_harness':str(prereq/'XChartInjectiveCheck.lean'),'prerequisite_sha256':hashlib.sha256((prereq/'XChartInjectiveCheck.lean').read_bytes()).hexdigest(),'candidate_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'harness_sha256':hashlib.sha256(s.encode()).hexdigest()}
(root/'harness-inputs.json').write_text(json.dumps(meta,indent=2)+'\n')
