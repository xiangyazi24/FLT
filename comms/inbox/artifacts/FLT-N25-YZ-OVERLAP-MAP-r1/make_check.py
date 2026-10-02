from pathlib import Path
import hashlib,re,json
r=Path('/workspace/shared/flt-n25-yz-overlap-map');src=Path('/workspace/shared/flt-n25-yz-zunit/RationalPointsN25QuotientTwoWBoundaryYZChartArtin.lean').read_text()
s='''import ZChartFractionEquivCheck
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
'''
records=[]
for n in ['YChartRing','yZ','yzW']:
 m=re.search(r'^(?:abbrev|def) '+n+r'\b',src,re.M);a=m.start();b=src.find('\n\n',a);nxt=re.search(r'^/--|^(?:abbrev|def|theorem) ',src[m.end():b],re.M);b=m.end()+nxt.start() if nxt else b;raw=src[a:b];s+=raw+'\n\n';records.append({'declaration':n,'first_line':src[:a].count('\n')+1,'sha256':hashlib.sha256(raw.encode()).hexdigest()})
s+='end MazurProof.RationalPointsN25QuotientTwoWBoundaryYZChartArtin\n'
p=(r/'N25F_YZOverlapMap.lean').read_text();body=p[p.index('namespace MazurProof.'):]
body=body.replace('open RationalPointsN25QuotientTwoWBoundaryYZLocal\n','').replace(' N25F_YZLocalZUnit','')
body=body.replace('YZLocalRing','L')
body=re.sub(r'\byzZGerm\b','(algebraMap YChartRing L yZ)',body)
body=re.sub(r'\byzWGerm\b','(algebraMap YChartRing L yzW)',body)
body=body.replace('yzZGerm_isUnit', '(show IsUnit (algebraMap YChartRing L yZ) from Fact.out)')
body=body.replace('/-- The unit realizing', '''variable {L : Type*} [CommRing L] [Algebra (ZMod 2) L] [Algebra YChartRing L]
  [IsScalarTower (ZMod 2) YChartRing L] [Fact (IsUnit (algebraMap YChartRing L yZ))]

/-- The unit realizing''')
refs=['yzZUnit','yzZUnit_val','yzZPoint','yzZPoint_z','yzZPoint_quadric','yzZPoint_cubic','zChartToYZLocal','zChartToYZLocal_zX','zChartToYZLocal_zY','zChartToYZLocal_zW']
for n in refs:
 spans=[m.start(1) for m in re.finditer(r'^(?:private )?(?:def|theorem|instance) ('+n+r')\b',body,re.M)]
 for m in reversed(list(re.finditer(r'\b'+n+r'\b',body))):
  if m.start() in spans:continue
  body=body[:m.start()]+'('+n+' (L := L))'+body[m.end():]
body='\n'.join(line.replace('(yzZPoint (L := L))','yzZPoint').replace('(zChartToYZLocal (L := L))','zChartToYZLocal') if re.match(r'\s*rw \[',line) else line for line in body.split('\n'))
s+='\n'+body+'\n'
for n in ['yzZUnit','yzZUnit_val','yzZPoint_z','zChartToYZLocal','zChartToYZLocal_zX','zChartToYZLocal_zY','zChartToYZLocal_zW','zChartToYZLocal_zY_isUnit']:
 s+=f'#check @MazurProof.N25F_YZOverlapMap.{n}\n#print axioms MazurProof.N25F_YZOverlapMap.{n}\n'
(r/'GenericYZOverlapMapCheck.lean').write_text(s);(r/'copied-y-declarations.json').write_text(json.dumps(records,indent=2)+'\n');print(len(s),hashlib.sha256(s.encode()).hexdigest())
