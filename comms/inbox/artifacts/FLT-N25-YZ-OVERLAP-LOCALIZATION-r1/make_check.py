from pathlib import Path
import re,hashlib
r=Path('/workspace/shared/flt-n25-yz-overlap-localization');s='import Mathlib.RingTheory.Localization.Away.Basic\n'+Path('/workspace/shared/flt-n25-yz-overlap-map/GenericYZOverlapMapCheck.lean').read_text()
p=(r/'N25F_YZOverlapLocalization.lean').read_text();body=p[p.index('namespace MazurProof.'):]
body=body.replace('open RationalPointsN25QuotientTwoWBoundaryYZLocal\n','').replace(' N25F_YZLocalZUnit','')
body=body.replace('YZLocalRing','L').replace('      yzZGerm := by','      algebraMap YChartRing L yZ := by')
body=body.replace('private theorem zChartToYZLocal_isUnit_of_powers', '''variable {L : Type*} [CommRing L] [Algebra (ZMod 2) L] [Algebra YChartRing L]
  [IsScalarTower (ZMod 2) YChartRing L] [Fact (IsUnit (algebraMap YChartRing L yZ))]

private theorem zChartToYZLocal_isUnit_of_powers''')
refs=['yzZUnit','zChartToYZLocal','zChartToYZLocal_zY','zChartToYZLocal_zY_isUnit','zChartToYZLocal_isUnit_of_powers','zYOpenToYZLocal','zYOpenToYZLocal_algebraMap']
for n in refs:
 spans=[m.start(1) for m in re.finditer(r'^(?:private )?(?:def|theorem) ('+n+r')\b',body,re.M)]
 for m in reversed(list(re.finditer(r'\b'+n+r'\b',body))):
  if m.start() in spans:continue
  body=body[:m.start()]+'('+n+' (L := L))'+body[m.end():]
s+='\n'+body+'\n'
for n in ['zYOpenToYZLocal','zYOpenToYZLocal_algebraMap','zYOpenToYZLocal_invSelf']:
 s+=f'#check @MazurProof.N25F_YZOverlapLocalization.{n}\n#print axioms MazurProof.N25F_YZOverlapLocalization.{n}\n'
(r/'GenericYZOverlapLocalizationCheck.lean').write_text(s);print(len(s),hashlib.sha256(s.encode()).hexdigest())
