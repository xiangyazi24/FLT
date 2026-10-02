from pathlib import Path
import hashlib,json,re
r=Path('/workspace/shared/flt-n25-affine-overlap-equiv')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
c=r/'N25F_YZAffineOverlapEquiv.lean'; h=r/'YZAffineOverlapEquivCheck.lean'
body=c.read_text().split('namespace MazurProof.N25F_YZAffineOverlapEquiv',1)[1]
hbody=h.read_text().split('namespace MazurProof.N25F_YZAffineOverlapEquiv',1)[1].split('\n#check @',1)[0].rstrip()+'\n'
assert body==hbody, 'Candidate body differs from exact-definition harness'
log=(r/'check-03.log').read_text()
audits=re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",log)
assert len(audits)==17
for n,a in audits: assert set(re.split(r',\s*',a.strip())) <= {'propext','Classical.choice','Quot.sound'}
assert not re.search(r'\bsorry\b|^axiom ',c.read_text(),re.M)
y=Path('/workspace/shared/flt-n25-yz-overlap-map')
provenance={
 'observed_source':'0b2cfe016226552b61f3ef4074a05e48cec50560',
 'fixture_source_base':'f0eb8381677bc483bddd93826871845030dd5c0e',
 'source_transition':'Parent reports r10 accepted all 14 preceding candidates at this source; requested synthInstance.maxHeartbeats synchronization only. Original exact-definition provenance retained below.',
 'source_y_definitions':json.loads((y/'copied-y-declarations.json').read_text()),
 'source_yX':{'file':str(y/'N25F_YZOverlapMap.lean'),'declaration':'MazurProof.N25F_YZOverlapMap.yX','text':'def yX : YChartRing := chartMap 1 (MvPolynomial.X 0)','sha256':hashlib.sha256(b'def yX : YChartRing := chartMap 1 (MvPolynomial.X 0)').hexdigest()},
 'imported_exact_definition_harnesses':[]}
for d,n in [('flt-n25-zfield-equivalence','ZChartFractionEquivCheck'),('flt-n25-zfraction-injective','ZChartInjectiveCheck')]:
 p=Path('/workspace/shared')/d
 provenance['imported_exact_definition_harnesses'].append({'file':str(p/(n+'.lean')),'source_sha256':sha(p/(n+'.lean')),'olean_sha256':sha(p/(n+'.olean'))})
(r/'source-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
validation={
 'main_declaration':'MazurProof.N25F_YZAffineOverlapEquiv.yzAffineOverlapEquiv',
 'type':'Localization.Away yZ ≃ₐ[ZMod 2] Localization.Away zY',
 'lean':'4.31.0-rc2','mathlib':'96fd0fff3b8837985ae21dd02e712cb5df72ec05',
 'check_kind':'Unconditional exact-actual-chart-definition harness; production body byte-identical',
 'production_body_matches_harness':True,'added_premises':False,'harness_parameters':[],
 'full_FLT_imports_compiled':False,'candidate_sha256':sha(c),'harness_sha256':sha(h),
 'reusable_olean_sha256':sha(r/'YZAffineOverlapEquivCheck.olean'),
 'audited_declarations':len(audits),'axioms':['propext','Classical.choice','Quot.sound'],
 'checks':[json.loads((r/'check-03.json').read_text())],
 'historical_checks':[json.loads((r/(n+'.json')).read_text()) for n in ['check-01','check-02']],
 'configuration_sync':json.loads((r/'configuration-sync.json').read_text()),
 'file_level_options':{'synthInstance.maxHeartbeats':200000},
 'import_environment':{'LEAN_PATH':'/workspace/shared/flt-n25-zfield-equivalence:/workspace/shared/flt-n25-zfraction-injective'},
 'no_predecessor_changes':True,'no_remote_writes':True}
validation['checks'][0]['timing_note']='Total wrapper duration includes shared compiler gate wait; compiler timeout remained 60 seconds.'
(r/'validation.json').write_text(json.dumps(validation,indent=2)+'\n')
print(json.dumps(validation,indent=2))
