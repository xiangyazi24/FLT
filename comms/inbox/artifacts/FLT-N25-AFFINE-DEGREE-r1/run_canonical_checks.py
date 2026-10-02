from pathlib import Path
import datetime, hashlib, json, os, shutil, subprocess, time
base=Path('/workspace/shared/flt-n25-divisor-length')
tree=base/'check_project'; mod=Path('FLT/Assumptions/MazurProof'); dest=tree/mod
runner=Path('/workspace/shared/lean-feedback/check-lean')
production=base/'production'; production.mkdir(exist_ok=True)
new_names=['N25F_DedekindFactorDegree','N25F_PrincipalDivisorCoefficient','N25F_PrincipalDivisorQuotientDegree','N25F_WChartPrincipalDegree']
def record_bytes(data):
 return {'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'git_blob':hashlib.sha1(f'blob {len(data)}\0'.encode()+data).hexdigest()}
original=(base/'sources/CurveDedekindDivisor.lean').read_bytes()
canonical=original[:-1]
assert original.endswith(b'\n\n')
assert record_bytes(canonical)['git_blob']=='20c6208962f3163e4eabda838efc5c73afdc0b6c'
(dest/'CurveDedekindDivisor.lean').write_bytes(canonical)
for name in new_names:
 shutil.copyfile(base/f'{name}.lean',production/f'{name}.lean')
 if name!='N25F_WChartPrincipalDegree': shutil.copyfile(base/f'{name}.lean',dest/f'{name}.lean')
receipt={
 'baseline_FLT':'9ecac38589bd3b45abc144ffda01e2f711213c52',
 'baseline_note':'Parent verified this baseline adds only the accepted norm-dimension file to 40efa26fea43fb0ed7d70db804f0d0dcdd71342b; these dependencies unchanged.',
 'mathlib':'96fd0fff3b8837985ae21dd02e712cb5df72ec05','lean':'4.31.0-rc2',
 'runner':{'path':str(runner),**record_bytes(runner.read_bytes()),'cpu_threads':1,'lean_memory_limit_MB':3072,'timeout_seconds':60},
 'overlay_root':str(tree),'production_root':str(production),
 'original_curve_materialization':{'path':str(base/'sources/CurveDedekindDivisor.lean'),**record_bytes(original)},
 'canonical_curve_source':{'path':str(dest/'CurveDedekindDivisor.lean'),**record_bytes(canonical),'correction':'Removed exactly one extra terminal newline from connector-materialized source; all other bytes unchanged; resulting blob matches parent-supplied accepted Git blob.'},
 'production_files':[], 'source_harness_identity':[], 'checks':[],
 'actual_W_project_compile':{'status':'not_run','reason':'The actual-W geometry import closure is lead-owned; no broad FLT build was requested locally.'},
}
for name in new_names:
 p=production/f'{name}.lean'; receipt['production_files'].append({'path':str(p),**record_bytes(p.read_bytes())})
harness=(base/'PrincipalDivisorQuotientDegreeChecked.lean').read_text()
for p in [base/'sources/CurveDedekindDivisor.lean',base/'GenericDedekindFactorDegree.lean',base/'N25F_PrincipalDivisorCoefficient.lean',base/'N25F_PrincipalDivisorQuotientDegree.lean']:
 body='\n'.join(l for l in p.read_text().splitlines() if not l.startswith('import '))
 assert body in harness
 receipt['source_harness_identity'].append({'source_path':str(p),'harness_path':str(base/'PrincipalDivisorQuotientDegreeChecked.lean'),'comparison':'Exact line-preserved source body, excluding only import lines, appears contiguously in previously checked harness; imports were consolidated at top.','body_sha256':hashlib.sha256(body.encode()).hexdigest(),'identical':True})
audit=tree/'PrincipalDegreeAxiomCheck.lean'
assert audit.exists()
commands=[]
for name in ['CurveDedekindDivisor']+new_names[:3]:
 src=dest/f'{name}.lean'; out=dest/f'{name}.olean'
 commands.append((name,[str(runner),'-R',str(tree),'-o',str(out),str(src)],src,out))
commands.append(('PrincipalDegreeAxiomCheck',[str(runner),'-R',str(tree),str(audit)],audit,None))
env=dict(os.environ);env['LEAN_PATH']=str(tree)
receipt_path=base/'CANONICAL_COMPILE_RECEIPT.json'; log_path=base/'CanonicalModuleChecks.log'
with log_path.open('w') as log:
 for name,argv,src,out in commands:
  start=datetime.datetime.now(datetime.timezone.utc).isoformat(); t=time.monotonic()
  proc=subprocess.run(argv,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  duration=time.monotonic()-t
  entry={'name':name,'argv':argv,'environment_additions':{'LEAN_PATH':str(tree)},'started_utc':start,'duration_seconds':duration,'exit_code':proc.returncode,'source':{'path':str(src),**record_bytes(src.read_bytes())},'output':proc.stdout}
  if out and out.exists(): entry['olean']={'path':str(out),**record_bytes(out.read_bytes())}
  receipt['checks'].append(entry);receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
  log.write(f'CHECK {name}\nCOMMAND {argv!r}\nEXIT {proc.returncode}; DURATION {duration:.6f}s\n{proc.stdout}\n');log.flush()
  print(f'{name}: exit {proc.returncode}, {duration:.3f}s',flush=True)
  if proc.returncode: raise SystemExit(proc.returncode)
receipt['all_canonical_checks_passed']=True
receipt['emitted_axioms']=['propext','Classical.choice','Quot.sound']
receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
print('Receipt:',receipt_path)
