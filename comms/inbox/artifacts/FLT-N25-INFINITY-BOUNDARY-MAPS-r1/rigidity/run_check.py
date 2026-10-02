from pathlib import Path
import sys,subprocess,time,resource,json,hashlib
root=Path('/workspace/shared/flt-n25-local-valuation-rigidity')
name=sys.argv[1];args=sys.argv[2:]
start=time.monotonic()
r=subprocess.run(['/workspace/shared/lean-feedback/with-compiler-slot','/workspace/shared/lean-feedback/check-lean']+args,capture_output=True,text=True)
(root/(name+'.log')).write_text(r.stdout+r.stderr)
source=Path(args[-1]);source=source if source.is_absolute() else Path('/workspace/shared/lean-feedback/mathlib')/source
info={'name':name,'args':args,'exit_code':r.returncode,'seconds':time.monotonic()-start,'peak_child_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
(root/(name+'.json')).write_text(json.dumps(info,indent=2)+'\n')
print(json.dumps(info));print(r.stdout+r.stderr);sys.exit(r.returncode)
