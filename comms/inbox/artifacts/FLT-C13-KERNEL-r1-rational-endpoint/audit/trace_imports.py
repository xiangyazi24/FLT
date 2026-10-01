"""Read-only static import-closure audit. Never loads or executes Lean code."""
from pathlib import Path
import hashlib, json, re

ROOT = Path('/workspace/shared')
OUT = ROOT/'flt-c13-endgame-audit'
PIN = '29e80dbc17c5fdf3a194618d65dc0676199e19f5'
DIRECTORY = {r['path']: r for r in json.loads((OUT/'OPERATIVE_DIRECTORY.json').read_text())}

def no_comments(s):
    result=[]; i=0; depth=0; string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i): depth+=1; i+=2
            elif s.startswith('-/',i): depth-=1; i+=2
            else:
                if s[i]=='\n': result.append('\n')
                i+=1
        elif string:
            if s[i]=='\\': result.extend('  '); i+=2
            elif s[i]=='"': result.append(' '); i+=1; string=False
            else: result.append('\n' if s[i]=='\n' else ' '); i+=1
        elif s.startswith('/-',i): depth=1; i+=2
        elif s.startswith('--',i):
            j=s.find('\n',i); i=len(s) if j<0 else j
        elif s[i]=='"': string=True;result.append(' ');i+=1
        else: result.append(s[i]);i+=1
    return ''.join(result)

def blob(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def record(p):
    b=p.read_bytes(); return {'local':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'git_blob':blob(b)}

bases=[ROOT/'flt-c13-r2-input',ROOT/'flt-c13-kernel-input',ROOT/'flt-c13-delivery-final',ROOT/'flt-c13-kernel-next',ROOT/'flt-c13-kernel-accepted-940d',ROOT/'flt-c13-kernel-accepted-29e8']
inventory={}
for base in bases:
    for p in (base/'FLT').rglob('*.lean'):
        inventory.setdefault(str(p.relative_to(base)),[]).append(p)
for p in (ROOT/'flt-c13-r2-next-audit/calibration-pinned-reference').glob('*.lean'):
    inventory.setdefault('FLT/Assumptions/MazurProof/'+p.name,[]).append(p)
for p in (OUT/'sources').glob('*.lean'):
    inventory.setdefault('FLT/Assumptions/MazurProof/'+p.name,[]).insert(0,p)
for p in (OUT/'external-sources').rglob('*.lean') if (OUT/'external-sources').exists() else []:
    inventory.setdefault(str(p.relative_to(OUT/'external-sources')),[]).insert(0,p)

for p in ROOT.glob('flt-c13-*/**/FLT__Assumptions__MazurProof__*.lean'):
    inventory.setdefault(p.name.replace('__','/'),[]).append(p)

root_names=['N13ConstructedRationalPointTheorem','N13ReductionClassifier','N13MumfordFullKummerTwoSurjective','N13GaussianGlobalZeroCarrierDlog','N13MumfordFullKummerIdentityFiber']
queue=['FLT.Assumptions.MazurProof.'+n for n in root_names];seen={};missing=[];external=[]
while queue:
    module=queue.pop(0)
    if module in seen: continue
    path=module.replace('.','/')+'.lean'; candidates=inventory.get(path,[]); tracked=DIRECTORY.get(path)
    selected=None; provenance=None
    overrides = {r['path']:r for r in json.loads((ROOT/'flt-c13-endgame-isolation/review-manifest.json').read_text())}
    if path in overrides:
        selected=Path(overrides[path]['local_path']); provenance='reviewed import-isolation overlay'
        assert hashlib.sha256(selected.read_bytes()).hexdigest()==overrides[path]['sha256']
    elif tracked:
        selected=next((p for p in candidates if blob(p.read_bytes())==tracked['sha']),None)
        provenance=PIN
    elif candidates:
        # New reviewed construction overlays are explicit and locally auditable.
        selected=next((p for p in candidates if str(p).startswith(str(ROOT/'flt-c13-kernel-next'))),None)
        if selected: provenance='reviewed local construction overlay'
        else:
            selected=next((p for p in candidates if str(p).startswith(str(ROOT/'flt-c13-delivery-final'))),None)
            if selected: provenance='source-reviewed 2561ea7c dependency overlay'
            elif not path.startswith('FLT/Assumptions/MazurProof/'):
                selected=candidates[0];provenance=PIN+' fetched external path'
    if selected is None:
        status='tracked_source_needs_materialization' if tracked else 'not_in_tracked_directory_or_local_overlay'
        item={'module':module,'path':path,'status':status,'expected_blob':tracked['sha'] if tracked else None}
        missing.append(item);seen[module]=item;continue
    text=selected.read_text();clean=no_comments(text)
    imports=[]
    for line in clean.splitlines():
        m=re.match(r'\s*(?:public\s+)?import\s+(.+)',line)
        if m:
            imports.extend(m.group(1).split())
    flags=[]
    for lineno,line in enumerate(clean.splitlines(),1):
        if re.search(r'\b(?:axiom|sorry|admit)\b|exactSpreadLine|C13Sextic_affine_x_is_cuspidal|CyclicExclusion13|coheren',line,re.I):
            flags.append({'line':lineno,'text':line.strip()})
    seen[module]={'module':module,'source_path':path,**record(selected),'provenance':provenance,'imports':imports,'flags':flags}
    for imp in imports:
        if imp.startswith('FLT.'):queue.append(imp)
        else:external.append(imp)

out={'roots':root_names,'operative_pin':PIN,'resolved_count':sum('local' in r for r in seen.values()),'entries':seen,'missing':missing,'external_library_imports':sorted(set(external))}
(OUT/'IMPORT_CLOSURE.json').write_text(json.dumps(out,indent=2)+'\n')
(OUT/'FETCH_QUEUE.json').write_text(json.dumps(missing,indent=2)+'\n')
print(json.dumps({'resolved':out['resolved_count'],'total_seen':len(seen),'missing':len(missing),'flagged_modules':[k for k,r in seen.items() if r.get('flags')],'missing_names':[r['module'] for r in missing]},indent=2))
