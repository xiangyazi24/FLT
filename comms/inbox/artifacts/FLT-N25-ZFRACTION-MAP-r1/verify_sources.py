from pathlib import Path
import hashlib,json
r=Path('/workspace/shared/flt-n25-zfraction-map')
prior={}
for name in ['flt-n25-xchart-map','flt-n25-zchart-equiv']:
 for d in json.loads((Path('/workspace/shared')/name/'source-inputs.json').read_text()): prior[d['file']]=d
for name in ['RationalPointsN25QuotientTwoPlaneFunctionField','RationalPointsN25QuotientTwoPlaneChartBridge']:
 meta=json.loads((r/f'{name}-source.json').read_text())
 data=(r/'sources'/f'{name}.lean').read_bytes()
 prior[f'{name}.lean']={'file':f'{name}.lean','repository':'xiangyazi24/FLT','ref':'f0eb8381677bc483bddd93826871845030dd5c0e','git_blob_sha':meta['sha'],'url':meta['url'],'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
used={d['file'] for d in json.loads((r/'copied-declarations.json').read_text())}
selected=[]
for filename in sorted(used):
 data=(r/'sources'/filename).read_bytes()
 if filename=='N25F_ZChartWChartEquiv.lean':
  d={'file':filename,'source':'Passed local predecessor /workspace/shared/flt-n25-zchart-equiv/N25F_ZChartWChartEquiv.lean','sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'scope':'Only zX and zY coordinate definitions copied, verbatim'}
 else:
  d=prior[filename]
  assert hashlib.sha256(data).hexdigest()==d['sha256'],filename
  assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==d['git_blob_sha'],filename
 selected.append(d)
(r/'source-inputs.json').write_text(json.dumps(selected,indent=2)+'\n')
print('verified',len(selected)-1,'accepted-source git blobs and one passed local predecessor')
