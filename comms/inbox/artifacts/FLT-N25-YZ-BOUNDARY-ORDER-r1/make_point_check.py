from pathlib import Path
import re
p=Path('/workspace/shared/flt-n25-yz-boundary-orders')
s=(p/'N25F_YZBoundaryOrder.lean').read_text()
body=s.split('/-- The actual YZ-local length order',1)[1].split('end MazurProof.N25F_YZBoundaryOrder',1)[0]
body='/-- The actual YZ-local length order'+body
start=body.index('private theorem ordFrac_image_eq_exp')
end=body.index('/-- The common-field image',start)
generic=body[start:end];body=body[:start]+body[end:]
for name in ['yzLocalFractionOrder','yzBoundaryOrder','yzLocalFractionOrder_yzWGerm','yzLocalFractionOrder_yzZGerm']:
    body=re.sub(r'(?<!def )(?<!theorem )\b'+name+r'\b', '('+name+' (f := f) (hf := hf))',body)
T='(Localization.AtPrime (RingHom.ker f.toRingHom))'
w=f'(algebraMap YChartRing {T} yzW)'
z=f'(algebraMap YChartRing {T} yZ)'
replacements={
 'YZLocalRing':T,'yzWGerm':w,'yzZGerm':z,
 'yzLocalToFraction':'(N25CurvePointFractionCheck.yzLocalToFraction f hf)',
 'yzLocalToFraction_isFractionRing':'(N25CurvePointFractionCheck.yzLocalToFraction_isFractionRing f hf)',
 'yzLocalToFraction_yzWGerm':'(N25CurvePointFractionCheck.yzLocalToFraction_yzW f hf)',
 'yzLocalToFraction_yzZGerm':'(N25CurvePointFractionCheck.yzLocalToFraction_yZ f hf)',
 'fraction_qy_ne_zero':'(N25CurvePointFractionCheck.fraction_qy_ne_zero f hf)',
 'yzWGerm_ord_eq_one':f'(Fact.out : Ring.ord {T} {w} = 1)',
 'yzWGerm_ne_zero':'(yzWGerm_ne_zero (f := f) (hf := hf))',
 'yzZGerm_isUnit':'(yzZGerm_isUnit (f := f) (hf := hf))'}
for n,replacement in replacements.items(): body=re.sub(r'\b'+n+r'\b',replacement,body)
header='''import CurvePointFractionCheck
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.OrderOfVanishing.Basic
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace N25YZBoundaryPointCheck
open MazurProof
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open N25F_ZChartFractionMap
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "K" => FractionRing W
'''+generic+f'''
variable [Module.IsTorsionFree (Polynomial (ZMod 2)) W] [IsDedekindDomain W]
variable {{f : YChartRing →ₐ[ZMod 2] ZMod 2}} {{hf : f yZ = 1}}
local instance : (RingHom.ker f.toRingHom).IsPrime := RingHom.ker_isPrime f.toRingHom
variable [IsDedekindDomain {T}]
variable [Fact (Ring.ord {T} {w} = 1)]

include hf in
private theorem yzWGerm_ne_zero : {w} ≠ 0 := by
  intro hzero
  have h := congrArg (N25CurvePointFractionCheck.yzLocalToFraction f hf) hzero
  rw [N25CurvePointFractionCheck.yzLocalToFraction_yzW, map_zero] at h
  exact (one_div_ne_zero (N25CurvePointFractionCheck.fraction_qy_ne_zero f hf)) h

include hf in
private theorem yzZGerm_isUnit : IsUnit {z} := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff {T} (RingHom.ker f.toRingHom) yZ).2
  apply Ideal.mem_primeCompl_iff.mpr
  intro h
  have hzero : f yZ = 0 := RingHom.mem_ker.mp h
  rw [hf] at hzero
  exact one_ne_zero hzero

'''
names=['yzLocalFractionOrder','yzBoundaryOrder','yzLocalFractionOrder_yzWGerm','yzLocalFractionOrder_yzZGerm','yzBoundaryOrder_qy','yzBoundaryOrder_qz']
footer='\n'+''.join('#check @'+x+'\n#print axioms '+x+'\n' for x in names)+'end N25YZBoundaryPointCheck\n'
(p/'CurvePointBoundaryOrderCheck.lean').write_text(header+body+footer)
