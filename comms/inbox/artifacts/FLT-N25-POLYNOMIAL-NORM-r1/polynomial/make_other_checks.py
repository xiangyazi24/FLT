from pathlib import Path
import re
r=Path('/workspace/shared/flt-n25-polynomial-boundary-orders')
s=(r/'N25F_PolynomialBoundaryOrders.lean').read_text();g=s[s.index('private theorem ordFrac_aeval_at_pole'):s.index('/-- The actual X boundary')]
# YZ harness retains the existing actual curve/point-family construction.
y=Path('/workspace/shared/flt-n25-yz-boundary-orders/CurvePointBoundaryOrderCheck.lean').read_text();y=y[:y.index('#check @yzLocalFractionOrder')];y=y.replace('import Mathlib.RingTheory.OrderOfVanishing.Basic','import Mathlib.RingTheory.OrderOfVanishing.Noetherian\nimport Mathlib.RingTheory.Valuation.IsTrivialOn\nimport Mathlib.Tactic.NormNum')
part=s[s.index('/-- The actual YZ boundary'):s.index('/-- The actual Z boundary')]
T='(Localization.AtPrime (RingHom.ker f.toRingHom))'
part=part.replace('YZLocalRing',T)
for name in ['yzLocalToFraction_isFractionRing','yzLocalToFraction']:
 part=re.sub(r'\b'+name+r'\b', f'(N25CurvePointFractionCheck.{name} f hf)', part)
for name in ['yzLocalFractionOrder','yzBoundaryOrder_qz']:
 part=re.sub(r'\b'+name+r'\b', f'({name} (f := f) (hf := hf))',part)
needle=' := by\n  letI : Algebra'
DVR=''' := by
  letI : IsDiscreteValuationRing '''+T+''' := by
    have hn : ¬ IsField '''+T+''' := by
      intro hfield
      letI : Field '''+T+''' := hfield.toField
      have hu := Ring.ord_of_isUnit (isUnit_iff_ne_zero.mpr (yzWGerm_ne_zero (f := f) (hf := hf)))
      have ho : Ring.ord '''+T+''' (algebraMap YChartRing '''+T+''' yzW) = 1 := Fact.out
      rw [ho] at hu
      exact one_ne_zero hu
    exact ((IsDiscreteValuationRing.TFAE '''+T+''' hn).out 0 2).mpr
      (inferInstance : IsDedekindDomain '''+T+''')
  letI : Algebra'''
part=part.replace(needle,DVR)
(r/'YZPolynomialBoundaryCheck.lean').write_text(y+'\n'+g+'\n'+part+'#check @yzLocalFractionOrder_aeval_qz\n#print axioms yzLocalFractionOrder_aeval_qz\nend N25YZBoundaryPointCheck\n')
# Z harness retains the earlier exact Z chart plus explicit source point facts.
z=Path('/workspace/shared/flt-n25-zboundary-order/GenericZBoundaryOrderCheck.lean').read_text();z=z[:z.index('end MazurProof.N25F_ZBoundaryOrder')];z=z.replace('import Mathlib.RingTheory.OrderOfVanishing.Basic','import Mathlib.RingTheory.OrderOfVanishing.Noetherian\nimport Mathlib.RingTheory.Valuation.IsTrivialOn\nimport Mathlib.Tactic.NormNum\nset_option synthInstance.maxHeartbeats 200000')
part=s[s.index('/-- The actual Z boundary'):s.index('end MazurProof.N25F_PolynomialBoundaryOrders')]
for name in ['zLocalToFraction_isFractionRing','zLocalToFraction','zLocalFractionOrder','zBoundaryOrder_qz']:
 part=re.sub(r'\b'+name+r'\b',f'({name} (pointEval := pointEval))',part)
(r/'ZPolynomialBoundaryCheck.lean').write_text(z+'\n'+g+'\n'+part+'#check @zLocalFractionOrder_aeval_qz\n#print axioms zLocalFractionOrder_aeval_qz\nend MazurProof.N25F_ZBoundaryOrder\n')
