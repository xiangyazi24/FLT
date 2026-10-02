from pathlib import Path
r=Path('/workspace/shared/flt-n25-xcoordinate-orders')
g=(r/'GenericCoordinateOrders.lean').read_text();g=g[g.index('theorem coordinate_orders'):g.index('#print axioms')].strip()
b=(r/'ProductionBody.lean').read_text().replace('open N25F_XLocalDVR\n','open N25F_XLocalDVR\n\nprivate '+g+'\n')
header='''import FLT.Assumptions.MazurProof.N25F_XBoundaryOrder
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.Tactic.NormNum

/-! Orders of the actual Y/X and Z/X germs at the X-boundary point,
derived from the defining quadric and cubic and the known W/X order. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
'''
(r/'N25F_XCoordinateOrders.lean').write_text(header+b)
x=Path('/workspace/shared/flt-n25-xboundary-order/XBoundaryOrderCheck.lean').read_text(); x=x[:x.index('namespace MazurProof.N25F_XLocalFractionEmbedding')]
x=x.replace('import Mathlib.RingTheory.OrderOfVanishing.Basic','import Mathlib.RingTheory.OrderOfVanishing.Noetherian\nimport Mathlib.Tactic.NormNum\nset_option synthInstance.maxHeartbeats 200000')
# Add the two exact source evaluator lemmas omitted by the earlier W-only check.
src=Path('/workspace/shared/flt-r10-acceptance/accepted/RationalPointsN25QuotientTwoWBoundaryXLocal.lean').read_text()
a=src.index('@[simp] theorem xChartEval_xY');z=src.index('theorem xWIdeal_le_xPrime',a)
x=x.replace('abbrev XLocalRing :=',src[a:z]+'\nabbrev XLocalRing :=')
b=b.replace('open N25F_XLocalDVR\n','open N25F_XLocalDVR\nlocal notation "W" => N25F_NonBoundaryPrincipalDivisor.W\nvariable [IsDedekindDomain W]\n')
b=b.replace('private theorem xCoordinateGermOrders','variable (xWGerm_ord_eq_three : Ring.ord XLocalRing xWGerm = 3)\ninclude xWGerm_ord_eq_three in\nprivate theorem xCoordinateGermOrders')
b=b.replace('  xCoordinateGermOrders.1','  (xCoordinateGermOrders xWGerm_ord_eq_three).1').replace('  xCoordinateGermOrders.2','  (xCoordinateGermOrders xWGerm_ord_eq_three).2')
b=b.replace('/-- The actual Y/X germ is','include xWGerm_ord_eq_three in\n/-- The actual Y/X germ is').replace('/-- The actual Z/X germ vanishes','include xWGerm_ord_eq_three in\n/-- The actual Z/X germ vanishes')
b=b.replace('end MazurProof.N25F_XCoordinateOrders','''#check @xYGerm_ord_eq_one
#check @xZGerm_ord_eq_two
#print axioms xYGerm_ord_eq_one
#print axioms xZGerm_ord_eq_two
end MazurProof.N25F_XCoordinateOrders''')
(r/'XCoordinateOrdersCheck.lean').write_text(x+'\n'+b)
