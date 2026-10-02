from pathlib import Path
r=Path('/workspace/shared/flt-n25-xqz-order')
a=Path('/workspace/shared/flt-n25-xcoordinate-orders/XCoordinateOrdersCheck.lean').read_text()
b=Path('/workspace/shared/flt-n25-xboundary-order/XBoundaryOrderCheck.lean').read_text();b=b[b.index('namespace MazurProof.N25F_XLocalFractionEmbedding'):b.index('#check @MazurProof.N25F_XBoundaryOrder')]
c=(r/'N25F_XBoundaryZOrder.lean').read_text();c=c[c.index('namespace MazurProof.N25F_XBoundaryZOrder'):]
c=c.replace(' N25F_ZChartFractionMap','')
c=c.replace('local notation "K" => FractionRing W','''local notation "K" => FractionRing W
variable [IsDedekindDomain W]
variable (xWGerm_ord_eq_three : Ring.ord XLocalRing xWGerm = 3)
variable (fraction_qz_ne_zero : algebraMap W K qz ≠ 0)
''')
c=c.replace('theorem xZGerm_ne_zero','include fraction_qz_ne_zero in\ntheorem xZGerm_ne_zero').replace('have hord := xZGerm_ord_eq_two','have hord := xZGerm_ord_eq_two xWGerm_ord_eq_three')
c=c.replace('theorem xLocalFractionOrder_xZGerm','include xWGerm_ord_eq_three fraction_qz_ne_zero in\ntheorem xLocalFractionOrder_xZGerm').replace('xZGerm xZGerm_ne_zero 2 xZGerm_ord_eq_two','xZGerm (xZGerm_ne_zero fraction_qz_ne_zero) 2 (xZGerm_ord_eq_two xWGerm_ord_eq_three)')
c=c.replace('/-- Z/W =','include xWGerm_ord_eq_three in\n/-- Z/W =')
c=c.replace('map_div₀, xLocalFractionOrder_xZGerm, xLocalFractionOrder_xWGerm,','map_div₀, xLocalFractionOrder_xZGerm xWGerm_ord_eq_three fraction_qz_ne_zero, xLocalFractionOrder_xWGerm xWGerm_ord_eq_three,')
c=c.replace('end MazurProof.N25F_XBoundaryZOrder','''#check @xBoundaryOrder_qz
#print axioms xLocalToFraction_xZGerm
#print axioms xZGerm_ne_zero
#print axioms xLocalFractionOrder_xZGerm
#print axioms xBoundaryOrder_qz
end MazurProof.N25F_XBoundaryZOrder''')
(r/'XBoundaryZOrderCheck.lean').write_text(a+'\n'+b+'\n'+c)
