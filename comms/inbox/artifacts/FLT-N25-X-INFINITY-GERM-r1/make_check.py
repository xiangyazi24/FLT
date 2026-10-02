from pathlib import Path
r=Path('/workspace/shared/flt-n25-x-infinity-germ')
s=(r/'N25F_XInfinityGerm.lean').read_text().replace('import FLT.Assumptions.MazurProof.N25F_XBoundaryZOrder','import XBoundaryZOrderCheck')
s=s.replace(' N25F_ZChartFractionMap','')
s=s.replace('local notation "K" => FractionRing W','''local notation "K" => FractionRing W
variable [IsDedekindDomain W]
variable (hord : Ring.ord XLocalRing xWGerm = 3)
variable (fraction_qz_ne_zero : algebraMap W K qz ≠ 0)
''')
s=s.replace('/-- In the actual X-boundary','include hord in\n/-- In the actual X-boundary').replace('xZGerm_ord_eq_two, xWGerm_ord_eq_three','xZGerm_ord_eq_two hord, hord')
# Thread only the existing order and coordinate-nonzero fixture parameters.
s=s.replace('Classical.choose xZGerm_dvd_xWGerm','Classical.choose (xZGerm_dvd_xWGerm hord)').replace('Classical.choose_spec xZGerm_dvd_xWGerm','Classical.choose_spec (xZGerm_dvd_xWGerm hord)')
import re
for name in ['xInverseZGerm','xZGerm_mul_xInverseZGerm']:
 # Don't change each declaration's binder name; all other references carry hord.
 s=re.sub(r'\b'+name+r'\b',lambda m: '('+name+' hord)',s)
 s=s.replace('def ('+name+' hord)', 'def '+name).replace('theorem ('+name+' hord)','theorem '+name)
s=s.replace('xZGerm_ne_zero','(xZGerm_ne_zero fraction_qz_ne_zero)')
s=s.replace('/-- The constructed germ','include fraction_qz_ne_zero in\n/-- The constructed germ').replace('/-- The reciprocal base-parameter germ','include fraction_qz_ne_zero in\n/-- The reciprocal base-parameter germ').replace('/-- The actual reciprocal base parameter','include fraction_qz_ne_zero in\n/-- The actual reciprocal base parameter')
s=s.replace('rw [xLocalToFraction_xInverseZGerm,','rw [xLocalToFraction_xInverseZGerm hord fraction_qz_ne_zero,')
s=s.replace('mem_nonZeroDivisors_iff_ne_zero.mpr xInverseZGerm_ne_zero','mem_nonZeroDivisors_iff_ne_zero.mpr (xInverseZGerm_ne_zero hord fraction_qz_ne_zero)')
s=s.replace('end MazurProof.N25F_XInfinityGerm','''#check @xInverseZGerm_ord_eq_one
#print axioms xZGerm_dvd_xWGerm
#print axioms xInverseZGerm
#print axioms xZGerm_mul_xInverseZGerm
#print axioms xLocalToFraction_xInverseZGerm
#print axioms xInverseZGerm_ne_zero
#print axioms xInverseZGerm_ord_eq_one
end MazurProof.N25F_XInfinityGerm''')
(r/'XInfinityGermCheck.lean').write_text(s)
